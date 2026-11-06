(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Qx2n Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx QhAd QVbl QQLG QQRC Q91D QCa8 QkTt Qy8Z Q8l1 QROt QZxv Q5m9 QXfH QzQg Q6Iq QSsB Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

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
Import Q6Iq.Mq3.
Import QSsB.Mq4.
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
Variables (joff_1463 joff_1467 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_197bc e_multf3 e_floatsitf e_divtf3 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1463 : decode_any (Z_to_bv 32 w_1463) = Some (Jal 1 joff_1463, 4%Z).
Hypothesis E_1463 : is_ecall (Z_to_bv 32 w_1463) = false.
Hypothesis D_1467 : decode_any (Z_to_bv 32 w_1467) = Some (Jal 1 joff_1467, 4%Z).
Hypothesis E_1467 : is_ecall (Z_to_bv 32 w_1467) = false.
Hypothesis LINK_1463 : gw_anch (base + 5852 + bv_signed joff_1463)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1467 : gw_anch (base + 5868 + bv_signed joff_1467)%Z (e_floatsitf + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

Local Definition gw_tbl_0 := tt.

Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_0)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_1)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_2)))).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_3)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_4)))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_5)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_6)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_7)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_8)))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_9)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_10)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_11)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_12)))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QSsB.Mq4.ssJ STRING_READ) ssJ (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_13))))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QSsB.Mq4.RFJ STRING_READ) RFJ (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_14))))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QSsB.Mq4.RFI STRING_READ) RFI (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_15))))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QSsB.Mq4.RERRNO RATP) RERRNO (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_16))).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QSsB.Mq4.Wfs RATP) Wfs (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_17))).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QSsB.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_18))))))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QSsB.Mq4.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_19))).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QSsB.Mq4.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_20))).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QSsB.Mq4.framL segs RATP) framL (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_21))).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QSsB.Mq4.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_22))).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_23)))).
Definition hinv : ltac:(gw_rebind_ty (@Q6Iq.Mq3.hinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.hinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@Q6Iq.Mq3.hinv segs got_ssp RATP ssp_guard) hinv gw_tbl_24).
Definition S_HEX : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_HEX segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_HEX segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@Q6Iq.Mq3.S_HEX segs base got_ssp RATP STRING_READ ssp_guard) S_HEX gw_tbl_25).
Definition hxfr : ltac:(gw_rebind_ty (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QSsB.Mq4.hxfr segs) hxfr gw_tbl_26).
Definition hxinv : ltac:(gw_rebind_ty (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) hxinv gw_tbl_27).
Definition SHLZn : ltac:(gw_rebind_ty (@QSsB.Mq4.SHLZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QSsB.Mq4.SHLZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QSsB.Mq4.SHLZn segs base got_ssp RATP STRING_READ ssp_guard) SHLZn gw_tbl_28).
Definition S_HLZ : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HLZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HLZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QSsB.Mq4.S_HLZ segs base got_ssp RATP STRING_READ ssp_guard) S_HLZ gw_tbl_29).
Definition S_H778 : ltac:(gw_rebind_ty (@QSsB.Mq4.S_H778 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_H778 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QSsB.Mq4.S_H778 segs base got_ssp RATP STRING_READ ssp_guard) S_H778 gw_tbl_30).
Definition S_H720 : ltac:(gw_rebind_ty (@QSsB.Mq4.S_H720 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_H720 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QSsB.Mq4.S_H720 segs base got_ssp RATP STRING_READ ssp_guard) S_H720 gw_tbl_31).
Definition SHRZn : ltac:(gw_rebind_ty (@QSsB.Mq4.SHRZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QSsB.Mq4.SHRZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QSsB.Mq4.SHRZn segs base got_ssp RATP STRING_READ ssp_guard) SHRZn gw_tbl_32).
Definition S_HRZ : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HRZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HRZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QSsB.Mq4.S_HRZ segs base got_ssp RATP STRING_READ ssp_guard) S_HRZ gw_tbl_33).
Definition S_H7F0 : ltac:(gw_rebind_ty (@QSsB.Mq4.S_H7F0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_H7F0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QSsB.Mq4.S_H7F0 segs base got_ssp RATP STRING_READ ssp_guard) S_H7F0 gw_tbl_34).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb8_c8_in) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb8_c8_in)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__Wfs := Wfs (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsH0__S_HEX := S_HEX (only parsing).
Notation F_fsX0__SHLZn := SHLZn (only parsing).
Notation F_fsX0__S_H720 := S_H720 (only parsing).
Notation F_fsX0__S_H778 := S_H778 (only parsing).
Notation F_fsX0__S_H7F0 := S_H7F0 (only parsing).
Notation F_fsX0__S_HLZ := S_HLZ (only parsing).
Notation F_fsX0__S_HRZ := S_HRZ (only parsing).
Notation F_fsX0__hxfr := hxfr (only parsing).
Notation F_fsX0__hxinv := hxinv (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 got_ssp RATP STRING_READ ssp_guard e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec.

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

Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QzQg.Mq0.Fok F).

Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

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

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.

#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

#[using="rf_getc_slow Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof. clear - rf_getc_slow Hp T1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.

#[using="Type"] Lemma rfj_ns : forall kmin c f, RFJ' kmin c f -> sh_stdio f = false /\ sh_shlim_neg f = false.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct (sh_stdio f) eqn:E.
- destruct (SS eq_refl) as (_ & _ & _ & _ & [_ FF]). destruct FF.
- split; [reflexivity|]. exact (proj1 (NS eq_refl)).
Qed.
#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="Type"] Lemma RFJ_rechar : forall kmin c c' f, RFJ' kmin c f -> (-1 <= c' < 256)%Z -> (c' <> 0%Z -> sh_rpos f <= p)%Z -> RFJ' kmin c' f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hr. split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. exact Hr.
Qed.
#[using="Type"] Lemma RFJ_weak : forall kmin k' c f, RFJ' kmin c f -> (k' <= kmin)%Z -> RFJ' k' c f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin k' c f (OK & Rc & CC & KM & NS & SS) Hk. split; [exact OK|]. split; [exact Rc|]. split; [exact CC|]. split; [intros E; specialize (KM E); lia|]. split; [exact NS | exact SS].
Qed.
#[using="RFI_unget rf_unget_eq Hp"] Lemma RFJ_ungetn : forall n kmin c f, RFJ' kmin c f -> sh_shlim_neg f = false -> (Z.of_nat n <= kmin)%Z ->
RFJ' (kmin - Z.of_nat n) c (fs_unget_loop n f).
Proof. clear - RFI_unget rf_unget_eq Hp ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - Hp RFI_unget rf_unget_eq. induction n as [|n IH]; intros kmin c f RJ Hsn Hn.
- replace (kmin - Z.of_nat 0)%Z with kmin by lia. exact RJ.
- cbn [fs_unget_loop]. replace (kmin - Z.of_nat (S n))%Z with ((kmin - 1) - Z.of_nat n)%Z by lia.
apply IH; [ exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(lia)) | rewrite (rf_unget_eq f Hsn); exact Hsn | lia ].
Qed.

Ltac c8ify_all H := repeat (lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l' end in
go constr:(@nil cell) cs end).

Ltac read_char_at r :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read segs _ T (zbytes txt) r _ _ BY (Qy5Y.zbytes_nth txt r ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt r)) by lia; clear RDb end.

Local Notation S_HEX := (@F_fsH0__S_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_hinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Local Notation S_HLZ := (@F_fsX0__S_HLZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H778 := (@F_fsX0__S_H778 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H720 := (@F_fsX0__S_H720 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_HRZ := (@F_fsX0__S_HRZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H7F0 := (@F_fsX0__S_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := gw_expose got_ssp; gw_expose ssp_guard; unfold F_fsX0__hxinv, F_floatscan_common__Wfs, FS_DEPTH, RERRNO;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold F_fsX0__hxfr; first [hyp | hyp_cells].

Ltac hx_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Hypothesis HS_H7F0 : S_H7F0.

#[using="Type"] Lemma lz_some_S : forall n g c f r, df_lz_loop n (g, c, f) = Some r ->
exists n', n = S n' /\ df_lz_loop n (g, c, f) = (if (c =? 48)%Z then df_lz_loop n' (1%Z, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f)).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_H7F0. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_H7F0 | gw_hide HS_H7F0 | idtac].
clear. intros [|n'] g c f r H; [discriminate H|]. exists n'. split; [reflexivity|].
rewrite df_lz_loop_S. unfold df_lz_body. rewrite (surjective_pairing (sh_getc f)). reflexivity.
Qed.
#[using="Type"] Lemma rz_some_S : forall n g l c f r, df_rz_loop n (g, l, c, f) = Some r ->
exists n', n = S n' /\ df_rz_loop n (g, l, c, f) = (if (c =? 48)%Z then df_rz_loop n' (1%Z, (l - 1)%Z, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f)).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_H7F0. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_H7F0 | gw_hide HS_H7F0 | idtac].
clear. intros [|n'] g l c f r H; [discriminate H|]. exists n'. split; [reflexivity|].
rewrite df_rz_loop_S. unfold df_rz_body. rewrite (surjective_pairing (sh_getc f)). reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_HRZ : S_HRZ.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ HI HF RJ Hk FOK FRM' Hsg Hst Rrp0 HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
site_facts FC RJ kmin 48%Z f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n' & En & HL'). injection En as En'. subst n'. change (48 =? 48)%Z with true in HL'. cbv iota in HL'. rewrite HL' in HL. clear HL'.
assert (Z48 : 48%Z <> 0%Z) by lia.
hx_read FC RJ kmin 48%Z f Z48.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply IH; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
- assert (N48 : c'' <> 48%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <- <-.
zs. zs. zs.
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold QSsB.Mq4.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_H720 : S_H720.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until gd. intros _ HI HF RJ Hk FOK FRM' Hsg Hst Hc0 Rg HK.
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
unfold HX_rz in HK. destruct (df_rz_loop fuelc _) as [[[[gd' rp'] c3] f3]|] eqn:HL; [|discriminate HK].
zs. zs. zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply (L_HRZ fuelc); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
- assert (N48 : c'' <> 48%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <- <-.
zs. zs. zs.
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold QSsB.Mq4.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_H778 : S_H778.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ HI HF RJ Hk FOK FRM' Hsg Hst Rcb HK.
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
unfold HX_alz in HK.
zs. zs. brf K1.
-
assert (N46 : c <> 46%Z) by (clear - K1 Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46).
zs. zs. zs.
stmt HS_H7F0. eapply NX; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold QSsB.Mq4.kminH; flia).
- assert (E46 : c = 46%Z) by (clear - K1 Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E46, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E46 in RJ.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
ufc2 FC. zs. zs. zs. zs. (brf K2; [ | exfalso; lia ]).
eapply L_H720; try eassumption; try flia; try mk_hxinv; try mk_hxfr.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_HLZ : S_HLZ.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ HI HF RJ Hk FOK FRM' Hsg Hst HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
site_facts FC RJ kmin 48%Z f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
destruct (lz_some_S _ _ _ _ _ HL) as (n' & En & HL'). injection En as En'. subst n'. change (48 =? 48)%Z with true in HL'. cbv iota in HL'. rewrite HL' in HL. clear HL'.
assert (Z48 : 48%Z <> 0%Z) by lia.
hx_read FC RJ kmin 48%Z f Z48.
set (c'' := znth txt (sh_rpos f)) in *.
zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply IH; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
- assert (N48 : c'' <> 48%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <-.
stmt L_H778. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_H7F0"] Lemma L_HEX : S_HEX.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ HI RJ Hk FOKR FRM' Hsg Hst Hcx HM.
pose proof HI as HI0. dest_hinv HI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
rewrite hexfloat_m_eq in HM.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in Hcx; discriminate Hcx).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *. cbv beta iota zeta in HM.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
assert (FOK : Fok Ft) by (intros kk H8 H10 H14 H15; apply FOKR; assumption).

zs. carve_frame 176%nat ST. rename FR into HFR.
do 14 zs.
lazymatch type of HFR with rw_cells _ _ _ (CB 64 ?jk :: ?rest) =>
apply (rw_cells_split_CB _ _ _ [] 64 jk rest [8;8;8;8;8;8;8;8]%nat) in HFR; [|reflexivity] end.
cbn [mk_CB_cells app] in HFR. c8ify_all HFR.
lazymatch type of HFR with rw_cells _ _ _ (C8 ?b0 :: C8 ?b1 :: C8 ?b2 :: C8 ?b3 :: C8 ?b4 :: C8 ?b5 :: C8 ?b6 :: C8 ?b7 :: _) =>
set (w0 := b0) in HFR; set (w8 := b1) in HFR; set (w16 := b2) in HFR; set (w24 := b3) in HFR;
set (w32 := b4) in HFR; set (w40 := b5) in HFR; set (w48 := b6) in HFR; set (w56 := b7) in HFR;
clearbody w0 w8 w16 w24 w32 w40 w48 w56 end.
match goal with H : list byte |- _ => try clear H end.
rewrite (FOKR 8 ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; lia)) in HFR.
zs. zs. zs. zs. zs.

zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs.

ufc2 FC. zs. zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
unfold HX_lz in HM. destruct (df_lz_loop fuelc _) as [[[gd' c3] f3]|] eqn:HL; [|discriminate HM].
zs. zs. zs. brf K1.
-
assert (E46 : c'' = 46%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. rewrite E46 in HL. change (46 =? 48)%Z with false in HL. injection HL as <- <- <-.
unfold HX_alz in HM. change (46 =? 48)%Z with false in HM. cbn [Z.eqb Pos.eqb] in HM. rewrite (surjective_pairing (sh_getc _)) in HM. rewrite E46 in RJ1.
zs.
destruct (Z.eq_dec (T + (sh_rpos f + 1))%Z (rf_rend T p true f)) as [SLOW2|FAST2];
[exfalso; exact (rf_slow_false _ _ _ RJ1 SLOW2)|].
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
replace (Z_to_bv 64 (T + sh_rpos f + 1)) with (Z_to_bv 64 (T + sh_rpos (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)))) by (cbn [sh_rpos]; f_equal; lia).
stmt L_H720. eapply NX with (kmin := (kmin + 1)%Z) (gd := 0%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
- assert (N46 : c'' <> 46%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
zs. zs. zs. zs. zs. brf K2.
+
assert (N48 : c'' <> 48%Z) by (clear - K2 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec; rewrite ?land_W64 in K2; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-.
unfold HX_alz in HM. replace (c'' =? 46)%Z with false in HM by (symmetry; apply Z.eqb_neq; exact N46).
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold QSsB.Mq4.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
+
assert (E48 : c'' = 48%Z) by (clear - K2 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec; rewrite ?land_W64 in K2; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & En2 & HL2). rewrite HL2 in HL. rewrite E48, Z.eqb_refl in HL. rewrite E48 in RJ1.
assert (Z48 : 48%Z <> 0%Z) by lia.
pose proof (RFI_getc T txt p J BYT Hp Hnul (kmin + 1) 48 _ RJ1 Z48) as RJ2.
pose proof (getc_stdio (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) as Hst2. cbn [sh_stdio] in Hst2.
destruct (Z.eq_dec (T + (sh_rpos f + 1))%Z (rf_rend T p true f)) as [SLOW2|FAST2];
[exfalso; exact (rf_slow_false _ _ _ RJ1 SLOW2)|].
pose proof (rf_getc_fast_lt T txt p J Hp (kmin + 1) 48 _ RJ1 Z48 FAST2) as LT2. cbn [sh_rpos] in LT2.
rewrite (rf_getc_fast T txt p J Hp (kmin + 1) 48 _ RJ1 FAST2) in *. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *.
pose proof (txt_char (sh_rpos f + 1) ltac:(unfold zlength in *; lia)) as Rch2.
zs. zs. zs. (brf K3; [ exfalso; lia | ]). zs. zs0.
read_char_at (sh_rpos f + 1)%Z.
set (c4 := znth txt (sh_rpos f + 1)) in *.
zs. zs. brf K4.
*
assert (E48' : c4 = 48%Z) by (clear - K4 Rch2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec; rewrite ?land_W64 in K4; Z.div_mod_to_equations; lia).
rewrite E48' in HL, RJ2.
pose proof (L_HLZ n2) as NX2; unfold F_fsX0__SHLZn in NX2. eapply NX2 with (kmin := (kmin + 1 + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst2; exact Hst).
* assert (N48' : c4 <> 48%Z) by (clear - K4 Rch2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1463 joff_1467 e_floatsitf CODE BASE4 BASER D_1463 E_1463 D_1467 E_1467 LINK_1463 LINK_1467 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec; rewrite ?land_W64 in K4; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n3 & _ & HL3). rewrite HL3 in HL. replace (c4 =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48'). injection HL as <- <- <-.
zs.
stmt L_H778. eapply NX with (kmin := (kmin + 1 + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst2; exact Hst).
Qed.
End Floatscan.

End G.
End Mq0.

Module Mq1.

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
Import Q6Iq.Mq3.
Import QSsB.Mq4.
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
Variables (hi_1618 : bv 20).
Variables (lo_1619 : bv 12).
Variables (joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 : bv 21).
Variables (G_10788 got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_197bc e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1589 : decode_any (Z_to_bv 32 w_1589) = Some (Jal 1 joff_1589, 4%Z).
Hypothesis E_1589 : is_ecall (Z_to_bv 32 w_1589) = false.
Hypothesis D_1595 : decode_any (Z_to_bv 32 w_1595) = Some (Jal 1 joff_1595, 4%Z).
Hypothesis E_1595 : is_ecall (Z_to_bv 32 w_1595) = false.
Hypothesis D_1600 : decode_any (Z_to_bv 32 w_1600) = Some (Jal 1 joff_1600, 4%Z).
Hypothesis E_1600 : is_ecall (Z_to_bv 32 w_1600) = false.
Hypothesis D_1607 : decode_any (Z_to_bv 32 w_1607) = Some (Jal 1 joff_1607, 4%Z).
Hypothesis E_1607 : is_ecall (Z_to_bv 32 w_1607) = false.
Hypothesis D_1611 : decode_any (Z_to_bv 32 w_1611) = Some (Jal 1 joff_1611, 4%Z).
Hypothesis E_1611 : is_ecall (Z_to_bv 32 w_1611) = false.
Hypothesis D_1618 : decode_any (Z_to_bv 32 w_1618) = Some (Auipc 10 hi_1618, 4%Z).
Hypothesis E_1618 : is_ecall (Z_to_bv 32 w_1618) = false.
Hypothesis D_1619 : decode_any (Z_to_bv 32 w_1619) = Some (FLoad FMT_D 10 10 lo_1619, 4%Z).
Hypothesis E_1619 : is_ecall (Z_to_bv 32 w_1619) = false.
Hypothesis D_1620 : decode_any (Z_to_bv 32 w_1620) = Some (Jal 1 joff_1620, 4%Z).
Hypothesis E_1620 : is_ecall (Z_to_bv 32 w_1620) = false.
Hypothesis D_1623 : decode_any (Z_to_bv 32 w_1623) = Some (Jal 1 joff_1623, 4%Z).
Hypothesis E_1623 : is_ecall (Z_to_bv 32 w_1623) = false.
Hypothesis D_1626 : decode_any (Z_to_bv 32 w_1626) = Some (Jal 1 joff_1626, 4%Z).
Hypothesis E_1626 : is_ecall (Z_to_bv 32 w_1626) = false.
Hypothesis ANCH_1619 : gw_anch (Z.shiftl (bv_signed hi_1618) 12 + (base + 6472) + bv_signed lo_1619)%Z G_10788.
Hypothesis LINK_1589 : gw_anch (base + 6356 + bv_signed joff_1589)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1595 : gw_anch (base + 6380 + bv_signed joff_1595)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1600 : gw_anch (base + 6400 + bv_signed joff_1600)%Z (e_divtf3 + 0)%Z.
Hypothesis LINK_1607 : gw_anch (base + 6428 + bv_signed joff_1607)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1611 : gw_anch (base + 6444 + bv_signed joff_1611)%Z (e_addtf3 + 0)%Z.
Hypothesis LINK_1620 : gw_anch (base + 6480 + bv_signed joff_1620)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_1623 : gw_anch (base + 6492 + bv_signed joff_1623)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1626 : gw_anch (base + 6504 + bv_signed joff_1626)%Z (e_addtf3 + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis RNG_G_10788 : gw_br G_10788 8.
Hypothesis ROM_G_10788 : ro_bytes segs G_10788 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 224; Z_to_bv 8 63].
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

Local Definition gw_tbl_0 := tt.

Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_0)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_1)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_2)))).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_3)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_4)))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_5)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_6)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_7)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_8)))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_9)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_10)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_11)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_12)))).
Definition getf2_post : ltac:(gw_rebind_ty (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.getf2_post segs) getf2_post (gw_ent (@QVbl.Mq1.getf2_post segs) getf2_post gw_tbl_13)).
Definition scalbn_post : ltac:(gw_rebind_ty (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.scalbn_post segs) scalbn_post (gw_ent (@Q91D.Mq4.scalbn_post segs) scalbn_post gw_tbl_14)).
Definition SCALBNL := (e_extendsftf2 + 1132)%Z.
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.SCALBNL e_extendsftf2) SCALBNL (gw_ent (@QQRC.Mq2.SCALBNL e_extendsftf2) SCALBNL gw_tbl_15)).
Definition COPYSIGNL := (e_extendsftf2 + 348)%Z.
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.COPYSIGNL e_extendsftf2) COPYSIGNL (gw_ent (@QQRC.Mq2.COPYSIGNL e_extendsftf2) COPYSIGNL gw_tbl_16)).
Definition FABSL := (e_extendsftf2 + 1120)%Z.
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.FABSL e_extendsftf2) FABSL (gw_ent (@QQRC.Mq2.FABSL e_extendsftf2) FABSL gw_tbl_17)).
Definition leafq_post : ltac:(gw_rebind_ty (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.leafq_post segs) leafq_post (gw_ent (@QQRC.Mq2.leafq_post segs) leafq_post gw_tbl_18)).
Definition scalbnl_post : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.scalbnl_post segs) scalbnl_post (gw_ent (@QQRC.Mq2.scalbnl_post segs) scalbnl_post gw_tbl_19)).
Definition scalbnl_stmt : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt (gw_ent (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt gw_tbl_20)).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_21)))).
Definition leaf1_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Qy8Z.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Q8l1.Mq0.leaf1_post segs) leaf1_post gw_tbl_22))).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.call2_post segs) call2_post (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post (gw_ent (@Q8l1.Mq0.call2_post segs) call2_post (gw_ent (@QQRC.Mq2.call2_post segs) call2_post gw_tbl_23)))).
Definition FMODL := (e_extendsftf2 + 388)%Z.
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.FMODL e_extendsftf2) FMODL (gw_ent (@Q8l1.Mq0.FMODL e_extendsftf2) FMODL gw_tbl_24)).
Definition rfmodl_post : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.rfmodl_post segs) rfmodl_post (gw_ent (@Q8l1.Mq0.rfmodl_post segs) rfmodl_post gw_tbl_25)).
Definition rfmodl_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt (gw_ent (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt gw_tbl_26)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QSsB.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_27))))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QSsB.Mq4.ssJ STRING_READ) ssJ (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_28))))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QSsB.Mq4.RFJ STRING_READ) RFJ (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_29))))).
Definition calla_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.calla_post segs) calla_post (gw_ent (@Qy8Z.Mq0.calla_post segs) calla_post gw_tbl_30)).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QSsB.Mq4.RFI STRING_READ) RFI (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_31))))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QSsB.Mq4.RERRNO RATP) RERRNO (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_32))).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QSsB.Mq4.Wfs RATP) Wfs (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_33))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QSsB.Mq4.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_34))).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_35)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_35)).
Local Definition gw_tbl_36 := (gw_ent (@QSsB.Mq4.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_35))).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_36)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_36)).
Local Definition gw_tbl_37 := (gw_ent (@QSsB.Mq4.framL segs RATP) framL (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_36))).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QSsB.Mq4.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_37))).
Definition hxfr : ltac:(gw_rebind_ty (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QSsB.Mq4.hxfr segs) hxfr gw_tbl_38).
Definition hxinv : ltac:(gw_rebind_ty (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_39)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_39)).
Local Definition gw_tbl_40 := (gw_ent (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) hxinv gw_tbl_39).
Definition S_H7F0 : ltac:(gw_rebind_ty (@QSsB.Mq4.S_H7F0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_40)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_H7F0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_40)).
Local Definition gw_tbl_41 := (gw_ent (@QSsB.Mq4.S_H7F0 segs base got_ssp RATP STRING_READ ssp_guard) S_H7F0 gw_tbl_40).
Definition SHDn : ltac:(gw_rebind_ty (@QSsB.Mq4.SHDn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_41)) := ltac:(gw_rebind_tm (@QSsB.Mq4.SHDn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_41)).
Local Definition gw_tbl_42 := (gw_ent (@QSsB.Mq4.SHDn segs base got_ssp RATP STRING_READ ssp_guard) SHDn gw_tbl_41).
Definition S_HD : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HD segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_42)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HD segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_42)).
Local Definition gw_tbl_43 := (gw_ent (@QSsB.Mq4.S_HD segs base got_ssp RATP STRING_READ ssp_guard) S_HD gw_tbl_42).
Definition S_HTL : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HTL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_43)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HTL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_43)).
Local Definition gw_tbl_44 := (gw_ent (@QSsB.Mq4.S_HTL segs base got_ssp RATP STRING_READ ssp_guard) S_HTL gw_tbl_43).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis divtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQRC.divtf3_spec segs e_divtf3) 9%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in exact T).
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs e_addtf3) 5%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QDXD.Mq0.addtf3_post segs) addtf3_post in exact T).  Arguments addtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).

Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition div_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.div_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.div_callE)).
Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition extenddftf2_callF : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.extenddftf2_callF) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.extenddftf2_callF)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsX0__SHDn := SHDn (only parsing).
Notation F_fsX0__S_H7F0 := S_H7F0 (only parsing).
Notation F_fsX0__S_HD := S_HD (only parsing).
Notation F_fsX0__S_HTL := S_HTL (only parsing).
Notation F_fsX0__hxfr := hxfr (only parsing).
Notation F_fsX0__hxinv := hxinv (only parsing).

#[using="G_10788 got_ssp RATP STRING_READ ssp_guard e_197bc e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 got_ssp RATP STRING_READ ssp_guard e_197bc e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec.

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

Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QzQg.Mq0.Fok F).
Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).

Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].

Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.

#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

#[using="rf_getc_slow Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof. clear - rf_getc_slow Hp T1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.

#[using="Type"] Lemma rfj_ns : forall kmin c f, RFJ' kmin c f -> sh_stdio f = false /\ sh_shlim_neg f = false.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct (sh_stdio f) eqn:E.
- destruct (SS eq_refl) as (_ & _ & _ & _ & [_ FF]). destruct FF.
- split; [reflexivity|]. exact (proj1 (NS eq_refl)).
Qed.
#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="Type"] Lemma RFJ_rechar : forall kmin c c' f, RFJ' kmin c f -> (-1 <= c' < 256)%Z -> (c' <> 0%Z -> sh_rpos f <= p)%Z -> RFJ' kmin c' f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hr. split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. exact Hr.
Qed.
#[using="Type"] Lemma RFJ_weak : forall kmin k' c f, RFJ' kmin c f -> (k' <= kmin)%Z -> RFJ' k' c f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin k' c f (OK & Rc & CC & KM & NS & SS) Hk. split; [exact OK|]. split; [exact Rc|]. split; [exact CC|]. split; [intros E; specialize (KM E); lia|]. split; [exact NS | exact SS].
Qed.
#[using="RFI_unget rf_unget_eq Hp"] Lemma RFJ_ungetn : forall n kmin c f, RFJ' kmin c f -> sh_shlim_neg f = false -> (Z.of_nat n <= kmin)%Z ->
RFJ' (kmin - Z.of_nat n) c (fs_unget_loop n f).
Proof. clear - RFI_unget rf_unget_eq Hp ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - Hp RFI_unget rf_unget_eq. induction n as [|n IH]; intros kmin c f RJ Hsn Hn.
- replace (kmin - Z.of_nat 0)%Z with kmin by lia. exact RJ.
- cbn [fs_unget_loop]. replace (kmin - Z.of_nat (S n))%Z with ((kmin - 1) - Z.of_nat n)%Z by lia.
apply IH; [ exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(lia)) | rewrite (rf_unget_eq f Hsn); exact Hsn | lia ].
Qed.

Local Notation S_H7F0 := (@F_fsX0__S_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation SHDn := (@F_fsX0__SHDn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HD := (@F_fsX0__S_HD ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HTL := (@F_fsX0__S_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation hxfr := (@F_fsX0__hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@F_fsX0__hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation SC0 := (f128_of_i32 1).

Notation HX_tail' := (HX_tail fuelc 53 (-1074)).

Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := gw_expose got_ssp; gw_expose ssp_guard; unfold F_fsX0__hxinv, F_floatscan_common__Wfs, FS_DEPTH, RERRNO;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold F_fsX0__hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Ltac hx_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Ltac hx_side := lazymatch goal with
| |- F_fsX0__hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- F_fsX0__hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- QSsB.Mq4.kminH _ _ _ => unfold QSsB.Mq4.kminH; flia
| |- QSsB.Mq4.hxI _ _ _ _ _ _ _ _ => unfold QSsB.Mq4.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- _ => idtac end.

Hypothesis HS_HTL : S_HTL.

#[using="Type"] Lemma ishexc_iff : forall c, (0 <= c < 256)%Z ->
(ishexc c = true <-> (48 <= c <= 57 \/ 65 <= c <= 70 \/ 97 <= c <= 102))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HTL. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HTL | gw_hide HS_HTL | idtac].
clear. intros c Hc.
pose proof (forallb_range (fun c => Bool.eqb (ishexc c) (((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102))))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply Bool.eqb_prop in E. rewrite E.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le. tauto.
Qed.
#[using="Type"] Lemma isdigitc_iff' : forall c, (0 <= c < 256)%Z -> (isdigitc c = true <-> (48 <= c <= 57))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HTL. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HTL | gw_hide HS_HTL | idtac].
clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. change (2 ^ 32)%Z with 4294967296%Z. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma lor32_letter : forall c, (65 <= c <= 70 \/ 97 <= c <= 102)%Z -> (97 <= Z.lor c 32 <= 102)%Z /\ (Z.lor c 32 = c \/ Z.lor c 32 = c + 32)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HTL. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HTL | gw_hide HS_HTL | idtac].
clear. intros c Hc.
assert (R : (0 <= c < 256)%Z) by lia.
pose proof (forallb_range (fun c => implb (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102)))%Z
(((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102)) && ((Z.lor c 32 =? c) || (Z.lor c 32 =? c + 32))))%Z 256 ltac:(vm_compute; reflexivity) c R) as E.
cbv beta in E.
replace (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102)))%Z with true in E by (symmetry; rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le; lia).
cbn [implb] in E. rewrite !Bool.andb_true_iff, Bool.orb_true_iff, !Z.leb_le, !Z.eqb_eq in E. lia.
Qed.
Ltac kswrap K := rewrite swrap32_small in K by lia; rewrite land_W64 in K.

#[using="Type"] Lemma x16_step : forall x d, (0 <= x < 2^32)%Z -> (0 <= d < 16)%Z ->
Z_to_bv 64 (bv_swrap 32 (d + Z.land (Z.shiftl (Z.land (sext32 x) 18446744073709551615) 4) 18446744073709551615)) = Z_to_bv 64 (sext32 (u32 (x * 16 + d))).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HTL. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HTL | gw_hide HS_HTL | idtac].
clear. intros x d Hx Hd. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite !land_W64, Z.shiftl_mul_pow2 by lia. change (2^4)%Z with 16%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low x) as L. pose proof (sext32_range x) as R. rewrite (Z.mod_small x) in L by lia.
set (S := sext32 x) in *. clearbody S.
Z.div_mod_to_equations. nia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1"] Lemma L_HBODY : forall n, SHDn n ->
forall m (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc d : Z) (s' : st_hex),
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc -> c <> 0%Z -> (0 <= d <= 15)%Z ->
(let '(x', y', sc', gt') :=
(if dc <=? 7 then (u32 (x * 16 + d), y, sc, gt)
else if dc <=? 29 then
let df := f128_of_i32 d in let c16 := f128_of_i32 16 in let sc := f128_div sc c16 in let t := f128_mul df sc in
(x, f128_add t y, sc, gt)
else if nz d && negb (nz gt) then
let h := f128_of_d (bv_unsigned D_05) in let t := f128_mul h sc in (x, f128_add t y, sc, 1)
else (x, y, sc, gt))%Z in
hx_dig_loop n (mkHX (fst (sh_getc f)) (snd (sh_getc f)) x' y' sc' gt' gr 1 rp (dc + 1))) = Some s' ->
HX_tail' sign pok (hx_c s') (hx_f s') (hx_x s') (hx_y s') (hx_gr s') (hx_gd s') (hx_rp s') (hx_dc s') = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) x10 (Z_to_bv 64 d) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x18b4)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SG2 SG3 FRM HS_HTL. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HTL | gw_hide HS_HTL | idtac].
intros n IH. intros until s'. intros HI HF RJ HKM FOK FRM' Hsg Hst HXI Hc0 Rd HLB HK.
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range sc) as Rsl. pose proof (hi64_range sc) as Rsh.

assert (NEXTC : forall m2 (x1' x5' x6' x7' x8' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) Ft2 fct2 ev2 (x2 y2 sc2 gt2 : Z),
hxinv m2 ev2 f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt2) (Z_to_bv 64 (lo64 sc2)) m2 ->
Fok Ft2 -> frm0 fct2 -> (0 <= x2 < 2^32)%Z -> (0 <= gt2 <= 1)%Z ->
hx_dig_loop n (mkHX (znth txt (sh_rpos f)) (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) x2 y2 sc2 gt2 gr 1 rp (dc + 1)) = Some s' ->
evt segs POST
(MS (mkR x1' HSP gp TPv x5' x6' x7' x8' (Z_to_bv 64 gr) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x2)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y2)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc2)) x28' x29' x30' x31')
Ft2 (Z_to_bv 64 (base + 0x197c)) fct2 None m2 (seg_rom segs))).
{ intros until gt2. intros HI2 HF2 FOK2 FRM2 Rx2 Rgt2 HL2.
pose proof HI2 as HI3. dest_hxinv HI3. unfold F_fsX0__hxfr in HF2.
match goal with H : rw_cells _ m2 Fp _ |- _ => rename H into FC2 end. ufc2 FC2.
zs. zs. zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isdigitc_iff' c'' Rch) as DIF.
zs. zs. zs. brf K1; kswrap K1.
-
assert (D : isdigitc c'' = true) by (apply (proj2 DIF); clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia).
assert (Hc1 : c'' <> 0%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia).
eapply (IH (base + 0x18ac)%Z); try eassumption. all: hx_side.
- assert (ND : isdigitc c'' = false) by (destruct (isdigitc c''); [exfalso; pose proof (proj1 DIF eq_refl) as DD; clear - K1 Rch DD w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia | reflexivity]).
eapply (IH (base + 0x19a8)%Z); try eassumption. all: hx_side. }

zs. zs. brf K1.
-
replace (dc <=? 7)%Z with false in HLB by (symmetry; apply Z.leb_gt; lia).
zs. zs. brf K2; rewrite ?land_W64 in K2.
+
replace (dc <=? 29)%Z with false in HLB by (symmetry; apply Z.leb_gt; clear - K2 Rdc Rr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia).
zs. brf K3; rewrite ?land_W64 in K3.
*
assert (Ed : d = 0%Z) by (clear - K3 Rd w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia). rewrite Ed in HLB. cbn [nz Z.eqb negb andb] in HLB.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
* assert (Nd : d <> 0%Z) by (clear - K3 Rd w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia).
replace (nz d) with true in HLB by (unfold nz; symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Nd). cbn [andb] in HLB.
zs. zs. brf K4; rewrite ?land_W64 in K4.
--
assert (Eg : gt = 1%Z) by (clear - K4 Rgt w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia). replace (negb (nz gt)) with false in HLB by (rewrite Eg; reflexivity).
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
-- assert (Eg : gt = 0%Z) by (clear - K4 Rgt w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia). replace (negb (nz gt)) with true in HLB by (rewrite Eg; reflexivity). cbv zeta in HLB.
zs. zs.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D_05); [eassumption | simpF; reflexivity]).
set (Hv := f128_of_d (bv_unsigned D_05)) in *. pose proof (lo64_range Hv). pose proof (hi64_range Hv).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := Hv) (Y := sc); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Tv := f128_mul Hv sc) in *. pose proof (lo64_range Tv). pose proof (hi64_range Tv).
zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := Tv) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_add Tv y) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs. zs.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
+
replace (dc <=? 29)%Z with true in HLB by (symmetry; apply Z.leb_le; clear - K2 Rdc Rr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec segs base; Z.div_mod_to_equations; lia). cbv zeta in HLB.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (Dv := f128_of_i32 d) in *. pose proof (lo64_range Dv). pose proof (hi64_range Dv).
zs. zs. zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (C16 := f128_of_i32 16) in *. pose proof (lo64_range C16). pose proof (hi64_range C16).
zs. zs. zs. zs. zs.
hcall_split 112%Z (eapply div_callE with (X := sc) (Y := C16); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (SC2 := f128_div sc C16) in *. pose proof (lo64_range SC2). pose proof (hi64_range SC2).
zs. zs. zs. zs. zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := Dv) (Y := SC2); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Tv := f128_mul Dv SC2) in *. pose proof (lo64_range Tv). pose proof (hi64_range Tv).
zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := Tv) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_add Tv y) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
-
replace (dc <=? 7)%Z with true in HLB by (symmetry; apply Z.leb_le; lia).
zs. zs. zs. rewrite x16_step by lia.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok. apply u32_range.
Qed.

#[using="Type"] Lemma lor32_range : forall c, (0 <= c < 256)%Z -> (32 <= Z.lor c 32 < 256)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HTL. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HTL | gw_hide HS_HTL | idtac].
clear. intros c Hc.
pose proof (forallb_range (fun c => (32 <=? Z.lor c 32) && (Z.lor c 32 <? 256))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

#[using="Type"] Lemma lor32_af : forall c, (0 <= c < 256)%Z -> (97 <= Z.lor c 32 <= 102)%Z -> (65 <= c <= 70 \/ 97 <= c <= 102)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HTL. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HTL | gw_hide HS_HTL | idtac].
clear. intros c Hc HL.
pose proof (forallb_range (fun c => implb ((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102)) (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102))))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. replace ((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102))%Z with true in E by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia).
cbn [implb] in E. rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le in E. lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL"] Lemma L_HD : S_HD.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros n. induction n as [|n IH]; intros pc m; intros until s'; intros _ HI HF RJ HKM FOK FRM' Hsg Hst HXI HL HK Hpc; [discriminate HL|].
pose proof (L_HBODY n IH) as BODY.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold F_fsX0__hxfr in HF. bury_disj.
pose proof HXI as HXI0. destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). pose proof HKM as HKM0. destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range sc) as Rsl. pose proof (hi64_range sc) as Rsh.
rewrite hx_dig_loop_S in HL. unfold hx_dig_cond in HL. cbn [hx_c] in HL.
pose proof (ishexc_iff c Rcb) as HIF. pose proof (isdigitc_iff' c Rcb) as DIF. pose proof (lor32_range c Rcb) as RL.

assert (DIGIT : forall d, (ishexc c || (c =? 46))%Z = true -> c <> 46%Z -> d = (if (c <=? 57)%Z then (c - 48)%Z else (Z.lor c 32 - 87)%Z) -> (0 <= d <= 15)%Z ->
forall m1 (x12' x13' x14' : word), m1 = m ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) (Z_to_bv 64 d) x12' x13' x14' x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x18b4)) fct None m1 (seg_rom segs))).
{ intros d CND N46 Ed Rd m1 x12' x13' x14' ->. rewrite CND in HL. unfold hx_dig_body in HL.
replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N46). rewrite <- Ed in HL. cbv zeta in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
remember (if (dc <=? 7)%Z then _ else _) as U eqn:EU in HL.
destruct U as [[[x2 y2] sc2] gt2]. cbv beta iota in HL.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in CND; discriminate CND).
eapply BODY; try eassumption; try flia. rewrite <- EU. exact HL. }
destruct Hpc as [[-> D] | [-> ND]].
-
assert (R9 : (48 <= c <= 57)%Z) by (apply (proj1 DIF); exact D).
zs. (brf K1; [ | exfalso; lia ]).
replace (Z_to_bv 64 (bv_swrap 32 (c + -48))) with (Z_to_bv 64 (c - 48)%Z) by (rewrite swrap32_small by lia; f_equal; lia).
eapply DIGIT; [ apply Bool.orb_true_iff; left; apply (proj2 HIF); lia | lia | replace (c <=? 57)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity | lia | reflexivity ].
-
zs. zs. brf K1.
+
assert (E46 : c = 46%Z) by (clear - K1 Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c =? 46)%Z with true in HL by (rewrite E46; reflexivity). rewrite Bool.orb_true_r in HL. unfold hx_dig_body in HL.
replace (c =? 46)%Z with true in HL by (rewrite E46; reflexivity). cbv iota in HL.
zs. (brf K2; [ exfalso; lia | ]).
zs. brf K3; rewrite ?land_W64 in K3.
*
assert (Eg : gr = 1%Z) by (clear - K3 Rgr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia). replace (nz gr) with true in HL by (rewrite Eg; reflexivity). cbv iota in HL. injection HL as <-.
cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
stmt HS_HTL. eapply NX; try eassumption. all: hx_side.
* assert (Eg : gr = 0%Z) by (clear - K3 Rgr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia). replace (nz gr) with false in HL by (rewrite Eg; reflexivity). cbv iota in HL.
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
assert (Z46 : 46%Z <> 0%Z) by lia. rewrite E46 in RJ.
zs. zs.
hx_read FC RJ kmin 46%Z f Z46.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isdigitc_iff' c'' Rch) as DIF2.
zs. zs. zs. brf K4; kswrap K4.
-- assert (D2 : isdigitc c'' = true) by (apply (proj2 DIF2); clear - K4 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia).
eapply (IH (base + 0x18ac)%Z); try eassumption. all: hx_side.
-- assert (ND2 : isdigitc c'' = false) by (destruct (isdigitc c''); [exfalso; pose proof (proj1 DIF2 eq_refl) as DD; clear - K4 Rch DD w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia | reflexivity]).
eapply (IH (base + 0x19a8)%Z); try eassumption. all: hx_side.
+ assert (N46 : c <> 46%Z) by (clear - K1 Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
zs. zs. zs. brf K2; kswrap K2.
*
pose proof (lor32_af c Rcb ltac:(clear - K2 RL w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia)) as RLc.
zs. (brf K3; [ | exfalso; lia ]). zs. (brf K4; [ exfalso; lia | ]). zs.
replace (Z_to_bv 64 (bv_swrap 32 (Z.lor c 32 + -87))) with (Z_to_bv 64 (Z.lor c 32 - 87)%Z) by (rewrite swrap32_small by lia; f_equal; lia).
eapply DIGIT; [ apply Bool.orb_true_iff; left; apply (proj2 HIF); lia | exact N46
| replace (c <=? 57)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity | clear - K2 RL RLc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia | reflexivity ].
*
assert (NH : ishexc c = false).
{ destruct (ishexc c) eqn:E; [|reflexivity]. exfalso. pose proof (proj1 HIF eq_refl) as CC0.
destruct CC0 as [C1 | C23].
- apply (proj2 DIF) in C1. rewrite C1 in ND. discriminate ND.
- pose proof (lor32_letter c C23) as [A B]. clear - K2 A w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia. }
rewrite NH in HL. replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N46). cbn [orb] in HL. injection HL as <-.
cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
stmt HS_HTL. eapply NX; try eassumption. all: hx_side.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL"] Lemma L_H7F0 : S_H7F0.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until rp. intros _ HI HF RJ HKM FOK FRM' Hsg Hst Rcb Rgd Rgr Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (lo64_range Y0) as R0l. pose proof (hi64_range Y0) as R0h. pose proof (lo64_range SC0) as R1l. pose proof (hi64_range SC0) as R1h.
unfold HX_dig in HK. destruct (hx_dig_loop fuelc _) as [s'|] eqn:HL; [|discriminate HK].
destruct s' as [c9 f9 x9 y9 sc9 gt9 gr9 gd9 rp9 dc9]. cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
pose proof (isdigitc_iff' c Rcb) as DIF.
zs. zs. zs. zs. zs. zs. zs. zs. zs.
zs. zs. zs. brf K1; kswrap K1.
- assert (ND : isdigitc c = false) by (destruct (isdigitc c); [exfalso; pose proof (proj1 DIF eq_refl) as DD; clear - K1 Rcb DD w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia | reflexivity]).
pose proof (L_HD fuelc (base + 0x19a8)%Z) as NX; unfold F_fsX0__SHDn in NX. eapply NX with (x := 0%Z) (dc := 0%Z) (gt := 0%Z); try eassumption. all: hx_side.
- assert (D : isdigitc c = true) by (apply (proj2 DIF); clear - K1 Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1618 lo_1619 joff_1589 joff_1595 joff_1600 joff_1607 joff_1611 joff_1620 joff_1623 joff_1626 G_10788 e_extenddftf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 CODE BASE4 BASER D_1589 E_1589 D_1595 E_1595 D_1600 E_1600 D_1607 E_1607 D_1611 E_1611 D_1618 E_1618 D_1619 E_1619 D_1620 E_1620 D_1623 E_1623 D_1626 E_1626 ANCH_1619 LINK_1589 LINK_1595 LINK_1600 LINK_1607 LINK_1611 LINK_1620 LINK_1623 LINK_1626 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc floatsitf_spec divtf3_spec extenddftf2_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia).
zs.
pose proof (L_HD fuelc (base + 0x18ac)%Z) as NX; unfold F_fsX0__SHDn in NX. eapply NX with (x := 0%Z) (dc := 0%Z) (gt := 0%Z); try eassumption. all: hx_side.
Qed.
End Floatscan.

End G.
End Mq1.

Module Mq2.

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
Import Q6Iq.Mq3.
Import QSsB.Mq4.
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
Variables (hi_1753 : bv 20).
Variables (lo_1754 : bv 12).
Variables (joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 : bv 21).
Variables (G_10788 got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_errno_loc e_197bc e_extenddftf2 e_multf3 e_floatsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1697 : decode_any (Z_to_bv 32 w_1697) = Some (Jal 1 joff_1697, 4%Z).
Hypothesis E_1697 : is_ecall (Z_to_bv 32 w_1697) = false.
Hypothesis D_1701 : decode_any (Z_to_bv 32 w_1701) = Some (Jal 1 joff_1701, 4%Z).
Hypothesis E_1701 : is_ecall (Z_to_bv 32 w_1701) = false.
Hypothesis D_1707 : decode_any (Z_to_bv 32 w_1707) = Some (Jal 1 joff_1707, 4%Z).
Hypothesis E_1707 : is_ecall (Z_to_bv 32 w_1707) = false.
Hypothesis D_1712 : decode_any (Z_to_bv 32 w_1712) = Some (Jal 1 joff_1712, 4%Z).
Hypothesis E_1712 : is_ecall (Z_to_bv 32 w_1712) = false.
Hypothesis D_1716 : decode_any (Z_to_bv 32 w_1716) = Some (Jal 1 joff_1716, 4%Z).
Hypothesis E_1716 : is_ecall (Z_to_bv 32 w_1716) = false.
Hypothesis D_1721 : decode_any (Z_to_bv 32 w_1721) = Some (Jal 1 joff_1721, 4%Z).
Hypothesis E_1721 : is_ecall (Z_to_bv 32 w_1721) = false.
Hypothesis D_1724 : decode_any (Z_to_bv 32 w_1724) = Some (Jal 1 joff_1724, 4%Z).
Hypothesis E_1724 : is_ecall (Z_to_bv 32 w_1724) = false.
Hypothesis D_1735 : decode_any (Z_to_bv 32 w_1735) = Some (Jal 1 joff_1735, 4%Z).
Hypothesis E_1735 : is_ecall (Z_to_bv 32 w_1735) = false.
Hypothesis D_1753 : decode_any (Z_to_bv 32 w_1753) = Some (Auipc 10 hi_1753, 4%Z).
Hypothesis E_1753 : is_ecall (Z_to_bv 32 w_1753) = false.
Hypothesis D_1754 : decode_any (Z_to_bv 32 w_1754) = Some (FLoad FMT_D 8 10 lo_1754, 4%Z).
Hypothesis E_1754 : is_ecall (Z_to_bv 32 w_1754) = false.
Hypothesis ANCH_1754 : gw_anch (Z.shiftl (bv_signed hi_1753) 12 + (base + 7012) + bv_signed lo_1754)%Z G_10788.
Hypothesis LINK_1697 : gw_anch (base + 6788 + bv_signed joff_1697)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_1701 : gw_anch (base + 6804 + bv_signed joff_1701)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1707 : gw_anch (base + 6828 + bv_signed joff_1707)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1712 : gw_anch (base + 6848 + bv_signed joff_1712)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_1716 : gw_anch (base + 6864 + bv_signed joff_1716)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1721 : gw_anch (base + 6884 + bv_signed joff_1721)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1724 : gw_anch (base + 6896 + bv_signed joff_1724)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1735 : gw_anch (base + 6940 + bv_signed joff_1735)%Z (e_extenddftf2 + 0)%Z.
Hypothesis CODE_e_errno_loc : code_at segs e_errno_loc errno_loc_code.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis RNG_G_10788 : gw_br G_10788 8.
Hypothesis ROM_G_10788 : ro_bytes segs G_10788 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 224; Z_to_bv 8 63].
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

Local Definition gw_tbl_0 := tt.

Definition SCANEXP := (base + 7584)%Z.
Local Definition gw_tbl_1 := (gw_ent (@Q5m9.Mq1.SCANEXP (base + 7584)%Z) SCANEXP gw_tbl_0).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QSsB.Mq4.ssJ STRING_READ) ssJ (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_1))))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QSsB.Mq4.RFJ STRING_READ) RFJ (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_2))))).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QSsB.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_3))))))).
Definition scanexp_rpost : ltac:(gw_rebind_ty (@Q5m9.Mq1.scanexp_rpost segs STRING_READ got_ssp ssp_guard) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q5m9.Mq1.scanexp_rpost segs STRING_READ got_ssp ssp_guard) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q5m9.Mq1.scanexp_rpost segs STRING_READ got_ssp ssp_guard) scanexp_rpost gw_tbl_4).
Definition scanexp_rstmt := ltac:(let t := constr:(ltac:(gw_rebind (@Q5m9.Mq1.scanexp_rstmt segs (base + 7584)%Z STRING_READ got_ssp ssp_guard) constr:(gw_tbl_5))) in let t := gw_fold_pcs t base (7584)%Z [0; 104; 112; 192; 224; 232; 292; 372; 380; 400; 476; 484; 516; 548; 576]%Z in exact t).
Local Definition gw_tbl_6 := (gw_ent (@Q5m9.Mq1.scanexp_rstmt segs (base + 7584)%Z STRING_READ got_ssp ssp_guard) scanexp_rstmt gw_tbl_5).
Definition getf2_post : ltac:(gw_rebind_ty (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.getf2_post segs) getf2_post (gw_ent (@QVbl.Mq1.getf2_post segs) getf2_post gw_tbl_6)).
Definition scalbn_post : ltac:(gw_rebind_ty (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.scalbn_post segs) scalbn_post (gw_ent (@Q91D.Mq4.scalbn_post segs) scalbn_post gw_tbl_7)).
Definition SCALBNL := (e_extendsftf2 + 1132)%Z.
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.SCALBNL e_extendsftf2) SCALBNL (gw_ent (@QQRC.Mq2.SCALBNL e_extendsftf2) SCALBNL gw_tbl_8)).
Definition COPYSIGNL := (e_extendsftf2 + 348)%Z.
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.COPYSIGNL e_extendsftf2) COPYSIGNL (gw_ent (@QQRC.Mq2.COPYSIGNL e_extendsftf2) COPYSIGNL gw_tbl_9)).
Definition FABSL := (e_extendsftf2 + 1120)%Z.
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.FABSL e_extendsftf2) FABSL (gw_ent (@QQRC.Mq2.FABSL e_extendsftf2) FABSL gw_tbl_10)).
Definition leafq_post : ltac:(gw_rebind_ty (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.leafq_post segs) leafq_post (gw_ent (@QQRC.Mq2.leafq_post segs) leafq_post gw_tbl_11)).
Definition scalbnl_post : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.scalbnl_post segs) scalbnl_post (gw_ent (@QQRC.Mq2.scalbnl_post segs) scalbnl_post gw_tbl_12)).
Definition scalbnl_stmt : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt (gw_ent (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt gw_tbl_13)).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@QzQg.Mq0.extenddftf2_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QzQg.Mq0.extenddftf2_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_14)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@QzQg.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QzQg.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_15)))).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_16)))).
Definition leaf1_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Qy8Z.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Q8l1.Mq0.leaf1_post segs) leaf1_post gw_tbl_17))).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.call2_post segs) call2_post (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post (gw_ent (@Q8l1.Mq0.call2_post segs) call2_post (gw_ent (@QQRC.Mq2.call2_post segs) call2_post gw_tbl_18)))).
Definition FMODL := (e_extendsftf2 + 388)%Z.
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.FMODL e_extendsftf2) FMODL (gw_ent (@Q8l1.Mq0.FMODL e_extendsftf2) FMODL gw_tbl_19)).
Definition rfmodl_post : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.rfmodl_post segs) rfmodl_post (gw_ent (@Q8l1.Mq0.rfmodl_post segs) rfmodl_post gw_tbl_20)).
Definition rfmodl_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt (gw_ent (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt gw_tbl_21)).
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fixunstfsi_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fixunstfsi_post segs) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_22)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@QzQg.Mq0.floatsitf_post segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.floatsitf_post segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_23)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@QzQg.Mq0.floatunsitf_post segs) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.floatunsitf_post segs) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_24)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.addtf3_post segs) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QzQg.Mq0.addtf3_post segs) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_25)))).
Definition multf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.multf3_post segs) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QzQg.Mq0.multf3_post segs) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_26)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@QzQg.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QzQg.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_27)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.divtf3_post segs) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QzQg.Mq0.divtf3_post segs) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_28)))).
Definition letf2_post : ltac:(gw_rebind_ty (@QzQg.Mq0.letf2_post segs) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QzQg.Mq0.letf2_post segs) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_29)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.frexpl_post segs) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@QzQg.Mq0.frexpl_post segs) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_30)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.signbitl_post segs) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QzQg.Mq0.signbitl_post segs) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_31)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fpclassifyl_post segs) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fpclassifyl_post segs) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_32)))).
Definition calla_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QzQg.Mq0.calla_post segs) calla_post (gw_ent (@Qy8Z.Mq0.calla_post segs) calla_post gw_tbl_33)).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QSsB.Mq4.RFI STRING_READ) RFI (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_34))))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_35)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_35)).
Local Definition gw_tbl_36 := (gw_ent (@QSsB.Mq4.RERRNO RATP) RERRNO (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_35))).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_36)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_36)).
Local Definition gw_tbl_37 := (gw_ent (@QSsB.Mq4.Wfs RATP) Wfs (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_36))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QSsB.Mq4.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_37))).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QSsB.Mq4.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_38))).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_39)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_39)).
Local Definition gw_tbl_40 := (gw_ent (@QSsB.Mq4.framL segs RATP) framL (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_39))).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_40)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_40)).
Local Definition gw_tbl_41 := (gw_ent (@QSsB.Mq4.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_40))).
Definition ERRNO_LOC : ltac:(gw_rebind_ty (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_41)) := ltac:(gw_rebind_tm (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_41)).
Local Definition gw_tbl_42 := (gw_ent (@QzQg.Mq0.ERRNO_LOC e_errno_loc) ERRNO_LOC gw_tbl_41).
Definition hxfr : ltac:(gw_rebind_ty (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_42)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_42)).
Local Definition gw_tbl_43 := (gw_ent (@QSsB.Mq4.hxfr segs) hxfr gw_tbl_42).
Definition hxinv : ltac:(gw_rebind_ty (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_43)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_43)).
Local Definition gw_tbl_44 := (gw_ent (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) hxinv gw_tbl_43).
Definition S_HTL : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HTL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_44)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HTL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_44)).
Local Definition gw_tbl_45 := (gw_ent (@QSsB.Mq4.S_HTL segs base got_ssp RATP STRING_READ ssp_guard) S_HTL gw_tbl_44).
Definition S_HE2 : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HE2 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_45)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HE2 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_45)).
Local Definition gw_tbl_46 := (gw_ent (@QSsB.Mq4.S_HE2 segs base got_ssp RATP STRING_READ ssp_guard) S_HE2 gw_tbl_45).
Definition SHNLn : ltac:(gw_rebind_ty (@QSsB.Mq4.SHNLn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_46)) := ltac:(gw_rebind_tm (@QSsB.Mq4.SHNLn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_46)).
Local Definition gw_tbl_47 := (gw_ent (@QSsB.Mq4.SHNLn segs base got_ssp RATP STRING_READ ssp_guard) SHNLn gw_tbl_46).
Definition S_HNL : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HNL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_47)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HNL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_47)).
Local Definition gw_tbl_48 := (gw_ent (@QSsB.Mq4.S_HNL segs base got_ssp RATP STRING_READ ssp_guard) S_HNL gw_tbl_47).
Definition S_HFIN : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HFIN segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_48)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HFIN segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_48)).
Local Definition gw_tbl_49 := (gw_ent (@QSsB.Mq4.S_HFIN segs base got_ssp RATP STRING_READ ssp_guard) S_HFIN gw_tbl_48).
Definition S_HZR : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HZR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_49)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HZR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_49)).
Local Definition gw_tbl_50 := (gw_ent (@QSsB.Mq4.S_HZR segs base got_ssp RATP STRING_READ ssp_guard) S_HZR gw_tbl_49).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_50))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_50))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_50))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_50))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).

Hypothesis scanexp_rspec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q5m9.Mq1.gw_all) (@Q5m9.Mq1.scanexp_rspec) (base + 7584)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_50))) in let T := gw_fold_pcs T base (7584)%Z [0; 104; 112; 192; 224; 232; 292; 372; 380; 400; 476; 484; 516; 548; 576]%Z in exact T).
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_50))) in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).
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

Definition errno_loc_spec : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.errno_loc_spec) constr:(gw_tbl_50)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.errno_loc_spec)).
Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_50)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition extenddftf2_callF : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.extenddftf2_callF) constr:(gw_tbl_50)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.extenddftf2_callF)).
Definition floatsitf_callsg : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.floatsitf_callsg) constr:(gw_tbl_50)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.floatsitf_callsg)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_50)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_50)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_50)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsX0__S_HE2 := S_HE2 (only parsing).
Notation F_fsX0__S_HFIN := S_HFIN (only parsing).
Notation F_fsX0__S_HNL := S_HNL (only parsing).
Notation F_fsX0__S_HTL := S_HTL (only parsing).
Notation F_fsX0__S_HZR := S_HZR (only parsing).
Notation F_fsX0__hxfr := hxfr (only parsing).
Notation F_fsX0__hxinv := hxinv (only parsing).

#[using="G_10788 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_extenddftf2 e_multf3 e_floatsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_slow RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_extenddftf2 e_multf3 e_floatsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos rf_getc_slow RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec.

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

Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QzQg.Mq0.Fok F).
Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).

Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].

Notation POST := (fs_post m0).

Ltac eplia := gw_expose got_ssp; gw_expose ssp_guard; unfold zlength in *; unfold hide2 in *; lia.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.

#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

#[using="rf_getc_slow Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof. clear - rf_getc_slow Hp T1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.
Ltac ufc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

#[using="Type"] Lemma rfj_ns : forall kmin c f, RFJ' kmin c f -> sh_stdio f = false /\ sh_shlim_neg f = false.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct (sh_stdio f) eqn:E.
- destruct (SS eq_refl) as (_ & _ & _ & _ & [_ FF]). destruct FF.
- split; [reflexivity|]. exact (proj1 (NS eq_refl)).
Qed.
#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="Type"] Lemma RFJ_rechar : forall kmin c c' f, RFJ' kmin c f -> (-1 <= c' < 256)%Z -> (c' <> 0%Z -> sh_rpos f <= p)%Z -> RFJ' kmin c' f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hr. split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. exact Hr.
Qed.
#[using="Type"] Lemma RFJ_weak : forall kmin k' c f, RFJ' kmin c f -> (k' <= kmin)%Z -> RFJ' k' c f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin k' c f (OK & Rc & CC & KM & NS & SS) Hk. split; [exact OK|]. split; [exact Rc|]. split; [exact CC|]. split; [intros E; specialize (KM E); lia|]. split; [exact NS | exact SS].
Qed.
#[using="RFI_unget rf_unget_eq Hp"] Lemma RFJ_ungetn : forall n kmin c f, RFJ' kmin c f -> sh_shlim_neg f = false -> (Z.of_nat n <= kmin)%Z ->
RFJ' (kmin - Z.of_nat n) c (fs_unget_loop n f).
Proof. clear - RFI_unget rf_unget_eq Hp ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - Hp RFI_unget rf_unget_eq. induction n as [|n IH]; intros kmin c f RJ Hsn Hn.
- replace (kmin - Z.of_nat 0)%Z with kmin by lia. exact RJ.
- cbn [fs_unget_loop]. replace (kmin - Z.of_nat (S n))%Z with ((kmin - 1) - Z.of_nat n)%Z by lia.
apply IH; [ exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(lia)) | rewrite (rf_unget_eq f Hsn); exact Hsn | lia ].
Qed.

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

Local Notation S_HTL := (@F_fsX0__S_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HE2 := (@F_fsX0__S_HE2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_HNL := (@F_fsX0__S_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HFIN := (@F_fsX0__S_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HZR := (@F_fsX0__S_HZR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation hxfr := (@F_fsX0__hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@F_fsX0__hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).

Notation HX_e2' := (HX_e2 53 (-1074)).

Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := gw_expose got_ssp; gw_expose ssp_guard; unfold F_fsX0__hxinv, F_floatscan_common__Wfs, FS_DEPTH, RERRNO;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg];
repeat match goal with H : ?b = false |- context [?b] => rewrite H end; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold F_fsX0__hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac hx_side := try lazymatch goal with
| |- F_fsX0__hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- F_fsX0__hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- QSsB.Mq4.kminH _ _ _ => unfold QSsB.Mq4.kminH; flia
| |- QSsB.Mq4.hxI _ _ _ _ _ _ _ _ => unfold QSsB.Mq4.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- @eq Z _ _ => flia
| |- _ => idtac end.

Hypothesis HS_HNL : S_HNL.
Hypothesis HS_HFIN : S_HFIN.

#[using="pre"] Lemma hx_release : forall m ev f w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev f -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> stk segs m (q - FS_DEPTH) q.
Proof. clear - pre segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HNL HS_HFIN. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
intros until w56. intros HI HF. dest_hxinv HI. unfold F_fsX0__hxfr in HF.
release_frame HF ST q. unfold FS_DEPTH. exact ST.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE pre"] Lemma L_HRET : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w40 w48 w56 : word) k c,
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1b20)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE pre segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HNL HS_HFIN. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
intros until c. intros HI HF RJ Hk FOK FRM'.
pose proof HI as HI0. pose proof HF as HF0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
pose proof (lo64_range yR). pose proof (hi64_range yR).
do 14 zs. zs. zs.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI0 HF0) as STK. unfold FS_DEPTH in STK.
apply evt_done. gw_expose got_ssp; gw_expose ssp_guard; unfold fs_post, F_floatscan_common__fs_post, F_floatscan_common__Wfs, FS_DEPTH, RERRNO, ssp_cells.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY|]. split; [split; [exact SSP1 | exact SSP2]|]. split; [exact ERR|].
split; [|exact FRM'].
intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
- rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
- rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1735 e_extenddftf2 CODE BASE4 BASER D_1735 E_1735 LINK_1735 extenddftf2_spec"] Lemma L_HZR : S_HZR.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1735 e_extenddftf2 CODE BASE4 BASER D_1735 E_1735 LINK_1735 extenddftf2_spec ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HNL HS_HFIN. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
intros m; intros until c. intros _ HI HF RJ Hk FOK FRM' Hsg Hy.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold F_fsX0__hxfr in HF. bury_disj.
zs. destruct Hsg as [-> | ->]; (zs; zs; zs; zs; callx (eapply extenddftf2_callF; [eassumption | simpF; reflexivity]);
unfold hx_zero, D_ZERO in Hy; rewrite <- Hy; eapply L_HRET; try eassumption).
all: hx_side.
Qed.

#[using="Type"] Lemma sext32_u32_cases : forall x, (0 <= x < 2^32)%Z ->
((x < 2^31)%Z /\ sext32 x = x) \/ ((2^31 <= x)%Z /\ sext32 x = (x + 18446744069414584320)%Z).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HNL HS_HFIN. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
clear. intros x Hx. rewrite sext32_eq. change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z in Hx.
destruct (Z.lt_ge_cases x 2147483648) as [L|G]; [left | right]; split; try lia; Z.div_mod_to_equations; lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 G_10788 e_errno_loc e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_HE2 : S_HE2.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 G_10788 e_errno_loc e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SPF2 SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until e2. intros _ HI HF RJ Hk FOK FRM' Hsg Rx Rrp Re2 HK.
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
unfold HX_e2 in HK. replace (x =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia).
change (- (-1074))%Z with 1074%Z in HK. change (-1074 - 2 * LDBL_MANT_DIG_)%Z with (-1300)%Z in HK.
zs. zs. zs.
let v := getreg 24%Z in replace v with (Z_to_bv 64 (4 * rp + e2 - 32)%Z) by (apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2, ?land_W64 by lia; Z.div_mod_to_equations; lia).
set (E := (4 * rp + e2 - 32)%Z) in *.
assert (RE : (-2^62 <= E <= 2^62)%Z) by (subst E; lia).
zs. zs. zs. brf K1.
-
replace (1074 <? E)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. zs. brf K2.
+
replace (E <? -1300)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
destruct (hx_norm_loop 33 (x, y, E)) as [[[x' y'] E']|] eqn:HN; [|discriminate HK].
pose proof (HX_fin_f _ _ _ _ _ _ _ HK) as Ef.
zs. brf K3.
*
assert (Rx2 : (2^31 <= x)%Z) by (destruct (sext32_u32_cases x ltac:(lia)) as [[A B]|[A B]]; rewrite B, ?land_W64 in K3; clear - K3 A Rx w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 G_10788 e_errno_loc e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia).
rewrite hx_norm_loop_S in HN. replace (2 ^ 31 <=? x)%Z with true in HN by (symmetry; apply Z.leb_le; lia). injection HN as <- <- <-.
zs.
stmt HS_HFIN. eapply NX; try eassumption. all: hx_side.
* assert (Rx2 : (x < 2^31)%Z) by (destruct (sext32_u32_cases x ltac:(lia)) as [[A B]|[A B]]; rewrite B, ?land_W64 in K3; clear - K3 A Rx w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 G_10788 e_errno_loc e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia).
zs. zs. zs. zs.
stmt HS_HNL. eapply NX; try eassumption. all: hx_side. all: try (simpF; reflexivity).
+
replace (E <? -1300)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). injection HK as Ey.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (M1 := f128_mul SF C_LDBL_MIN) in *. pose proof (lo64_range M1). pose proof (hi64_range M1).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := M1) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. rewrite Ey. eapply L_HRET; try eassumption. all: hx_side.
-
replace (1074 <? E)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). injection HK as Ey.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
let v := getreg 12%Z in replace v with (Z_to_bv 64 (lo64 C_LDBL_MAX)) by (apply Z_to_bv_eqm; reflexivity).
zs.
hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (M1 := f128_mul SF C_LDBL_MAX) in *. pose proof (lo64_range M1). pose proof (hi64_range M1).
zs. let v := getreg 12%Z in replace v with (Z_to_bv 64 (lo64 C_LDBL_MAX)) by (apply Z_to_bv_eqm; reflexivity).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := M1) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. rewrite Ey. eapply L_HRET; try eassumption. all: hx_side.
Qed.

#[using="Type"] Lemma shl4_step : forall xv, (0 <= xv < 2^32)%Z ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (Z.land (sext32 xv) 18446744073709551615) 4)) = Z_to_bv 64 (sext32 (u32 (xv * 16))).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HNL HS_HFIN. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
clear. intros xv Hx. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^4)%Z with 16%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low xv) as L. pose proof (sext32_range xv) as R. rewrite (Z.mod_small xv) in L by lia.
set (S := sext32 xv) in *. clearbody S. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma u32_mul16 : forall xv k, (0 <= xv)%Z -> u32 (u32 (xv * 16) * 16 ^ Z.of_nat k) = u32 (xv * 16 ^ Z.of_nat (S k)).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HNL HS_HFIN. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
clear. intros xv k Hx. unfold u32. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE"] Lemma L_X16 : forall (k : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct (xv : Z),
(1 <= k <= 8)%nat -> (0 <= xv < 2^32)%Z ->
(forall xv', xv' = u32 (xv * 16 ^ Z.of_nat k) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0) (Z_to_bv 64 (sext32 xv')) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x19e4)) fct None m (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (- Z.of_nat k)) (Z_to_bv 64 (sext32 xv)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x19d8)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_HNL HS_HFIN. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
induction k as [|k IH]; intros until xv; intros Hk Rxv KONT; [lia|].
zs. zs. rewrite shl4_step by lia. zs. brf K1; rewrite ?land_W64 in K1.
-
replace (Z_to_bv 64 (- Z.of_nat (S k) + 1)) with (Z_to_bv 64 (- Z.of_nat k)) by (f_equal; lia).
eapply IH; [clear - K1 Hk w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE segs base; Z.div_mod_to_equations; lia | apply u32_range |].
intros xv' ->. rewrite u32_mul16 by lia. apply KONT. reflexivity.
- assert (Ek : k = 0%nat) by (clear - K1 Hk w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE segs base; Z.div_mod_to_equations; lia). subst k.
replace (Z_to_bv 64 (- Z.of_nat 1 + 1)) with (Z_to_bv 64 0) by (f_equal; lia).
apply KONT. change (16 ^ Z.of_nat 1)%Z with 16%Z. reflexivity.
Qed.

#[using="scanexp_rspec Hpok1 BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3"] Lemma scanexp_callE : forall (ra' : word) (q' : Z) (gp' tp' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
Proof. clear - scanexp_rspec Hpok1 BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3 segs ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 HP30 SE_T SPLO SPF SPT SG1 Q1 FRM HS_HNL HS_HFIN. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_HNL | gw_hide HS_HNL | idtac]; first [clear HS_HFIN | gw_hide HS_HFIN | idtac].
intros until e10. intros HS FC RJ Hk Hc STX BY SSP ST Q1' Q2 Q3 Q4 Q5 Q6 MI.
pose proof (gw_unhyp scanexp_rspec) as SX. unfold scanexp_rstmt in SX.
eapply evt_mono.
{ eapply SX with (pre := pre) (post := post); try eassumption; unfold SCANEXP_DEPTH; try flia; clear - Hpok scanexp_rspec segs ssp_guard; unfold hide2 in *; flia. }
intros ms' P. unfold scanexp_rpost, SCANEXP_DEPTH in P. exact P.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_H9D0 : forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y rp e2 : Z),
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z -> (-2^60 <= e2 <= 2^60)%Z ->
HX_e2' sign fR x y (4 * rp + e2 - 32) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 e2) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1a28)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SPF2 SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros until e2. intros HI HF RJ Hk FOK FRM' Hsg Rx Rrp Re2 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold F_fsX0__hxfr in HF. bury_disj.
zs. brf K1; rewrite ?land_W64 in K1.
- assert (Nx : x <> 0%Z) by (intros ->; apply K1; reflexivity).
stmt L_HE2. eapply NX; try eassumption. all: hx_side.
- assert (Ex : x = 0%Z) by (destruct (sext32_u32_cases x Rx) as [[A B]|[A B]]; rewrite B in K1; clear - K1 A Rx w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec segs base; Z.div_mod_to_equations; lia).
unfold HX_e2 in HK. rewrite Ex, Z.eqb_refl in HK. injection HK as Ey.
zs. stmt L_HZR. eapply NX; try eassumption. all: hx_side. all: symmetry; exact Ey.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq extenddftf2_spec floatsitf_spec multf3_spec fc pre post fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_H9B8 : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign kmin c (g : shfile) (x y rp : Z),
hxinv m ev g -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' kmin c g -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z ->
HX_e2' sign (sh_unget g) x y (4 * rp + 0 - 32) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1a10)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq extenddftf2_spec floatsitf_spec multf3_spec fc pre post fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_HNL HS_HFIN segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR Hpok Hpok1 ST0 BYT Hnul SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros until rp. intros HI HF RJ Hk FOK FRM' Hsg Rx Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
site_facts FC RJ kmin c g. destruct (rfj_ns _ _ _ RJ) as [Hns Hsn]. specialize (KM Hsn).
pose proof (HX_e2_f _ _ _ _ _ _ _ HK) as Ef.
pose proof (RFI_unget T txt p J Hp kmin c g RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq g Hsn) in RJu, Ef, HK. rewrite <- Ef in RJu.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs. zs0.
eapply L_H9D0 with (e2 := 0%Z) (ev := ev); try eassumption. all: hx_side.
unfold F_fsX0__hxinv. rewrite Ef. mk_hxinv. rewrite Ef in HK |- *. exact HK.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec fc pre post kmin0 c0 Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN"] Lemma L_H98C : forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign kmin c (f : shfile) (x y rp : Z),
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z ->
match (if (Z.lor c 32 =? 112)%Z then
match scanexp fuelc f pok with
| None => None
| Some (f, e2) =>
if (e2 =? LLONG_MIN_)%Z then
(if nz pok then Some (inl (sh_unget f, 0%Z))
else Some (inr (sh_lim0 f, f128_of_i32 0)))
else Some (inl (f, e2))
end
else Some (inl (sh_unget f, 0%Z))) with
| None => None
| Some (inr r) => Some r
| Some (inl (f, e2)) => HX_e2' sign f x y (4 * rp + e2 - 32)
end = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x19e4)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec fc pre post kmin0 c0 Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok FRM. try gw_hide Hpok; first [clear FRM | gw_hide FRM | idtac].
intros until rp. intros HI HF RJ Hk FOK FRM' Hsg Hst Rcb Rx Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold F_fsX0__hxfr in HF. bury_disj.
site_facts FC RJ kmin c f.
zs. zs. zs. brf K1.
-
and33n K1 c Rcb 80%Z N1. replace (Z.lor c 32 =? 112)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
eapply L_H9B8; try eassumption. all: hx_side.
- and33y K1 c Rcb 80%Z E1. rewrite E1, Z.eqb_refl in HK.
destruct (scanexp fuelc f pok) as [[fS e10]|] eqn:HSX; [|discriminate HK].
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in E1; discriminate E1).
pose proof (scanexp_bound fuelc f pok fS e10 ltac:(rewrite Hbuf; exact BYT) HSX) as Re10.
assert (Hst2 : sh_stdio fS = sh_stdio f0) by (rewrite <- Hst; exact (proj1 (scanexp_stdio _ _ _ _ _ HSX))).
zs. zs. zs. zs.
hcall_split 240%Z (eapply scanexp_callE with (f := f) (kmin := kmin) (c := c) (fS := fS) (e10 := e10);
[ exact HSX | exact FC | exact RJ | flia | exact Hc0 | intros E; apply ST0; rewrite <- Hst; exact E | exact BY | exact (conj SSP1 SSP2)
| eassumption | eplia | eplia | eplia | eplia | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ _ fS _) |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ ?k ?c fS |- _ => rename H into RJ2 end.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; gw_expose got_ssp; gw_expose ssp_guard end.
match goal with H : (1 <= ?k)%Z, H2 : RFJ _ _ _ _ _ ?k _ fS |- _ => rename H into Hk2 end.
zs. zs. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (Hne : e10 <> LLONG_MIN_) by (intros E; apply K2; rewrite E; vm_compute; reflexivity).
replace (e10 =? LLONG_MIN_)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne).
assert (Re : (-2^60 <= e10 <= 2^60)%Z) by (destruct Re10 as [E|R]; [exfalso; exact (Hne E) | exact R]).
pose proof (HX_e2_f _ _ _ _ _ _ _ HK) as Ef.
eapply L_H9D0 with (ev := ev); try eassumption. all: hx_side.
unfold F_fsX0__hxinv. rewrite Ef. mk_hxinv. rewrite Ef. exact RJ2. flia. rewrite Ef in HK |- *. exact HK.
+ assert (Ee : e10 = LLONG_MIN_) by (destruct Re10 as [E|R]; [exact E | exfalso; clear - K2 R w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec segs base; unfold LLONG_MIN_ in *; Z.div_mod_to_equations; lia]).
rewrite Ee, Z.eqb_refl in HK. replace (nz pok) with true in HK by (rewrite Hpok1; reflexivity).
rewrite Hpok1. zs. (brf K3; [ exfalso; lia | ]). rewrite <- Hpok1.
eapply L_H9B8 with (ev := ev); try eassumption. all: hx_side.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN"] Lemma L_HTL : S_HTL.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok FRM. try gw_hide Hpok; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until dc. intros _ HI HF RJ HKM FOK FRM' Hsg Hst HXI HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold F_fsX0__hxfr in HF. bury_disj.
destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. destruct (rfj_ns _ _ _ RJ) as [Hns Hsn]. specialize (KM Hsn).
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
unfold HX_tail in HK.
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Eg : gd = 0%Z) by (clear - K1 Rgd w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia). specialize (Hk2 Eg).
replace (negb (nz gd)) with true in HK by (rewrite Eg; reflexivity). replace (nz pok) with true in HK by (rewrite Hpok1; reflexivity). cbv iota in HK.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K2; [ exfalso; lia | ]). zs. zs. zs0. zs. rewrite Hpok1. zs. (brf K3; [ exfalso; lia | ]). rewrite <- Hpok1. zs. zs0.
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu.
assert (Hsn1 : sh_shlim_neg (sh_unget f) = false) by (rewrite (rf_unget_eq f Hsn); exact Hsn).
pose proof (RFI_unget T txt p J Hp (kmin - 1) c (sh_unget f) RJu ltac:(flia)) as RJu2.
assert (Hsn2 : sh_shlim_neg (sh_unget (sh_unget f)) = false) by (rewrite (rf_unget_eq _ Hsn1); cbn; exact Hsn1).
zs. brf K4; rewrite ?land_W64 in K4.
+
assert (Er : gr = 0%Z) by (clear - K4 Rgr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia). rewrite Er in HK. cbn [nz Z.eqb negb] in HK. injection HK as Ef Ey.
rewrite (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in Ef. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in Ef.
rewrite (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in RJu2. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJu2. rewrite Ef in RJu2.
stmt L_HZR. eapply NX with (ev := ev); try eassumption. all: hx_side. all: unfold F_fsX0__hxinv; rewrite <- Ef; mk_hxinv.
+ assert (Er : gr = 1%Z) by (clear - K4 Rgr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia). rewrite Er in HK. cbn [nz Z.eqb negb] in HK. injection HK as Ef Ey.
pose proof (RFI_unget T txt p J Hp (kmin - 1 - 1) c _ RJu2 ltac:(flia)) as RJu3.
rewrite (rf_unget_eq _ Hsn2), (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in Ef. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in Ef.
rewrite (rf_unget_eq _ Hsn2), (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in RJu3. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJu3. rewrite Ef in RJu3.
zs. zs0. zs.
stmt L_HZR. eapply NX with (ev := ev); try eassumption. all: hx_side. all: unfold F_fsX0__hxinv; rewrite <- Ef; mk_hxinv.
-
assert (Eg : gd = 1%Z) by (clear - K1 Rgd w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia).
replace (negb (nz gd)) with false in HK by (rewrite Eg; reflexivity). cbv iota in HK.

assert (G974 : forall rpF, rpF = (if nz gr then rp else dc) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rpF) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x19cc)) fct None m (seg_rom segs))).
{ intros rpF ErpF. rewrite <- ErpF in HK. cbv zeta in HK.
assert (RrpF : (-2^32 <= rpF <= 2^32)%Z) by (subst rpF; destruct (nz gr); flia).
zs. zs. brf K2.
-
replace (dc <=? 7)%Z with false in HK by (symmetry; apply Z.leb_gt; lia).
eapply L_H98C; try eassumption. all: hx_side.
- replace (dc <=? 7)%Z with true in HK by (symmetry; apply Z.leb_le; lia).
zs. replace (Z_to_bv 64 (dc + -8)) with (Z_to_bv 64 (- Z.of_nat (Z.to_nat (8 - dc)))) by (f_equal; lia).
eapply (L_X16 (Z.to_nat (8 - dc))); [lia | exact Rx |]. intros xv' Exv.
replace (Z.of_nat (Z.to_nat (8 - dc))) with (8 - dc)%Z in Exv by lia. rewrite <- Exv in HK.
eapply L_H98C; try eassumption. all: hx_side. all: subst xv'; apply u32_range. }
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ assert (Er : gr = 0%Z) by (clear - K2 Rgr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia).
apply G974. rewrite Er. reflexivity.
+ assert (Er : gr = 1%Z) by (clear - K2 Rgr w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1753 lo_1754 joff_1697 joff_1701 joff_1707 joff_1712 joff_1716 joff_1721 joff_1724 joff_1735 G_10788 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_1697 E_1697 D_1701 E_1701 D_1707 E_1707 D_1712 E_1712 D_1716 E_1716 D_1721 E_1721 D_1724 E_1724 D_1735 E_1735 D_1753 E_1753 D_1754 E_1754 ANCH_1754 LINK_1697 LINK_1701 LINK_1707 LINK_1712 LINK_1716 LINK_1721 LINK_1724 LINK_1735 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq scanexp_rspec extenddftf2_spec floatsitf_spec multf3_spec; Z.div_mod_to_equations; lia).
zs. apply G974. rewrite Er. reflexivity.
Qed.
End Floatscan.

End G.
End Mq2.

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
Import Q6Iq.Mq3.
Import QSsB.Mq4.
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
Variables (joff_1759 joff_1764 joff_1769 joff_1775 joff_1780 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_errno_loc e_197bc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1759 : decode_any (Z_to_bv 32 w_1759) = Some (Jal 1 joff_1759, 4%Z).
Hypothesis E_1759 : is_ecall (Z_to_bv 32 w_1759) = false.
Hypothesis D_1764 : decode_any (Z_to_bv 32 w_1764) = Some (Jal 1 joff_1764, 4%Z).
Hypothesis E_1764 : is_ecall (Z_to_bv 32 w_1764) = false.
Hypothesis D_1769 : decode_any (Z_to_bv 32 w_1769) = Some (Jal 1 joff_1769, 4%Z).
Hypothesis E_1769 : is_ecall (Z_to_bv 32 w_1769) = false.
Hypothesis D_1775 : decode_any (Z_to_bv 32 w_1775) = Some (Jal 1 joff_1775, 4%Z).
Hypothesis E_1775 : is_ecall (Z_to_bv 32 w_1775) = false.
Hypothesis D_1780 : decode_any (Z_to_bv 32 w_1780) = Some (Jal 1 joff_1780, 4%Z).
Hypothesis E_1780 : is_ecall (Z_to_bv 32 w_1780) = false.
Hypothesis D_1808 : decode_any (Z_to_bv 32 w_1808) = Some (Jal 1 joff_1808, 4%Z).
Hypothesis E_1808 : is_ecall (Z_to_bv 32 w_1808) = false.
Hypothesis D_1809 : decode_any (Z_to_bv 32 w_1809) = Some (Jal 1 joff_1809, 4%Z).
Hypothesis E_1809 : is_ecall (Z_to_bv 32 w_1809) = false.
Hypothesis D_1813 : decode_any (Z_to_bv 32 w_1813) = Some (Jal 1 joff_1813, 4%Z).
Hypothesis E_1813 : is_ecall (Z_to_bv 32 w_1813) = false.
Hypothesis D_1818 : decode_any (Z_to_bv 32 w_1818) = Some (Jal 1 joff_1818, 4%Z).
Hypothesis E_1818 : is_ecall (Z_to_bv 32 w_1818) = false.
Hypothesis D_1827 : decode_any (Z_to_bv 32 w_1827) = Some (Jal 1 joff_1827, 4%Z).
Hypothesis E_1827 : is_ecall (Z_to_bv 32 w_1827) = false.
Hypothesis D_1834 : decode_any (Z_to_bv 32 w_1834) = Some (Jal 1 joff_1834, 4%Z).
Hypothesis E_1834 : is_ecall (Z_to_bv 32 w_1834) = false.
Hypothesis D_1840 : decode_any (Z_to_bv 32 w_1840) = Some (Jal 1 joff_1840, 4%Z).
Hypothesis E_1840 : is_ecall (Z_to_bv 32 w_1840) = false.
Hypothesis D_1844 : decode_any (Z_to_bv 32 w_1844) = Some (Jal 1 joff_1844, 4%Z).
Hypothesis E_1844 : is_ecall (Z_to_bv 32 w_1844) = false.
Hypothesis D_1849 : decode_any (Z_to_bv 32 w_1849) = Some (Jal 1 joff_1849, 4%Z).
Hypothesis E_1849 : is_ecall (Z_to_bv 32 w_1849) = false.
Hypothesis D_1854 : decode_any (Z_to_bv 32 w_1854) = Some (Jal 1 joff_1854, 4%Z).
Hypothesis E_1854 : is_ecall (Z_to_bv 32 w_1854) = false.
Hypothesis D_1861 : decode_any (Z_to_bv 32 w_1861) = Some (Jal 1 joff_1861, 4%Z).
Hypothesis E_1861 : is_ecall (Z_to_bv 32 w_1861) = false.
Hypothesis D_1864 : decode_any (Z_to_bv 32 w_1864) = Some (Jal 1 joff_1864, 4%Z).
Hypothesis E_1864 : is_ecall (Z_to_bv 32 w_1864) = false.
Hypothesis D_1867 : decode_any (Z_to_bv 32 w_1867) = Some (Jal 1 joff_1867, 4%Z).
Hypothesis E_1867 : is_ecall (Z_to_bv 32 w_1867) = false.
Hypothesis D_1872 : decode_any (Z_to_bv 32 w_1872) = Some (Jal 1 joff_1872, 4%Z).
Hypothesis E_1872 : is_ecall (Z_to_bv 32 w_1872) = false.
Hypothesis D_1874 : decode_any (Z_to_bv 32 w_1874) = Some (Jal 1 joff_1874, 4%Z).
Hypothesis E_1874 : is_ecall (Z_to_bv 32 w_1874) = false.
Hypothesis D_1895 : decode_any (Z_to_bv 32 w_1895) = Some (Jal 0 joff_1895, 4%Z).
Hypothesis E_1895 : is_ecall (Z_to_bv 32 w_1895) = false.
Hypothesis LINK_1759 : gw_anch (base + 7036 + bv_signed joff_1759)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1764 : gw_anch (base + 7056 + bv_signed joff_1764)%Z (e_subtf3 + 0)%Z.
Hypothesis LINK_1769 : gw_anch (base + 7076 + bv_signed joff_1769)%Z (e_addtf3 + 0)%Z.
Hypothesis LINK_1775 : gw_anch (base + 7100 + bv_signed joff_1775)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_1780 : gw_anch (base + 7120 + bv_signed joff_1780)%Z (e_getf2 + 0)%Z.
Hypothesis LINK_1808 : gw_anch (base + 7232 + bv_signed joff_1808)%Z (e_scalbn + 0)%Z.
Hypothesis LINK_1809 : gw_anch (base + 7236 + bv_signed joff_1809)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_1813 : gw_anch (base + 7252 + bv_signed joff_1813)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1818 : gw_anch (base + 7272 + bv_signed joff_1818)%Z (e_extendsftf2 + 348)%Z.
Hypothesis LINK_1827 : gw_anch (base + 7308 + bv_signed joff_1827)%Z (e_letf2 + 0)%Z.
Hypothesis LINK_1834 : gw_anch (base + 7336 + bv_signed joff_1834)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1840 : gw_anch (base + 7360 + bv_signed joff_1840)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1844 : gw_anch (base + 7376 + bv_signed joff_1844)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_1849 : gw_anch (base + 7396 + bv_signed joff_1849)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1854 : gw_anch (base + 7416 + bv_signed joff_1854)%Z (e_addtf3 + 0)%Z.
Hypothesis LINK_1861 : gw_anch (base + 7444 + bv_signed joff_1861)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1864 : gw_anch (base + 7456 + bv_signed joff_1864)%Z (e_addtf3 + 0)%Z.
Hypothesis LINK_1867 : gw_anch (base + 7468 + bv_signed joff_1867)%Z (e_subtf3 + 0)%Z.
Hypothesis LINK_1872 : gw_anch (base + 7488 + bv_signed joff_1872)%Z (e_letf2 + 0)%Z.
Hypothesis LINK_1874 : gw_anch (base + 7496 + bv_signed joff_1874)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_1895 : gw_anch (base + 7580 + bv_signed joff_1895)%Z (e_extendsftf2 + 1132)%Z.
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

Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_0)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_1)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_2)))).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_3)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_4)))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_5)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_6)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_7)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_8)))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_9)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_10)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_11)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_12)))).
Definition getf2_post : ltac:(gw_rebind_ty (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.getf2_post segs) getf2_post (gw_ent (@QVbl.Mq1.getf2_post segs) getf2_post gw_tbl_13)).
Definition scalbn_post : ltac:(gw_rebind_ty (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.scalbn_post segs) scalbn_post (gw_ent (@Q91D.Mq4.scalbn_post segs) scalbn_post gw_tbl_14)).
Definition SCALBNL := (e_extendsftf2 + 1132)%Z.
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.SCALBNL e_extendsftf2) SCALBNL (gw_ent (@QQRC.Mq2.SCALBNL e_extendsftf2) SCALBNL gw_tbl_15)).
Definition COPYSIGNL := (e_extendsftf2 + 348)%Z.
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.COPYSIGNL e_extendsftf2) COPYSIGNL (gw_ent (@QQRC.Mq2.COPYSIGNL e_extendsftf2) COPYSIGNL gw_tbl_16)).
Definition FABSL := (e_extendsftf2 + 1120)%Z.
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.FABSL e_extendsftf2) FABSL (gw_ent (@QQRC.Mq2.FABSL e_extendsftf2) FABSL gw_tbl_17)).
Definition leafq_post : ltac:(gw_rebind_ty (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.leafq_post segs) leafq_post (gw_ent (@QQRC.Mq2.leafq_post segs) leafq_post gw_tbl_18)).
Definition scalbnl_post : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.scalbnl_post segs) scalbnl_post (gw_ent (@QQRC.Mq2.scalbnl_post segs) scalbnl_post gw_tbl_19)).
Definition scalbnl_stmt : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt (gw_ent (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt gw_tbl_20)).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_21)))).
Definition leaf1_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Qy8Z.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Q8l1.Mq0.leaf1_post segs) leaf1_post gw_tbl_22))).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.call2_post segs) call2_post (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post (gw_ent (@Q8l1.Mq0.call2_post segs) call2_post (gw_ent (@QQRC.Mq2.call2_post segs) call2_post gw_tbl_23)))).
Definition FMODL := (e_extendsftf2 + 388)%Z.
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.FMODL e_extendsftf2) FMODL (gw_ent (@Q8l1.Mq0.FMODL e_extendsftf2) FMODL gw_tbl_24)).
Definition rfmodl_post : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.rfmodl_post segs) rfmodl_post (gw_ent (@Q8l1.Mq0.rfmodl_post segs) rfmodl_post gw_tbl_25)).
Definition rfmodl_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt (gw_ent (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt gw_tbl_26)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QSsB.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_27))))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QSsB.Mq4.ssJ STRING_READ) ssJ (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_28))))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QSsB.Mq4.RFJ STRING_READ) RFJ (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_29))))).
Definition calla_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.calla_post segs) calla_post (gw_ent (@Qy8Z.Mq0.calla_post segs) calla_post gw_tbl_30)).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QSsB.Mq4.RFI STRING_READ) RFI (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_31))))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QSsB.Mq4.RERRNO RATP) RERRNO (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_32))).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QSsB.Mq4.Wfs RATP) Wfs (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_33))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QSsB.Mq4.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_34))).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_35)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_35)).
Local Definition gw_tbl_36 := (gw_ent (@QSsB.Mq4.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_35))).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_36)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_36)).
Local Definition gw_tbl_37 := (gw_ent (@QSsB.Mq4.framL segs RATP) framL (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_36))).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QSsB.Mq4.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_37))).
Definition ERRNO_LOC : ltac:(gw_rebind_ty (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.ERRNO_LOC e_errno_loc) ERRNO_LOC gw_tbl_38).
Definition hxfr : ltac:(gw_rebind_ty (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_39)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxfr segs) constr:(gw_tbl_39)).
Local Definition gw_tbl_40 := (gw_ent (@QSsB.Mq4.hxfr segs) hxfr gw_tbl_39).
Definition hxinv : ltac:(gw_rebind_ty (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_40)) := ltac:(gw_rebind_tm (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_40)).
Local Definition gw_tbl_41 := (gw_ent (@QSsB.Mq4.hxinv segs got_ssp RATP ssp_guard) hxinv gw_tbl_40).
Definition SHNLn : ltac:(gw_rebind_ty (@QSsB.Mq4.SHNLn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_41)) := ltac:(gw_rebind_tm (@QSsB.Mq4.SHNLn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_41)).
Local Definition gw_tbl_42 := (gw_ent (@QSsB.Mq4.SHNLn segs base got_ssp RATP STRING_READ ssp_guard) SHNLn gw_tbl_41).
Definition S_HNL : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HNL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_42)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HNL segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_42)).
Local Definition gw_tbl_43 := (gw_ent (@QSsB.Mq4.S_HNL segs base got_ssp RATP STRING_READ ssp_guard) S_HNL gw_tbl_42).
Definition S_HFIN : ltac:(gw_rebind_ty (@QSsB.Mq4.S_HFIN segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_43)) := ltac:(gw_rebind_tm (@QSsB.Mq4.S_HFIN segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_43)).
Local Definition gw_tbl_44 := (gw_ent (@QSsB.Mq4.S_HFIN segs base got_ssp RATP STRING_READ ssp_guard) S_HFIN gw_tbl_43).

Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).

Hypothesis scalbnl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.scalbnl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in exact T).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis floatunsitf_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq4.gw_all) (@QQLG.Mq4.floatunsitf_spec) e_floatunsitf)) in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatunsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis getf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq1.getf2_spec segs e_getf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in exact T).  Arguments getf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis scalbn_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq4.gw_all) (@Q91D.Mq4.scalbn_spec) e_scalbn)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in exact T).  Arguments scalbn_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis copysignl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.copysignl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_44))) in exact T).  Arguments copysignl_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope.
Hypothesis letf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.letf2_spec segs e_letf2) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QVbl.Mq2.letf2_post segs) letf2_post in exact T).  Arguments letf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).
Definition floatunsitf_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatunsitf_callv) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatunsitf_callv)).

Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).

Definition errno_loc_spec : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.errno_loc_spec) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.errno_loc_spec)).
Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition sub_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.sub_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.sub_callE)).
Definition letf2_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.letf2_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.letf2_callE)).
Definition getf2_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.getf2_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.getf2_callE)).
Definition scalbn_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.scalbn_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.scalbn_callE)).
Definition copysignl_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.copysignl_callE) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.copysignl_callE)).
Definition extenddftf2_callF : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.extenddftf2_callF) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.extenddftf2_callF)).
Definition floatsitf_callsg : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.floatsitf_callsg) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.floatsitf_callsg)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_44)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsX0__S_HFIN := S_HFIN (only parsing).
Notation F_fsX0__S_HNL := S_HNL (only parsing).
Notation F_fsX0__hxfr := hxfr (only parsing).
Notation F_fsX0__hxinv := hxinv (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1759 E_1759 D_1764 E_1764 D_1769 E_1769 D_1775 E_1775 D_1780 E_1780 D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1759 LINK_1764 LINK_1769 LINK_1775 LINK_1780 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO rf_getc_slow RFI_unget rf_unget_eq scalbnl_spec floatsitf_spec floatunsitf_spec getf2_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1759 joff_1764 joff_1769 joff_1775 joff_1780 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1759 E_1759 D_1764 E_1764 D_1769 E_1769 D_1775 E_1775 D_1780 E_1780 D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1759 LINK_1764 LINK_1769 LINK_1775 LINK_1780 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO rf_getc_slow RFI_unget rf_unget_eq scalbnl_spec floatsitf_spec floatunsitf_spec getf2_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec.

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

Notation RFJ' := (RFJ T txt p true J).

Local Notation FokR := (@QzQg.Mq0.FokR F).
Local Notation Fok := (@QzQg.Mq0.Fok F).
Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).

Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
Ltac unbury := unfold hide2 in *.
Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].

Notation POST := (fs_post m0).

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.

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

#[using="Type"] Lemma rfj_ns : forall kmin c f, RFJ' kmin c f -> sh_stdio f = false /\ sh_shlim_neg f = false.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct (sh_stdio f) eqn:E.
- destruct (SS eq_refl) as (_ & _ & _ & _ & [_ FF]). destruct FF.
- split; [reflexivity|]. exact (proj1 (NS eq_refl)).
Qed.
#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="Type"] Lemma RFJ_rechar : forall kmin c c' f, RFJ' kmin c f -> (-1 <= c' < 256)%Z -> (c' <> 0%Z -> sh_rpos f <= p)%Z -> RFJ' kmin c' f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hr. split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. exact Hr.
Qed.
#[using="Type"] Lemma RFJ_weak : forall kmin k' c f, RFJ' kmin c f -> (k' <= kmin)%Z -> RFJ' k' c f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros kmin k' c f (OK & Rc & CC & KM & NS & SS) Hk. split; [exact OK|]. split; [exact Rc|]. split; [exact CC|]. split; [intros E; specialize (KM E); lia|]. split; [exact NS | exact SS].
Qed.
#[using="RFI_unget rf_unget_eq Hp"] Lemma RFJ_ungetn : forall n kmin c f, RFJ' kmin c f -> sh_shlim_neg f = false -> (Z.of_nat n <= kmin)%Z ->
RFJ' (kmin - Z.of_nat n) c (fs_unget_loop n f).
Proof. clear - RFI_unget rf_unget_eq Hp ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - Hp RFI_unget rf_unget_eq. induction n as [|n IH]; intros kmin c f RJ Hsn Hn.
- replace (kmin - Z.of_nat 0)%Z with kmin by lia. exact RJ.
- cbn [fs_unget_loop]. replace (kmin - Z.of_nat (S n))%Z with ((kmin - 1) - Z.of_nat n)%Z by lia.
apply IH; [ exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(lia)) | rewrite (rf_unget_eq f Hsn); exact Hsn | lia ].
Qed.

Local Notation S_HNL := (@F_fsX0__S_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HFIN := (@F_fsX0__S_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation hxfr := (@F_fsX0__hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@F_fsX0__hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).

Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := gw_expose got_ssp; gw_expose ssp_guard; unfold F_fsX0__hxinv, F_floatscan_common__Wfs, FS_DEPTH, RERRNO;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg];
repeat match goal with H : ?b = false |- context [?b] => rewrite H end; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold F_fsX0__hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac hx_side := try lazymatch goal with
| |- F_fsX0__hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- F_fsX0__hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- QSsB.Mq4.kminH _ _ _ => unfold QSsB.Mq4.kminH; flia
| |- QSsB.Mq4.hxI _ _ _ _ _ _ _ _ => unfold QSsB.Mq4.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- @eq Z _ _ => flia
| |- _ => idtac end.

#[using="pre"] Lemma hx_release : forall m ev f w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev f -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> stk segs m (q - FS_DEPTH) q.
Proof. clear - pre segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until w56. intros HI HF. dest_hxinv HI. unfold F_fsX0__hxfr in HF.
release_frame HF ST q. unfold FS_DEPTH. exact ST.
Qed.

#[using="Type"] Lemma shl1_step : forall xv, (0 <= xv < 2^32)%Z ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (Z.land (sext32 xv) 18446744073709551615) 1)) = Z_to_bv 64 (sext32 (u32 (2 * xv))).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros xv Hx. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^1)%Z with 2%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low xv) as L. pose proof (sext32_range xv) as R. rewrite (Z.mod_small xv) in L by lia.
set (S := sext32 xv) in *. clearbody S. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma lor1_even : forall a, (a mod 2 = 0)%Z -> Z.lor a 1 = (a + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros a Ha. assert (L : Z.land a 1 = 0%Z) by (change 1%Z with (Z.ones 1); rewrite Z.land_ones; [exact Ha | lia]).
rewrite <- Z.lxor_lor, Z.add_nocarry_lxor by exact L. reflexivity.
Qed.
#[using="Type"] Lemma sext32_succ_even : forall a, (0 <= a < 2^32)%Z -> (a mod 2 = 0)%Z -> sext32 (a + 1) = (sext32 a + 1)%Z /\ (sext32 a mod 2 = 0)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros a Ha Ea. rewrite !sext32_eq. change (2^32)%Z with 4294967296%Z in Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma sext32_u32_cases : forall x, (0 <= x < 2^32)%Z ->
((x < 2^31)%Z /\ sext32 x = x) \/ ((2^31 <= x)%Z /\ sext32 x = (x + 18446744069414584320)%Z).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros x Hx. rewrite sext32_eq. change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z in Hx.
destruct (Z.lt_ge_cases x 2147483648) as [L|G]; [left | right]; split; try lia; Z.div_mod_to_equations; lia.
Qed.

#[using="RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre SPF SPT SG1"] Lemma hx_post_tail : forall m m' F' fc' k c ev w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> RFJ' k c fR -> (0 <= k)%Z ->
FokR F' -> frm0 fc' ->
munch [(q - 112, q)]%Z m m' -> wmono segs m m' -> mem_inv segs m' -> stk segs m' (q - 112) q ->
forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom segs)).
Proof. clear - RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre SPF SPT SG1 segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF2 SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until w56. intros HI HF RJ Hk FOK FRM' MU2 WM2 MI2 ST2. intros.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI HF) as STK. unfold FS_DEPTH in STK.
dest_hxinv HI. bury_disj. unbury.
pose proof (rw_cells_bound _ _ _ _ FC) as B1. cbn [cells_size csize Nat.add rf_cells] in B1.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 _].
gw_expose got_ssp; gw_expose ssp_guard; unfold fs_post, F_floatscan_common__fs_post, F_floatscan_common__Wfs, FS_DEPTH, RERRNO, ssp_cells.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split.
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split.
{ eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia] | exact ST2 | lia ]. }
split. { eapply rw_cells_transport; [exact FC | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize rf_cells length Nat.add]; lia]. }
split; [exact RJ|]. split; [exact Hk|].
split. { eapply bytes_at_transport; [exact BY | exact MU2 | cbn [disjoint_from]; rewrite ?LTX; lia]. }
split. { split.
- eapply rw_cells_transport; [exact SSP1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia].
- eapply rw_cells_transport; [exact SSP2 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split; [exact FOK | exact FRM'].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1895 e_extendsftf2 CODE D_1895 E_1895 LINK_1895 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec pre SPLO SPF SPT SG1 Q1"] Lemma L_HCFC : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w40 w48 w56 : word) k c (Y e2 : Z),
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1d54)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1895 e_extendsftf2 CODE D_1895 E_1895 LINK_1895 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec pre SPLO SPF SPT SG1 Q1 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF2 SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros until e2. intros HI HF RJ Hk FOK FRM' He2 Hy.
pose proof HI as HI0. pose proof HF as HF0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
pose proof (lo64_range Y). pose proof (hi64_range Y).
zs. rewrite ?swrap32_landW. rewrite swrap32_small by lia.
zs. zs.
do 14 zs. zs. zs.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI0 HF0) as STK. unfold FS_DEPTH in STK.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 ST2].
pose proof (gw_unhyp scalbnl_spec) as SS. unfold scalbnl_stmt in SS.
replace (Z_to_bv 64 (q + -176 + 176)) with (Z_to_bv 64 q) by (f_equal; lia).
eapply evt_mono. { eapply SS; [exact ST2 | lia | lia | exact He2 | exact MI]. }
intros ms' P. unfold scalbnl_post in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & ST3).
rewrite <- Hy. unbury. eapply (hx_post_tail m m'); try eassumption.
intros kk H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity).
destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_letf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec letf2_spec addtf3_spec subtf3_spec multf3_spec pre Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HC64 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w48 w56 : word) sign k c (x y BI e2 : Z),
hxinv m ev fR -> hxfr w0 (Z_to_bv 64 (hi64 BI)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> (0 <= x < 2^32)%Z -> (-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl (f128_sub (f128_add (f128_mul (f128_of_i32 sign) y) (f128_add (f128_mul (f128_of_i32 sign) (f128_of_u32 x)) BI)) BI) e2 ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1cbc)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_letf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec letf2_spec addtf3_spec subtf3_spec multf3_spec pre Hp SE_T SPLO SPF SPT SG1 Q1 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SPF2 SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros until e2. intros HI HF RJ Hk FOK FRM' Hsg Rx He2 Hy.
pose proof HI as HI0. dest_hxinv HI. unfold F_fsX0__hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range BI). pose proof (hi64_range BI).
pose proof (sext32_range x) as RSx.
zs. destruct Hsg as [Hsg | Hsg]; rewrite Hsg in *.
all: zs; callx (eapply floatsitf_callsg; [eassumption | lia]).
all: set (SF := f128_of_i32 _) in *; pose proof (lo64_range SF); pose proof (hi64_range SF).
all: zs; zs; zs; zs; callx (eapply floatunsitf_callv with (u := x); [eassumption | lia | reflexivity]).
all: set (XF := f128_of_u32 x) in *; pose proof (lo64_range XF); pose proof (hi64_range XF).
all: zs; zs; zs; zs; zs.
all: hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V1 := f128_mul SF XF) in *; pose proof (lo64_range V1); pose proof (hi64_range V1).
all: zs; zs; zs; zs; zs.
all: hcall_split 48%Z (eapply add_callE with (X := V1) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V2 := f128_add V1 BI) in *; pose proof (lo64_range V2); pose proof (hi64_range V2).
all: zs; zs; zs; zs; zs; zs; zs.
all: hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V3 := f128_mul SF y) in *; pose proof (lo64_range V3); pose proof (hi64_range V3).
all: zs; zs; zs.
all: hcall_split 48%Z (eapply add_callE with (X := V3) (Y := V2); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V4 := f128_add V3 V2) in *; pose proof (lo64_range V4); pose proof (hi64_range V4).
all: zs; zs; zs.
all: hcall_split 48%Z (eapply sub_callE with (X := V4) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (YF := f128_sub V4 BI) in *; pose proof (lo64_range YF); pose proof (hi64_range YF).
all: zs; zs; zs; zs; zs; callx (eapply letf2_callE with (X := YF) (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
all: pose proof (f128_le_range YF 0) as RLE.
all: zs; brf K1.
1,3: eapply L_HCFC; try eassumption; hx_side.
all: zs; callx (eapply errno_loc_spec; eassumption).
all: zs; unfold RERRNO; zs0.
all: eapply L_HCFC; try eassumption; hx_side.
Qed.
#[using="Type"] Lemma sgtz_b2z : forall E, (-2^62 <= E <= 2^62)%Z ->
Z.b2z (9223372036854775808 <? Z.lxor (Z.land E 18446744073709551615) 9223372036854775808) = (if 0 <? E then 1 else 0)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros E HE. rewrite (land_W64 E). change 9223372036854775808%Z with (2^63)%Z.
rewrite zb_lxor_sign by (Z.div_mod_to_equations; lia).
destruct (Z.ltb_spec 0 E).
- replace (2^63 <? _)%Z with true; [reflexivity|]. symmetry. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
- replace (2^63 <? _)%Z with false; [reflexivity|]. symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma bits_clamp : forall E, (-2^62 <= E <= 2^62)%Z ->
Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land E 18446744073709551615) 9223372036854775808)) 18446744073709551615)
(Z.land E 18446744073709551615) = Z.max 0 E.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros E HE. rewrite sgtz_b2z by lia. destruct (Z.ltb_spec 0 E).
- change (0 - 1)%Z with (-1)%Z. rewrite Z.land_m1_l. rewrite (land_W64_small E) by lia. rewrite Z.land_comm, land_W64_small by lia. lia.
- change (0 - 0)%Z with 0%Z. rewrite !Z.land_0_l. lia.
Qed.
#[using="Type"] Lemma land1_sext32 : forall x, (0 <= x < 2^32)%Z -> Z.land (sext32 x) 1 = (x mod 2)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros x Hx. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1)%Z with 2%Z.
rewrite sext32_eq. change (2^32)%Z with 4294967296%Z in Hx. Z.div_mod_to_equations. lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HFIN : S_HFIN.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 Q1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SPF2 SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until e2. intros _ HI HF RJ Hk FOK FRM' Hsg Rx Re2 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold F_fsX0__hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (sext32_range x) as RSx.
unfold HX_fin in HK.
remember (if (53 <=? 32 + e2 - -1074)%Z then 53%Z else Z.max 0 (32 + e2 - -1074)) as bits eqn:Eb in HK.
assert (Rb : (0 <= bits <= 53)%Z) by (subst bits; destruct (Z.leb_spec 53 (32 + e2 - -1074))%Z; lia).
replace (bits <=? 112)%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbv zeta in HK.

assert (G : forall (xa xb : word),
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 xa xb x12 x13 x14 x15 x16 x17
(Z_to_bv 64 bits) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1c24)) fct None m (seg_rom segs))).
2: { zs. zs. zs. zs. brf K1.
- replace (53 <=? 32 + e2 - -1074)%Z with true in Eb by (symmetry; apply Z.leb_le; lia). subst bits. apply G.
- replace (53 <=? 32 + e2 - -1074)%Z with false in Eb by (symmetry; apply Z.leb_gt; lia).
zs. fixw3. zs. zs. zs.
let v := getreg 18%Z in replace v with (Z_to_bv 64 bits) by (rewrite bits_clamp by lia; f_equal; rewrite Eb; lia).
let v := getreg 11%Z in set (JK := v); clearbody JK.
apply G. }
intros xa xb.
zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. zs. zs. zs.
rewrite !swrap32_small by lia. rewrite Z.add_0_r.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]).
lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM3 end end. simpF.
set (D1 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits)) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits)) with D1 in HK.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D1); [eassumption | simpF; reflexivity]).
set (HB := f128_of_d (bv_unsigned D1)) in *. pose proof (lo64_range HB). pose proof (hi64_range HB).
zs. zs. zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs. callx (eapply copysignl_callE with (X := HB) (Y := SF); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
set (BI := m_copysignl HB SF) in *. pose proof (lo64_range BI). pose proof (hi64_range BI).
zs. zs. zs. zs. brf K3.
-
replace (bits <=? 31)%Z with false in HK by (symmetry; apply Z.leb_gt; clear - K3 Rb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; Z.div_mod_to_equations; lia).
injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
- replace (bits <=? 31)%Z with true in HK by (symmetry; apply Z.leb_le; clear - K3 Rb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; Z.div_mod_to_equations; lia).
zs. zs. zs. zs. zs. callx (eapply letf2_callE with (X := y) (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range y 0) as RLE. set (LE := f128_le y 0) in *.
zs. zs. brf K4; rewrite (land1_sext32 x) in K4 by lia; rewrite Zmod_odd in K4.
+
replace (Z.odd x) with true in HK by (destruct (Z.odd x); [reflexivity | exfalso; apply K4; reflexivity]). cbn [negb andb] in HK.
injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
+ replace (Z.odd x) with false in HK by (destruct (Z.odd x); [exfalso; clear - K4 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; lia | reflexivity]). cbn [negb andb] in HK.
assert (Ex2 : (x mod 2 = 0)%Z) by (rewrite Zmod_odd; destruct (Z.odd x); [exfalso; clear - K4 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; lia | reflexivity]).
zs. zs. brf K5; rewrite ?land_W64 in K5.
*
assert (EL : LE = 0%Z) by (clear - K5 RLE w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; Z.div_mod_to_equations; lia).
replace (nz LE) with false in HK by (rewrite EL; reflexivity). injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
* assert (NL : LE <> 0%Z) by (clear - K5 RLE w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; Z.div_mod_to_equations; lia).
replace (nz LE) with true in HK by (unfold nz; symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NL). injection HK as Ey.
rewrite lor1_even in Ey by exact Ex2.
destruct (sext32_succ_even x ltac:(lia) Ex2) as [SE1 SE2].
zs. rewrite ?land_W64_small by lia. rewrite (lor1_even (sext32 x)) by exact SE2. rewrite <- SE1.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs. zs. zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1759 joff_1764 joff_1769 joff_1775 joff_1780 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1759 E_1759 D_1764 E_1764 D_1769 E_1769 D_1775 E_1775 D_1780 E_1780 D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1759 LINK_1764 LINK_1769 LINK_1775 LINK_1780 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec getf2_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HNL : S_HNL.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1759 joff_1764 joff_1769 joff_1775 joff_1780 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1759 E_1759 D_1764 E_1764 D_1769 E_1769 D_1775 E_1775 D_1780 E_1780 D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1759 LINK_1764 LINK_1769 LINK_1775 LINK_1780 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec getf2_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 Q1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SPF2 SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros n. induction n as [|n IH]; intros m; intros until e2'; intros _ HI HF RJ Hk FOK FRM' Hsg HF5 Rx Re2 HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold F_fsX0__hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
rewrite hx_norm_loop_S in HL. replace (2 ^ 31 <=? x)%Z with false in HL by (symmetry; apply Z.leb_gt; lia).
unfold hx_norm_body in HL. replace (u32 (2 * x)) with (2 * x)%Z in HL by (unfold u32; symmetry; apply Z.mod_small; lia).
set (H5 := f128_of_d (bv_unsigned D_05)) in *. pose proof (lo64_range H5). pose proof (hi64_range H5).
assert (Rn : (Z.of_nat (S n) = Z.of_nat n + 1)%Z) by lia. rewrite Rn in Re2.

assert (TAIL : forall m1 (x1' x5' x6' x7' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) Ft1 fct1 (x2 y2 : Z),
hxinv m1 ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m1 ->
Fok Ft1 -> frm0 fct1 -> reg_get Ft1 8 = D_05 -> (2 * x <= x2 <= 2 * x + 1)%Z ->
hx_norm_loop n (x2, y2, e2 - 1)%Z = Some (x', y', e2') ->
evt segs POST
(MS (mkR x1' HSP gp TPv x5' x6' x7' (Z_to_bv 64 (-1074)) x9 (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 (hi64 y2)) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x2)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28' x29' x30' x31')
Ft1 (Z_to_bv 64 (base + 0x1ba8)) fct1 None m1 (seg_rom segs))).
{ intros until y2. intros HI1 HF1 FOK1 FRM1 HF51 Rx2 HL2. clear HL.
clear MI MU WM ST BY SSP1 SSP2 ERR FC HF. dest_hxinv HI1. unfold F_fsX0__hxfr in HF1.
pose proof (lo64_range y2). pose proof (hi64_range y2).
zs. zs. zs. replace (Z_to_bv 64 (e2 + -1)) with (Z_to_bv 64 (e2 - 1)%Z) by (f_equal; lia).
destruct (sext32_u32_cases x2 ltac:(lia)) as [[A B]|[A B]].
-
zs. brf K1; rewrite ?B, ?land_W64 in K1; [clear - K1 A Rx w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1759 joff_1764 joff_1769 joff_1775 joff_1780 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1759 E_1759 D_1764 E_1764 D_1769 E_1769 D_1775 E_1775 D_1780 E_1780 D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1759 LINK_1764 LINK_1769 LINK_1775 LINK_1780 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec getf2_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; exfalso; Z.div_mod_to_equations; lia|].
eapply IH; try eassumption. all: hx_side.
-
zs. brf K1; rewrite ?B, ?land_W64 in K1; [|clear - K1 A Rx w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1759 joff_1764 joff_1769 joff_1775 joff_1780 joff_1808 joff_1809 joff_1813 joff_1818 joff_1827 joff_1834 joff_1840 joff_1844 joff_1849 joff_1854 joff_1861 joff_1864 joff_1867 joff_1872 joff_1874 joff_1895 e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_floatunsitf e_extendsftf2 CODE BASE4 BASER D_1759 E_1759 D_1764 E_1764 D_1769 E_1769 D_1775 E_1775 D_1780 E_1780 D_1808 E_1808 D_1809 E_1809 D_1813 E_1813 D_1818 E_1818 D_1827 E_1827 D_1834 E_1834 D_1840 E_1840 D_1844 E_1844 D_1849 E_1849 D_1854 E_1854 D_1861 E_1861 D_1864 E_1864 D_1867 E_1867 D_1872 E_1872 D_1874 E_1874 D_1895 E_1895 LINK_1759 LINK_1764 LINK_1769 LINK_1775 LINK_1780 LINK_1808 LINK_1809 LINK_1813 LINK_1818 LINK_1827 LINK_1834 LINK_1840 LINK_1844 LINK_1849 LINK_1854 LINK_1861 LINK_1864 LINK_1867 LINK_1872 LINK_1874 LINK_1895 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec floatsitf_spec floatunsitf_spec getf2_spec extenddftf2_spec scalbn_spec copysignl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec; exfalso; Z.div_mod_to_equations; lia].
destruct n as [|n2]; [discriminate HL2|]. rewrite hx_norm_loop_S in HL2.
replace (2 ^ 31 <=? x2)%Z with true in HL2 by (symmetry; apply Z.leb_le; lia). injection HL2 as <- <- <-.
stmt L_HFIN. eapply NX; try eassumption. all: hx_side. }
zs. zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D_05); [eassumption | simpF; rewrite <- HF5; do 2 f_equal; apply bv_eq; vm_compute; reflexivity]).
fold H5.
zs. zs. zs. zs. zs. callx (eapply getf2_callE with (X := y) (Y := H5); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_ge_range y H5) as RGE. set (GE := f128_ge y H5) in *.
zs. rewrite shl1_step by lia. replace (u32 (2 * x)) with (2 * x)%Z by (unfold u32; symmetry; apply Z.mod_small; lia).
zs. brs K1.
-
replace (0 <=? GE)%Z with true in HL by (symmetry; apply Z.leb_le; lia).
rewrite lor1_even in HL by (Z.div_mod_to_equations; lia).
destruct (sext32_succ_even (2 * x) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as [SE1 SE2].
pose proof (sext32_range (2 * x)) as RS2.
zs. rewrite ?land_W64. rewrite (lor1_even (sext32 (2 * x))) by exact SE2. rewrite <- SE1.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (ONE := f128_of_i32 1) in *. pose proof (lo64_range ONE). pose proof (hi64_range ONE).
zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply sub_callE with (X := y) (Y := ONE); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (YM1 := f128_sub y ONE) in *. pose proof (lo64_range YM1). pose proof (hi64_range YM1).
zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := y) (Y := YM1); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply TAIL; try eassumption. all: hx_side. all: try (simpF; first [exact HF5 | reflexivity]).
-
replace (0 <=? GE)%Z with false in HL by (symmetry; apply Z.leb_gt; lia).
zs. zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := y) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply TAIL; try eassumption. all: hx_side. all: try (simpF; first [exact HF5 | reflexivity]).
Qed.
End Floatscan.

End G.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA QM7w Q8P7 QTyG QDXD Qe1A Q1u2 Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import QytA QM7w Q8P7 QTyG.Mq1.
Import QCa8.Mq5.
Import QDXD.Mq3.
Import QkTt.Mq6.
Import Qy8Z.Mq1.
Import QROt.Mq5.
Import QSsB.
Import QQRC.Mq4.
Import Qe1A.Mq7.
Import Qe1A.Mqa.
Import Q8l1.
Import Q5m9.Mq9.

Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rmalloc_sym ralloc_meta_entry rmalloc_entry ralloc_slot_entry : Z).
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
Hypothesis AL_rmalloc_sym : gw_al rmalloc_sym 4.
Hypothesis AL_ralloc_meta_entry : gw_al ralloc_meta_entry 4.
Hypothesis AL_rmalloc_entry : gw_al rmalloc_entry 4.
Hypothesis AL_ralloc_slot_entry : gw_al ralloc_slot_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qe1A.Mq7.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq4.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QSsB.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QkTt.Mq6.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Q5m9.Mq9.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qe1A.Mqa.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QROt.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_0)))))))))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@Qe1A.Mqa.rmalloc_fp RATP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qe1A.Mqa.rmalloc_fp RATP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qe1A.Mq7.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq4.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QSsB.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qe1A.Mqa.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QROt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_1)))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qe1A.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QSsB.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qe1A.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq5.rarea_rep segs) (@rarea_rep) gw_tbl_2))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qe1A.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QSsB.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qe1A.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq5.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qe1A.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QSsB.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qe1A.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qe1A.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QSsB.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qe1A.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qe1A.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QSsB.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qe1A.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq5.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qe1A.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QSsB.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qe1A.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq5.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qe1A.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QSsB.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qe1A.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq5.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qe1A.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QSsB.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qe1A.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq5.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qe1A.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QSsB.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qe1A.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qe1A.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QSsB.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qe1A.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Qe1A.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@QSsB.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Q5m9.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qe1A.Mqa.rpres_except segs) (@rpres_except) (gw_ent (@QROt.Mq5.rpres_except segs) (@rpres_except) gw_tbl_12)))))))).
Definition rcoreQ : ltac:(gw_rebind_ty (@QROt.Mq5.rcoreQ segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QROt.Mq5.rcoreQ segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QSsB.rcoreQ segs RATP RGOT_SSP ref_reserved rmalloc_entry RC__) (@rcoreQ) (gw_ent (@Qe1A.Mqa.rcoreQ segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@rcoreQ) (gw_ent (@QROt.Mq5.rcoreQ segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@rcoreQ) gw_tbl_13))).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_15 := (gw_ent (@Qe1A.Mq7.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq4.rimplT segs RC__) (@rimplT) (gw_ent (@QSsB.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@Q5m9.Mq9.rimplT segs RC__) (@rimplT) (gw_ent (@Qe1A.Mqa.rimplT segs RC__) (@rimplT) (gw_ent (@QROt.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_14)))))))).
Definition rbig_stmt : ltac:(gw_rebind_ty (@QROt.Mq5.rbig_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq5.rbig_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QSsB.rbig_stmt segs RATP RGOT_SSP ref_reserved rmalloc_entry RC__) (@rbig_stmt) (gw_ent (@Qe1A.Mqa.rbig_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@rbig_stmt) (gw_ent (@QROt.Mq5.rbig_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@rbig_stmt) gw_tbl_15))).
Definition rAMP_BIG : ltac:(gw_rebind_ty (@Qe1A.Mqa.rAMP_BIG ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Qe1A.Mqa.rAMP_BIG ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@Qe1A.Mqa.rAMP_BIG ref_reserved RC__) (@rAMP_BIG) gw_tbl_16).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Qe1A.Mq7.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq4.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QSsB.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Q5m9.Mq9.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qe1A.Mqa.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QROt.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_17)))))))).
Definition ram_post : ltac:(gw_rebind_ty (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@Qe1A.Mq7.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) (gw_ent (@QQRC.Mq4.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) (gw_ent (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) (gw_ent (@Q5m9.Mq9.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) (gw_ent (@Qe1A.Mqa.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) gw_tbl_18))))).
Definition ralloc_meta_stmt : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@Qe1A.Mq7.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) (gw_ent (@QQRC.Mq4.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) (gw_ent (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) (gw_ent (@Q5m9.Mq9.ralloc_meta_stmt segs ralloc_meta_entry RATP RGOT_SSP ref_reserved RC__) (@ralloc_meta_stmt) (gw_ent (@Qe1A.Mqa.ralloc_meta_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@ralloc_meta_stmt) gw_tbl_19))))).
Definition malloc_core_allzero_stmt : ltac:(gw_rebind_ty (@QSsB.malloc_core_allzero_stmt RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QSsB.malloc_core_allzero_stmt RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QSsB.malloc_core_allzero_stmt RC__) (@malloc_core_allzero_stmt) gw_tbl_20).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@QSsB.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@QkTt.Mq6.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_21))).
Definition RMALLOC_SYM : ltac:(gw_rebind_ty (@QDXD.Mq3.RMALLOC_SYM rmalloc_sym) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RMALLOC_SYM rmalloc_sym) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@QSsB.RMALLOC_SYM rmalloc_sym) (@RMALLOC_SYM) (gw_ent (@QDXD.Mq3.RMALLOC_SYM rmalloc_sym) (@RMALLOC_SYM) gw_tbl_22)).
Definition raddr_exposed : ltac:(gw_rebind_ty (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_23)).
Notation gw_tbl_24 := (gw_ent (@QSsB.raddr_exposed segs RC__) (@raddr_exposed) (gw_ent (@QkTt.Mq6.raddr_exposed segs RC__) (@raddr_exposed) (gw_ent (@QDXD.Mq3.raddr_exposed segs RC__) (@raddr_exposed) gw_tbl_23))).
Definition rblock_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_24)).
Notation gw_tbl_25 := (gw_ent (@QSsB.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@QkTt.Mq6.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@QDXD.Mq3.rblock_range RIMG_HI RC__) (@rblock_range) gw_tbl_24))).
Definition ralloc_static : ltac:(gw_rebind_ty (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_25)).
Notation gw_tbl_26 := (gw_ent (@QSsB.ralloc_static RATP) (@ralloc_static) (gw_ent (@QkTt.Mq6.ralloc_static RATP) (@ralloc_static) (gw_ent (@QDXD.Mq3.ralloc_static RATP) (@ralloc_static) gw_tbl_25))).
Definition rclient_addr : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_26)).
Notation gw_tbl_27 := (gw_ent (@QSsB.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) (gw_ent (@QkTt.Mq6.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) (gw_ent (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) gw_tbl_26))).
Definition rheap_pres : ltac:(gw_rebind_ty (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_27)).
Notation gw_tbl_28 := (gw_ent (@QSsB.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) (gw_ent (@QkTt.Mq6.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) (gw_ent (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) gw_tbl_27))).
Definition rmalloc_post : ltac:(gw_rebind_ty (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_28)).
Notation gw_tbl_29 := (gw_ent (@QSsB.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) (gw_ent (@QkTt.Mq6.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) (gw_ent (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) gw_tbl_28))).
Definition rmalloc_stmt : ltac:(gw_rebind_ty (@QDXD.Mq3.rmalloc_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_sym RC__) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rmalloc_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_sym RC__) constr:(gw_tbl_29)).
Notation gw_tbl_30 := (gw_ent (@QSsB.rmalloc_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_sym RC__) (@rmalloc_stmt) (gw_ent (@QDXD.Mq3.rmalloc_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_sym RC__) (@rmalloc_stmt) gw_tbl_29)).
Definition rmalloc_impl_stmt : ltac:(gw_rebind_ty (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) constr:(gw_tbl_30)).
Notation gw_tbl_31 := (gw_ent (@QSsB.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) (@rmalloc_impl_stmt) (gw_ent (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) (@rmalloc_impl_stmt) gw_tbl_30)).
Definition ras_pre2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_pre2 ref_reserved RC__) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_pre2 ref_reserved RC__) constr:(gw_tbl_31)).
Notation gw_tbl_32 := (gw_ent (@Qe1A.Mq7.ras_pre2 ref_reserved RC__) (@ras_pre2) (gw_ent (@QQRC.Mq4.ras_pre2 ref_reserved RC__) (@ras_pre2) gw_tbl_31)).
Definition ras_post2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_32)).
Notation gw_tbl_33 := (gw_ent (@Qe1A.Mq7.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) (gw_ent (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) gw_tbl_32)).
Definition ralloc_slot_stmt2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ralloc_slot_stmt2 segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ralloc_slot_stmt2 segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_33)).
Notation gw_tbl_34 := (gw_ent (@Qe1A.Mq7.ralloc_slot_stmt2 segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt2) (gw_ent (@QQRC.Mq4.ralloc_slot_stmt2 segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt2) gw_tbl_33)).
Definition ras_post : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_34)).
Notation gw_tbl_35 := (gw_ent (@Qe1A.Mq7.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@QQRC.Mq4.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@QSsB.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@QROt.Mq5.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) gw_tbl_34))))).
Definition ralloc_slot_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_35)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_35)).
Notation gw_tbl_36 := (gw_ent (@Qe1A.Mq7.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) (gw_ent (@QQRC.Mq4.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) (gw_ent (@QSsB.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) (gw_ent (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) (gw_ent (@QROt.Mq5.ralloc_slot_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@ralloc_slot_stmt) gw_tbl_35))))).

Hypothesis ramp_big : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qe1A.Mqa.gw_all) (@Qe1A.Mqa.ramp_big) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).
Hypothesis rbig_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qe1A.Mqa.gw_all) (@Qe1A.Mqa.rbig_spec) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).

Hypothesis ralloc_meta_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q5m9.Mq9.gw_all) (@Q5m9.Mq9.ralloc_meta_spec) ralloc_meta_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).
Hypothesis renf_implT : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq7.gw_all) (@Qy8Z.Mq7.renf_implT) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).
Hypothesis rmalloc_fp_cases : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq8.gw_all) (@QQRC.Mq8.rmalloc_fp_cases) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).
Hypothesis rmalloc_fp_image : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq8.gw_all) (@QQRC.Mq8.rmalloc_fp_image) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).
Hypothesis rauxv_ok_malloc_fp : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq8.gw_all) (@QQRC.Mq8.rauxv_ok_malloc_fp) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).
Hypothesis rmalloc_core_implT : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QROt.Mq5.gw_all) (@QROt.Mq5.rmalloc_core_implT) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_36))) in exact T).
Hypothesis ralloc_slot_ok : gw_hyp (forall (ram_pre : QUZl.mstate -> Prop), ralloc_meta_stmt ram_pre -> QkQT.AMP_AS_g ref_reserved Q6q3.rc_secret ram_pre -> forall f, ralloc_slot_stmt2 f).
Hypothesis rmalloc_stmt_of_impl : gw_hyp (rmalloc_impl_stmt -> rmalloc_stmt).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_36)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmalloc_impl_spec_proof : ltac:(gw_ctx_fold_ty2 (@QSsB.rmalloc_impl_spec_proof) constr:(gw_tbl_36)) := ltac:(gw_ctx_fold_tm2 (@QSsB.rmalloc_impl_spec_proof)).
Definition rmalloc_spec_proof : ltac:(gw_ctx_fold_ty2 (@QSsB.rmalloc_spec_proof) constr:(gw_tbl_36)) := ltac:(gw_ctx_fold_tm2 (@QSsB.rmalloc_spec_proof)).

Definition ras_pre2_intro : ltac:(gw_ctx_fold_ty2 (@Qe1A.Mq7.ras_pre2_intro) constr:(gw_tbl_36)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.Mq7.ras_pre2_intro)).
Definition ralloc_slot_spec : ltac:(gw_ctx_fold_ty2 (@Qe1A.Mq7.ralloc_slot_spec) constr:(gw_tbl_36)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.Mq7.ralloc_slot_spec)).

Notation ram_pre := (am_pre_g ref_reserved rc_secret).

#[using="ralloc_meta_entry rmalloc_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rmalloc_sym ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rmalloc_sym AL_ralloc_meta_entry AL_rmalloc_entry AL_ralloc_slot_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ramp_big rbig_spec ralloc_meta_spec renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT ralloc_slot_ok rmalloc_stmt_of_impl"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

#[using="Type"] Lemma mcz_proof : malloc_core_allzero_stmt.
Proof. clear - segs. exact (@Q1u2.malloc_core_allzero_ctrl _ mem pans_mem pupd_mem pans_mem_range). Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO ralloc_meta_entry ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay ramp_big rbig_spec ralloc_meta_spec renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT ralloc_slot_ok"] Theorem rmalloc_impl_spec : rmalloc_impl_stmt.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO ralloc_meta_entry ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay ramp_big rbig_spec ralloc_meta_spec renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT ralloc_slot_ok.
exact (rmalloc_impl_spec_proof ras_pre2 as_inv2 ralloc_slot_spec mcz_proof ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO ralloc_meta_entry rmalloc_entry ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay ramp_big rbig_spec ralloc_meta_spec renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT ralloc_slot_ok rmalloc_stmt_of_impl"] Theorem rmalloc_spec : rmalloc_stmt.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO ralloc_meta_entry rmalloc_entry ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay ramp_big rbig_spec ralloc_meta_spec renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT ralloc_slot_ok rmalloc_stmt_of_impl.
exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec mcz_proof ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End RC__1.

End G.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsB.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 : Z).
Variables (hi_59 hi_67 hi_145 : bv 20).
Variables (lo_62 lo_70 lo_147 : bv 12).
Variables (joff_15 joff_185 joff_238 : bv 21).
Variables (e_memcpy : Z).
Hypothesis CODE : code_at segs base (realloc_code w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1092.
Let rmremap_entry := (rvm_wait_entry + 312)%Z.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Jal 1 joff_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (Auipc 15 hi_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_62 : decode_any (Z_to_bv 32 w_62) = Some (Load SZ8 true 15 15 lo_62, 4%Z).
Hypothesis E_62 : is_ecall (Z_to_bv 32 w_62) = false.
Hypothesis D_67 : decode_any (Z_to_bv 32 w_67) = Some (Auipc 15 hi_67, 4%Z).
Hypothesis E_67 : is_ecall (Z_to_bv 32 w_67) = false.
Hypothesis D_70 : decode_any (Z_to_bv 32 w_70) = Some (OpImm ALU_ADD 15 15 lo_70, 4%Z).
Hypothesis E_70 : is_ecall (Z_to_bv 32 w_70) = false.
Hypothesis D_145 : decode_any (Z_to_bv 32 w_145) = Some (Auipc 6 hi_145, 4%Z).
Hypothesis E_145 : is_ecall (Z_to_bv 32 w_145) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (OpImm ALU_ADD 6 6 lo_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_185 : decode_any (Z_to_bv 32 w_185) = Some (Jal 1 joff_185, 4%Z).
Hypothesis E_185 : is_ecall (Z_to_bv 32 w_185) = false.
Hypothesis D_238 : decode_any (Z_to_bv 32 w_238) = Some (Jal 1 joff_238, 4%Z).
Hypothesis E_238 : is_ecall (Z_to_bv 32 w_238) = false.
Hypothesis ANCH_62 : gw_anch (Z.shiftl (bv_signed hi_59) 12 + (base + 236) + bv_signed lo_62)%Z (RATP + 131968).
Hypothesis ANCH_70 : gw_anch (Z.shiftl (bv_signed hi_67) 12 + (base + 268) + bv_signed lo_70)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_147 : gw_anch (Z.shiftl (bv_signed hi_145) 12 + (base + 580) + bv_signed lo_147)%Z RDEBRUIJN.
Hypothesis LINK_15 : gw_anch (base + 60 + bv_signed joff_15)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_185 : gw_anch (base + 740 + bv_signed joff_185)%Z (rmremap_entry + 0)%Z.
Hypothesis LINK_238 : gw_anch (base + 952 + bv_signed joff_238)%Z (e_memcpy + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QSsB.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QSsB.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QSsB.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QSsB.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QSsB.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QSsB.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QSsB.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QSsB.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QSsB.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QSsB.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_10))).

Hypothesis lor_shl5 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.lor_shl5) (base + -712)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-712)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).

Definition rmrep_havoc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_havoc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_havoc)).

Definition rr_epilogue : ltac:(gw_ctx_fold_ty2 (@QSsB.Mq9.rr_epilogue) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QSsB.Mq9.rr_epilogue)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rpres_write : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rpres_write) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rpres_write)).

Definition rwr8_rep : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rwr8_rep) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rwr8_rep)).
Definition rwr32_rep : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rwr32_rep) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rwr32_rep)).

#[using="RDEBRUIJN rerrno_loc_entry rmremap_entry e_memcpy RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_15 E_15 D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 D_145 E_145 D_147 E_147 D_185 E_185 D_238 E_238 ANCH_62 ANCH_70 ANCH_147 LINK_15 LINK_185 LINK_238 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmremap_entry lor_shl5"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rr_ss_mem (m : word -> option byte) (P E n k : Z) : word -> option byte :=
let r := E - P - n in
let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition rr_inplace_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (P E n k : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ m' = rr_ss_mem m P E n k
/\ mem_inv segs m'.

#[using="Type"] Lemma land31_idem k : Z.land (Z.land k 31) 31 = Z.land k 31.
Proof. clear - k. rewrite <- Z.land_assoc. reflexivity. Qed.
End RC__1.

Ltac read_k := lazymatch goal with BKc : bytes_at segs ?mc (?P - 3) [b8 ?k] |- _ =>
pose proof (bytes_at_read segs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at segs ?mc (?P - 3) _ |- _ =>
let H := fresh "SO" in
pose proof (wr_at_store_ok segs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section RC__2.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 CODE ROM_reservedZ LAY_ref_reserved lor_shl5 rmremap_entry"] Lemma rr_inplace_walk : forall (ra sp gp tp t1 t2 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(v0 v1 v2 v3 v4 v5 v6 : word) F fc (m : word -> option byte) (P E n k lo : Z),
mem_inv segs m ->
wr_at segs m (P - 3) (E - P + 3) ->
bytes_at segs m (P - 3) [b8 k] ->
rw_cells segs m (bv_unsigned sp + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra] ->
E + 1 <= lo -> lo <= bv_unsigned sp + -64 ->
16 <= P -> P + n <= E -> E - P - n < 2^31 -> 0 <= n -> 0 <= k < 256 ->
evt segs (rr_inplace_post ra sp gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t5 t6 (Z_to_bv 64 P) F fc m P E n k)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t1 t2 s0 s1
(Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x3cc)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 CODE ROM_reservedZ LAY_ref_reserved lor_shl5 rmremap_entry segs base.
intros until lo. intros MI WR BK FR ELO LOS P16 PNE EP N0 HK.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
set (r := E - P - n).
assert (K31 : 0 <= Z.land k 31 < 32).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32. split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia. }

assert (J : forall (a1v a2v t0v : word) (m4 : word -> option byte) (r' : Z),
a1v = Z_to_bv 64 r' -> 0 <= r' <= 5 ->
mem_inv segs m4 -> wr_at segs m4 (P - 3) (E - P + 3) -> bytes_at segs m4 (P - 3) [b8 k] ->
rw_cells segs m4 (bv_unsigned sp + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra] ->
(let '(m4', r'') := (if 5 <=? r then (write_to_mem (write_to_mem (if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0]) (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5)
else ((if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0]), r)) in m4 = m4' /\ r' = r'') ->
evt segs (rr_inplace_post ra sp gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t5 t6 (Z_to_bv 64 P) F fc m P E n k)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0v t1 t2 s0 s1
(Z_to_bv 64 P) a1v a2v a3 a4 a5 (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x408)) fc None m4 (seg_rom segs))).
{ intros a1v a2v t0v m4 r' -> R' MI4 WR4 BK4 FR4 HM.
clear MI WR BK FR.

read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k) by lia.
step. rewrite ?(unsigned_lit r'), (Z.shiftl_mul_pow2 r') by lia.
step. rewrite ?(unsigned_lit (r' * 2 ^ 5)), ?(unsigned_lit (Z.land k 31)) by lia.
rewrite (lor_shl5 r' (Z.land k 31)) by lia. rewrite !land31_idem.
assert (BV : 0 <= Z.land k 31 + Z.shiftl r' 5 < 256) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
sok 0 1%nat (P + -3).
step. change (le1 (Z_to_bv 64 (Z.land k 31 + Z.shiftl r' 5))) with (le1 (wz (Z.land k 31 + Z.shiftl r' 5))).
rewrite (le1_wz (Z.land k 31 + Z.shiftl r' 5)) by gw_exact BV. sdk.
eapply rr_epilogue; [eassumption|].
unfold rr_inplace_post. do 13 eexists. split; [reflexivity|]. split; [|assumption].
unfold rr_ss_mem. fold r.
destruct (5 <=? r); destruct HM as [-> ->]; subst; reflexivity. }

step. step. rewrite ?(unsigned_lit E), ?(unsigned_lit (n + P)), ?(unsigned_lit n), ?(unsigned_lit P) by lia.
rewrite (swrap32_small (E - (n + P))) by lia. replace (E - (n + P)) with r by lia.

step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
-
step. step. eapply (J _ _ _ m 0); try eassumption; [reflexivity| lia|].
rewrite KR. change (5 <=? 0) with false. change (0 =? 0) with true. cbv beta iota zeta. split; [subst; reflexivity| reflexivity].
-
step. rewrite ?(unsigned_lit E), ?(unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
replace (E - (n + P)) with r by lia.
step. rewrite ?(unsigned_lit r), (swrap32_small (0 - r)) by lia.
step. replace (E + (0 - r)) with (E - r + 0) by lia.
step.
sok (n + 3) 1%nat (E - r + 0).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
+
step. eapply (J _ _ _ _ r); try eassumption; [reflexivity| lia|].
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia).
split; [|reflexivity]. subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
+
sok (E - P - 2) 1%nat (E + 4 + -9).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
sok (E - P - 1) 4%nat (E + 4 + -8).
step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
step. eapply (J _ _ _ _ 5); try eassumption; [reflexivity| lia|].
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia).
split; [|reflexivity]. subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End RC__2.

Import QJE4.Mq4.

Section RC__3.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmremap_entry"] Lemma rr_inplace_mrep : forall (st0 : mstate) (m1 : word -> option byte) (g b : aptr) (r : region) (i n off k : Z) (p e : aptr),
let stride := get_stride (get_meta_rec st0 g) in
rmrep st0 m1 -> ticks_ok st0 ->
(s_regions st0) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> 0 <= i < 32 ->
snd b + 16 + stride * (i + 1) <= round_up_pg (r_len r) -> 16 <= stride ->
(forall b' gh, (s_groups st0) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * i - 4 \/ snd b + 16 + stride * i + stride - 4 <= snd b') ->
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> stride - 4 - 16 * off - n < 2^32 -> 0 <= k < 256 ->
fst p = fst b -> snd p = snd b + 16 + stride * i + 16 * off ->
fst e = fst b -> snd e = snd b + 16 + stride * i + stride - 4 ->
rmrep (havoc p n (set_size p e n k st0)) (rr_ss_mem m1 (r_base r + snd p) (r_base r + snd e) n k)
/\ ticks_ok (havoc p n (set_size p e n k st0)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmremap_entry.
intros until e. intros stride MR TK Hr Hk B0 I0 SPAN S16 NOGRP OFF0 N0 FIT R32 HK Fp Sp Fe Se.
assert (SK : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; lia).
pose proof (fun stx mx o v => rwr8_rep st0 g b r i n Hr Hk B0 I0 SPAN S16 NOGRP stx mx o v) as W8.
pose proof (fun stx mx o v => rwr32_rep st0 g b r i n Hr Hk B0 I0 SPAN S16 NOGRP stx mx o v) as W32.
cbv zeta in W8, W32. fold stride in W8, W32.
enough (H : rmrep (set_size p e n k st0) (rr_ss_mem m1 (r_base r + snd p) (r_base r + snd e) n k) /\ ticks_ok (set_size p e n k st0))
by exact (rmrep_havoc _ _ p n (proj1 H) (proj2 H)).
unfold set_size, rr_ss_mem, aadd. rewrite Fp, Sp, Fe, Se. cbn [fst snd].
set (rsv := snd b + 16 + stride * i + stride - 4 - (snd b + 16 + stride * i + 16 * off) - n).
replace (r_base r + (snd b + 16 + stride * i + stride - 4) - (r_base r + (snd b + 16 + stride * i + 16 * off)) - n) with rsv by (unfold rsv; lia).
assert (RSV : 0 <= rsv <= stride - 4 - n /\ rsv = stride - 4 - 16 * off - n) by (unfold rsv; lia).
set (stF := if negb (rsv =? 0) then _ else _).
set (mF := if rsv =? 0 then _ else _).
assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st0 /\ s_groups stF = s_groups st0).
{ subst stF mF. destruct (Z.eqb_spec rsv 0) as [E0|NE]; cbn [negb].
- split; [gw_exact MR|]. split; [gw_exact TK|]. split; reflexivity.
- destruct (W8 st0 m1 (snd b + 16 + stride * i + stride - 4 + - rsv) 0 MR TK eq_refl eq_refl) as [MF TF]; [lia| lia|].
replace (r_base r + (snd b + 16 + stride * i + stride - 4) - rsv) with (r_base r + (snd b + 16 + stride * i + stride - 4 + - rsv)) by lia.
split; [gw_exact MF|]. split; [gw_exact TF|]. split; reflexivity. }
clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
set (stG := if 5 <=? rsv then _ else _).
set (mG := if 5 <=? rsv then _ else _).
assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
/\ s_regions (fst stG) = s_regions st0 /\ s_groups (fst stG) = s_groups st0).
{ subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
-
rewrite (wr32_wr8_comm st0 g b i n I0 (fst b, snd b + 16 + stride * i + stride - 4 + -4) (fst b, snd b + 16 + stride * i + stride - 4 + -5)) by (cbn; lia || reflexivity).
destruct (W8 _ _ (snd b + 16 + stride * i + stride - 4 + -5) 0 MF TF ERf EGf) as [M1 T1]; [lia| lia|].
destruct (W32 _ _ (snd b + 16 + stride * i + stride - 4 + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [lia| lia| lia|].
replace (r_base r + (snd b + 16 + stride * i + stride - 4) - 4) with (r_base r + (snd b + 16 + stride * i + stride - 4 + -4)) by lia.
replace (r_base r + (snd b + 16 + stride * i + stride - 4) - 5) with (r_base r + (snd b + 16 + stride * i + stride - 4 + -5)) by lia.
split; [gw_exact M2|]. split; [gw_exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
- split; [gw_exact MF|]. split; [gw_exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
destruct PG as (MG & TG & -> & R2 & ERg & EGg).
assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
{ rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
assert (0 <= Z.land k 31 < 32).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32. split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia. }
lia. }
destruct (W8 _ _ (snd b + 16 + stride * i + 16 * off + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [lia| gw_exact KV|].
replace (r_base r + (snd b + 16 + stride * i + 16 * off) - 3) with (r_base r + (snd b + 16 + stride * i + 16 * off + -3)) by lia.
split; [gw_exact MH| gw_exact TH].
Qed.

#[using="rvm_wait_entry rmremap_entry"] Lemma rpres_rr_ss : forall (C : Z -> Prop) m0 m P E n k,
rpres_except C m0 m ->
16 <= P -> P + n <= E -> 0 <= n -> E + 1 <= 2^64 ->
C (P - 3) -> (forall x, P + n <= x < E -> C x) ->
rpres_except C m0 (rr_ss_mem m P E n k).
Proof. clear - rvm_wait_entry rmremap_entry.
intros C m0 m P E n k HP P16 PNE N0 ETOP HC3 HC.
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
unfold rr_ss_mem. cbv zeta.
set (r := E - P - n).
set (mF := if r =? 0 then _ else _).
assert (HF : rpres_except C m0 mF).
{ subst mF. destruct (Z.eqb_spec r 0); [gw_exact HP|]. apply rpres_write; [gw_exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mF.
set (mG := if 5 <=? r then _ else _).
assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 r); cbn [fst snd].
- split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
apply rpres_write; [gw_exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
- split; [gw_exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply rpres_write; [gw_exact HG| lia | cbn; lia | cbn; intros x Hx; replace x with (P - 3) by lia; gw_exact HC3].
Qed.

End RC__3.

End G.
