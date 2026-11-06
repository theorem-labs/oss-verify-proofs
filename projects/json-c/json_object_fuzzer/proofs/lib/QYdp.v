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
Variables (joff_1125 joff_1132 joff_1135 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1125 : decode_any (Z_to_bv 32 w_1125) = Some (Jal 1 joff_1125, 4%Z).
Hypothesis E_1125 : is_ecall (Z_to_bv 32 w_1125) = false.
Hypothesis D_1132 : decode_any (Z_to_bv 32 w_1132) = Some (Jal 1 joff_1132, 4%Z).
Hypothesis E_1132 : is_ecall (Z_to_bv 32 w_1132) = false.
Hypothesis D_1135 : decode_any (Z_to_bv 32 w_1135) = Some (Jal 1 joff_1135, 4%Z).
Hypothesis E_1135 : is_ecall (Z_to_bv 32 w_1135) = false.
Hypothesis LINK_1125 : gw_anch (base + 4500 + bv_signed joff_1125)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_1132 : gw_anch (base + 4528 + bv_signed joff_1132)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1135 : gw_anch (base + 4540 + bv_signed joff_1135)%Z (e_addtf3 + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
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
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_27))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_28))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_29))).
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
Definition S_A62C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A62C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A62C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.S_A62C segs base got_ssp RATP STRING_READ ssp_guard) S_A62C gw_tbl_37).
Definition S_A5C4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A5C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A5C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_A5C4 segs base got_ssp RATP STRING_READ ssp_guard) S_A5C4 gw_tbl_38).
Hypothesis floatunsitf_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq4.gw_all) (@QQLG.Mq4.floatunsitf_spec) e_floatunsitf)) in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatunsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs e_addtf3) 5%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QDXD.Mq0.addtf3_post segs) addtf3_post in exact T).  Arguments addtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
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

Definition floatunsitf_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatunsitf_callv) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatunsitf_callv)).

Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition cb44_merge : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb44_merge) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb44_merge)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__S_A5C4 := S_A5C4 (only parsing).
Notation F_floatscan_common__S_A62C := S_A62C (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1125 joff_1132 joff_1135 got_ssp RATP STRING_READ ssp_guard e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_A62C := (@F_floatscan_common__S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A5C4 := (@F_floatscan_common__S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold F_floatscan_common__dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.
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

Hypothesis HS_A62C : S_A62C.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1125 joff_1132 joff_1135 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A62C"] Lemma L_A5C4 : S_A5C4.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1125 joff_1132 joff_1135 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (1 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 1) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 1) 2047) in *.
assert (Ek : kk = ((a + 1) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.

assert (G648 : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (h' = false -> z' + 2 <= 2052)%Z -> (2 <= (z' - a) mod 2048)%Z ->
df_asm_loop f a (mkAS 2 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) z' x') = Some sres ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) x9 (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1184)) fct None m' (seg_rom segs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Rz4' Hrs' HL'.
clear HL MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (X312 kk) as Rt. pose proof (REL2 kk ltac:(lia) (zone_in _ _ _ _ _ Kin)) as Et.
pose proof (u32arr_read segs _ _ _ kk _ _ XW (nth_error_wnth ws' kk ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws' kk (znth x' kk) (eq_sym Et) Rt).
set (t := znth x' kk) in *.
zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 Y) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_A62C. eapply NX; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW2 | split; [exact LX2 | exact REL2]] |]. split; [exact X312|]. split; [lia|]. split; [hlia Rz4'|]. split; [lia|]. exact Raw. }
zs. zs. replace (1 + a)%Z with (a + 1)%Z by lia. replace (a + 1 + 0)%Z with (a + 1)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia).
destruct (inring_plus a z 1 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G648 _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | hlia Rz4 | exact Hrs' | exact HL].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 1 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 2) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 2) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs. zs.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
+
rewrite Ez in HL. rewrite Ez. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
assert (Ekz : kk = z) by lia.
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; rewrite Ek in Ekz; clear - Raw Ekz Ra Ez w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1125 joff_1132 joff_1135 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia]).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; cbn; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
eapply (G648 _ ws x 0%Z false); [mk_dfinv | | exact X31H | | lia | lia | | exact HL].
* eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear - Hq Hne Ri0 Ra Rz Ez Hrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1125 joff_1132 joff_1135 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
* unfold inring. clear - Ra Rz Ez Hrs0 Rk K1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1125 joff_1132 joff_1135 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
* clear - Ra Rz Ez Hrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1125 joff_1132 joff_1135 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1125 E_1125 D_1132 E_1132 D_1135 E_1135 LINK_1125 LINK_1132 LINK_1135 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
+
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL.
fix_idx.
pose proof (u32arr_store_ok segs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
let v := getreg 11%Z in replace v with (Z_to_bv 64 (XA + 4 * z + 4)%Z) by (f_equal; lia).
zs.
pose proof (u32arr_write segs _ _ _ z (Z_to_bv 64 0) XW ltac:(lia)) as XW'. clear XW.
replace (q + -8312 + 4 * z + 4 + -4)%Z with (q + -8312 + 4 * z)%Z by lia.
store_done. rename XW' into XW.
assert (XR' : xrel (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (zone h w a (z + 1))).
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hi0 Hr.
destruct (Z.eq_dec i0 z) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|].
destruct Hr as [Hr | [[Hh Hzi] | Hr]]; [| right; left; split; [exact Hh | lia] | right; right; exact Hr].
apply (proj1 (inring_grow a z i0 ltac:(lia) ltac:(lia))) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a z i0); lia. }
assert (X31' : X31 (zupd x z 0)).
{ intros i0. destruct (Z.eq_dec i0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
eapply (G648 _ (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (z + 1)%Z h);
[mk_dfinv | exact XR' | exact X31' | | lia | hlia Rz4 | | exact HL].
* apply (proj2 (inring_grow a z kk ltac:(lia) ltac:(lia))). right. rewrite Ek, Zminus_mod_idemp_l, Hrs0. f_equal. lia.
* replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)), Hrs0, Z.mod_small by lia. lia.
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
Variables (joff_1178 joff_1185 joff_1188 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1178 : decode_any (Z_to_bv 32 w_1178) = Some (Jal 1 joff_1178, 4%Z).
Hypothesis E_1178 : is_ecall (Z_to_bv 32 w_1178) = false.
Hypothesis D_1185 : decode_any (Z_to_bv 32 w_1185) = Some (Jal 1 joff_1185, 4%Z).
Hypothesis E_1185 : is_ecall (Z_to_bv 32 w_1185) = false.
Hypothesis D_1188 : decode_any (Z_to_bv 32 w_1188) = Some (Jal 1 joff_1188, 4%Z).
Hypothesis E_1188 : is_ecall (Z_to_bv 32 w_1188) = false.
Hypothesis LINK_1178 : gw_anch (base + 4712 + bv_signed joff_1178)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_1185 : gw_anch (base + 4740 + bv_signed joff_1185)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1188 : gw_anch (base + 4752 + bv_signed joff_1188)%Z (e_addtf3 + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
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
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_27))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_28))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_29))).
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
Definition S_F1 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_F1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_F1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.S_F1 segs base got_ssp RATP STRING_READ ssp_guard) S_F1 gw_tbl_37).
Definition S_A69C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A69C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A69C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_A69C segs base got_ssp RATP STRING_READ ssp_guard) S_A69C gw_tbl_38).
Hypothesis floatunsitf_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq4.gw_all) (@QQLG.Mq4.floatunsitf_spec) e_floatunsitf)) in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatunsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs e_addtf3) 5%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QDXD.Mq0.addtf3_post segs) addtf3_post in exact T).  Arguments addtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
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

Definition floatunsitf_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatunsitf_callv) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatunsitf_callv)).

Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition cb44_merge : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb44_merge) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb44_merge)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__S_A69C := S_A69C (only parsing).
Notation F_floatscan_common__S_F1 := S_F1 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1178 joff_1185 joff_1188 got_ssp RATP STRING_READ ssp_guard e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_F1 := (@F_floatscan_common__S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A69C := (@F_floatscan_common__S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_F1 : S_F1.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1178 joff_1185 joff_1188 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_F1"] Lemma L_A69C : S_A69C.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1178 joff_1185 joff_1188 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (3 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 3) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 3) 2047) in *.
assert (Ek : kk = ((a + 3) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL.

assert (G6BC : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (4 <= (z' - a) mod 2048)%Z ->
fin_K1 53 (-1074) sign 1024 zero0 a z' x' 4 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1258)) fct None m' (seg_rom segs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Hrs' HK'.
clear HL HK MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (X312 kk) as Rt. pose proof (REL2 kk ltac:(lia) (zone_in _ _ _ _ _ Kin)) as Et.
pose proof (u32arr_read segs _ _ _ kk _ _ XW (nth_error_wnth ws' kk ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws' kk (znth x' kk) (eq_sym Et) Rt).
set (t := znth x' kk) in *.
zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 Y) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_F1. eapply NX; try eassumption; try lia; try mk_dfinv.
- apply (xrel_window _ _ h' w); split; [exact LW2 | split; [exact LX2 | exact REL2]].
- intros Hne. change MASK with 2047%Z in Hne |- *. destruct (inring_plus a z' 4 ltac:(lia) ltac:(lia) ltac:(lia) Hne) as [Hin' _]. exact Hin'. }
zs. replace (3 + a)%Z with (a + 3)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [as_i] in HL.
change (3 + 1 <? LD_B1B_DIG)%Z with false in HL. injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
destruct (inring_plus a z 3 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G6BC _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | exact Hrs' | exact HK].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 3 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
cbn [as_i] in HL. change (3 + 1 <? LD_B1B_DIG)%Z with false in HL. rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 4) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 4) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs. zs. showall.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
+
rewrite Ez in HL. rewrite Ez. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
assert (Ekz : kk = z) by lia.
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; rewrite Ek in Ekz; clear - Raw Ekz Ra Ez w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1178 joff_1185 joff_1188 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia]).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; cbn; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
eapply (G6BC _ ws x 0%Z false); [mk_dfinv | | exact X31H | | lia | | exact HK].
* eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear - Hq Hne Ri0 Ra Rz Ez Hrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1178 joff_1185 joff_1188 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
* unfold inring. clear - Ra Rz Ez Hrs0 Rk K1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1178 joff_1185 joff_1188 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
* clear - Ra Rz Ez Hrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1178 joff_1185 joff_1188 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1178 E_1178 D_1185 E_1185 D_1188 E_1188 LINK_1178 LINK_1185 LINK_1188 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
+
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL. injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
fix_idx.
pose proof (u32arr_store_ok segs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
let v := getreg 11%Z in replace v with (Z_to_bv 64 (XA + 4 * z + 4)%Z) by (f_equal; lia).
zs.
pose proof (u32arr_write segs _ _ _ z (Z_to_bv 64 0) XW ltac:(lia)) as XW'. clear XW.
replace (q + -8312 + 4 * z + 4 + -4)%Z with (q + -8312 + 4 * z)%Z by lia.
store_done. rename XW' into XW.
assert (XR' : xrel (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (zone h w a (z + 1))).
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hi0 Hr.
destruct (Z.eq_dec i0 z) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|].
destruct Hr as [Hr | [[Hh Hzi] | Hr]]; [| right; left; split; [exact Hh | lia] | right; right; exact Hr].
apply (proj1 (inring_grow a z i0 ltac:(lia) ltac:(lia))) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a z i0); lia. }
assert (X31' : X31 (zupd x z 0)).
{ intros i0. destruct (Z.eq_dec i0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
eapply (G6BC _ (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (z + 1)%Z h);
[mk_dfinv | exact XR' | exact X31' | | lia | | exact HK].
* apply (proj2 (inring_grow a z kk ltac:(lia) ltac:(lia))). right. rewrite Ek, Zminus_mod_idemp_l, Hrs0. f_equal. lia.
* replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)), Hrs0, Z.mod_small by lia. lia.
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
Variables (hi_1278 hi_1281 hi_1284 hi_1290 : bv 20).
Variables (lo_1279 lo_1282 lo_1285 lo_1291 : bv 12).
Variables (joff_1294 joff_1299 joff_1306 joff_1311 joff_1314 joff_1321 : bv 21).
Variables (G_10778 G_10788 G_10798 got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_extenddftf2 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1278 : decode_any (Z_to_bv 32 w_1278) = Some (Auipc 10 hi_1278, 4%Z).
Hypothesis E_1278 : is_ecall (Z_to_bv 32 w_1278) = false.
Hypothesis D_1279 : decode_any (Z_to_bv 32 w_1279) = Some (FLoad FMT_D 14 10 lo_1279, 4%Z).
Hypothesis E_1279 : is_ecall (Z_to_bv 32 w_1279) = false.
Hypothesis D_1281 : decode_any (Z_to_bv 32 w_1281) = Some (Auipc 10 hi_1281, 4%Z).
Hypothesis E_1281 : is_ecall (Z_to_bv 32 w_1281) = false.
Hypothesis D_1282 : decode_any (Z_to_bv 32 w_1282) = Some (FLoad FMT_D 15 10 lo_1282, 4%Z).
Hypothesis E_1282 : is_ecall (Z_to_bv 32 w_1282) = false.
Hypothesis D_1284 : decode_any (Z_to_bv 32 w_1284) = Some (Auipc 10 hi_1284, 4%Z).
Hypothesis E_1284 : is_ecall (Z_to_bv 32 w_1284) = false.
Hypothesis D_1285 : decode_any (Z_to_bv 32 w_1285) = Some (FLoad FMT_D 15 10 lo_1285, 4%Z).
Hypothesis E_1285 : is_ecall (Z_to_bv 32 w_1285) = false.
Hypothesis D_1290 : decode_any (Z_to_bv 32 w_1290) = Some (Auipc 10 hi_1290, 4%Z).
Hypothesis E_1290 : is_ecall (Z_to_bv 32 w_1290) = false.
Hypothesis D_1291 : decode_any (Z_to_bv 32 w_1291) = Some (FLoad FMT_D 14 10 lo_1291, 4%Z).
Hypothesis E_1291 : is_ecall (Z_to_bv 32 w_1291) = false.
Hypothesis D_1294 : decode_any (Z_to_bv 32 w_1294) = Some (Jal 1 joff_1294, 4%Z).
Hypothesis E_1294 : is_ecall (Z_to_bv 32 w_1294) = false.
Hypothesis D_1299 : decode_any (Z_to_bv 32 w_1299) = Some (Jal 1 joff_1299, 4%Z).
Hypothesis E_1299 : is_ecall (Z_to_bv 32 w_1299) = false.
Hypothesis D_1306 : decode_any (Z_to_bv 32 w_1306) = Some (Jal 1 joff_1306, 4%Z).
Hypothesis E_1306 : is_ecall (Z_to_bv 32 w_1306) = false.
Hypothesis D_1311 : decode_any (Z_to_bv 32 w_1311) = Some (Jal 1 joff_1311, 4%Z).
Hypothesis E_1311 : is_ecall (Z_to_bv 32 w_1311) = false.
Hypothesis D_1314 : decode_any (Z_to_bv 32 w_1314) = Some (Jal 1 joff_1314, 4%Z).
Hypothesis E_1314 : is_ecall (Z_to_bv 32 w_1314) = false.
Hypothesis D_1321 : decode_any (Z_to_bv 32 w_1321) = Some (Jal 1 joff_1321, 4%Z).
Hypothesis E_1321 : is_ecall (Z_to_bv 32 w_1321) = false.
Hypothesis ANCH_1279 : gw_anch (Z.shiftl (bv_signed hi_1278) 12 + (base + 5112) + bv_signed lo_1279)%Z G_10788.
Hypothesis ANCH_1282 : gw_anch (Z.shiftl (bv_signed hi_1281) 12 + (base + 5124) + bv_signed lo_1282)%Z G_10798.
Hypothesis ANCH_1285 : gw_anch (Z.shiftl (bv_signed hi_1284) 12 + (base + 5136) + bv_signed lo_1285)%Z G_10778.
Hypothesis ANCH_1291 : gw_anch (Z.shiftl (bv_signed hi_1290) 12 + (base + 5160) + bv_signed lo_1291)%Z G_10778.
Hypothesis LINK_1294 : gw_anch (base + 5176 + bv_signed joff_1294)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_1299 : gw_anch (base + 5196 + bv_signed joff_1299)%Z (e_addtf3 + 0)%Z.
Hypothesis LINK_1306 : gw_anch (base + 5224 + bv_signed joff_1306)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1311 : gw_anch (base + 5244 + bv_signed joff_1311)%Z (e_extendsftf2 + 388)%Z.
Hypothesis LINK_1314 : gw_anch (base + 5256 + bv_signed joff_1314)%Z (e_letf2 + 0)%Z.
Hypothesis LINK_1321 : gw_anch (base + 5284 + bv_signed joff_1321)%Z (e_addtf3 + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis RNG_G_10788 : gw_br G_10788 8.
Hypothesis ROM_G_10788 : ro_bytes segs G_10788 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 224; Z_to_bv 8 63].
Hypothesis RNG_G_10798 : gw_br G_10798 8.
Hypothesis ROM_G_10798 : ro_bytes segs G_10798 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 208; Z_to_bv 8 63].
Hypothesis RNG_G_10778 : gw_br G_10778 8.
Hypothesis ROM_G_10778 : ro_bytes segs G_10778 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 232; Z_to_bv 8 63].
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
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_27))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_28))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_29))).
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
Definition S_F3 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_F3 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_F3 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.S_F3 segs base got_ssp RATP STRING_READ ssp_guard) S_F3 gw_tbl_37).
Definition S_F2 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_F2 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_F2 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_F2 segs base got_ssp RATP STRING_READ ssp_guard) S_F2 gw_tbl_38).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis rfmodl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq0.gw_all) (@Q8l1.Mq0.rfmodl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).
Hypothesis letf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.letf2_spec segs e_letf2) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QVbl.Mq2.letf2_post segs) letf2_post in exact T).  Arguments letf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs e_addtf3) 5%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QDXD.Mq0.addtf3_post segs) addtf3_post in exact T).  Arguments addtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).

Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
Ltac fixw2 := rewrite ?swrap32_landW, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.

Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition letf2_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.letf2_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.letf2_callE)).
Definition fmodl_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.fmodl_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.fmodl_callE)).
Definition extenddftf2_callF : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.extenddftf2_callF) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.extenddftf2_callF)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Definition F_floatscan_common__Fok_trans10 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_trans10) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_trans10)).
Notation F_floatscan_common__S_F2 := S_F2 (only parsing).
Notation F_floatscan_common__S_F3 := S_F3 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="G_10778 G_10788 G_10798 got_ssp RATP STRING_READ ssp_guard e_extenddftf2 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1278 E_1278 D_1279 E_1279 D_1281 E_1281 D_1282 E_1282 D_1284 E_1284 D_1285 E_1285 D_1290 E_1290 D_1291 E_1291 D_1294 E_1294 D_1299 E_1299 D_1306 E_1306 D_1311 E_1311 D_1314 E_1314 D_1321 E_1321 ANCH_1279 ANCH_1282 ANCH_1285 ANCH_1291 LINK_1294 LINK_1299 LINK_1306 LINK_1311 LINK_1314 LINK_1321 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 RNG_G_10798 ROM_G_10798 RNG_G_10778 ROM_G_10778 LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec rfmodl_spec letf2_spec addtf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

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
Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).
Local Notation Fok_trans10 := (@F_floatscan_common__Fok_trans10 F).
Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_F3 := (@F_floatscan_common__S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F2 := (@F_floatscan_common__S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Notation POST := (fs_post m0).

Hypothesis HS_F3 : S_F3.

Ltac pickC := first [left; reflexivity | right; left; reflexivity | right; right; reflexivity].

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1306 joff_1311 joff_1314 joff_1321 e_letf2 e_floatsitf e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1306 E_1306 D_1311 E_1311 D_1314 E_1314 D_1321 E_1321 LINK_1306 LINK_1311 LINK_1314 LINK_1321 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec rfmodl_spec letf2_spec addtf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_8BC : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
match (if 2 <=? LDBL_MANT_DIG_ - bits' then
let one := f128_of_i32 1 in
match m_fmodl FR one with
| None => None
| Some rr => if f128_le rr 0 =? 0 then Some (f128_add FR C_ONE) else Some FR
end
else Some FR) with
| None => None
| Some frac => fin_K3 1024 Y frac BI e2
end = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1458)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1306 joff_1311 joff_1314 joff_1321 e_letf2 e_floatsitf e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1306 E_1306 D_1311 E_1311 D_1314 E_1314 D_1321 E_1321 LINK_1306 LINK_1311 LINK_1314 LINK_1321 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec rfmodl_spec letf2_spec addtf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros until bits'. intros DI RJ Hk FOK FRM' Hsg He2 Hb HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
change LDBL_MANT_DIG_ with 113%Z in HK.
replace (2 <=? 113 - bits')%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbv beta iota in HK.
destruct (m_fmodl FR (f128_of_i32 1)) as [rr|] eqn:HFM; [|discriminate HK].
zs. fixw2. zs. zs. (brf K1; [ exfalso; lia | ]); try (exfalso; mlia2).
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
pose proof (lo64_range (f128_of_i32 1)). pose proof (hi64_range (f128_of_i32 1)).
zs. zs. zs. zs. zs.
callx (eapply fmodl_callE with (X := FR) (Y := f128_of_i32 1) (r := rr); [eassumption | eassumption | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact HFM]).
match goal with H : forall k : bv 5, _ -> reg_get _ k = reg_get _ k |- _ => rename H into FOK1 end.
pose proof (lo64_range rr). pose proof (hi64_range rr).
zs. zs. zs. callx (eapply letf2_callE with (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range rr 0) as RLE.
zs. brf K2.
-
replace (f128_le rr 0 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; mlia2).
stmt HS_F3. eapply NX; try eassumption; try lia. mk_dfinv. eapply Fok_trans10; eassumption.
- replace (f128_le rr 0 =? 0)%Z with true in HK by (symmetry; apply Z.eqb_eq; mlia2).
zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE with (Y := C_ONE); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs.
stmt HS_F3. eapply NX; try eassumption; try lia. mk_dfinv. eapply Fok_trans10; eassumption.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1294 joff_1299 joff_1306 joff_1311 joff_1314 joff_1321 e_extenddftf2 e_letf2 e_floatsitf e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1294 E_1294 D_1299 E_1299 D_1306 E_1306 D_1311 E_1311 D_1314 E_1314 D_1321 E_1321 LINK_1294 LINK_1299 LINK_1306 LINK_1311 LINK_1314 LINK_1321 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec rfmodl_spec letf2_spec addtf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_898 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 : word) Ft fct
j0 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z) (C : word),
dfinv m j0 (Z_to_bv 64 (lo64 FR)) w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
reg_get Ft 10 = fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign)) ->
(let FR' := f128_add FR (f128_of_d (bv_unsigned (fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign))))) in
match (if 2 <=? LDBL_MANT_DIG_ - bits' then
let one := f128_of_i32 1 in
match m_fmodl FR' one with
| None => None
| Some rr => if f128_le rr 0 =? 0 then Some (f128_add FR' C_ONE) else Some FR'
end
else Some FR') with
| None => None
| Some frac => fin_K3 1024 Y frac BI e2
end = Some yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1434)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1294 joff_1299 joff_1306 joff_1311 joff_1314 joff_1321 e_extenddftf2 e_letf2 e_floatsitf e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1294 E_1294 D_1299 E_1299 D_1306 E_1306 D_1311 E_1311 D_1314 E_1314 D_1321 E_1321 LINK_1294 LINK_1299 LINK_1306 LINK_1311 LINK_1314 LINK_1321 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec rfmodl_spec letf2_spec addtf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros until C. intros DI RJ Hk FOK FRM' Hsg He2 Hb HF10 HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
cbv zeta in HK.
set (DW := fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign))) in *.
zs. zs. callx (eapply extenddftf2_callF with (D := bv_unsigned DW); [eassumption | rewrite HF10; reflexivity]).
set (E := f128_of_d (bv_unsigned DW)) in *. pose proof (lo64_range E). pose proof (hi64_range E).
zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := FR) (Y := E); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs.
eapply L_8BC; try eassumption; try lia. mk_dfinv.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1278 hi_1281 hi_1284 hi_1290 lo_1279 lo_1282 lo_1285 lo_1291 joff_1294 joff_1299 joff_1306 joff_1311 joff_1314 joff_1321 G_10778 G_10788 G_10798 e_extenddftf2 e_letf2 e_floatsitf e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1278 E_1278 D_1279 E_1279 D_1281 E_1281 D_1282 E_1282 D_1284 E_1284 D_1285 E_1285 D_1290 E_1290 D_1291 E_1291 D_1294 E_1294 D_1299 E_1299 D_1306 E_1306 D_1311 E_1311 D_1314 E_1314 D_1321 E_1321 ANCH_1279 ANCH_1282 ANCH_1285 ANCH_1291 LINK_1294 LINK_1299 LINK_1306 LINK_1311 LINK_1314 LINK_1321 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 RNG_G_10798 ROM_G_10798 RNG_G_10778 ROM_G_10778 LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec rfmodl_spec letf2_spec addtf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_F2 : S_F2.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1278 hi_1281 hi_1284 hi_1290 lo_1279 lo_1282 lo_1285 lo_1291 joff_1294 joff_1299 joff_1306 joff_1311 joff_1314 joff_1321 G_10778 G_10788 G_10798 e_extenddftf2 e_letf2 e_floatsitf e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1278 E_1278 D_1279 E_1279 D_1281 E_1281 D_1282 E_1282 D_1284 E_1284 D_1285 E_1285 D_1290 E_1290 D_1291 E_1291 D_1294 E_1294 D_1299 E_1299 D_1306 E_1306 D_1311 E_1311 D_1314 E_1314 D_1321 E_1321 ANCH_1279 ANCH_1282 ANCH_1285 ANCH_1291 LINK_1294 LINK_1299 LINK_1306 LINK_1311 LINK_1314 LINK_1321 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 RNG_G_10798 ROM_G_10798 RNG_G_10778 ROM_G_10778 LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec rfmodl_spec letf2_spec addtf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until bits'. intros _ DI RJ Hk FOK FRM' Hsg He2 Hb XR X31H Ra Rz Hin HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
destruct XR as (LW' & LX & REL).
unfold fin_K2 in HK. change (Z.land (a + 4) MASK) with (Z.land (a + 4) 2047) in *. change (Z.land (a + 4 + 1) MASK) with (Z.land (a + 4 + 1) 2047) in HK.
pose proof (land_mask_range (a + 4) 2047 ltac:(lia)) as Rk. pose proof (land_mask_range (a + 5) 2047 ltac:(lia)) as Rk5.
replace (a + 4 + 1)%Z with (a + 5)%Z in HK by lia.
zs. zs. brf K1.
-
replace (Z.land (a + 4) 2047 =? z)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HK.
set (k4 := Z.land (a + 4) 2047) in *.
specialize (Hin ltac:(lia)).
pose proof (X31H k4) as Rt. pose proof (REL k4 ltac:(lia) Hin) as E4.
pose proof (u32arr_read segs _ _ _ k4 _ _ XW (nth_error_wnth ws k4 ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k4 (znth x k4) (eq_sym E4) Rt).
set (t := znth x k4) in *.

assert (G898 : forall (C : word) m' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x27' x28' x29' x30' x31' : word) Ft' fct' ev',
dfinv m' j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev' ws sign fR -> Fok Ft' -> frm0 fct' ->
reg_get Ft' 10 = fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign)) ->
(C = D_025 \/ C = D_05 \/ C = D_075) ->
(let signd := fcvt_d_w RNE (Z_to_bv 64 sign) in
let od := if (t <? 500000000) && (nz t || negb (Z.land (a + 5) 2047 =? z)) then Some (fmul_d RNE D_025 signd)
else if 500000000 <? t then Some (fmul_d RNE D_075 signd)
else if t =? 500000000 then (if Z.land (a + 5) 2047 =? z then Some (fmul_d RNE D_05 signd) else Some (fmul_d RNE D_075 signd))
else None in
od = Some (fmul_d RNE C signd))%Z ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27' x28' x29' x30' x31')
Ft' (Z_to_bv 64 (base + 0x1434)) fct' None m' (seg_rom segs))).
{ intros until ev'. intros DI2 FOK2 FRM2 HF HC Hod. cbv zeta in Hod. rewrite Hod in HK. cbv beta iota in HK.
eapply L_898; [exact DI2 | exact RJ | exact Hk | exact FOK2 | exact FRM2 | exact Hsg | lia | lia | exact HF | cbv zeta; exact HK]. }
zs. zs. zs. zs. brf K2.
+
zs. zs. brf K3.
*
zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
*
zs. zs. zs. zs. zs. brf K4.
--
zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
-- zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
+ zs. brf K3.
*
zs. zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with true by (symmetry; apply Z.ltb_lt; lia).
unfold nz. replace (t =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
*
zs. zs. zs. brf K4.
--
zs. zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with false by (symmetry; apply Z.eqb_neq; lia). unfold nz. cbn [negb orb andb].
destruct (t =? 0)%Z; reflexivity.
--
replace ((t <? 500000000) && (nz t || negb (Z.land (a + 5) 2047 =? z)))%Z with false in HK
by (unfold nz; replace (t =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); replace (Z.land (a + 5) 2047 =? z)%Z with true by (symmetry; apply Z.eqb_eq; lia);
cbn [negb orb andb]; destruct (t <? 500000000)%Z; reflexivity).
replace (500000000 <? t)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HK.
zs. zs. zs.
eapply L_8BC; try eassumption; try lia; try mk_dfinv.
-
replace (Z.land (a + 4) 2047 =? z)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
zs. zs. zs. zs.
stmt HS_F3. eapply NX; try eassumption; try lia; try mk_dfinv.
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
Definition SN324 : ltac:(gw_rebind_ty (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) SN324 gw_tbl_9).
Definition S_NK : ltac:(gw_rebind_ty (@QzQg.Mq0.S_NK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_NK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_NK segs base got_ssp RATP STRING_READ ssp_guard) S_NK gw_tbl_10).
Definition S_N484 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N484 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N484 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.S_N484 segs base got_ssp RATP STRING_READ ssp_guard) S_N484 gw_tbl_11).
Definition S_N3E8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N3E8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N3E8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.S_N3E8 segs base got_ssp RATP STRING_READ ssp_guard) S_N3E8 gw_tbl_12).
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

Ltac show_goal := match goal with |- ?g => idtac g end.
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

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__S_N3E8 := S_N3E8 (only parsing).
Notation F_floatscan_common__S_N484 := S_N484 (only parsing).
Notation F_floatscan_common__S_NK := S_NK (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_NK := (@F_floatscan_common__S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).
Local Notation S_N484 := (@F_floatscan_common__S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N3E8 := (@F_floatscan_common__S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold F_floatscan_common__dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Notation POST := (fs_post m0).

Hypothesis HS_NK : S_NK.
Hypothesis HS_N484 : S_N484.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 HS_NK HS_N484"] Lemma L_N3E8 : S_N3E8.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 HS_NK HS_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros fo IH iq m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HZ0 HS1 HA6 Naz HB HK.
pose proof DI as DI0. dest_dfinv DI. destruct XR as (LW' & LX & REL).

assert (GC : forall sh, (sh = (if 45 <? rp then 9 else 1))%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) (Z_to_bv 64 rp)
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xf9c)) fct None m (seg_rom segs))).
{ intros sh Hsh. rewrite <- Hsh in HB.
assert (Hsh2 : (sh = 1 \/ sh = 9)%Z) by (destruct (45 <? rp)%Z; lia).
destruct (df_dnk_loop FUEL_RING z sh _) as [[kk carry a1 i rp1 xx]|] eqn:HDK; [|discriminate HB]. unfold FUEL_RING in HDK.
zs. (brf K6; [ exfalso; lia | ]).
zs. zs. fixw3. replace (sh + e2)%Z with (e2 + sh)%Z by lia. zs. zs. zs. zs. zs. zs. zs. zs.
let v17 := getreg 17%Z in
replace v17 with (Z_to_bv 64 (2 ^ sh - 1)%Z) by (destruct Hsh2 as [E|E]; rewrite E; apply Z_to_bv_eqm; vm_compute; reflexivity).
let v7 := getreg 7%Z in
replace v7 with (Z_to_bv 64 (Z.shiftr 1000000000 sh)) by (destruct Hsh2 as [E|E]; rewrite E; apply Z_to_bv_eqm; vm_compute; reflexivity).
stmt HS_NK. eapply (NX 2050%nat) with (x := x) (h := h) (w := w) (k := a) (carry := 0%Z) (a := a) (i := iq) (rp := rp) (z := z) (sh := sh) (e2 := (e2 + sh)%Z) (B := (rp - 18450)%Z) (s1 := mkDK kk carry a1 i rp1 xx);
[mk_dfinv | assumption | assumption | exact (conj LW' (conj LX REL)) | exact X31H | lia | lia | lia | rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; lia | exact Naz | lia | exact Hsh2 | cbn; lia | exact Rw | lia | lia | exact HDK | ].
intros m' ws' b96' y17 y28 y29 y30 y31 w' DI2 XR2 X312 Ra1 Rc1 Rrp1 Rw1 Hk1; cbn [dk_x dk_a dk_carry dk_rp dk_k] in DI2, XR2, X312, Ra1, Rc1, Rrp1, Rw1, Hk1 |- *.
eapply (HS_N484 fo IH (mkDK kk carry a1 i rp1 xx)); try eassumption; try lia; cbn [dk_x dk_a dk_carry dk_rp dk_k]; try lia.
all: try (revert HB; destruct (nz carry); [destruct (negb ((z + 1) mod 2048 =? a1)%Z) |]; intros HB; exact HB).
all: show_goal. }
zs. fixw2. fixw. zs. zs. brs K5.
- zs. eapply GC. replace (45 <? rp)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- zs. zs. eapply GC. replace (45 <? rp)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_got_ssp_RATP : gw_le (got_ssp + 8) RATP.
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
Definition S_M : ltac:(gw_rebind_ty (@QzQg.Mq0.S_M segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_M segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.S_M segs base got_ssp RATP STRING_READ ssp_guard) S_M gw_tbl_9).
Definition S_P : ltac:(gw_rebind_ty (@QzQg.Mq0.S_P segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_P segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_P segs base got_ssp RATP STRING_READ ssp_guard) S_P gw_tbl_10).
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

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb8_c8_in) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb8_c8_in)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__S_M := S_M (only parsing).
Notation F_floatscan_common__S_P := S_P (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_RATP LAY_RATP_ssp_guard LAY_got_ssp_RERRNO"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_RATP LAY_RATP_ssp_guard LAY_got_ssp_RERRNO.

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

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_M := (@F_floatscan_common__S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_P := (@F_floatscan_common__S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac lo96w H := apply (cb8_c8_in _ _ [_; _; _; _; _; _; _; _; _; _; _; _] []) in H; cbn [app] in H.

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

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold F_floatscan_common__dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Notation POST := (fs_post m0).

Hypothesis HS_M : S_M.

#[using="Type"] Lemma df_pad_loop_step : forall n k j x, df_pad_loop (S n) k (j, x) = if (j <? 9)%Z then df_pad_loop n k (df_pad_body k (j, x)) else Some (j, x).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_M. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_M | gw_hide HS_M | idtac]. reflexivity. Qed.

#[using="Type"] Lemma df_pad_loop_pow : forall (n : nat) (j k : Z) (x : list Z) jx,
(1 <= j <= 9)%Z -> (0 <= k < zlength x)%Z -> (0 <= znth x k)%Z -> (znth x k * 10 ^ (9 - j) < 2^32)%Z ->
df_pad_loop n k (j, x) = Some jx ->
length (snd jx) = length x /\ znth (snd jx) k = (znth x k * 10 ^ (9 - j))%Z /\ (forall i, i <> k -> znth (snd jx) i = znth x i).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_M. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_M | gw_hide HS_M | idtac].
clear. induction n as [|n IH]; intros j k x jx Hj Hk Hx Hb HL; [discriminate HL|].
rewrite df_pad_loop_step in HL. destruct (Z.ltb_spec j 9) as [Hlt|Hge].
- unfold df_pad_body in HL.
assert (P1 : (10 ^ (9 - j) = 10 * 10 ^ (9 - (j + 1)))%Z) by (replace (9 - j)%Z with (Z.succ (9 - (j + 1)))%Z by lia; rewrite Z.pow_succ_r by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - (j + 1)))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (E10 : u32 (znth x k * 10) = (znth x k * 10)%Z) by (unfold u32; apply Z.mod_small; nia).
rewrite E10 in HL.
destruct (IH (j + 1)%Z k (zupd x k (znth x k * 10)%Z) jx ltac:(lia)
ltac:(unfold zlength in *; rewrite zupd_length; lia)
ltac:(rewrite znth_zupd_eq by lia; lia)
ltac:(rewrite znth_zupd_eq by lia; rewrite P1 in Hb; lia) HL) as (L1 & L2 & L3).
split; [rewrite L1; apply zupd_length|]. split.
+ rewrite L2. rewrite znth_zupd_eq by lia. rewrite P1. lia.
+ intros i Hi. rewrite (L3 i Hi). apply znth_zupd_neq. lia.
- injection HL as <-. cbn [snd]. replace (9 - j)%Z with 0%Z by lia. rewrite Z.pow_0_r, Z.mul_1_r. auto.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard AL_ssp_guard pre"] Lemma L_PADL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (i v : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
Z.of_nat n = (9 - i)%Z -> (1 <= i <= 8)%Z -> (0 <= v)%Z -> (v * 10 ^ (9 - i) < 2^32)%Z ->
(evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (v * 10 ^ (9 - i))) (Z_to_bv 64 10) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x9b0)) fct None m (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 (Z_to_bv 64 v) (Z_to_bv 64 10) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (i - 9)) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x9a4)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard AL_ssp_guard pre segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_M. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_M | gw_hide HS_M | idtac].
induction n as [|n IH]; intros until v; intros DI Hn Ri Rv Hb CONT; [lia|].
pose proof DI as DI'. dest_dfinv DI'. bury_disj.
assert (P1 : (10 ^ (9 - i) = 10 * 10 ^ (9 - (i + 1)))%Z) by (replace (9 - i)%Z with (Z.succ (9 - (i + 1)))%Z by lia; rewrite Z.pow_succ_r by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - (i + 1)))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (Rv10 : (0 <= v * 10 < 2^32)%Z) by nia.
zs. fixw3. fixw. zs. zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Hi7 : i <> 8%Z) by (clear - K1 Ri w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard AL_ssp_guard segs base; mlia).
replace (i - 9 + 1)%Z with ((i + 1) - 9)%Z by lia.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign (i + 1)%Z (v * 10)%Z);
[exact DI | lia | lia | lia | rewrite P1 in Hb; lia | ].
replace (v * 10 * 10 ^ (9 - (i + 1)))%Z with (v * 10 ^ (9 - i))%Z by (rewrite P1; lia). apply CONT.
- assert (Ei : i = 8%Z) by (clear - K1 Ri w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard AL_ssp_guard segs base; mlia). subst i.
replace (Z_to_bv 64 (8 - 9 + 1)) with (Z_to_bv 64 0) by (f_equal; lia).
replace (v * 10)%Z with (v * 10 ^ (9 - 8))%Z by (change (10 ^ (9 - 8))%Z with 10%Z; lia). apply CONT.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_RATP LAY_RATP_ssp_guard LAY_got_ssp_RERRNO T0 T1 SPLO SPF SPF2 SPT SG1 Q1 HS_M"] Lemma L_P : S_P.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_RATP LAY_RATP_ssp_guard LAY_got_ssp_RERRNO T0 T1 SPLO SPF SPF2 SPT SG1 Q1 HS_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 SEP SE_T SG2 SG3 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rj Rk Hx0 Rlnz Rrp Hxk Hkj Hkj45 HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_pad in HK. unfold nz in HK. rewrite (s32_id lrp) in HK by lia.
pose proof LOW as LOWw. lo96w LOWw. rewrite le_bytes_to_word_le8 in LOWw.
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Ej : j = 0%Z) by (clear - K1 Rj w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_RATP LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; mlia).
rewrite Ej, Z.eqb_refl in HK. cbn [negb] in HK. cbv beta iota in HK.
assert (Hk1 : (1 <= kz)%Z) by (destruct (Z.eq_dec kz 0) as [E|]; [exfalso; apply Hx0; apply Hkj; [exact E | exact Ej] | lia]).
zs. try rewrite le_bytes_to_word_le8.
stmt HS_M. eapply NX; [exact DI0 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | exact Hx0 | lia | lia | exact HK].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr. rewrite !Z.sub_0_r, !Z.mod_small in Hr by lia. left. lia.
- assert (Hj : j <> 0%Z) by (clear - K1 Rj w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_RATP LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; mlia).
replace (j =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hj). cbn [negb] in HK.
destruct (df_pad_loop 10 kz (j, x)) as [jx|] eqn:HL; [|discriminate HK]. cbv beta iota in HK. destruct jx as [j' x']. cbn [snd] in HK |- *.
specialize (Hxk Hj). pose proof (X31H kz) as Rt.
assert (P10 : (10 ^ j <= 10 ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
assert (P9 : (10 ^ j * 10 ^ (9 - j) = 1000000000)%Z) by (rewrite <- Z.pow_add_r by lia; replace (j + (9 - j))%Z with 9%Z by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - j))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (Hb : (0 <= znth x kz * 10 ^ (9 - j) < 1000000000)%Z) by nia.
destruct (df_pad_loop_pow 10 j kz x (j', x') ltac:(lia) ltac:(unfold zlength; lia) ltac:(lia) ltac:(lia) HL) as (L1 & L2 & L3). cbn [snd] in L1, L2, L3.
set (v' := (znth x kz * 10 ^ (9 - j))%Z) in *.
assert (Kin : digz kz j kz) by (unfold digz; right; right; split; [reflexivity | exact Hj]).
pose proof (REL kz ltac:(lia) Kin) as Et.
pose proof (u32arr_read segs _ _ _ kz _ _ XW (nth_error_wnth ws kz ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. try rewrite le_bytes_to_word_le8. brs K2.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws kz (znth x kz) (eq_sym Et) Rt).
zs. zs.
replace (j + -9)%Z with (j - 9)%Z by lia.
eapply (L_PADL (Z.to_nat (9 - j)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 _ ev ws sign j (znth x kz));
[exact DI0 | lia | lia | lia | lia | ].
fold v'.
pose proof (u32arr_store_ok segs _ _ _ kz _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ kz (Z_to_bv 64 v') XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. fixw3. fixw. zs.
stmt HS_M. eapply NX; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | | lia | | lia | lia | exact HK].
+ split; [rewrite upd_length; exact LW'|]. split; [rewrite L1; exact LX|].
intros i Hi Hr. unfold inring in Hr. rewrite !Z.sub_0_r, !Z.mod_small in Hr by lia.
destruct (Z.eq_dec i kz) as [->|Hne].
* rewrite L2. rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
* rewrite (L3 i Hne). rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz. lia.
+ intros i. destruct (Z.eq_dec i kz) as [->|Hne]; [rewrite L2; lia | rewrite (L3 i Hne); apply X31H].
+ destruct (Z.eq_dec 0 kz) as [E0|Hne]; [| rewrite (L3 0%Z Hne); exact Hx0].
subst kz. rewrite L2. subst v'. clear - Hx0 Rt P2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_RATP LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. nia.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
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
Definition S_UK : ltac:(gw_rebind_ty (@QzQg.Mq0.S_UK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_UK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.S_UK segs base got_ssp RATP STRING_READ ssp_guard) S_UK gw_tbl_9).
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
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__S_UK := S_UK (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_UK := (@F_floatscan_common__S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Notation POST := (fs_post m0).

Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
#[using="Type"] Lemma lor_b2z_zero : forall p q, Z.lor (Z.b2z p) (Z.b2z q) = 0%Z <-> (p = false /\ q = false).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. destruct p, q; cbn; split; intros H; try discriminate H; try (destruct H; congruence); auto. Qed.
#[using="Type"] Lemma lxor_pos_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((0 <? Z.lxor a b) = negb (a =? b))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne]; cbn.
- rewrite Z.lxor_nilpotent. reflexivity.
- apply Z.ltb_lt. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
Qed.
#[using="Type"] Lemma lxor_lt1_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((Z.lxor a b <? 1) = (a =? b))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne].
- rewrite Z.lxor_nilpotent. reflexivity.
- apply Z.ltb_ge. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_UK : S_UK.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO Hp T1 SE_T SPF SPF2 SPT SG1 SG3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SPLO SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
unfold F_floatscan_common__S_UK. induction n as [|n IH]; intros m; intros until s1; intros DI FOK FRM' XR X31H Ra Rz Rk Kin Rc HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_upk_loop_step in HL. unfold df_upk_body in HL. cbn [uk_k uk_x uk_z uk_carry] in HL. change MASK with 2047%Z in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs. unfold inring in Kin. pose proof (Z.mod_pos_bound (k - a) 2048 ltac:(flia)) as Rks.
pose proof (X31H k) as Rt. pose proof (REL k ltac:(flia) (or_introl Kin)) as Et.
pose proof (u32arr_read segs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(clear - Rk w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia) ltac:(clear - Rk LW' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia)) ltac:(clear - Rk w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia) eq_refl) as RD.
zs. zs. fix_idx. zs. rewrite zx32_wval, <- Et. set (t := znth x k) in *. clear RD.
zs. zs.
set (tmp := (Z.shiftl t 29 + carry)%Z) in *.
assert (Rtmp : (0 <= tmp < 2^60 + 2^31)%Z) by (subst tmp; rewrite Z.shiftl_mul_pow2 by flia; flia).
assert (Etmp : u64 tmp = tmp) by (unfold u64; apply Z.mod_small; flia). rewrite !Etmp in HL.
pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
rewrite !land2047 in HL. fold km in HL.

assert (G240 : forall (v carry' cand : Z) m' ws',
(0 <= v < 2^31)%Z -> (0 <= carry' < 2^31)%Z -> cand = (if v =? 0 then k else z)%Z ->
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
(forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel ws' (zupd x k v) (zone h' w a z')) ->
(let x' := zupd x k v in
let z' := (if (k =? km) && negb (k =? a) && (znth x' k =? 0) then k else z)%Z in
let s' := mkUK k carry' z' x' in
match (if (k =? a)%Z then inr s' else inl (mkUK ((k - 1) mod 2048) carry' z' x')) with
| inl s'' => df_upk_loop n a s''
| inr s'' => Some s''
end = Some s1) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 v) (Z_to_bv 64 cand) x31)
Ft (Z_to_bv 64 (base + 0xddc)) fct None m' (seg_rom segs))).
{ intros v carry' cand m' ws' Rv Rc' Hcand DI2 XRz HB. cbv zeta in HB.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'.
set (x' := zupd x k v) in *.
assert (X31' : X31 x').
{ intros ii. subst x'. destruct (Z.eq_dec ii k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X31H]. }
assert (Exk : znth x' k = v) by (subst x'; rewrite znth_zupd_eq by (unfold zlength; flia); reflexivity). rewrite Exk in HB.
assert (Hkm1 : k <> a -> inring a z ((k - 1) mod 2048) /\ inring a k ((k - 1) mod 2048)).
{ intros Hka. unfold inring. rewrite !Zminus_mod_idemp_l. clear - Kin Hka Ra Rz Rk Rrs Rks w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. Z.div_mod_to_equations. nia. }

zs. zs. zs. fixkg. replace (z + -1)%Z with (z - 1)%Z by flia. fold km. zs. zs. zs. zs. zs.
rewrite (lxor_pos_iff k km), (lxor_lt1_iff k a) by flia.

assert (LATCH : forall z' (x29' x30' : word),
z' = (if (k =? km) && negb (k =? a) && (v =? 0) then k else z)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 km) x29' x30' (Z_to_bv 64 (Z.b2z (negb (k =? km)))))
Ft (Z_to_bv 64 (base + 0xd7c)) fct None m' (seg_rom segs))).
{ intros z' x29' x30' Hz'. rewrite <- Hz' in HB.
assert (Rz' : (0 <= z' < 2048)%Z) by (rewrite Hz'; destruct (_ && _ && _); flia).
zs. zs. brf K4.
-
replace (k =? a)%Z with true in HB by (symmetry; apply Z.eqb_eq; flia). injection HB as <-.
assert (Ez' : z' = z) by (rewrite Hz'; replace (k =? a)%Z with true by (symmetry; apply Z.eqb_eq; flia); cbn [negb andb]; destruct (k =? km)%Z; reflexivity).
clear Hz'. subst z'.
replace (Z_to_bv 64 k) with (Z_to_bv 64 a) by (f_equal; flia).
eapply (CONT _ _ _ _ _ _ _ h); [mk_dfinv | cbn [uk_x uk_z]; apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | cbn; flia | cbn; flia | cbn; flia | cbn; intros E; split; [exact E | flia] | cbn; flia].
- replace (k =? a)%Z with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
zs. rewrite land2047, ?landW_mod2048. replace (k + -1)%Z with (k - 1)%Z by flia.
destruct (Hkm1 ltac:(flia)) as [Hin1 Hin2].
assert (Hz2 : z' = (if (k =? km) && (v =? 0) then k else z)%Z).
{ rewrite Hz'. replace (k =? a)%Z with false by (symmetry; apply Z.eqb_neq; flia). cbn [negb]. destruct (k =? km)%Z; reflexivity. }
clear Hz'.
replace ((k =? km) && negb false && (v =? 0))%Z with ((k =? km) && (v =? 0))%Z in HB by (destruct (k =? km)%Z; reflexivity).
destruct ((k =? km) && (v =? 0))%Z eqn:Ec; subst z'.
+
assert (Ekm : k = km) by (apply andb_prop in Ec; destruct Ec as [Ec _]; apply Z.eqb_eq in Ec; exact Ec).
destruct (Z.eq_dec z 0) as [Ez0|Hz0].
*
assert (Ek : k = 2047%Z) by (rewrite Ekm; subst km; rewrite Ez0; reflexivity).
eapply IH with (h := true) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
-- destruct Hq as [Hq | [[_ Hq] | Hq]]; [| left; flia | right; right; right; exact Hq]. right. left.
unfold inring in Hq |- *. clear - Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ez0 Ek w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. Z.div_mod_to_equations. nia.
-- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
intros E. destruct (Hlow3 E) as [E2 _]. discriminate E2.
* assert (Ek : k = (z - 1)%Z) by (rewrite Ekm; subst km; apply Z.mod_small; flia).
eapply IH with (h := h) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
-- destruct Hq as [Hq | [[Hh Hq] | Hq]]; [ | | right; right; right; exact Hq].
{ right. left. unfold inring in Hq |- *. clear - Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ek w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. Z.div_mod_to_equations. nia. }
destruct (Z.eq_dec ii k) as [->|Hne]; [left; reflexivity | right; right; left; split; [exact Hh | flia]].
-- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
intros E. destruct (Hlow3 E) as [E2 R2]. split; [exact E2 | flia].
+
eapply IH with (h := h) (z := z) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin1 | flia | exact HB | exact CONT]. }
zs. brf K3.
-
eapply LATCH. symmetry.
destruct (Z.eqb_spec k km); destruct (Z.eqb_spec k a); cbn [negb andb Z.b2z Z.lor] in K3 |- *; try reflexivity. exfalso. apply K3. reflexivity.
-
apply (proj1 (lor_b2z_zero _ _)) in K3. destruct K3 as [K3a K3b].
apply (proj1 (Bool.negb_false_iff _)) in K3a.
zs. zs.
eapply LATCH. rewrite K3a, K3b. cbn [negb andb]. exact Hcand. }
zs. zs. brf K2.
-
replace (1000000000 <? tmp)%Z with false in HL by (symmetry; apply Z.ltb_ge; flia).
rewrite (u32_id tmp) in HL by flia.
zs.
pose proof (u32arr_store_ok segs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ k (Z_to_bv 64 tmp) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 tmp)) (zupd x k tmp) (zone h' w a z')).
{ intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
zs. zs. brf K5.
+  eapply (G240 tmp 0%Z k); [flia | flia | replace (tmp =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
+ zs. eapply (G240 tmp 0%Z z); [flia | flia | replace (tmp =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
-
replace (1000000000 <? tmp)%Z with true in HL by (symmetry; apply Z.ltb_lt; flia).
assert (Rq : (0 <= tmp / 1000000000 < 2^31)%Z) by (split; [apply Z.div_pos; flia | apply Z.div_lt_upper_bound; flia]).
pose proof (Z.mod_pos_bound tmp 1000000000 ltac:(flia)) as Rr.
rewrite (u32_id (tmp / 1000000000)) in HL by flia. rewrite (u32_id (tmp mod 1000000000)) in HL by flia.
zs. zs. zs. showall.
rewrite (magic_div_1e9_reg tmp) by flia.
zs. zs.
replace (tmp - tmp / 1000000000 * 1000000000)%Z with (tmp mod 1000000000)%Z by (rewrite Zmod_eq_full by flia; flia).
pose proof (u32arr_store_ok segs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ k (Z_to_bv 64 (tmp mod 1000000000)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 (tmp mod 1000000000))) (zupd x k (tmp mod 1000000000)) (zone h' w a z')).
{ intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
zs. zs. brf K5.
+  zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z z); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
+ zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z k); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
Qed.

End Floatscan.

End G.
End Mq5.

Module Mq6.

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
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_5).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_6).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_7))).
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
Definition S_E : ltac:(gw_rebind_ty (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) S_E gw_tbl_13).
Definition SDn : ltac:(gw_rebind_ty (@QzQg.Mq0.SDn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SDn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.SDn segs base got_ssp RATP STRING_READ ssp_guard) SDn gw_tbl_14).
Definition S_D : ltac:(gw_rebind_ty (@QzQg.Mq0.S_D segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_D segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.S_D segs base got_ssp RATP STRING_READ ssp_guard) S_D gw_tbl_15).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_16).
Definition S_B0C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_B0C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_B0C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.S_B0C segs base got_ssp RATP STRING_READ ssp_guard) S_B0C gw_tbl_17).
Definition S_A9C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A9C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A9C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.S_A9C segs base got_ssp RATP STRING_READ ssp_guard) S_A9C gw_tbl_18).
Definition S_A44 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A44 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A44 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.S_A44 segs base got_ssp RATP STRING_READ ssp_guard) S_A44 gw_tbl_19).
Definition SRZn : ltac:(gw_rebind_ty (@QzQg.Mq0.SRZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SRZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.SRZn segs base got_ssp RATP STRING_READ ssp_guard) SRZn gw_tbl_20).
Definition S_RZ : ltac:(gw_rebind_ty (@QzQg.Mq0.S_RZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_RZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.S_RZ segs base got_ssp RATP STRING_READ ssp_guard) S_RZ gw_tbl_21).
Definition S_9EC : ltac:(gw_rebind_ty (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) S_9EC gw_tbl_22).
Definition S_A64 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A64 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A64 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.S_A64 segs base got_ssp RATP STRING_READ ssp_guard) S_A64 gw_tbl_23).
Definition S_7F4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) S_7F4 gw_tbl_24).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis shgetc_callJ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.shgetc_callJ) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments shgetc_callJ _%_bv_scope _%_Z_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope _%_Z_scope _ _%_Z_scope _%_Z_scope _ _%_list_scope _%_list_scope _%_list_scope _%_bv_scope.
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

Definition rw_cells_C8_CB8 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.rw_cells_C8_CB8) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.rw_cells_C8_CB8)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb8_c8_in) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb8_c8_in)).
Definition winv_dfinvG : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.winv_dfinvG) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.winv_dfinvG)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__SRZn := SRZn (only parsing).
Notation F_floatscan_common__S_7F4 := S_7F4 (only parsing).
Notation F_floatscan_common__S_9EC := S_9EC (only parsing).
Notation F_floatscan_common__S_A44 := S_A44 (only parsing).
Notation F_floatscan_common__S_A64 := S_A64 (only parsing).
Notation F_floatscan_common__S_A9C := S_A9C (only parsing).
Notation F_floatscan_common__S_B0C := S_B0C (only parsing).
Notation F_floatscan_common__S_D := S_D (only parsing).
Notation F_floatscan_common__S_E := S_E (only parsing).
Notation F_floatscan_common__S_RZ := S_RZ (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__dfinvG := dfinvG (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Notation F_floatscan_common__winv_dfinvG := winv_dfinvG (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Local Notation S_E := (@F_floatscan_common__S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_D := (@F_floatscan_common__S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation winv_dfinvG := (@F_floatscan_common__winv_dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_B0C := (@F_floatscan_common__S_B0C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A9C := (@F_floatscan_common__S_A9C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A44 := (@F_floatscan_common__S_A44 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_RZ := (@F_floatscan_common__S_RZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_9EC := (@F_floatscan_common__S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A64 := (@F_floatscan_common__S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@F_floatscan_common__S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac lo96w H := apply (cb8_c8_in _ _ [_; _; _; _; _; _; _; _; _; _; _; _] []) in H; cbn [app] in H.
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
Ltac mk_dfinvG := unfold F_floatscan_common__dfinvG; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

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
Ltac mk_winv := unfold F_floatscan_common__winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Notation POST := (fs_post m0).

Hypothesis HS_D : S_D.
Hypothesis HS_E : S_E.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
Ltac eplia := gw_expose got_ssp; gw_expose ssp_guard; unfold zlength in *; unfold hide2 in *; lia.

Ltac mk_winv2 := unfold F_floatscan_common__winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
#[using="Type"] Lemma znth_X0 : forall i, znth X0 i = 0%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_D HS_E. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_D | gw_hide HS_D | idtac]; first [clear HS_E | gw_hide HS_E | idtac].
clear. intros i. unfold X0. destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite znth_zupd_eq; [reflexivity|]. rewrite zlength_zrepeat; unfold KMAX; lia.
- rewrite znth_zupd_neq by lia. rewrite znth_zrepeat. destruct (_ && _); reflexivity.
Qed.
#[using="Type"] Lemma X0_len : length X0 = 2048%nat.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_D HS_E. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_D | gw_hide HS_D | idtac]; first [clear HS_E | gw_hide HS_E | idtac]. clear. unfold X0, KMAX. rewrite zupd_length. pose proof (zlength_zrepeat 0 2048 ltac:(lia)) as E. unfold zlength in E. lia. Qed.
#[using="Type"] Lemma xrel_X0 : forall ws, length ws = 2048%nat -> wval ws 0 = 0%Z -> xrel ws X0 (digz 0 0).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_D HS_E. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_D | gw_hide HS_D | idtac]; first [clear HS_E | gw_hide HS_E | idtac].
clear. intros ws LW W0. split; [exact LW|]. split; [exact X0_len|].
intros i Hi Hr. unfold digz in Hr. assert (Ei : i = 0%Z) by lia. rewrite Ei, znth_X0, W0. reflexivity.
Qed.
Ltac x0_facts := splits; try lia; try (apply xrel_X0; assumption); unfold X31; intros; rewrite ?znth_X0 in *; try lia.
#[using="Type"] Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_D HS_E. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_D | gw_hide HS_D | idtac]; first [clear HS_E | gw_hide HS_E | idtac].
clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_D HS_E. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_D | gw_hide HS_D | idtac]; first [clear HS_E | gw_hide HS_E | idtac]. clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_D HS_E. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_D | gw_hide HS_D | idtac]; first [clear HS_E | gw_hide HS_E | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.

#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_D HS_E. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_D | gw_hide HS_D | idtac]; first [clear HS_E | gw_hide HS_E | idtac].
clear - BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D"] Lemma L_B0C : S_B0C.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum T0 T1 SEP SE_T SPF2 SG2 SG3 FRM HS_E. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac].
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hcond HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rrpp : (sh_rpos f <= p)%Z).
{ clear - RJ Hcond w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos. destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es; [destruct (SS0 eq_refl) as (Qa & Qb & Qc); exact Qb | apply (proj2 (proj2 (NS0 eq_refl))); intros E0; rewrite E0 in Hcond; cbv in Hcond; discriminate Hcond]. }
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
unfold dfK_dig in HK. destruct (df_dig_loop fuelc _) as [s'|] eqn:HL; [|discriminate HK].
pose proof LOW as LOWw. lo96w LOWw.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite (seqz46 c) by lia. zs. zs. zs. zs. zs.
match goal with |- context [Z_to_bv 64 (q + -8416 + 104 + 8176)%Z] => replace (q + -8416 + 104 + 8176)%Z with (q + -136)%Z by lia | _ => idtac end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
stmt HS_D. eapply (NX fuelc) with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try lia.
{ mk_dfinv. }
{ unfold digI. x0_facts. }
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A9C : S_A9C.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum T0 T1 SEP SE_T SPF2 SG2 SG3 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hne HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. brf K1; rewrite ?land_W64 in K1.
-
stmt L_B0C. eapply NX; try eassumption; try lia.
replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Bool.orb_false_r.
apply (proj2 (isdigitc_iff c ltac:(lia))). clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos. Z.div_mod_to_equations. lia.
-
assert (Hd : isdigitc c = false).
{ apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c ltac:(lia))) in D. clear - K1 D Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos. Z.div_mod_to_equations. lia. }
assert (HL : df_dig_loop fuelc (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0)).
{ clear - HK Hd Hne w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos. unfold dfK_dig in HK. destruct fuelc as [|fu]; [discriminate HK|].
cbn [df_dig_loop]. unfold df_dig_cond. cbn [dl_c]. rewrite Hd. replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
unfold dfK_dig in HK. rewrite HL in HK.
pose proof LOW as LOWw. lo96w LOWw.
zs. zs. zs. zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
stmt HS_E. eapply NX with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try lia.
{ mk_dfinvG. }
{ unfold dig_facts. x0_facts. }
{ rewrite znth_X0. intros X; exfalso; exact (X eq_refl). }
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A44 : S_A44.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum T0 T1 SEP SE_T SPF2 SG2 SG3 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until gotdig. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rlrp Rg Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs.
pose proof (u32arr_store_ok segs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1.
- stmt L_A9C. eapply NX with (gotrad := 1%Z); try eassumption; try lia. { rewrite <- winv_dfinvG. mk_winv. }
clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos. rewrite land_W64 in K1. Z.div_mod_to_equations; lia.
- assert (E46 : c = 46%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos; rewrite land_W64 in K1; Z.div_mod_to_equations; lia).
zs. stmt L_B0C. eapply NX with (gotrad := 1%Z); try eassumption; try lia. { rewrite <- winv_dfinvG. mk_winv. }
all: rewrite E46; reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E"] Lemma L_RZ : S_RZ.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac].
unfold F_floatscan_common__S_RZ. induction n as [|n IH].
{ intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK. discriminate HL. }
intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK.
dest_winv WI. bury_disj.
rewrite df_rz_loop_step in HL. rewrite Z.eqb_refl in HL.
site_facts FC RJ kmin 48%Z f.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].

assert (HEAD : forall m2 (x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) = 48%Z ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x5bc)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2 E48. rewrite E48 in RJ1.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 w32 w48 w80 b96 ev ws sign (kmin + 1)%Z (snd (sh_getc f)) (lrp + -1)%Z 1%Z g' lrp' c' f');
try eassumption; try lia.
rewrite E48 in HL. replace (lrp + -1)%Z with (lrp - 1)%Z by lia. exact HL. }

assert (EXIT : forall m2 (x1' x5' x6' x7' x9' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) <> 48%Z ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x5dc)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2 N48.
assert (E : (g', lrp', c', f') = (1%Z, (lrp - 1)%Z, fst (sh_getc f), snd (sh_getc f))).
{ clear - HL N48 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ. destruct n as [|n2]; [discriminate HL|]. rewrite df_rz_loop_step in HL.
replace (fst (sh_getc f) =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
injection E as -> -> -> ->. clear HL.
pose proof WI2 as WI3. dest_winv WI3.
zs.
stmt L_A44. eapply NX with (gotdig := 1%Z) (lrp := (lrp + -1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia).
all: replace (lrp + -1)%Z with (lrp - 1)%Z by lia; exact HK. }
clear HL HK IH.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin 48 f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. call_split 160%Z (eapply (gw_unhyp shgetc_callJ) with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; gw_expose got_ssp; gw_expose ssp_guard end.
set (c'' := fst (sh_getc f)) in *.
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ eapply EXIT; [mk_winv2 | clear - K2 Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia].
+ eapply HEAD; [mk_winv2 | clear - K2 Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0.
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ eapply HEAD; [mk_winv2 | exact K2].
+ eapply EXIT; [mk_winv2 | exact K2].
Qed.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E"] Lemma L_9EC : S_9EC.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rg HL HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (E48 : c = 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia). rewrite E48 in RJ, HL.
pose proof L_RZ as NX. unfold F_floatscan_common__S_RZ, F_floatscan_common__SRZn in NX. eapply (NX fuelc) with (lrp := 0%Z); try eassumption; try lia. norm_m1074. mk_winv2.
- assert (N48 : c <> 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia).
assert (E : (g', lrp', c', f') = (gotdig, 0%Z, c, f)).
{ clear - HL HK N48 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ. unfold dfK_dig in HK. destruct fuelc as [|n2]; [|rewrite df_rz_loop_step in HL].
- exfalso. cbn [df_dig_loop] in HK. discriminate HK.
- replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
injection E as -> -> -> ->. clear HL.
zs. stmt L_A44. eapply NX with (lrp := 0%Z); try eassumption; try lia. norm_m1074. mk_winv2.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A64 : S_A64.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum T0 T1 SEP SE_T SPF2 SG2 SG3 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
pose proof (u32arr_store_ok segs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1; rewrite ?land_W64 in K1.
- exfalso. clear - K1 Rc Hne w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos. Z.div_mod_to_equations; lia.
- norm_m1074. stmt L_A9C. eapply NX with (gotdig := 1%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try lia. rewrite <- winv_dfinvG. mk_winv.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_7F4 : S_7F4.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum T0 T1 SEP SE_T SPF2 SG2 SG3 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
pose proof (u32arr_store_ok segs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1; rewrite ?land_W64 in K1.
- norm_m1074. stmt L_A9C. eapply NX with (gotdig := 0%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try lia. rewrite <- winv_dfinvG. mk_winv.
- exfalso. clear - K1 Rc Hne w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos. Z.div_mod_to_equations; lia.
Qed.

End Floatscan.

End G.
End Mq6.

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

Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_0))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_1))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_2).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_3).
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
Definition S_N2D4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N2D4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N2D4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.S_N2D4 segs base got_ssp RATP STRING_READ ssp_guard) S_N2D4 gw_tbl_9).
Definition S_U1A8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) S_U1A8 gw_tbl_10).
Definition S_UK : ltac:(gw_rebind_ty (@QzQg.Mq0.S_UK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_UK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.S_UK segs base got_ssp RATP STRING_READ ssp_guard) S_UK gw_tbl_11).
Definition SU1C4 : ltac:(gw_rebind_ty (@QzQg.Mq0.SU1C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SU1C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.SU1C4 segs base got_ssp RATP STRING_READ ssp_guard) SU1C4 gw_tbl_12).
Definition S_U1C4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_U1C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_U1C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.S_U1C4 segs base got_ssp RATP STRING_READ ssp_guard) S_U1C4 gw_tbl_13).
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

Notation F_floatscan_common__SU1C4 := SU1C4 (only parsing).
Notation F_floatscan_common__S_N2D4 := S_N2D4 (only parsing).
Notation F_floatscan_common__S_U1A8 := S_U1A8 (only parsing).
Notation F_floatscan_common__S_U1C4 := S_U1C4 (only parsing).
Notation F_floatscan_common__S_UK := S_UK (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

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
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QzQg.Mq0.Fok F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_N2D4 := (@F_floatscan_common__S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_U1A8 := (@F_floatscan_common__S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_UK := (@F_floatscan_common__S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_U1C4 := (@F_floatscan_common__S_U1C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold F_floatscan_common__dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Notation POST := (fs_post m0).

Hypothesis HS_N2D4 : S_N2D4.
Hypothesis HS_UK : S_UK.

Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
#[using="Type"] Lemma th0_valU : znth th_list 0 = 10384593%Z. Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_N2D4 HS_UK. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_N2D4 | gw_hide HS_N2D4 | idtac]; first [clear HS_UK | gw_hide HS_UK | idtac]. reflexivity. Qed.
#[using="Type"] Lemma mod_add2046 : forall u, ((u + 2046) mod 2048 = ((u - 1) mod 2048 - 1) mod 2048)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_N2D4 HS_UK. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_N2D4 | gw_hide HS_N2D4 | idtac]; first [clear HS_UK | gw_hide HS_UK | idtac]. clear. intros u. rewrite Zminus_mod_idemp_l. rewrite <- (Z.mod_add (u - 1 - 1) 1 2048) by flia. f_equal. flia. Qed.

#[using="fc pre post fuelc f0 kmin0 c0 HS_N2D4"] Lemma L_UPX : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^20 <= rp <= 560)%Z -> (-2^20 <= e2 <= 0)%Z ->
up_K sign rp a z e2 x = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xe70)) fct None m (seg_rom segs)).
Proof. clear - fc pre post fuelc f0 kmin0 c0 HS_N2D4 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_UK. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_UK | gw_hide HS_UK | idtac].
intros until e2. intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Rrp Re2 HK. unfold up_K in HK.
destruct (df_dn_loop FUEL_SCALE _) as [s'|] eqn:HL; [|discriminate HK].
stmt HS_N2D4. eapply (NX 2000%nat); try eassumption; try (cbn; flia).
all: try (intros E; specialize (Rzh E); cbn; flia).
all: try (intros E; specialize (Rw E); cbn; flia).
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK"] Lemma L_U1C4 : S_U1C4.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 SEP SE_T SPLO SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
unfold F_floatscan_common__S_U1C4, F_floatscan_common__SU1C4. induction fo as [|fo IH]; intros m; intros until s'; intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Haz Rrp Re2 HL HK; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_up_loop_step in HL. unfold df_up_cond in HL. cbn [us_rp us_x us_a] in HL.
change (9 * LD_B1B_DIG)%Z with 36%Z in HL. rewrite th0_valU in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs.
assert (Hrs1 : (0 < (z - a) mod 2048)%Z) by (clear - Haz Ra Rz Rrs w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; Z.div_mod_to_equations; flia).

assert (GHEAD : forall m' ws' x' (h' w' : bool) (a' z' rp' : Z) (x6' x7' x16' x28' x29' x30' x31' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' x' (zone h' w' a' z') -> X31 x' -> (0 <= a' < 2048)%Z -> (0 <= z' < 2048)%Z -> (h' = false -> z' <= 2047)%Z -> (w' = false -> 9 * a' + rp' <= 560)%Z -> a' <> z' ->
(-2^20 <= rp' <= 45)%Z ->
df_up_loop fo (mkUS rp' a' z' (e2 - 29) x') = Some s' ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp') x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a'))
(Z_to_bv 64 z') (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp') x24 x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0xd60)) fct None m' (seg_rom segs))).
{ intros m' ws' x' h' w' a' z' rp' x6' x7' x16' x28' x29' x30' x31' DI2 XR2 X312 Ra' Rz' Rzh' Rw' Haz' Rrp' HL'.
eapply (IH m' x1 x6' x7' x8 x9 x16' x20 x22 x24 x25 x26 x27 x28' x29' x30' x31' Ft fct j0 b96 ev ws' sign k c x' h' w' rp' a' z' (e2 - 29)%Z s');
[exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | flia | exact XR2 | exact X312 | flia | exact Rzh' | exact Rw' | exact Haz' | flia | flia | exact HL' | exact HK]. }
clear IH.

assert (GBODY : forall (x16' : word), (rp <= 36)%Z ->
match df_up_body (mkUS rp a z e2 x) with Some s'' => df_up_loop fo s'' | None => None end = Some s' ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd70)) fct None m (seg_rom segs))).
{ intros x16' Rrp36 HB. clear HL HK. unfold df_up_body in HB. cbn [us_a us_z us_x us_rp us_e2] in HB. change MASK with 2047%Z in HB.
destruct (df_upk_loop FUEL_RING a _) as [[k1 carry1 z1 x1']|] eqn:HUK; [|discriminate HB].
unfold FUEL_RING in HUK. rewrite land2047 in HUK.

zs. zs. zs. zs. fixkg. rewrite mod_add2047.
stmt HS_UK.
eapply (NX 2050%nat) with (h := h) (w := w) (x := x) (s1 := mkUK k1 carry1 z1 x1');
[exact DI | exact FOK | exact FRM' | exact (conj LW' (conj LX REL)) | exact X31H | flia | flia | apply Z.mod_pos_bound; flia | | flia | exact HUK | ].
{ unfold inring. rewrite Zminus_mod_idemp_l. clear - Hrs1 Rrs Ra Rz w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. Z.div_mod_to_equations. flia. }
clear NX.
intros m' ws' x7' x18' x29' x30' x31' h' DI2 XR2 X312 Hk1 Rc1 Rz1 Hlow1 Haz1.
cbn [uk_x uk_z uk_k uk_carry] in DI2, XR2, X312, Hk1, Rc1, Rz1, Hlow1, Haz1 |- *. subst k1.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HUK Rrs Hrs1 LW' LX REL X31H.
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
assert (Rzh1 : (h' = false -> z1 <= 2047)%Z) by (intros E; destruct (Hlow1 E) as [E0 R0]; specialize (Rzh E0); flia).
pose proof (Z.mod_pos_bound (z1 - a) 2048 ltac:(flia)) as Rrs2.
unfold nz in HB.

zs. fixw3. fixw. replace (e2 + -29)%Z with (e2 - 29)%Z by flia. zs. zs. brf K1.
-
replace (negb (carry1 =? 0)) with true in HB by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).
rewrite !land2047 in HB.
zs. zs. fixkg. replace (a + -1)%Z with (a - 1)%Z by flia.
pose proof (Z.mod_pos_bound (a - 1) 2048 ltac:(flia)) as Ra'. set (a' := ((a - 1) mod 2048)%Z) in *.
assert (FRONT : forall q0, (0 <= q0 < 2048)%Z -> inring a' z1 q0 -> q0 <> a' -> z1 <> a' -> inring a z1 q0).
{ intros q0 Hq H1 H2 H3. apply (inring_front a z1 q0); try flia; assumption. }
assert (FULL : z1 = a' -> forall q0, (0 <= q0 < 2048)%Z -> q0 <> a' -> inring a z1 q0).
{ intros E q0 Hq Hne. unfold inring. clear - E Hq Hne Ra Rz1 Ra' Haz1 Rrs2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. subst a'. Z.div_mod_to_equations. nia. }
assert (Ea' : a' = (if (a =? 0)%Z then 2047%Z else (a - 1)%Z)).
{ subst a'. destruct (Z.eqb_spec a 0) as [->|Hne]; [reflexivity | rewrite Z.mod_small by flia; reflexivity]. }
set (w' := (w || (a =? 0)%Z)%bool).
assert (W1 : forall q0, (0 <= q0 < 2048)%Z -> w' = true -> (a' <= q0)%Z -> q0 <> a' -> w = true /\ (a <= q0)%Z).
{ intros q0 Hq. subst w'. rewrite Ea'. destruct (Z.eqb_spec a 0) as [Ea0|Na0]; intros Hw' Hai Hne.
- exfalso. clear - Hq Hai Hne w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. flia.
- rewrite Bool.orb_false_r in Hw'. split; [exact Hw' | clear - Hai Hne w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia]. }
assert (W2 : w' = false -> (9 * a' + (rp + 9) <= 560)%Z).
{ subst w'. rewrite Ea'. destruct (Z.eqb_spec a 0) as [Ea0|Na0]; intros Hw'; [rewrite Bool.orb_true_r in Hw'; discriminate Hw'|].
rewrite Bool.orb_false_r in Hw'. specialize (Rw Hw'). clear - Rw Na0 Ra w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. flia. }
clearbody w'. clear Ea'.
clearbody a'. clear Rrs2.

assert (TAIL : forall m2 ws2 x2 (h2 : bool) (z2 : Z) (x5' x6' x17' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws2 sign fR ->
xrel ws2 x2 (fun i => zone h2 w' a' z2 i /\ i <> a') -> X31 x2 -> (0 <= z2 < 2048)%Z -> (h2 = false -> z2 <= 2047)%Z -> a' <> z2 ->
df_up_loop fo (mkUS (rp + 9) a' z2 (e2 - 29) (zupd x2 a' carry1)) = Some s' ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 carry1) x17'
(Z_to_bv 64 z1) (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 z2) x29' x30' x31')
Ft (Z_to_bv 64 (base + 0xe44)) fct None m2 (seg_rom segs))).
{ intros m2 ws2 x2 h2 z2 x5' x6' x17' DI3 XR3 X313 Rz2 Rzh2 Haz2 HL3.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC DI2 LW2 LX2 REL2 X312 HB.
pose proof DI3 as DI'. dest_dfinv DI'. destruct XR3 as (LW3 & LX3 & REL3).
zs. zs. zs. fix_idx.
pose proof (u32arr_store_ok segs _ _ _ a' _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ a' (Z_to_bv 64 carry1) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. zs. zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 9 + 0)%Z with (rp + 9)%Z by flia. zs.
eapply (GHEAD _ (upd ws2 (Z.to_nat a') (Z_to_bv 64 carry1)) (zupd x2 a' carry1) h2 w' a' z2 (rp + 9)%Z);
[mk_dfinv | | | flia | flia | exact Rzh2 | exact W2 | flia | flia | exact HL3].
* split; [rewrite upd_length; exact LW3|]. split; [rewrite zupd_length; exact LX3|].
intros q0 Hq Hr. destruct (Z.eq_dec q0 a') as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL3; [flia|]. split; [exact Hr | exact Hne].
* intros q0. destruct (Z.eq_dec q0 a') as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X313]. }
zs. brf K2.
+
replace (a' =? z1) with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
zs.
eapply (TAIL m' ws' x1' h' z1); [exact DI2 | | exact X312 | flia | exact Rzh1 | flia | exact HB].
split; [exact LW2|]. split; [exact LX2|]. intros q0 Hq [Hr Hne]. apply REL2; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (W1 q0 Hq Hw' Hai Hne)]. apply (FRONT q0); try flia. exact Hr.
+
replace (a' =? z1) with true in HB by (symmetry; apply Z.eqb_eq; flia). cbv beta iota in HB.
pose proof (Z.mod_pos_bound (z1 - 1) 2048 ltac:(flia)) as Rz2. set (z2 := ((z1 - 1) mod 2048)%Z) in *.
zs. zs. zs. fix_idx. zs. fixkg. rewrite mod_add2046. fold z2.
pose proof (Z.mod_pos_bound (z2 - 1) 2048 ltac:(flia)) as Rz3. set (z3 := ((z2 - 1) mod 2048)%Z) in *.
assert (Hz2in : inring a z1 z2) by (apply (FULL ltac:(flia)); [flia | subst z2; clear - Rz1 Rz2 K2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; Z.div_mod_to_equations; flia]).
assert (Hz3in : inring a z1 z3) by (apply (FULL ltac:(flia)); [flia | subst z3 z2; clear - Rz1 Rz2 Rz3 K2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; Z.div_mod_to_equations; flia]).
assert (Hz23 : z3 <> z2) by (subst z3; clear - Rz2 Rz3 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; Z.div_mod_to_equations; flia).
assert (LOWz2 : z1 <> 0%Z -> z2 = (z1 - 1)%Z) by (intros; subst z2; apply Z.mod_small; flia).
assert (Hz21 : z2 <> z1) by (subst z2; clear - Rz1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; Z.div_mod_to_equations; flia).
clearbody z2 z3.
pose proof (X312 z3) as Rt3. pose proof (REL2 z3 ltac:(flia) (or_introl Hz3in)) as Et3.
pose proof (X312 z2) as Rt2. pose proof (REL2 z2 ltac:(flia) (or_introl Hz2in)) as Et2.
zs. zs. fix_idx.
pose proof (u32arr_read segs _ _ _ z2 _ _ XW (nth_error_wnth ws' z2 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD2.
zs. rewrite (sx32_wval ws' z2 (znth x1' z2) (eq_sym Et2) Rt2). clear RD2.
pose proof (u32arr_read segs _ _ _ z3 _ _ XW (nth_error_wnth ws' z3 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD3.
zs. rewrite (sx32_wval ws' z3 (znth x1' z3) (eq_sym Et3) Rt3). clear RD3.
set (t3 := znth x1' z3) in *. set (t2 := znth x1' z2) in *.
zs.
assert (Rt23 : (0 <= Z.lor t3 t2 < 2^31)%Z).
{ split; [apply Z.lor_nonneg; flia|]. apply (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 t3 t2 31); flia. }
pose proof (u32arr_store_ok segs _ _ _ z3 _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ z3 (Z_to_bv 64 (Z.lor t3 t2)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
eapply (TAIL _ (upd ws' (Z.to_nat z3) (Z_to_bv 64 (Z.lor t3 t2))) (zupd x1' z3 (Z.lor t3 t2)) (if (z1 =? 0)%Z then true else h') z2);
[mk_dfinv | | | flia | | flia | exact HB].
* split; [rewrite !upd_length; exact LW2|]. split; [rewrite !zupd_length; exact LX2|].
intros q0 Hq [Hr Hne].
destruct (Z.eq_dec q0 z3) as [->|Hne3].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|]. left.
apply (FULL ltac:(flia) q0 Hq Hne).
* intros q0. destruct (Z.eq_dec q0 z3) as [->|Hne3]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312].
* destruct (Z.eqb_spec z1 0) as [Ez1|Hz1]; [intros E; discriminate E|]. intros E. specialize (Rzh1 E). specialize (LOWz2 Hz1). flia.
-
replace (negb (carry1 =? 0)) with false in HB by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
eapply (GHEAD m' ws' x1' h' w a z1 rp); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | flia | flia | exact Rzh1 | exact Rw | flia | flia | exact HB]. }

zs. brs K0.
-
replace (rp <? 36) with true in HL by (symmetry; apply Z.ltb_lt; flia). cbn [orb] in HL.
eapply (GBODY x16); [flia | exact HL].
- replace (rp <? 36) with false in HL by (symmetry; apply Z.ltb_ge; flia). cbn [orb] in HL.
zs. brf K1; rewrite ?land_W64 in K1.
+
replace (rp =? 36) with false in HL by (symmetry; apply Z.eqb_neq; mlia). cbn [andb] in HL. injection HL as <-.
cbn [us_rp us_a us_z us_e2 us_x] in HK.
eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | exact Rw | flia | flia | exact HK].
+ replace (rp =? 36) with true in HL by (symmetry; apply Z.eqb_eq; mlia). cbn [andb] in HL.

assert (Hain : inring a z a) by (unfold inring; rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; exact Hrs1).
pose proof (X31H a) as Rta. pose proof (REL a ltac:(flia) (or_introl Hain)) as Eta.
pose proof (u32arr_read segs _ _ _ a _ _ XW (nth_error_wnth ws a ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RDa.
zs. rewrite (sx32_wval ws a (znth x a) (eq_sym Eta) Rta). set (ta := znth x a) in *.
zs. brf K2.
*
replace (ta <? 10384593) with false in HL by (symmetry; apply Z.ltb_ge; flia). injection HL as <-.
cbn [us_rp us_a us_z us_e2 us_x] in HK.
eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | exact Rw | flia | flia | exact HK].
* replace (ta <? 10384593) with true in HL by (symmetry; apply Z.ltb_lt; flia).
eapply (GBODY _); [flia | exact HL].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK"] Lemma L_U1A8 : S_U1A8.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 SEP SE_T SPLO SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros fo m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Haz Rrp Re2 HL HK. pose proof DI as DI0. dest_dfinv DI.
zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 0)%Z with rp by flia. zs.
pose proof L_U1C4 as NX. unfold F_floatscan_common__S_U1C4, F_floatscan_common__SU1C4 in NX. eapply NX; try eassumption; try flia.
Qed.

End Floatscan.

End G.
