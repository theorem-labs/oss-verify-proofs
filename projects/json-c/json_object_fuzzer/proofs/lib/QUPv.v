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
Variables (joff_1077 joff_1090 joff_1094 joff_1106 joff_1109 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_multf3 e_floatsitf e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1077 : decode_any (Z_to_bv 32 w_1077) = Some (Jal 1 joff_1077, 4%Z).
Hypothesis E_1077 : is_ecall (Z_to_bv 32 w_1077) = false.
Hypothesis D_1090 : decode_any (Z_to_bv 32 w_1090) = Some (Jal 1 joff_1090, 4%Z).
Hypothesis E_1090 : is_ecall (Z_to_bv 32 w_1090) = false.
Hypothesis D_1094 : decode_any (Z_to_bv 32 w_1094) = Some (Jal 1 joff_1094, 4%Z).
Hypothesis E_1094 : is_ecall (Z_to_bv 32 w_1094) = false.
Hypothesis D_1106 : decode_any (Z_to_bv 32 w_1106) = Some (Jal 1 joff_1106, 4%Z).
Hypothesis E_1106 : is_ecall (Z_to_bv 32 w_1106) = false.
Hypothesis D_1109 : decode_any (Z_to_bv 32 w_1109) = Some (Jal 1 joff_1109, 4%Z).
Hypothesis E_1109 : is_ecall (Z_to_bv 32 w_1109) = false.
Hypothesis LINK_1077 : gw_anch (base + 4308 + bv_signed joff_1077)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1090 : gw_anch (base + 4360 + bv_signed joff_1090)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1094 : gw_anch (base + 4376 + bv_signed joff_1094)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_1106 : gw_anch (base + 4424 + bv_signed joff_1106)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1109 : gw_anch (base + 4436 + bv_signed joff_1109)%Z (e_addtf3 + 0)%Z.
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
Definition S_A5C4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A5C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A5C4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.S_A5C4 segs base got_ssp RATP STRING_READ ssp_guard) S_A5C4 gw_tbl_37).
Definition S_A568 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A568 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A568 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_A568 segs base got_ssp RATP STRING_READ ssp_guard) S_A568 gw_tbl_38).
Definition S_A534 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A534 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_39)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A534 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_39)).
Local Definition gw_tbl_40 := (gw_ent (@QzQg.Mq0.S_A534 segs base got_ssp RATP STRING_READ ssp_guard) S_A534 gw_tbl_39).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_40)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).
Definition floatunsitf_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatunsitf_callv) constr:(gw_tbl_40)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatunsitf_callv)).

Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_40)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_40)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition cb44_merge : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb44_merge) constr:(gw_tbl_40)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb44_merge)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__S_A534 := S_A534 (only parsing).
Notation F_floatscan_common__S_A568 := S_A568 (only parsing).
Notation F_floatscan_common__S_A5C4 := S_A5C4 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_40)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_multf3 e_floatsitf e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1077 E_1077 D_1090 E_1090 D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1077 LINK_1090 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec addtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1077 joff_1090 joff_1094 joff_1106 joff_1109 got_ssp RATP STRING_READ ssp_guard e_multf3 e_floatsitf e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1077 E_1077 D_1090 E_1090 D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1077 LINK_1090 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec addtf3_spec multf3_spec.

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

Local Notation S_A5C4 := (@F_floatscan_common__S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A568 := (@F_floatscan_common__S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A534 := (@F_floatscan_common__S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_A5C4 : S_A5C4.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1094 joff_1106 joff_1109 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec fc pre post fuelc f0 kmin0 c0 Hp SPLO SPF SPT SG1 Q1 HS_A5C4"] Lemma L_A578 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 t : Z) (f : nat) sres,
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 1 -> (0 <= t < 2^31)%Z ->
df_asm_loop f a (mkAS 1 (f128_add (f128_mul C_1E9 zero0) (f128_of_u32 t)) z x) = Some sres -> (4 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 t) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1114)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1094 joff_1106 joff_1109 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec fc pre post fuelc f0 kmin0 c0 Hp SPLO SPF SPT SG1 Q1 HS_A5C4 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SE_T SPF2 SG2 SG3 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros until sres. intros DI RJ Hk FOK FRM' Hsg He2 Ra AI Rt HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := zero0); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 zero0) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_A5C4. eapply NX; try eassumption; try lia; try mk_dfinv.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1090 joff_1094 joff_1106 joff_1109 e_multf3 e_floatsitf e_addtf3 e_floatunsitf CODE BASE4 BASER D_1090 E_1090 D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1090 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec addtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_A5C4"] Lemma L_A568 : S_A568.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1090 joff_1094 joff_1106 joff_1109 e_multf3 e_floatsitf e_addtf3 e_floatunsitf CODE BASE4 BASER D_1090 E_1090 D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1090 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec addtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until xa. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI Naz Hxa HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (X31H a) as Rt. rewrite <- Hxa in Rt.
unfold fin_K0 in HK. rewrite (df_final_split 53 (-1074) sign 1024 zero0) in HK. fold zero0 in HK.
destruct (df_asm_loop 5 a _) as [sres|] eqn:HL; [|discriminate HK].
rewrite df_asm_loop_step in HL. cbn [as_i] in HL. change (0 <? LD_B1B_DIG)%Z with true in HL.
unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
rewrite Z.add_0_r, land2047, (Z.mod_small a 2048) in HL by lia.
replace (a =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). rewrite <- Hxa in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.
assert (Hza : ((z - a) mod 2048 <> 0)%Z).
{ intros E. apply Naz. symmetry. apply (mod_eq_idx a a z); try lia. all: rewrite Z.sub_diag, E; reflexivity. }
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW' | split; [exact LX | exact REL]] |]. split; [exact X31H|]. split; [lia|]. split; [hlia Rz4|]. split; [lia|]. exact Raw.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1077 joff_1094 joff_1106 joff_1109 e_multf3 e_floatsitf e_addtf3 e_floatunsitf CODE BASE4 BASER D_1077 E_1077 D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1077 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A5C4"] Lemma L_A534 : S_A534.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1077 joff_1094 joff_1106 joff_1109 e_multf3 e_floatsitf e_addtf3 e_floatunsitf CODE BASE4 BASER D_1077 E_1077 D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1077 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until S1. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI Eaz HS1 HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
unfold fin_K0 in HK. rewrite (df_final_split 53 (-1074) sign 1024 zero0) in HK. fold zero0 in HK.
destruct (df_asm_loop 5 a _) as [sres|] eqn:HL; [|discriminate HK].
rewrite df_asm_loop_step in HL. cbn [as_i] in HL. change (0 <? LD_B1B_DIG)%Z with true in HL.
unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
rewrite Z.add_0_r, land2047, (Z.mod_small a 2048) in HL by lia.
replace (a =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). rewrite !land2047 in HL.
subst a.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. zs. zs. zs. subst S1. fix_idx.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
-
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; lia]).
subst z. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
let v := getreg 9%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
pose proof (X31H 2047%Z) as Rt. pose proof (REL 2047%Z ltac:(lia) ltac:(right; right; split; [exact Hw | lia])) as Et.
pose proof (u32arr_read segs _ _ _ 2047%Z _ _ XW (nth_error_wnth ws 2047%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. fix_idx. zs. rewrite (sx32_wval ws 2047%Z (znth x 2047%Z) (eq_sym Et) Rt).
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578 with (h := false) (w := w); try eassumption; try lia; try mk_dfinv.
split; [|split; [exact X31H | split; [lia | split; [lia| split; [cbn; lia | exact Raw]]]]].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear - Hq Hne Ri0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1077 joff_1094 joff_1106 joff_1109 e_multf3 e_floatsitf e_addtf3 e_floatunsitf CODE BASE4 BASER D_1077 E_1077 D_1094 E_1094 D_1106 E_1106 D_1109 E_1109 LINK_1077 LINK_1094 LINK_1106 LINK_1109 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
-
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL.
rewrite znth_zupd_eq in HL by (unfold zlength; lia).
pose proof (u32arr_store_ok segs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
let v := getreg 9%Z in replace v with (Z_to_bv 64 (XA + 4 * z + 4)%Z) by (f_equal; lia).
zs.
pose proof (u32arr_write segs _ _ _ z (Z_to_bv 64 0) XW ltac:(lia)) as XW'. clear XW.
replace (q + -8312 + 4 * z + 4 + -4)%Z with (q + -8312 + 4 * z)%Z by lia.
store_done. rename XW' into XW.
pose proof (u32arr_read segs _ _ _ z _ _ XW (nth_error_wnth (upd ws (Z.to_nat z) (Z_to_bv 64 0)) z ltac:(lia) ltac:(rewrite upd_length; lia)) ltac:(lia) eq_refl) as RD.
zs. fix_idx. zs.
replace (sx32 (wnth (upd ws (Z.to_nat z) (Z_to_bv 64 0)) z)) with (Z_to_bv 64 0).
2:{ symmetry. apply (sx32_wval _ z 0); [rewrite wval_upd_same by lia; reflexivity | lia]. }
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578 with (h := h) (w := w); try eassumption; try lia; try mk_dfinv.
split; [|split; [| split; [lia | split; [hlia Rz4| split; [| exact Raw]]]]].
+ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hi0 Hr. destruct (Z.eq_dec i0 z) as [->|Hne].
* rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
* rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|].
destruct Hr as [Hr | [[Hh Hzi] | Hr]]; [| right; left; split; [exact Hh | lia] | right; right; exact Hr].
apply (proj1 (inring_grow z z i0 ltac:(lia) ltac:(rewrite Z.sub_diag; cbn; lia))) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx z z i0); lia.
+ intros i0. destruct (Z.eq_dec i0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H].
+ replace (z + 1 - z)%Z with 1%Z by lia. reflexivity.
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
Variables (joff_1148 joff_1160 joff_1163 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1148 : decode_any (Z_to_bv 32 w_1148) = Some (Jal 1 joff_1148, 4%Z).
Hypothesis E_1148 : is_ecall (Z_to_bv 32 w_1148) = false.
Hypothesis D_1160 : decode_any (Z_to_bv 32 w_1160) = Some (Jal 1 joff_1160, 4%Z).
Hypothesis E_1160 : is_ecall (Z_to_bv 32 w_1160) = false.
Hypothesis D_1163 : decode_any (Z_to_bv 32 w_1163) = Some (Jal 1 joff_1163, 4%Z).
Hypothesis E_1163 : is_ecall (Z_to_bv 32 w_1163) = false.
Hypothesis LINK_1148 : gw_anch (base + 4592 + bv_signed joff_1148)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_1160 : gw_anch (base + 4640 + bv_signed joff_1160)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1163 : gw_anch (base + 4652 + bv_signed joff_1163)%Z (e_addtf3 + 0)%Z.
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
Definition S_A69C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A69C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A69C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.S_A69C segs base got_ssp RATP STRING_READ ssp_guard) S_A69C gw_tbl_37).
Definition S_A62C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A62C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A62C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_A62C segs base got_ssp RATP STRING_READ ssp_guard) S_A62C gw_tbl_38).
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

Notation F_floatscan_common__S_A62C := S_A62C (only parsing).
Notation F_floatscan_common__S_A69C := S_A69C (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1148 joff_1160 joff_1163 got_ssp RATP STRING_READ ssp_guard e_multf3 e_addtf3 e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec.

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

Local Notation S_A69C := (@F_floatscan_common__S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A62C := (@F_floatscan_common__S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_A69C : S_A69C.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1148 joff_1160 joff_1163 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A69C"] Lemma L_A62C : S_A62C.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1148 joff_1160 joff_1163 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (2 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 2) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 2) 2047) in *.
assert (Ek : kk = ((a + 2) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.

assert (G648 : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (h' = false -> z' + 1 <= 2052)%Z -> (3 <= (z' - a) mod 2048)%Z ->
df_asm_loop f a (mkAS 3 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) z' x') = Some sres ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) (Z_to_bv 64 XA) (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x11e4)) fct None m' (seg_rom segs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Rz4' Hrs' HL'.
clear HL MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (X312 kk) as Rt. pose proof (REL2 kk ltac:(lia) (zone_in _ _ _ _ _ Kin)) as Et.
pose proof (u32arr_read segs _ _ _ kk _ _ XW (nth_error_wnth ws' kk ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. fix_idx. zs. rewrite (sx32_wval ws' kk (znth x' kk) (eq_sym Et) Rt).
set (t := znth x' kk) in *.
zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 Y) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_A69C. eapply NX; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW2 | split; [exact LX2 | exact REL2]] |]. split; [exact X312|]. split; [lia|]. split; [hlia Rz4'|]. split; [lia|]. exact Raw. }
zs. replace (2 + a)%Z with (a + 2)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia).
destruct (inring_plus a z 2 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G648 _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | hlia Rz4 | exact Hrs' | exact HL].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 2 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 3) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 3) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
+
rewrite Ez in HL. rewrite Ez. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
assert (Ekz : kk = z) by lia.
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; rewrite Ek in Ekz; clear - Raw Ekz Ra Ez w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1148 joff_1160 joff_1163 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec; Z.div_mod_to_equations; lia]).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; cbn; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
eapply (G648 _ ws x 0%Z false); [mk_dfinv | | exact X31H | | lia | lia | | exact HL].
* eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear - Hq Hne Ri0 Ra Rz Ez Hrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1148 joff_1160 joff_1163 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
* unfold inring. clear - Ra Rz Ez Hrs0 Rk K1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1148 joff_1160 joff_1163 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
* clear - Ra Rz Ez Hrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1148 joff_1160 joff_1163 e_multf3 e_addtf3 e_floatunsitf CODE BASE4 BASER D_1148 E_1148 D_1160 E_1160 D_1163 E_1163 LINK_1148 LINK_1160 LINK_1163 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec addtf3_spec multf3_spec. Z.div_mod_to_equations. lia.
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
Variables (hi_730 hi_1433 : bv 20).
Variables (lo_733 lo_1435 : bv 12).
Variables (joff_560 joff_603 joff_648 joff_718 joff_722 joff_727 joff_737 joff_742 joff_1421 joff_1425 joff_1430 joff_1439 : bv 21).
Variables (G_116a8 got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_multf3 e_floatsitf e_floatunsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_560 : decode_any (Z_to_bv 32 w_560) = Some (Jal 1 joff_560, 4%Z).
Hypothesis E_560 : is_ecall (Z_to_bv 32 w_560) = false.
Hypothesis D_603 : decode_any (Z_to_bv 32 w_603) = Some (Jal 1 joff_603, 4%Z).
Hypothesis E_603 : is_ecall (Z_to_bv 32 w_603) = false.
Hypothesis D_648 : decode_any (Z_to_bv 32 w_648) = Some (Jal 1 joff_648, 4%Z).
Hypothesis E_648 : is_ecall (Z_to_bv 32 w_648) = false.
Hypothesis D_718 : decode_any (Z_to_bv 32 w_718) = Some (Jal 1 joff_718, 4%Z).
Hypothesis E_718 : is_ecall (Z_to_bv 32 w_718) = false.
Hypothesis D_722 : decode_any (Z_to_bv 32 w_722) = Some (Jal 1 joff_722, 4%Z).
Hypothesis E_722 : is_ecall (Z_to_bv 32 w_722) = false.
Hypothesis D_727 : decode_any (Z_to_bv 32 w_727) = Some (Jal 1 joff_727, 4%Z).
Hypothesis E_727 : is_ecall (Z_to_bv 32 w_727) = false.
Hypothesis D_730 : decode_any (Z_to_bv 32 w_730) = Some (Auipc 12 hi_730, 4%Z).
Hypothesis E_730 : is_ecall (Z_to_bv 32 w_730) = false.
Hypothesis D_733 : decode_any (Z_to_bv 32 w_733) = Some (OpImm ALU_ADD 12 12 lo_733, 4%Z).
Hypothesis E_733 : is_ecall (Z_to_bv 32 w_733) = false.
Hypothesis D_737 : decode_any (Z_to_bv 32 w_737) = Some (Jal 1 joff_737, 4%Z).
Hypothesis E_737 : is_ecall (Z_to_bv 32 w_737) = false.
Hypothesis D_742 : decode_any (Z_to_bv 32 w_742) = Some (Jal 1 joff_742, 4%Z).
Hypothesis E_742 : is_ecall (Z_to_bv 32 w_742) = false.
Hypothesis D_1421 : decode_any (Z_to_bv 32 w_1421) = Some (Jal 1 joff_1421, 4%Z).
Hypothesis E_1421 : is_ecall (Z_to_bv 32 w_1421) = false.
Hypothesis D_1425 : decode_any (Z_to_bv 32 w_1425) = Some (Jal 1 joff_1425, 4%Z).
Hypothesis E_1425 : is_ecall (Z_to_bv 32 w_1425) = false.
Hypothesis D_1430 : decode_any (Z_to_bv 32 w_1430) = Some (Jal 1 joff_1430, 4%Z).
Hypothesis E_1430 : is_ecall (Z_to_bv 32 w_1430) = false.
Hypothesis D_1433 : decode_any (Z_to_bv 32 w_1433) = Some (Auipc 10 hi_1433, 4%Z).
Hypothesis E_1433 : is_ecall (Z_to_bv 32 w_1433) = false.
Hypothesis D_1435 : decode_any (Z_to_bv 32 w_1435) = Some (OpImm ALU_ADD 10 10 lo_1435, 4%Z).
Hypothesis E_1435 : is_ecall (Z_to_bv 32 w_1435) = false.
Hypothesis D_1439 : decode_any (Z_to_bv 32 w_1439) = Some (Jal 1 joff_1439, 4%Z).
Hypothesis E_1439 : is_ecall (Z_to_bv 32 w_1439) = false.
Hypothesis ANCH_733 : gw_anch (Z.shiftl (bv_signed hi_730) 12 + (base + 2920) + bv_signed lo_733)%Z G_116a8.
Hypothesis ANCH_1435 : gw_anch (Z.shiftl (bv_signed hi_1433) 12 + (base + 5732) + bv_signed lo_1435)%Z G_116a8.
Hypothesis LINK_560 : gw_anch (base + 2240 + bv_signed joff_560)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_603 : gw_anch (base + 2412 + bv_signed joff_603)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_648 : gw_anch (base + 2592 + bv_signed joff_648)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_718 : gw_anch (base + 2872 + bv_signed joff_718)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_722 : gw_anch (base + 2888 + bv_signed joff_722)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_727 : gw_anch (base + 2908 + bv_signed joff_727)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_737 : gw_anch (base + 2948 + bv_signed joff_737)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_742 : gw_anch (base + 2968 + bv_signed joff_742)%Z (e_divtf3 + 0)%Z.
Hypothesis LINK_1421 : gw_anch (base + 5684 + bv_signed joff_1421)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1425 : gw_anch (base + 5700 + bv_signed joff_1425)%Z (e_floatunsitf + 0)%Z.
Hypothesis LINK_1430 : gw_anch (base + 5720 + bv_signed joff_1430)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1439 : gw_anch (base + 5756 + bv_signed joff_1439)%Z (e_floatsitf + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis RNG_G_116a8 : gw_br G_116a8 64.
Hypothesis ROM_G_116a8 : ro_bytes segs G_116a8 [Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 100; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 232; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 39; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 160; Z_to_bv 8 134; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 66; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 150; Z_to_bv 8 152; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 225; Z_to_bv 8 245; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 28; Z_to_bv 8 2; Z_to_bv 8 29; Z_to_bv 8 14; Z_to_bv 8 24; Z_to_bv 8 3; Z_to_bv 8 30; Z_to_bv 8 22; Z_to_bv 8 20; Z_to_bv 8 15; Z_to_bv 8 25; Z_to_bv 8 17; Z_to_bv 8 4; Z_to_bv 8 8; Z_to_bv 8 31; Z_to_bv 8 27; Z_to_bv 8 13; Z_to_bv 8 23; Z_to_bv 8 21; Z_to_bv 8 19; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 26; Z_to_bv 8 12; Z_to_bv 8 18; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 5; Z_to_bv 8 10; Z_to_bv 8 9].
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
Definition S_T : ltac:(gw_rebind_ty (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) S_T gw_tbl_37).
Definition S_DD0 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_DD0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_DD0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_DD0 segs base got_ssp RATP STRING_READ ssp_guard) S_DD0 gw_tbl_38).
Definition S_DD24 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_DD24 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_39)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_DD24 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_39)).
Local Definition gw_tbl_40 := (gw_ent (@QzQg.Mq0.S_DD24 segs base got_ssp RATP STRING_READ ssp_guard) S_DD24 gw_tbl_39).
Definition S_M : ltac:(gw_rebind_ty (@QzQg.Mq0.S_M segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_40)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_M segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_40)).
Local Definition gw_tbl_41 := (gw_ent (@QzQg.Mq0.S_M segs base got_ssp RATP STRING_READ ssp_guard) S_M gw_tbl_40).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis floatunsitf_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq4.gw_all) (@QQLG.Mq4.floatunsitf_spec) e_floatunsitf)) in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatunsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis divtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQRC.divtf3_spec segs e_divtf3) 9%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_41))) in exact T).
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_41)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).
Definition floatunsitf_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatunsitf_callv) constr:(gw_tbl_41)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatunsitf_callv)).

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

Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_41)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition div_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.div_callE) constr:(gw_tbl_41)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.div_callE)).
Definition L_RET1 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.L_RET1) constr:(gw_tbl_41)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.L_RET1)).
Definition floatsitf_callsg : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.floatsitf_callsg) constr:(gw_tbl_41)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.floatsitf_callsg)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__L_RET1 := L_RET1 (only parsing).
Notation F_floatscan_common__S_DD0 := S_DD0 (only parsing).
Notation F_floatscan_common__S_DD24 := S_DD24 (only parsing).
Notation F_floatscan_common__S_M := S_M (only parsing).
Notation F_floatscan_common__S_T := S_T (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_41)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="G_116a8 got_ssp RATP STRING_READ ssp_guard e_multf3 e_floatsitf e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_560 E_560 D_603 E_603 D_648 E_648 D_718 E_718 D_722 E_722 D_727 E_727 D_730 E_730 D_733 E_733 D_737 E_737 D_742 E_742 D_1421 E_1421 D_1425 E_1425 D_1430 E_1430 D_1433 E_1433 D_1435 E_1435 D_1439 E_1439 ANCH_733 ANCH_1435 LINK_560 LINK_603 LINK_648 LINK_718 LINK_722 LINK_727 LINK_737 LINK_742 LINK_1421 LINK_1425 LINK_1430 LINK_1439 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec divtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_730 hi_1433 lo_733 lo_1435 joff_560 joff_603 joff_648 joff_718 joff_722 joff_727 joff_737 joff_742 joff_1421 joff_1425 joff_1430 joff_1439 G_116a8 got_ssp RATP STRING_READ ssp_guard e_multf3 e_floatsitf e_floatunsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_560 E_560 D_603 E_603 D_648 E_648 D_718 E_718 D_722 E_722 D_727 E_727 D_730 E_730 D_733 E_733 D_737 E_737 D_742 E_742 D_1421 E_1421 D_1425 E_1425 D_1430 E_1430 D_1433 E_1433 D_1435 E_1435 D_1439 E_1439 ANCH_733 ANCH_1435 LINK_560 LINK_603 LINK_648 LINK_718 LINK_722 LINK_727 LINK_737 LINK_742 LINK_1421 LINK_1425 LINK_1430 LINK_1439 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec divtf3_spec multf3_spec.

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

Local Notation L_RET1 := (@F_floatscan_common__L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_T := (@F_floatscan_common__S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD0 := (@F_floatscan_common__S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD24 := (@F_floatscan_common__S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_M := (@F_floatscan_common__S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.

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

Hypothesis HS_T : S_T.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_603 e_multf3 CODE BASE4 BASER D_603 E_603 LINK_603 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD0 : S_DD0.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_603 e_multf3 CODE BASE4 BASER D_603 E_603 LINK_603 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM HS_T. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_T | gw_hide HS_T | idtac].
intros m; intros until Y. intros _ DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
zs. call_split 80%Z (eapply mul_callE with (X := X) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL.
Qed.

Ltac some_snd H := apply (f_equal (fun o : option (shfile * Z) => match o with Some pr => snd pr | None => 0%Z end)) in H; cbv beta iota delta [snd] in H.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_603 e_multf3 CODE BASE4 BASER D_603 E_603 LINK_603 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO multf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD28 : forall m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X Y : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = f128_mul X Y ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x8c4)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_603 e_multf3 CODE BASE4 BASER D_603 E_603 LINK_603 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO multf3_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM HS_T. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_T | gw_hide HS_T | idtac].
intros until Y. intros DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
zs. zs. zs. zs. zs.
pose proof L_DD0 as NX. unfold F_floatscan_common__S_DD0 in NX. eapply NX; try eassumption.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_560 joff_603 e_multf3 e_floatunsitf CODE BASE4 BASER D_560 E_560 D_603 E_603 LINK_560 LINK_603 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD24 : S_DD24.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_560 joff_603 e_multf3 e_floatunsitf CODE BASE4 BASER D_560 E_560 D_603 E_603 LINK_560 LINK_603 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO floatunsitf_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM HS_T. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_T | gw_hide HS_T | idtac].
intros m; intros until u. intros _ DI RJ Hk FOK FRM' Ru Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h.
zs. callx (eapply floatunsitf_callv with (u := u); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
eapply L_DD28; try eassumption; try mk_dfinv.
Qed.

Ltac pose_rd0 := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
match goal with XW2 : u32arr segs mm _ ?wsx |- _ =>
let R := fresh "RD" in
pose proof (u32arr_read segs _ _ _ 0%Z _ _ XW2 (nth_error_wnth wsx 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as R;
replace (XA + 4 * 0)%Z with XA in R by lia end end.
#[using="Type"] Lemma p10s_lit : forall j, (0 <= j <= 7)%Z -> (0 <= znth p10s j < 2^31)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_T. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_T | gw_hide HS_T | idtac]. clear. intros j Hj. destruct (p10s_range j Hj) as [R _]. lia. Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_730 hi_1433 lo_733 lo_1435 joff_560 joff_603 joff_648 joff_718 joff_722 joff_727 joff_737 joff_742 joff_1421 joff_1425 joff_1430 joff_1439 G_116a8 e_multf3 e_floatsitf e_floatunsitf e_divtf3 CODE BASE4 BASER D_560 E_560 D_603 E_603 D_648 E_648 D_718 E_718 D_722 E_722 D_727 E_727 D_730 E_730 D_733 E_733 D_737 E_737 D_742 E_742 D_1421 E_1421 D_1425 E_1425 D_1430 E_1430 D_1433 E_1433 D_1435 E_1435 D_1439 E_1439 ANCH_733 ANCH_1435 LINK_560 LINK_603 LINK_648 LINK_718 LINK_722 LINK_727 LINK_737 LINK_742 LINK_1421 LINK_1425 LINK_1430 LINK_1439 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec divtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_T"] Lemma L_M : S_M.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_730 hi_1433 lo_733 lo_1435 joff_560 joff_603 joff_648 joff_718 joff_722 joff_727 joff_737 joff_742 joff_1421 joff_1425 joff_1430 joff_1439 G_116a8 e_multf3 e_floatsitf e_floatunsitf e_divtf3 CODE BASE4 BASER D_560 E_560 D_603 E_603 D_648 E_648 D_718 E_718 D_722 E_722 D_727 E_727 D_730 E_730 D_733 E_733 D_737 E_737 D_742 E_742 D_1421 E_1421 D_1425 E_1425 D_1430 E_1430 D_1433 E_1433 D_1435 E_1435 D_1439 E_1439 ANCH_733 ANCH_1435 LINK_560 LINK_603 LINK_648 LINK_718 LINK_722 LINK_727 LINK_737 LINK_742 LINK_1421 LINK_1425 LINK_1430 LINK_1439 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 LAY_got_ssp_RERRNO floatsitf_spec floatunsitf_spec divtf3_spec multf3_spec Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rlnz Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_mid in HK.
assert (Kin0 : inring 0 kz 0) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H 0%Z) as Rt0. pose proof (REL 0%Z ltac:(lia) Kin0) as Et0.
set (x0 := znth x 0) in *.

zs. fixw3. fixw. try replace (lnz + 0)%Z with lnz by lia.
zs. zs. brs K1.
{
replace (lnz <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (lnz <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. brs K2.
{
replace (rp <? 18)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r in HK. cbv iota in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (rp <? 18)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. fixw3. fixw. try replace (rp + 0)%Z with rp by lia.
zs. brs K3.
{
replace (lnz <=? rp)%Z with false in HK by (symmetry; apply Z.leb_gt; lia). cbn [andb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (lnz <=? rp)%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbn [andb] in HK.

pose proof (u32arr_read segs _ _ _ 0%Z _ _ XW (nth_error_wnth ws 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
replace (XA + 4 * 0)%Z with XA in RD0 by lia.
zs. zs. brf K4.
-
replace (rp =? 9)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
zs. zs. brs K5.
+
assert (Rrp2 : (10 <= rp <= 17)%Z) by lia.
replace (rp <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
zs. rewrite (Z.shiftl_mul_pow2 rp 1) by lia. change (2^1)%Z with 2%Z.
zs. zs. fixw3. fixw.
zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0).
zs. fixw3. fixw. zs. fixw3. fixw.
match goal with |- context [Z_to_bv 64 (?e + 27)%Z] => replace (e + 27)%Z with (53 - 3 * (rp - 9))%Z by lia end.
set (bitlim := (53 - 3 * (rp - 9))%Z) in *.

assert (G94 : forall (x10' : word), yR = f128_mul (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (rp - 10))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10' (Z_to_bv 64 30) x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
(Z_to_bv 64 8) x19 x20 (Z_to_bv 64 x0) x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1630)) fct None m (seg_rom segs))).
{ intros x10' Hy. clear HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs. fixw3. fixw. zs. zs. rewrite (Z.shiftl_mul_pow2 (rp + -10)) by lia. change (2^2)%Z with 4%Z. zs. zs.

assert (G_DC : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
evt segs POST
(MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (rp - 10))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Ft (Z_to_bv 64 (base + 0x1678)) fct None m2 (seg_rom segs))).
{ intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
pose proof DI2 as DI'. dest_dfinv DI'.
pose proof (p10s_lit (rp - 10)%Z ltac:(lia)) as Rp.
zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
zs. eapply L_DD28; try eassumption; try mk_dfinv. }
assert (Hc : (rp = 10 \/ rp = 11 \/ rp = 12 \/ rp = 13 \/ rp = 14 \/ rp = 15 \/ rp = 16 \/ rp = 17)%Z) by lia.
clear Hy. clearbody bitlim.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_DC; mk_dfinv). }
zs. zs. brs K6.
*
replace (30 <? bitlim)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK.
eapply G94. symmetry. exact HK.
* replace (30 <? bitlim)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
zs. rewrite srlw_small by lia.
assert (Rs0 : (0 <= Z.shiftr x0 bitlim)%Z) by (apply Z.shiftr_nonneg; lia).
assert (Rs1 : (Z.shiftr x0 bitlim <= x0)%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]; assert (1 <= 2 ^ bitlim)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia); nia).
zs. brf K7.
--
replace (Z.shiftr x0 bitlim =? 0)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
eapply G94. symmetry. exact HK.
-- replace (Z.shiftr x0 bitlim =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)).
+
assert (Rrp1 : (1 <= rp <= 8)%Z) by lia.
replace (rp <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK. rename HK into HyR.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs.
zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs. fixw3. fixw. zs. zs. zs. try rewrite zext32_small by lia. try (rewrite (Z.shiftl_mul_pow2 (8 - rp)) by lia; change (2^2)%Z with 4%Z). zs. zs.

assert (G_E4 : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
evt segs POST
(MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (8 - rp))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Ft (Z_to_bv 64 (base + 0xb80)) fct None m2 (seg_rom segs))).
{ intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
pose proof DI2 as DI'. dest_dfinv DI'.
pose proof (p10s_lit (8 - rp)%Z ltac:(lia)) as Rp.
zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
set (PF := f128_of_i32 (znth p10s (8 - rp))) in *. pose proof (lo64_range PF) as R4l. pose proof (hi64_range PF) as R4h.
zs. zs. zs. zs.
zs. call_split 112%Z (eapply div_callE with (X := P) (Y := PF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL. }
assert (Hc : (rp = 1 \/ rp = 2 \/ rp = 3 \/ rp = 4 \/ rp = 5 \/ rp = 6 \/ rp = 7 \/ rp = 8)%Z) by lia.
clear HyR.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_E4; mk_dfinv).
-
replace (rp =? 9)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs. zs.
pose proof L_DD24 as NX. unfold F_floatscan_common__S_DD24 in NX. eapply NX; try eassumption; try lia; try mk_dfinv; try (symmetry; exact HK).
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
Definition S_NK : ltac:(gw_rebind_ty (@QzQg.Mq0.S_NK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_NK segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.S_NK segs base got_ssp RATP STRING_READ ssp_guard) S_NK gw_tbl_9).
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

Notation F_floatscan_common__S_NK := S_NK (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_NK := (@F_floatscan_common__S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).

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

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_NK : S_NK.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre Hp T1 SE_T SPF SPF2 SPT SG1 SG3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SPLO SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
unfold F_floatscan_common__S_NK.
induction fi as [|fi IH]; intros until s1; intros DI FOK FRM' XR X31H Ra Rz Rk Hkz Nkz Rc Hsh Rrp Rw RB Re2 HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_dnk_loop_step in HL. cbn [dk_k] in HL.
replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; flia). cbn [negb] in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs. pose proof (Z.mod_pos_bound (k - a) 2048 ltac:(flia)) as Rks.
assert (Kin : inring a z k) by (unfold inring; assert ((k - a) mod 2048 <> (z - a) mod 2048)%Z; [intros E; apply Nkz; apply (mod_eq_idx a z k); flia | flia]).
pose proof (X31H k) as Rt. pose proof (REL k ltac:(flia) (zone_in h _ _ _ _ Kin)) as Et.
pose proof (u32arr_read segs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *.
zs. rewrite srlw_small by flia.
pose proof (shr_half t sh ltac:(flia) ltac:(flia)) as Rts.
zs. fixw2. fixw.
set (v := (Z.shiftr t sh + carry)%Z) in *.
assert (Rv : (0 <= v < 2^31)%Z) by (subst v; flia).
zs. zs. showall.
pose proof (lor_lxor_nonneg k a v ltac:(flia) ltac:(flia) ltac:(flia)) as Rlor.
pose proof (u32arr_store_ok segs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ k (Z_to_bv 64 v) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
set (x' := zupd x k v) in *.
assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (zone h w a z)).
{ split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
intros i0 Hq Hr. subst x'. destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia | exact Hr]. }
assert (X31' : X31 x').
{ intros i0. subst x'. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X31H]. }
set (tmp := Z.land t (Z.shiftl 1 sh - 1)) in *.
assert (Rtmp : (0 <= tmp <= 2^sh - 1)%Z) by (subst tmp; rewrite Z.shiftl_1_l; apply land_mask_range; destruct Hsh as [-> | ->]; cbn; flia).
pose proof (dn_carry_bound sh tmp Hsh Rtmp) as Rc'.
assert (Rtmp2 : (0 <= tmp < 512)%Z) by (destruct Hsh as [-> | ->]; cbn in Rtmp; flia).
assert (Ebody : df_dnk_body z sh (mkDK k carry a i rp x) =
mkDK (Z.land (k + 1) MASK) (Z.shiftr 1000000000 sh * tmp)
(if (k =? a) && (v =? 0) then Z.land (a + 1) MASK else a)%Z
(if (k =? a) && (v =? 0) then i - 1 else i)%Z
(if (k =? a) && (v =? 0) then rp - 9 else rp)%Z x').
{ unfold df_dnk_body. cbn [dk_k dk_x dk_carry dk_a dk_i dk_rp]. fold t. fold tmp.
replace (u32 (Z.shiftr t sh + carry)) with v by (subst v; unfold u32; symmetry; apply Z.mod_small; flia). fold x'.
replace (znth x' k) with v by (subst x'; rewrite znth_zupd_eq by (unfold zlength; flia); reflexivity).
replace (u32 (Z.shiftr 1000000000 sh * tmp)) with (Z.shiftr 1000000000 sh * tmp)%Z by (unfold u32; symmetry; apply Z.mod_small; flia).
destruct ((k =? a) && (v =? 0))%Z; reflexivity. }
rewrite Ebody in HL. clear Ebody. change MASK with 2047%Z in HL.
assert (Hk1 : ((k + 1 - a) mod 2048 = (k - a) mod 2048 + 1)%Z).
{ unfold inring in Kin. replace (k + 1 - a)%Z with ((k - a) + 1)%Z by flia. rewrite <- (Zplus_mod_idemp_l (k - a)). apply Z.mod_small. flia. }

assert (LATCH : forall (cnd : bool) m' (a' : Z) (x30' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign fR ->
(0 <? Z.lor (Z.lxor k a) v)%Z = cnd ->
a' = (if cnd then a else (a + 1) mod 2048)%Z ->
df_dnk_loop fi z sh (mkDK ((k + 1) mod 2048) (Z.shiftr 1000000000 sh * tmp) a' (if cnd then i else i - 1) (if cnd then rp else rp - 9) x')%Z = Some s1 ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
(Z_to_bv 64 z) (Z_to_bv 64 a') x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) (Z_to_bv 64 tmp) x30' (Z_to_bv 64 v))
Ft (Z_to_bv 64 (base + 0xfcc)) fct None m' (seg_rom segs))).
{ intros cnd m' a' x30' DI2 Hcnd Ha' HL2. clear HL MI MU WM FRhi BY SSP1 SSP2 LOW ERR XW LW FC. try clear ST.
pose proof DI2 as DI2'. dest_dfinv DI2'.
assert (Ra' : (0 <= a' < 2048)%Z) by (subst a'; destruct cnd; [flia | apply Z.mod_pos_bound; flia]).

assert (Wz : forall i0, (if cnd then w else if (a =? 2047)%Z then false else w) = true -> (a' <= i0)%Z -> w = true /\ (a <= i0)%Z).
{ intros i0. rewrite Ha'. destruct cnd; [intros E L; split; [exact E | exact L] |].
destruct (Z.eqb_spec a 2047) as [Ea|Na]; [intros E; discriminate E|].
intros E L. split; [exact E|]. rewrite Z.mod_small in L by flia. clear - L w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. flia. }
assert (Wr : (if cnd then w else if (a =? 2047)%Z then false else w) = false -> (9 * a' + (if cnd then rp else rp - 9) <= 560)%Z).
{ rewrite Ha'. destruct cnd; [exact Rw|]. destruct (Z.eqb_spec a 2047) as [Ea|Na].
- intros _. rewrite Ea. change ((2047 + 1) mod 2048)%Z with 0%Z. clear - Rrp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. flia.
- intros E. specialize (Rw E). rewrite Z.mod_small by flia. clear - Rw Na Ra w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. flia. }
zs. rewrite Hcnd. zs. zs. fixw2. fixw.
replace (Z_to_bv 64 (tmp * Z.shiftr 1000000000 sh)) with (Z_to_bv 64 (Z.shiftr 1000000000 sh * tmp)) by (f_equal; flia).
zs. zs. zs. rewrite land2047. zs.

rewrite rp_upd.
zs. brf K9; rewrite ?land_W64 in K9.
-
destruct fi as [|fi']; [discriminate HL2|]. rewrite df_dnk_loop_step in HL2. cbn [dk_k] in HL2. replace ((k + 1) mod 2048 =? z)%Z with true in HL2 by (symmetry; apply Z.eqb_eq; clear - K9 Rk w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; rewrite ?land2047 in K9; Z.div_mod_to_equations; flia). cbn [negb] in HL2.
injection HL2 as <-.
eapply (CONT _ _ _ _ _ _ _ _ (if cnd then w else if (a =? 2047)%Z then false else w)); [mk_dfinv | cbn [dk_x dk_a] | exact X31' | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia | flia ] | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia | flia ] | cbn; destruct cnd; flia | cbn [dk_a dk_rp]; exact Wr | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia | flia ]].
subst a'. destruct cnd; [exact XR'|].

destruct XR' as (L1 & L2 & R3). split; [exact L1|]. split; [exact L2|]. intros i0 Hq Hr. apply R3; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (Wz i0 Hw' Hai)].
unfold inring in Hr |- *. rewrite Zminus_mod_idemp_r in Hr. clear - Hr Hq Ra Rz Kin w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. unfold inring in Kin. Z.div_mod_to_equations. nia.
-
eapply IH with (x := x') (h := h) (w := (if cnd then w else if (a =? 2047)%Z then false else w)) (k := ((k + 1) mod 2048)%Z) (carry := (Z.shiftr 1000000000 sh * tmp)%Z) (a := a') (z := z) (sh := sh) (e2 := e2) (B := B) (s1 := s1);
[mk_dfinv | assumption | assumption | | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | | clear - K9 Rk w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; rewrite ?land2047 in K9; Z.div_mod_to_equations; flia | flia | exact Hsh | destruct cnd; flia | exact Wr | flia | flia | exact HL2 | exact CONT].
+ subst a'. destruct cnd; [exact XR'|].
destruct XR' as (L1 & L2 & R3). split; [exact L1|]. split; [exact L2|]. intros i0 Hq Hr. apply R3; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (Wz i0 Hw' Hai)].
unfold inring in Hr |- *. rewrite Zminus_mod_idemp_r in Hr. clear - Hr Hq Ra Rz Kin w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. unfold inring in Kin. Z.div_mod_to_equations. nia.
+ subst a'. destruct cnd.
* rewrite Zminus_mod_idemp_l, Hk1. unfold inring in Kin. flia.
* rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. replace (k + 1 - (a + 1))%Z with (k - a)%Z by flia.
unfold inring in Kin. clear - Kin Ra Rz Rk K9 Hk1 Rrs Rks w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. Z.div_mod_to_equations. nia. }

zs. brf K2.
-
replace ((k =? a) && (v =? 0))%Z with false in HL.
2:{ symmetry. destruct (Z.eqb_spec k a); destruct (Z.eqb_spec v 0); cbn; try reflexivity. exfalso. apply K2. apply (proj2 (lor_lxor_zero k a v ltac:(flia) ltac:(flia) ltac:(flia))). split; assumption. }
zs.
replace (Z_to_bv 64 (Z.land t (Z.land (2 ^ sh - 1) 18446744073709551615))) with (Z_to_bv 64 tmp)
by (subst tmp; rewrite Z.shiftl_1_l; f_equal; f_equal; rewrite land_W64; symmetry; apply Z.mod_small; destruct Hsh as [-> | ->]; cbn; flia).
rewrite land2047 in HL.
eapply (LATCH true); [mk_dfinv | apply Z.ltb_lt; flia | reflexivity | exact HL].
-
destruct (proj1 (lor_lxor_zero k a v ltac:(flia) ltac:(flia) ltac:(flia)) ltac:(flia)) as [Eka Ev].
replace ((k =? a) && (v =? 0))%Z with true in HL by (symmetry; rewrite Eka, Ev, !Z.eqb_refl; reflexivity).
clear K2. zs. zs. zs. zs. rewrite land2047.
replace (Z_to_bv 64 (Z.land t (Z.land (2 ^ sh - 1) 18446744073709551615))) with (Z_to_bv 64 tmp)
by (subst tmp; rewrite Z.shiftl_1_l; f_equal; f_equal; rewrite land_W64; symmetry; apply Z.mod_small; destruct Hsh as [-> | ->]; cbn; flia).
rewrite !land2047 in HL. subst k.
eapply (LATCH false); [mk_dfinv | rewrite Z.lxor_nilpotent, Z.lor_0_l, Ev; reflexivity | reflexivity | exact HL].
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
Variables (hi_792 hi_843 : bv 20).
Variables (lo_796 lo_845 : bv 12).
Variables (G_107c0 G_116a8 got_ssp RATP STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_792 : decode_any (Z_to_bv 32 w_792) = Some (Auipc 16 hi_792, 4%Z).
Hypothesis E_792 : is_ecall (Z_to_bv 32 w_792) = false.
Hypothesis D_796 : decode_any (Z_to_bv 32 w_796) = Some (OpImm ALU_ADD 16 16 lo_796, 4%Z).
Hypothesis E_796 : is_ecall (Z_to_bv 32 w_796) = false.
Hypothesis D_843 : decode_any (Z_to_bv 32 w_843) = Some (Auipc 13 hi_843, 4%Z).
Hypothesis E_843 : is_ecall (Z_to_bv 32 w_843) = false.
Hypothesis D_845 : decode_any (Z_to_bv 32 w_845) = Some (Load SZ8 true 13 13 lo_845, 4%Z).
Hypothesis E_845 : is_ecall (Z_to_bv 32 w_845) = false.
Hypothesis ANCH_796 : gw_anch (Z.shiftl (bv_signed hi_792) 12 + (base + 3168) + bv_signed lo_796)%Z G_116a8.
Hypothesis ANCH_845 : gw_anch (Z.shiftl (bv_signed hi_843) 12 + (base + 3372) + bv_signed lo_845)%Z G_107c0.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis RNG_G_116a8 : gw_br G_116a8 64.
Hypothesis ROM_G_116a8 : ro_bytes segs G_116a8 [Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 100; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 232; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 39; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 160; Z_to_bv 8 134; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 66; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 150; Z_to_bv 8 152; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 225; Z_to_bv 8 245; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 28; Z_to_bv 8 2; Z_to_bv 8 29; Z_to_bv 8 14; Z_to_bv 8 24; Z_to_bv 8 3; Z_to_bv 8 30; Z_to_bv 8 22; Z_to_bv 8 20; Z_to_bv 8 15; Z_to_bv 8 25; Z_to_bv 8 17; Z_to_bv 8 4; Z_to_bv 8 8; Z_to_bv 8 31; Z_to_bv 8 27; Z_to_bv 8 13; Z_to_bv 8 23; Z_to_bv 8 21; Z_to_bv 8 19; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 26; Z_to_bv 8 12; Z_to_bv 8 18; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 5; Z_to_bv 8 10; Z_to_bv 8 9].
Hypothesis RNG_G_107c0 : gw_br G_107c0 8.
Hypothesis ROM_G_107c0 : ro_bytes segs G_107c0 (le8 (Z_to_bv 64 19342813113834067)).
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
Definition S_U1A8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) S_U1A8 gw_tbl_9).
Definition S_T : ltac:(gw_rebind_ty (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) S_T gw_tbl_10).
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

Notation F_floatscan_common__S_T := S_T (only parsing).
Notation F_floatscan_common__S_U1A8 := S_U1A8 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="G_107c0 G_116a8 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO.

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

Local Notation S_U1A8 := (@F_floatscan_common__S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_T := (@F_floatscan_common__S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_U1A8 : S_U1A8.

#[using="Type"] Lemma lor_shl32 : forall k, (0 <= k < 2^31)%Z -> (Z.lor (Z.land (Z.shiftl k 32) 18446744073709551615) 4294967295 + 1 = (k + 1) * 4294967296)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change (2^32)%Z with 4294967296%Z.
rewrite land_W64, (Z.mod_small (k * 4294967296)) by lia.
rewrite <- Z.lxor_lor. 2:{ change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. rewrite Z.mod_mul. reflexivity. lia. }
rewrite <- Z.add_nocarry_lxor. { lia. }
change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. apply Z.mod_mul. lia.
Qed.
#[using="Type"] Lemma tz_dec32 : forall j, Z_to_bv 64 ((j + 1) * 4294967296 + 18446744069414584320) = Z_to_bv 64 (j * 4294967296).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros j. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma df_tz_loop_step : forall n x z, df_tz_loop (S n) x z = if (znth x (z - 1) =? 0)%Z then df_tz_loop n x (z - 1) else Some z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma df_al_loop_step : forall n p10 z s, df_al_loop (S n) p10 z s = if negb (al_k s =? z)%Z then df_al_loop n p10 z (df_al_body p10 s) else Some s.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma divuw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z ->
v_divuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros v i Hv Hi. unfold v_divuw. rewrite !unsigned_lit by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
rewrite (Z.mod_small i), (Z.mod_small v) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
assert (0 <= v / i < 2147483648)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite swrap32_eq. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma magic_q9 : forall rp, (-2^20 <= rp <= 2^20)%Z ->
(Z.shiftr (bv_signed (Z_to_bv 64 (Z.land rp 18446744073709551615 * 954437177))) 33
+ Z.shiftr (Z.land (Z.land rp 18446744073709551615 * 954437177) 18446744073709551615) 63 = Z.quot rp 9)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros rp Hrp.
rewrite (Z_to_bv_eqm (Z.land rp 18446744073709551615 * 954437177) (rp * 954437177)).
2:{ rewrite land_W64. apply Z.mul_mod_idemp_l. lia. }
rewrite signed_of_Z by lia. rewrite !land_W64. rewrite Z.mul_mod_idemp_l by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^33)%Z with 8589934592%Z. change (2^63)%Z with 9223372036854775808%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (intros; apply Z.rem_nonpos; lia).
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma rem9_fix : forall rp, (-2^20 <= rp <= 2^20)%Z ->
bv_swrap 32 (Z.land (bv_swrap 32 (Z.land rp 18446744073709551615 - Z.land (Z.quot rp 9) 18446744073709551615)) 18446744073709551615
- Z.land (Z.shiftl (Z.land (Z.quot rp 9) 18446744073709551615) 3) 18446744073709551615) = Z.rem rp 9.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros rp Hrp. rewrite !land_W64, !swrap32_eq, Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma shr63_neg : forall v, (-2^63 <= v < 0)%Z -> Z.shiftr v 63 = (-1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shr63_nonneg : forall v, (0 <= v < 2^63)%Z -> Z.shiftr v 63 = 0%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
#[using="Type"] Lemma shr30_4z : forall z, (0 <= z)%Z -> Z.shiftr (z * 4294967296) 30 = (4 * z)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros z Hz. rewrite Z.shiftr_div_pow2 by lia. change (2^30)%Z with 1073741824%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma zext32_small : forall v, (0 <= v < 2^32)%Z -> Z.land v 4294967295 = v.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros v Hv. change 4294967295%Z with (2^32 - 1)%Z. apply land_mask_small; lia. Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard pre"] Lemma L_TZL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (rp kz j z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= j <= kz)%Z ->
df_tz_loop n x j = Some z ->
(forall x15', (1 <= z <= j)%Z -> znth x (z - 1) <> 0%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 (kz - z + 1)) (Z_to_bv 64 (XA + 4 * (z - 2))) (Z_to_bv 64 z) (Z_to_bv 64 18446744069414584320) x15' x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc10)) fct None m (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 ((j + 1) * 4294967296)) (Z_to_bv 64 (kz - j)) (Z_to_bv 64 (XA + 4 * (j - 1))) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 18446744069414584320) x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xbf8)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard pre segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
induction n as [|n IH]; intros until z; intros DI XR X31H Rkz Hx0 Rj HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_tz_loop_step in HL.
assert (Kin : inring 0 kz (j - 1)) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H (j - 1)%Z) as Rt. pose proof (REL (j - 1)%Z ltac:(lia) Kin) as Et.
pose proof (u32arr_read segs _ _ _ (j - 1)%Z _ _ XW (nth_error_wnth ws (j - 1)%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws (j - 1)%Z (znth x (j - 1)) (eq_sym Et) Rt). set (t := znth x (j - 1)) in *. clear RD.
zs. zs. rewrite tz_dec32. zs. replace (j + 1 + -1)%Z with j by lia. zs. replace (XA + 4 * (j - 1) + -4)%Z with (XA + 4 * (j - 1 - 1))%Z by lia.
zs. brf K1.
-
replace (t =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
assert (Hj1 : j <> 1%Z) by (intros E; apply Hx0; subst t; rewrite E in K1; exact K1).
replace (kz - j + 1)%Z with (kz - (j - 1))%Z by lia. replace (j * 4294967296)%Z with ((j - 1 + 1) * 4294967296)%Z by (f_equal; lia).
replace (Z_to_bv 64 j) with (Z_to_bv 64 (j - 1 + 1)) by (f_equal; lia).
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz (j - 1)%Z z);
[exact DI | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HL | ].
intros x15' Rz Hnz. eapply CONT; [lia | exact Hnz].
- replace (t =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). injection HL as <-.
replace (j - 1 - 1)%Z with (j - 2)%Z by lia.
eapply CONT; [lia | subst t; exact K1].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_843 lo_845 G_107c0 CODE D_843 E_843 D_845 E_845 ANCH_845 RNG_got_ssp RNG_ssp_guard RNG_G_107c0 ROM_G_107c0 fc pre post fuelc f0 kmin0 c0 HM HS_U1A8"] Lemma L_UPI : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp a z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 z) -> X31 x -> (0 <= a < z)%Z -> (1 <= z <= 2047)%Z -> (-2^16 <= rp <= 2^16 /\ 9 * a + rp <= 560)%Z ->
dfK_up 53 (-1074) sign fR rp a z 0 x = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd1c)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_843 lo_845 G_107c0 CODE D_843 E_843 D_845 E_845 ANCH_845 RNG_got_ssp RNG_ssp_guard RNG_G_107c0 ROM_G_107c0 fc pre post fuelc f0 kmin0 c0 HM HS_U1A8 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until z. intros DI RJ Hk FOK FRM' Hsg XR X31H Ra Rz Rrp HK.
unfold dfK_up in HK. destruct (df_up_loop FUEL_SCALE _) as [[rp' a' z' e2' x']|] eqn:HL; [|discriminate HK].
pose proof DI as DI'. dest_dfinv DI'. bury_disj.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
stmt HS_U1A8. eapply (NX 2000%nat) with (h := false) (w := false) (x := x) (s' := mkUS rp' a' z' e2' x');
[exact DI | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | lia | | exact X31H | lia | intros _; lia | intros _; lia | lia | lia | cbn; lia | unfold FUEL_SCALE in HL; exact HL | ].
- eapply xrel_iff; [| exact XR]. intros i Hi [Hr | [[Hr _] | [Hr _]]]; [| discriminate Hr | discriminate Hr]. unfold inring in Hr |- *. clear - Hr Hi Ra Rz w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_843 lo_845 G_107c0 CODE D_843 E_843 D_845 E_845 ANCH_845 RNG_got_ssp RNG_ssp_guard RNG_G_107c0 ROM_G_107c0 segs base. Z.div_mod_to_equations. nia.
- unfold up_K, fin_K0. cbn [us_rp us_a us_z us_e2 us_x]. unfold dfK_dn in HK.
destruct (df_dn_loop FUEL_SCALE _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate HK]. cbn [ds_a ds_z ds_x ds_e2].
cbv beta zeta in HK. change (- (-1074) - 53 + 3)%Z with 1024%Z in HK. fold zero0 in HK.
destruct (df_final _ _ _ _ _ _ _ _ _ _) as [y|]; [|discriminate HK]. injection HK as <-. reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre T1 SPF SPF2 SPT SG1"] Lemma L_ALK : forall (n : nat) m (x1 x6 x7 x8 x9 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (k carry a rp z p10 j10 rpm9 kz rp0 : Z) (s1 : st_al),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (inring 0 z) -> X31 x ->
(1 <= z <= 2046)%Z -> (0 <= k < z)%Z -> (0 <= a <= k)%Z -> (a = k -> carry <> 0%Z \/ (k = 0%Z /\ znth x 0 <> 0%Z)) ->
(0 <= carry < 2^30)%Z -> (0 <= j10 <= 7)%Z -> p10 = znth p10s j10 -> (rp = rp0 - 9 * a)%Z -> (-2^15 <= rp0 <= 2^15)%Z ->
(1 <= rpm9 <= 8)%Z -> (1 <= kz <= 2046)%Z ->
df_al_loop n p10 z (mkAL k a rp carry x) = Some s1 ->
(forall m' ws' (x6' x7' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (al_x s1) (inring 0 z) -> X31 (al_x s1) -> al_k s1 = z ->
(0 <= al_a s1 <= z)%Z -> (al_a s1 = z -> al_carry s1 <> 0%Z) -> (0 <= al_carry s1 < 2^30)%Z -> (al_rp s1 = rp0 - 9 * al_a s1)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * z)) x6' x7' x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) (Z_to_bv 64 (al_carry s1)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (al_a s1)) x20 x21 x22 (Z_to_bv 64 (al_rp s1)) (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xce8)) fct None m' (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 carry) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xcc0)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre T1 SPF SPF2 SPT SG1 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 SEP SE_T SPLO SG2 SG3 Q1 FRM HS_U1A8. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
induction n as [|n IH]; intros until s1; intros DI FOK FRM' XR X31H Rz Rk Ra Hak Rc Rj Hp10 Rrp Rrp0 Rrpm9 Rkz HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in HL.
unfold df_al_body in HL. cbn [al_k al_x al_a al_rp al_carry] in HL.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10]. rewrite <- Hp10 in Rp10, Dp10.
assert (Kin : inring 0 z k) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) Kin) as Et.
pose proof (u32arr_read segs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
zs. rewrite divuw_small by lia.
pose proof (Z.mod_pos_bound t p10 ltac:(lia)) as Rtm.
assert (Rtq : (0 <= t / p10 < 214748365)%Z) by (clear - Rt Rp10 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | nia]]).
zs. fixw3. fixw.
set (v := (t / p10 + carry)%Z) in *.
assert (Rv : (0 <= v < 2^31)%Z) by (clear - Rtq Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; subst v; lia).
zs. zs.
pose proof (u32arr_store_ok segs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (Rc' : (0 <= t mod p10 * (1000000000 / p10) < 1000000000)%Z).
{ clear - Rtm Rp10 Dp10 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. set (u := (t mod p10)%Z) in *. set (w := (1000000000 / p10)%Z) in *. clearbody u w. nia. }
set (carry' := (t mod p10 * (1000000000 / p10))%Z) in *.
rewrite (u32_id v) in HL by (clear - Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia). rewrite (Z.mul_comm (1000000000 / p10) (t mod p10)) in HL. fold carry' in HL. rewrite (u32_id carry') in HL by (clear - Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia).
set (x' := zupd x k v) in *.
assert (Exk : znth x' k = v) by (clear - LX Rk Rz w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; subst x'; rewrite znth_zupd_eq by (unfold zlength; lia); reflexivity). rewrite Exk in HL.
assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (inring 0 z)).
{ clear - LW' LX REL Rk Rz Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
intros q0 Hq Hr. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia | exact Hr]. }
assert (X31' : X31 x').
{ clear - X31H LX Rk Rz Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. intros q0. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); exact Rv | rewrite znth_zupd_neq by lia; apply X31H]. }
pose proof (lor_lxor_nonneg k a v ltac:(lia) ltac:(lia) ltac:(lia)) as Rw.

assert (G0FC : forall (cb : bool),
cb = (0 <? Z.lor (Z.lxor k a) v)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 t) (Z_to_bv 64 (t / p10)) x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (if cb then a else a + 1)%Z) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 (Z_to_bv 64 v) x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc98)) fct None m1 (seg_rom segs))).
{ intros cb Hcb.
assert (Ecb : cb = negb ((k =? a) && (v =? 0))%Z).
{ rewrite Hcb. clear - Rw Rk Ra Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. destruct ((k =? a) && (v =? 0))%Z eqn:Eb; cbn [negb].
- apply andb_prop in Eb. destruct Eb as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
apply Z.ltb_ge. rewrite (proj2 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia)) (conj E1 E2)). lia.
- apply Z.ltb_lt. assert (Hne : Z.lor (Z.lxor k a) v <> 0%Z); [|lia].
intros E0. apply (proj1 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia))) in E0. destruct E0 as [E1 E2].
apply Bool.andb_false_iff in Eb. destruct Eb as [Eb|Eb]; apply Z.eqb_neq in Eb; lia. }
zs. zs. rewrite <- Hcb. zs. zs. fixw3. fixw. replace (t - t / p10 * p10)%Z with (t mod p10)%Z by (rewrite Zmod_eq_full by lia; lia).
zs. zs. try rewrite (land_W64_small (t mod p10)) by (clear - Rtm w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia). try rewrite (swrap32_small (t mod p10 * (1000000000 / p10))) by (clear - Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia). fold carry'.
zs. zs. rewrite rp_upd. zs. replace (XA + 4 * k + 4)%Z with (XA + 4 * (k + 1))%Z by lia.
set (a2 := (if cb then a else a + 1)%Z) in *. set (rp2 := (if cb then rp else rp - 9)%Z) in *.
assert (Ea2 : (if (k =? a) && (v =? 0) then (Z.land (a + 1) MASK, rp - 9) else (a, rp))%Z = (a2, rp2)).
{ subst a2 rp2. rewrite Ecb. destruct ((k =? a) && (v =? 0))%Z; cbn [negb]; [|reflexivity]. change MASK with 2047%Z. rewrite land2047, Z.mod_small by lia. reflexivity. }
rewrite Ea2 in HL. clear Ea2.
assert (Ra2 : (0 <= a2 <= k + 1)%Z) by (subst a2; destruct cb; lia).
assert (Hak2 : (a2 = k + 1 -> carry' <> 0)%Z).
{ subst a2. rewrite Ecb. destruct (Z.eqb_spec k a) as [Eka|Hka]; destruct (Z.eqb_spec v 0) as [Ev|Hv]; cbn [andb negb]; try lia.
intros _. destruct (Hak (eq_sym Eka)) as [Hc | [Hk0 Hx0]]; [exfalso; subst v; lia|].
assert (Ht0 : t <> 0%Z) by (subst t; rewrite Hk0; exact Hx0).
assert (Htp : (t < p10)%Z). { subst v. assert (t / p10 = 0)%Z by lia. destruct (Z.lt_ge_cases t p10); [assumption|]. exfalso. assert (1 <= t / p10)%Z by (apply Z.div_le_lower_bound; lia). lia. }
subst carry'. rewrite Z.mod_small by lia. assert (10 <= 1000000000 / p10)%Z by (apply Z.div_le_lower_bound; lia). nia. }
assert (Rrp2 : (rp2 = rp0 - 9 * a2)%Z) by (subst rp2 a2; destruct cb; lia).
clearbody a2 rp2. clear Hcb Ecb.
zs. brf K3.
-
destruct n as [|n']; [discriminate HL|]. rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k + 1 =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in HL. injection HL as <-.
replace (Z_to_bv 64 (XA + 4 * (k + 1))) with (Z_to_bv 64 (XA + 4 * z)) by (f_equal; lia).
replace (Z_to_bv 64 (k + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
eapply CONT; [mk_dfinv | exact XR' | exact X31' | cbn; lia | cbn; lia | cbn; intros E; apply Hak2; lia | cbn; lia | cbn; lia].
-
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev _ sign x' (k + 1)%Z carry' a2 rp2 z p10 j10 rpm9 kz rp0 s1);
[mk_dfinv | exact FOK | exact FRM' | exact XR' | exact X31' | lia | lia | lia | intros E; left; exact (Hak2 E) | lia | lia | exact Hp10 | lia | lia | lia | lia | exact HL | exact CONT]. }
zs. brf K2.
-
eapply (G0FC true). symmetry. apply Z.ltb_lt. lia.
-
zs. zs. rewrite land2047, (Z.mod_small (a + 1) 2048) by lia. zs.
eapply (G0FC false). symmetry. apply Z.ltb_ge. lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO HM T1 SPF SPF2 SPT SG1 HS_U1A8"] Lemma L_T : S_T.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO HM T1 SPF SPF2 SPT SG1 HS_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 SEP SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_tz in HK. destruct (df_tz_loop FUEL_RING x kz) as [z|] eqn:HTZ; [|discriminate HK]. unfold FUEL_RING in HTZ.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
rewrite lor_shl32 by lia. replace (Z.shiftl kz 2 + XA + -4)%Z with (XA + 4 * (kz - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (Z_to_bv 64 0) with (Z_to_bv 64 (kz - kz)) by (f_equal; lia).
eapply (L_TZL 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz kz z);
[exact DI0 | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HTZ | ].
intros x15' Rz Hnz. clear HTZ.
unfold dfK_al in HK. unfold nz in HK.

zs. fixw3. fixw. replace (kz - (kz - z + 1))%Z with (z - 1)%Z by lia.
zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite magic_q9 by lia. rewrite rem9_fix by lia.
pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as Rrem.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; intros; apply Z.rem_nonpos; lia).
set (r9 := Z.rem rp 9) in *. assert (Rr9 : (-8 <= r9 <= 8)%Z) by (clear - Rrem w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; lia). clearbody r9. clear Rrem.
zs. fixw3. fixw. replace (z - 1 + 1)%Z with z by lia.

assert (G178 : forall m' ws' x' (a' rp' z' rpm9 : Z) (x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' x' (inring 0 z') -> X31 x' -> (0 <= a' < z')%Z -> (1 <= z' <= 2047)%Z -> (-2^15 - 9 * 2047 <= rp' <= 2^15 /\ 9 * a' + rp' <= 537)%Z -> (1 <= rpm9 <= 8)%Z ->
dfK_up 53 (-1074) sign fR (rp' + (9 - rpm9)) a' z' 0 x' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 x10' (Z_to_bv 64 rpm9) x12' x13' x14' x15'' x16' x17'
(Z_to_bv 64 z') (Z_to_bv 64 a') x20 x21 x22 (Z_to_bv 64 rp') (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd14)) fct None m' (seg_rom segs))).
{ intros m' ws' x' a' rp' z' rpm9 x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' DI2 XR2 X312 Ra' Rz' Rrp' Rrpm9 HK2.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HK. pose proof DI2 as DI'. dest_dfinv DI'.
zs. fixw3. fixw. zs. replace (rp' - rpm9 + 9)%Z with (rp' + (9 - rpm9))%Z by lia.
eapply L_UPI; [exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | exact XR2 | exact X312 | lia | lia | lia | exact HK2]. }
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (E0 : r9 = 0%Z) by (clear - K1 Rr9 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; mlia).
rewrite E0, Z.eqb_refl in HK. cbv beta iota in HK.
zs. zs.
eapply L_UPI; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | lia | lia | exact HK].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
-
assert (Hne0 : r9 <> 0%Z) by (clear - K1 Rr9 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; mlia).
replace (r9 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0). cbv beta iota in HK.

assert (G0B4 : forall rpm9 (x14' : word), rpm9 = (if 0 <=? rp then r9 else r9 + 9)%Z -> (1 <= rpm9 <= 8)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) x14' x15' x16 x17
(Z_to_bv 64 z) x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc50)) fct None m (seg_rom segs))).
{ intros rpm9 x14' Hrpm9 Rrpm9. rewrite <- Hrpm9 in HK.
set (j10 := (8 - rpm9)%Z) in *.

assert (G0E4 : forall (x16' : word),
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (z - 1 + 1)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (znth p10s j10)) x16' (Z_to_bv 64 1000001536)
(Z_to_bv 64 z) (Z_to_bv 64 0) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc80)) fct None m (seg_rom segs))).
{ intros x16'.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10].
destruct (df_al_loop FUEL_RING _ z _) as [[k1 a1 rp1 c1 x1']|] eqn:HAL; [|discriminate HK]. unfold FUEL_RING in HAL.
zs. zs. zs. rewrite zext32_small by lia. zs. rewrite divw_small by lia. zs. zs.
replace (Z_to_bv 64 (z - 1 + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
replace (Z_to_bv 64 XA) with (Z_to_bv 64 (XA + 4 * 0))%Z by (f_equal; lia).
eapply (L_ALK 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x 0%Z 0%Z 0%Z rp z (znth p10s j10) j10 rpm9 kz rp (mkAL k1 a1 rp1 c1 x1'));
[exact DI0 | exact FOK | exact FRM' | | exact X31H | lia | lia | lia | intros _; right; split; [reflexivity | exact Hx0] | lia | lia | reflexivity | lia | lia | lia | lia | exact HAL | ].
{ eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia. }
intros m' ws' x6' x7' x28' DI2 XR2 X312 Hk1 Ra1 Hac1 Rc1 Rrp1. cbn [al_x al_k al_a al_carry al_rp] in DI2, XR2, X312, Hk1, Ra1, Hac1, Rc1, Rrp1 |- *. subst k1.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HAL LW' LX REL X31H.
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
unfold nz in HK.
zs. brf K4.
+
replace (negb (c1 =? 0)) with false in HK by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia). cbv beta iota in HK.
eapply (G178 m' ws' x1' a1 rp1 z rpm9); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | lia | lia | lia | lia | exact HK].
+
replace (negb (c1 =? 0)) with true in HK by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbv beta iota in HK.
zs. fixw3. fixw. replace (z - 1 + 2)%Z with (z + 1)%Z by lia.
zs. try rewrite signed_of_Z by lia. rewrite shr30_4z by lia. zs. zs.
pose proof (u32arr_store_ok segs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ z (Z_to_bv 64 c1) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
eapply (G178 _ (upd ws' (Z.to_nat z) (Z_to_bv 64 c1)) (zupd x1' z c1) a1 rp1 (z + 1)%Z rpm9); [mk_dfinv | | | lia | lia | lia | lia | exact HK].
* split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros q0 Hq Hr. destruct (Z.eq_dec q0 z) as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
-- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL2; [lia|].
unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
* intros q0. destruct (Z.eq_dec q0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X312]. }

zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
assert (Hc : (rpm9 = 1 \/ rpm9 = 2 \/ rpm9 = 3 \/ rpm9 = 4 \/ rpm9 = 5 \/ rpm9 = 6 \/ rpm9 = 7 \/ rpm9 = 8)%Z) by lia.
clear HK Hrpm9. subst j10.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rpm9; (zs; eapply G0E4). }

zs. try rewrite (signed_of_Z rp) by lia.
destruct (Z.lt_ge_cases rp 0) as [Hneg|Hpos].
+ rewrite (shr63_neg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
+ rewrite (shr63_nonneg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with true by (symmetry; apply Z.leb_le; lia). lia.
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
Variables (hi_792 hi_843 : bv 20).
Variables (lo_796 lo_845 : bv 12).
Variables (G_107c0 G_116a8 got_ssp RATP STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_792 : decode_any (Z_to_bv 32 w_792) = Some (Auipc 16 hi_792, 4%Z).
Hypothesis E_792 : is_ecall (Z_to_bv 32 w_792) = false.
Hypothesis D_796 : decode_any (Z_to_bv 32 w_796) = Some (OpImm ALU_ADD 16 16 lo_796, 4%Z).
Hypothesis E_796 : is_ecall (Z_to_bv 32 w_796) = false.
Hypothesis D_843 : decode_any (Z_to_bv 32 w_843) = Some (Auipc 13 hi_843, 4%Z).
Hypothesis E_843 : is_ecall (Z_to_bv 32 w_843) = false.
Hypothesis D_845 : decode_any (Z_to_bv 32 w_845) = Some (Load SZ8 true 13 13 lo_845, 4%Z).
Hypothesis E_845 : is_ecall (Z_to_bv 32 w_845) = false.
Hypothesis ANCH_796 : gw_anch (Z.shiftl (bv_signed hi_792) 12 + (base + 3168) + bv_signed lo_796)%Z G_116a8.
Hypothesis ANCH_845 : gw_anch (Z.shiftl (bv_signed hi_843) 12 + (base + 3372) + bv_signed lo_845)%Z G_107c0.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis RNG_G_116a8 : gw_br G_116a8 64.
Hypothesis ROM_G_116a8 : ro_bytes segs G_116a8 [Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 100; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 232; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 39; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 160; Z_to_bv 8 134; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 66; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 128; Z_to_bv 8 150; Z_to_bv 8 152; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 225; Z_to_bv 8 245; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 28; Z_to_bv 8 2; Z_to_bv 8 29; Z_to_bv 8 14; Z_to_bv 8 24; Z_to_bv 8 3; Z_to_bv 8 30; Z_to_bv 8 22; Z_to_bv 8 20; Z_to_bv 8 15; Z_to_bv 8 25; Z_to_bv 8 17; Z_to_bv 8 4; Z_to_bv 8 8; Z_to_bv 8 31; Z_to_bv 8 27; Z_to_bv 8 13; Z_to_bv 8 23; Z_to_bv 8 21; Z_to_bv 8 19; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 26; Z_to_bv 8 12; Z_to_bv 8 18; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 5; Z_to_bv 8 10; Z_to_bv 8 9].
Hypothesis RNG_G_107c0 : gw_br G_107c0 8.
Hypothesis ROM_G_107c0 : ro_bytes segs G_107c0 (le8 (Z_to_bv 64 19342813113834067)).
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
Definition S_U1A8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.S_U1A8 segs base got_ssp RATP STRING_READ ssp_guard) S_U1A8 gw_tbl_9).
Definition S_T : ltac:(gw_rebind_ty (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_T segs base got_ssp RATP STRING_READ ssp_guard) S_T gw_tbl_10).
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

Notation F_floatscan_common__S_T := S_T (only parsing).
Notation F_floatscan_common__S_U1A8 := S_U1A8 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="G_107c0 G_116a8 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
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

Local Notation S_U1A8 := (@F_floatscan_common__S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_T := (@F_floatscan_common__S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_U1A8 : S_U1A8.

#[using="Type"] Lemma lor_shl32 : forall k, (0 <= k < 2^31)%Z -> (Z.lor (Z.land (Z.shiftl k 32) 18446744073709551615) 4294967295 + 1 = (k + 1) * 4294967296)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change (2^32)%Z with 4294967296%Z.
rewrite land_W64, (Z.mod_small (k * 4294967296)) by lia.
rewrite <- Z.lxor_lor. 2:{ change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. rewrite Z.mod_mul. reflexivity. lia. }
rewrite <- Z.add_nocarry_lxor. { lia. }
change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. apply Z.mod_mul. lia.
Qed.
#[using="Type"] Lemma tz_dec32 : forall j, Z_to_bv 64 ((j + 1) * 4294967296 + 18446744069414584320) = Z_to_bv 64 (j * 4294967296).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros j. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma df_tz_loop_step : forall n x z, df_tz_loop (S n) x z = if (znth x (z - 1) =? 0)%Z then df_tz_loop n x (z - 1) else Some z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma df_al_loop_step : forall n p10 z s, df_al_loop (S n) p10 z s = if negb (al_k s =? z)%Z then df_al_loop n p10 z (df_al_body p10 s) else Some s.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma divuw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z ->
v_divuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros v i Hv Hi. unfold v_divuw. rewrite !unsigned_lit by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
rewrite (Z.mod_small i), (Z.mod_small v) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
assert (0 <= v / i < 2147483648)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite swrap32_eq. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma magic_q9 : forall rp, (-2^20 <= rp <= 2^20)%Z ->
(Z.shiftr (bv_signed (Z_to_bv 64 (Z.land rp 18446744073709551615 * 954437177))) 33
+ Z.shiftr (Z.land (Z.land rp 18446744073709551615 * 954437177) 18446744073709551615) 63 = Z.quot rp 9)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros rp Hrp.
rewrite (Z_to_bv_eqm (Z.land rp 18446744073709551615 * 954437177) (rp * 954437177)).
2:{ rewrite land_W64. apply Z.mul_mod_idemp_l. lia. }
rewrite signed_of_Z by lia. rewrite !land_W64. rewrite Z.mul_mod_idemp_l by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^33)%Z with 8589934592%Z. change (2^63)%Z with 9223372036854775808%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (intros; apply Z.rem_nonpos; lia).
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma rem9_fix : forall rp, (-2^20 <= rp <= 2^20)%Z ->
bv_swrap 32 (Z.land (bv_swrap 32 (Z.land rp 18446744073709551615 - Z.land (Z.quot rp 9) 18446744073709551615)) 18446744073709551615
- Z.land (Z.shiftl (Z.land (Z.quot rp 9) 18446744073709551615) 3) 18446744073709551615) = Z.rem rp 9.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
clear. intros rp Hrp. rewrite !land_W64, !swrap32_eq, Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma shr63_neg : forall v, (-2^63 <= v < 0)%Z -> Z.shiftr v 63 = (-1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shr63_nonneg : forall v, (0 <= v < 2^63)%Z -> Z.shiftr v 63 = 0%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
#[using="Type"] Lemma shr30_4z : forall z, (0 <= z)%Z -> Z.shiftr (z * 4294967296) 30 = (4 * z)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros z Hz. rewrite Z.shiftr_div_pow2 by lia. change (2^30)%Z with 1073741824%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma zext32_small : forall v, (0 <= v < 2^32)%Z -> Z.land v 4294967295 = v.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac]. clear. intros v Hv. change 4294967295%Z with (2^32 - 1)%Z. apply land_mask_small; lia. Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard pre"] Lemma L_TZL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (rp kz j z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= j <= kz)%Z ->
df_tz_loop n x j = Some z ->
(forall x15', (1 <= z <= j)%Z -> znth x (z - 1) <> 0%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 (kz - z + 1)) (Z_to_bv 64 (XA + 4 * (z - 2))) (Z_to_bv 64 z) (Z_to_bv 64 18446744069414584320) x15' x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc10)) fct None m (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 ((j + 1) * 4294967296)) (Z_to_bv 64 (kz - j)) (Z_to_bv 64 (XA + 4 * (j - 1))) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 18446744069414584320) x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xbf8)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard pre segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_U1A8. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
induction n as [|n IH]; intros until z; intros DI XR X31H Rkz Hx0 Rj HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_tz_loop_step in HL.
assert (Kin : inring 0 kz (j - 1)) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H (j - 1)%Z) as Rt. pose proof (REL (j - 1)%Z ltac:(lia) Kin) as Et.
pose proof (u32arr_read segs _ _ _ (j - 1)%Z _ _ XW (nth_error_wnth ws (j - 1)%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws (j - 1)%Z (znth x (j - 1)) (eq_sym Et) Rt). set (t := znth x (j - 1)) in *. clear RD.
zs. zs. rewrite tz_dec32. zs. replace (j + 1 + -1)%Z with j by lia. zs. replace (XA + 4 * (j - 1) + -4)%Z with (XA + 4 * (j - 1 - 1))%Z by lia.
zs. brf K1.
-
replace (t =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
assert (Hj1 : j <> 1%Z) by (intros E; apply Hx0; subst t; rewrite E in K1; exact K1).
replace (kz - j + 1)%Z with (kz - (j - 1))%Z by lia. replace (j * 4294967296)%Z with ((j - 1 + 1) * 4294967296)%Z by (f_equal; lia).
replace (Z_to_bv 64 j) with (Z_to_bv 64 (j - 1 + 1)) by (f_equal; lia).
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz (j - 1)%Z z);
[exact DI | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HL | ].
intros x15' Rz Hnz. eapply CONT; [lia | exact Hnz].
- replace (t =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). injection HL as <-.
replace (j - 1 - 1)%Z with (j - 2)%Z by lia.
eapply CONT; [lia | subst t; exact K1].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_843 lo_845 G_107c0 CODE D_843 E_843 D_845 E_845 ANCH_845 RNG_got_ssp RNG_ssp_guard RNG_G_107c0 ROM_G_107c0 fc pre post fuelc f0 kmin0 c0 HS_U1A8"] Lemma L_UPI : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp a z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 z) -> X31 x -> (0 <= a < z)%Z -> (1 <= z <= 2047)%Z -> (-2^16 <= rp <= 2^16 /\ 9 * a + rp <= 560)%Z ->
dfK_up 53 (-1074) sign fR rp a z 0 x = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd1c)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_843 lo_845 G_107c0 CODE D_843 E_843 D_845 E_845 ANCH_845 RNG_got_ssp RNG_ssp_guard RNG_G_107c0 ROM_G_107c0 fc pre post fuelc f0 kmin0 c0 HS_U1A8 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until z. intros DI RJ Hk FOK FRM' Hsg XR X31H Ra Rz Rrp HK.
unfold dfK_up in HK. destruct (df_up_loop FUEL_SCALE _) as [[rp' a' z' e2' x']|] eqn:HL; [|discriminate HK].
pose proof DI as DI'. dest_dfinv DI'. bury_disj.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
stmt HS_U1A8. eapply (NX 2000%nat) with (h := false) (w := false) (x := x) (s' := mkUS rp' a' z' e2' x');
[exact DI | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | lia | | exact X31H | lia | intros _; lia | intros _; lia | lia | lia | cbn; lia | unfold FUEL_SCALE in HL; exact HL | ].
- eapply xrel_iff; [| exact XR]. intros i Hi [Hr | [[Hr _] | [Hr _]]]; [| discriminate Hr | discriminate Hr]. unfold inring in Hr |- *. clear - Hr Hi Ra Rz w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_843 lo_845 G_107c0 CODE D_843 E_843 D_845 E_845 ANCH_845 RNG_got_ssp RNG_ssp_guard RNG_G_107c0 ROM_G_107c0 segs base. Z.div_mod_to_equations. nia.
- unfold up_K, fin_K0. cbn [us_rp us_a us_z us_e2 us_x]. unfold dfK_dn in HK.
destruct (df_dn_loop FUEL_SCALE _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate HK]. cbn [ds_a ds_z ds_x ds_e2].
cbv beta zeta in HK. change (- (-1074) - 53 + 3)%Z with 1024%Z in HK. fold zero0 in HK.
destruct (df_final _ _ _ _ _ _ _ _ _ _) as [y|]; [|discriminate HK]. injection HK as <-. reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre T1 SPF SPF2 SPT SG1"] Lemma L_ALK : forall (n : nat) m (x1 x6 x7 x8 x9 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (k carry a rp z p10 j10 rpm9 kz rp0 : Z) (s1 : st_al),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (inring 0 z) -> X31 x ->
(1 <= z <= 2046)%Z -> (0 <= k < z)%Z -> (0 <= a <= k)%Z -> (a = k -> carry <> 0%Z \/ (k = 0%Z /\ znth x 0 <> 0%Z)) ->
(0 <= carry < 2^30)%Z -> (0 <= j10 <= 7)%Z -> p10 = znth p10s j10 -> (rp = rp0 - 9 * a)%Z -> (-2^15 <= rp0 <= 2^15)%Z ->
(1 <= rpm9 <= 8)%Z -> (1 <= kz <= 2046)%Z ->
df_al_loop n p10 z (mkAL k a rp carry x) = Some s1 ->
(forall m' ws' (x6' x7' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (al_x s1) (inring 0 z) -> X31 (al_x s1) -> al_k s1 = z ->
(0 <= al_a s1 <= z)%Z -> (al_a s1 = z -> al_carry s1 <> 0%Z) -> (0 <= al_carry s1 < 2^30)%Z -> (al_rp s1 = rp0 - 9 * al_a s1)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * z)) x6' x7' x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) (Z_to_bv 64 (al_carry s1)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (al_a s1)) x20 x21 x22 (Z_to_bv 64 (al_rp s1)) (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xce8)) fct None m' (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 carry) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xcc0)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO pre T1 SPF SPF2 SPT SG1 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 SEP SE_T SPLO SG2 SG3 Q1 FRM HS_U1A8. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_U1A8 | gw_hide HS_U1A8 | idtac].
induction n as [|n IH]; intros until s1; intros DI FOK FRM' XR X31H Rz Rk Ra Hak Rc Rj Hp10 Rrp Rrp0 Rrpm9 Rkz HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in HL.
unfold df_al_body in HL. cbn [al_k al_x al_a al_rp al_carry] in HL.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10]. rewrite <- Hp10 in Rp10, Dp10.
assert (Kin : inring 0 z k) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) Kin) as Et.
pose proof (u32arr_read segs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
zs. rewrite divuw_small by lia.
pose proof (Z.mod_pos_bound t p10 ltac:(lia)) as Rtm.
assert (Rtq : (0 <= t / p10 < 214748365)%Z) by (clear - Rt Rp10 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | nia]]).
zs. fixw3. fixw.
set (v := (t / p10 + carry)%Z) in *.
assert (Rv : (0 <= v < 2^31)%Z) by (clear - Rtq Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; subst v; lia).
zs. zs.
pose proof (u32arr_store_ok segs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (Rc' : (0 <= t mod p10 * (1000000000 / p10) < 1000000000)%Z).
{ clear - Rtm Rp10 Dp10 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. set (u := (t mod p10)%Z) in *. set (w := (1000000000 / p10)%Z) in *. clearbody u w. nia. }
set (carry' := (t mod p10 * (1000000000 / p10))%Z) in *.
rewrite (u32_id v) in HL by (clear - Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia). rewrite (Z.mul_comm (1000000000 / p10) (t mod p10)) in HL. fold carry' in HL. rewrite (u32_id carry') in HL by (clear - Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia).
set (x' := zupd x k v) in *.
assert (Exk : znth x' k = v) by (clear - LX Rk Rz w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; subst x'; rewrite znth_zupd_eq by (unfold zlength; lia); reflexivity). rewrite Exk in HL.
assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (inring 0 z)).
{ clear - LW' LX REL Rk Rz Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
intros q0 Hq Hr. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia | exact Hr]. }
assert (X31' : X31 x').
{ clear - X31H LX Rk Rz Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. intros q0. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); exact Rv | rewrite znth_zupd_neq by lia; apply X31H]. }
pose proof (lor_lxor_nonneg k a v ltac:(lia) ltac:(lia) ltac:(lia)) as Rw.

assert (G0FC : forall (cb : bool),
cb = (0 <? Z.lor (Z.lxor k a) v)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 t) (Z_to_bv 64 (t / p10)) x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (if cb then a else a + 1)%Z) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 (Z_to_bv 64 v) x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc98)) fct None m1 (seg_rom segs))).
{ intros cb Hcb.
assert (Ecb : cb = negb ((k =? a) && (v =? 0))%Z).
{ rewrite Hcb. clear - Rw Rk Ra Rv w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base. destruct ((k =? a) && (v =? 0))%Z eqn:Eb; cbn [negb].
- apply andb_prop in Eb. destruct Eb as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
apply Z.ltb_ge. rewrite (proj2 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia)) (conj E1 E2)). lia.
- apply Z.ltb_lt. assert (Hne : Z.lor (Z.lxor k a) v <> 0%Z); [|lia].
intros E0. apply (proj1 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia))) in E0. destruct E0 as [E1 E2].
apply Bool.andb_false_iff in Eb. destruct Eb as [Eb|Eb]; apply Z.eqb_neq in Eb; lia. }
zs. zs. rewrite <- Hcb. zs. zs. fixw3. fixw. replace (t - t / p10 * p10)%Z with (t mod p10)%Z by (rewrite Zmod_eq_full by lia; lia).
zs. zs. try rewrite (land_W64_small (t mod p10)) by (clear - Rtm w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia). try rewrite (swrap32_small (t mod p10 * (1000000000 / p10))) by (clear - Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO segs base; lia). fold carry'.
zs. zs. rewrite rp_upd. zs. replace (XA + 4 * k + 4)%Z with (XA + 4 * (k + 1))%Z by lia.
set (a2 := (if cb then a else a + 1)%Z) in *. set (rp2 := (if cb then rp else rp - 9)%Z) in *.
assert (Ea2 : (if (k =? a) && (v =? 0) then (Z.land (a + 1) MASK, rp - 9) else (a, rp))%Z = (a2, rp2)).
{ subst a2 rp2. rewrite Ecb. destruct ((k =? a) && (v =? 0))%Z; cbn [negb]; [|reflexivity]. change MASK with 2047%Z. rewrite land2047, Z.mod_small by lia. reflexivity. }
rewrite Ea2 in HL. clear Ea2.
assert (Ra2 : (0 <= a2 <= k + 1)%Z) by (subst a2; destruct cb; lia).
assert (Hak2 : (a2 = k + 1 -> carry' <> 0)%Z).
{ subst a2. rewrite Ecb. destruct (Z.eqb_spec k a) as [Eka|Hka]; destruct (Z.eqb_spec v 0) as [Ev|Hv]; cbn [andb negb]; try lia.
intros _. destruct (Hak (eq_sym Eka)) as [Hc | [Hk0 Hx0]]; [exfalso; subst v; lia|].
assert (Ht0 : t <> 0%Z) by (subst t; rewrite Hk0; exact Hx0).
assert (Htp : (t < p10)%Z). { subst v. assert (t / p10 = 0)%Z by lia. destruct (Z.lt_ge_cases t p10); [assumption|]. exfalso. assert (1 <= t / p10)%Z by (apply Z.div_le_lower_bound; lia). lia. }
subst carry'. rewrite Z.mod_small by lia. assert (10 <= 1000000000 / p10)%Z by (apply Z.div_le_lower_bound; lia). nia. }
assert (Rrp2 : (rp2 = rp0 - 9 * a2)%Z) by (subst rp2 a2; destruct cb; lia).
clearbody a2 rp2. clear Hcb Ecb.
zs. brf K3.
-
destruct n as [|n']; [discriminate HL|]. rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k + 1 =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in HL. injection HL as <-.
replace (Z_to_bv 64 (XA + 4 * (k + 1))) with (Z_to_bv 64 (XA + 4 * z)) by (f_equal; lia).
replace (Z_to_bv 64 (k + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
eapply CONT; [mk_dfinv | exact XR' | exact X31' | cbn; lia | cbn; lia | cbn; intros E; apply Hak2; lia | cbn; lia | cbn; lia].
-
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev _ sign x' (k + 1)%Z carry' a2 rp2 z p10 j10 rpm9 kz rp0 s1);
[mk_dfinv | exact FOK | exact FRM' | exact XR' | exact X31' | lia | lia | lia | intros E; left; exact (Hak2 E) | lia | lia | exact Hp10 | lia | lia | lia | lia | exact HL | exact CONT]. }
zs. brf K2.
-
eapply (G0FC true). symmetry. apply Z.ltb_lt. lia.
-
zs. zs. rewrite land2047, (Z.mod_small (a + 1) 2048) by lia. zs.
eapply (G0FC false). symmetry. apply Z.ltb_ge. lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO T1 SPF SPF2 SPT SG1 HS_U1A8"] Lemma L_T : S_T.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO T1 SPF SPF2 SPT SG1 HS_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 BYT Hp Hnul Hnum HP30 T0 SEP SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_tz in HK. destruct (df_tz_loop FUEL_RING x kz) as [z|] eqn:HTZ; [|discriminate HK]. unfold FUEL_RING in HTZ.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
rewrite lor_shl32 by lia. replace (Z.shiftl kz 2 + XA + -4)%Z with (XA + 4 * (kz - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (Z_to_bv 64 0) with (Z_to_bv 64 (kz - kz)) by (f_equal; lia).
eapply (L_TZL 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz kz z);
[exact DI0 | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HTZ | ].
intros x15' Rz Hnz. clear HTZ.
unfold dfK_al in HK. unfold nz in HK.

zs. fixw3. fixw. replace (kz - (kz - z + 1))%Z with (z - 1)%Z by lia.
zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite magic_q9 by lia. rewrite rem9_fix by lia.
pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as Rrem.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; intros; apply Z.rem_nonpos; lia).
set (r9 := Z.rem rp 9) in *. assert (Rr9 : (-8 <= r9 <= 8)%Z) by (clear - Rrem w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; lia). clearbody r9. clear Rrem.
zs. fixw3. fixw. replace (z - 1 + 1)%Z with z by lia.

assert (G178 : forall m' ws' x' (a' rp' z' rpm9 : Z) (x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' x' (inring 0 z') -> X31 x' -> (0 <= a' < z')%Z -> (1 <= z' <= 2047)%Z -> (-2^15 - 9 * 2047 <= rp' <= 2^15 /\ 9 * a' + rp' <= 537)%Z -> (1 <= rpm9 <= 8)%Z ->
dfK_up 53 (-1074) sign fR (rp' + (9 - rpm9)) a' z' 0 x' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 x10' (Z_to_bv 64 rpm9) x12' x13' x14' x15'' x16' x17'
(Z_to_bv 64 z') (Z_to_bv 64 a') x20 x21 x22 (Z_to_bv 64 rp') (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd14)) fct None m' (seg_rom segs))).
{ intros m' ws' x' a' rp' z' rpm9 x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' DI2 XR2 X312 Ra' Rz' Rrp' Rrpm9 HK2.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HK. pose proof DI2 as DI'. dest_dfinv DI'.
zs. fixw3. fixw. zs. replace (rp' - rpm9 + 9)%Z with (rp' + (9 - rpm9))%Z by lia.
eapply L_UPI; [exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | exact XR2 | exact X312 | lia | lia | lia | exact HK2]. }
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (E0 : r9 = 0%Z) by (clear - K1 Rr9 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; mlia).
rewrite E0, Z.eqb_refl in HK. cbv beta iota in HK.
zs. zs.
eapply L_UPI; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | lia | lia | exact HK].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
-
assert (Hne0 : r9 <> 0%Z) by (clear - K1 Rr9 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_792 hi_843 lo_796 lo_845 G_107c0 G_116a8 CODE D_792 E_792 D_796 E_796 D_843 E_843 D_845 E_845 ANCH_796 ANCH_845 RNG_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard RNG_G_116a8 ROM_G_116a8 RNG_G_107c0 ROM_G_107c0 LAY_got_ssp_RERRNO; mlia).
replace (r9 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0). cbv beta iota in HK.

assert (G0B4 : forall rpm9 (x14' : word), rpm9 = (if 0 <=? rp then r9 else r9 + 9)%Z -> (1 <= rpm9 <= 8)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) x14' x15' x16 x17
(Z_to_bv 64 z) x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc50)) fct None m (seg_rom segs))).
{ intros rpm9 x14' Hrpm9 Rrpm9. rewrite <- Hrpm9 in HK.
set (j10 := (8 - rpm9)%Z) in *.

assert (G0E4 : forall (x16' : word),
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (z - 1 + 1)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (znth p10s j10)) x16' (Z_to_bv 64 1000001536)
(Z_to_bv 64 z) (Z_to_bv 64 0) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc80)) fct None m (seg_rom segs))).
{ intros x16'.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10].
destruct (df_al_loop FUEL_RING _ z _) as [[k1 a1 rp1 c1 x1']|] eqn:HAL; [|discriminate HK]. unfold FUEL_RING in HAL.
zs. zs. zs. rewrite zext32_small by lia. zs. rewrite divw_small by lia. zs. zs.
replace (Z_to_bv 64 (z - 1 + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
replace (Z_to_bv 64 XA) with (Z_to_bv 64 (XA + 4 * 0))%Z by (f_equal; lia).
eapply (L_ALK 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x 0%Z 0%Z 0%Z rp z (znth p10s j10) j10 rpm9 kz rp (mkAL k1 a1 rp1 c1 x1'));
[exact DI0 | exact FOK | exact FRM' | | exact X31H | lia | lia | lia | intros _; right; split; [reflexivity | exact Hx0] | lia | lia | reflexivity | lia | lia | lia | lia | exact HAL | ].
{ eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia. }
intros m' ws' x6' x7' x28' DI2 XR2 X312 Hk1 Ra1 Hac1 Rc1 Rrp1. cbn [al_x al_k al_a al_carry al_rp] in DI2, XR2, X312, Hk1, Ra1, Hac1, Rc1, Rrp1 |- *. subst k1.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HAL LW' LX REL X31H.
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
unfold nz in HK.
zs. brf K4.
+
replace (negb (c1 =? 0)) with false in HK by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia). cbv beta iota in HK.
eapply (G178 m' ws' x1' a1 rp1 z rpm9); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | lia | lia | lia | lia | exact HK].
+
replace (negb (c1 =? 0)) with true in HK by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbv beta iota in HK.
zs. fixw3. fixw. replace (z - 1 + 2)%Z with (z + 1)%Z by lia.
zs. try rewrite signed_of_Z by lia. rewrite shr30_4z by lia. zs. zs.
pose proof (u32arr_store_ok segs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ z (Z_to_bv 64 c1) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
eapply (G178 _ (upd ws' (Z.to_nat z) (Z_to_bv 64 c1)) (zupd x1' z c1) a1 rp1 (z + 1)%Z rpm9); [mk_dfinv | | | lia | lia | lia | lia | exact HK].
* split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros q0 Hq Hr. destruct (Z.eq_dec q0 z) as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
-- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL2; [lia|].
unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
* intros q0. destruct (Z.eq_dec q0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X312]. }

zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
assert (Hc : (rpm9 = 1 \/ rpm9 = 2 \/ rpm9 = 3 \/ rpm9 = 4 \/ rpm9 = 5 \/ rpm9 = 6 \/ rpm9 = 7 \/ rpm9 = 8)%Z) by lia.
clear HK Hrpm9. subst j10.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rpm9; (zs; eapply G0E4). }

zs. try rewrite (signed_of_Z rp) by lia.
destruct (Z.lt_ge_cases rp 0) as [Hneg|Hpos].
+ rewrite (shr63_neg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
+ rewrite (shr63_nonneg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with true by (symmetry; apply Z.leb_le; lia). lia.
Qed.

End Floatscan.

End G.
End Mq5.

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
Variables (hi_1363 : bv 20).
Variables (lo_1364 : bv 12).
Variables (joff_1329 joff_1332 joff_1341 joff_1345 joff_1349 joff_1354 joff_1365 joff_1370 joff_1382 joff_1391 joff_1419 : bv 21).
Variables (G_10788 got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1329 : decode_any (Z_to_bv 32 w_1329) = Some (Jal 1 joff_1329, 4%Z).
Hypothesis E_1329 : is_ecall (Z_to_bv 32 w_1329) = false.
Hypothesis D_1332 : decode_any (Z_to_bv 32 w_1332) = Some (Jal 1 joff_1332, 4%Z).
Hypothesis E_1332 : is_ecall (Z_to_bv 32 w_1332) = false.
Hypothesis D_1341 : decode_any (Z_to_bv 32 w_1341) = Some (Jal 1 joff_1341, 4%Z).
Hypothesis E_1341 : is_ecall (Z_to_bv 32 w_1341) = false.
Hypothesis D_1345 : decode_any (Z_to_bv 32 w_1345) = Some (Jal 1 joff_1345, 4%Z).
Hypothesis E_1345 : is_ecall (Z_to_bv 32 w_1345) = false.
Hypothesis D_1349 : decode_any (Z_to_bv 32 w_1349) = Some (Jal 1 joff_1349, 4%Z).
Hypothesis E_1349 : is_ecall (Z_to_bv 32 w_1349) = false.
Hypothesis D_1354 : decode_any (Z_to_bv 32 w_1354) = Some (Jal 1 joff_1354, 4%Z).
Hypothesis E_1354 : is_ecall (Z_to_bv 32 w_1354) = false.
Hypothesis D_1363 : decode_any (Z_to_bv 32 w_1363) = Some (Auipc 10 hi_1363, 4%Z).
Hypothesis E_1363 : is_ecall (Z_to_bv 32 w_1363) = false.
Hypothesis D_1364 : decode_any (Z_to_bv 32 w_1364) = Some (FLoad FMT_D 10 10 lo_1364, 4%Z).
Hypothesis E_1364 : is_ecall (Z_to_bv 32 w_1364) = false.
Hypothesis D_1365 : decode_any (Z_to_bv 32 w_1365) = Some (Jal 1 joff_1365, 4%Z).
Hypothesis E_1365 : is_ecall (Z_to_bv 32 w_1365) = false.
Hypothesis D_1370 : decode_any (Z_to_bv 32 w_1370) = Some (Jal 1 joff_1370, 4%Z).
Hypothesis E_1370 : is_ecall (Z_to_bv 32 w_1370) = false.
Hypothesis D_1382 : decode_any (Z_to_bv 32 w_1382) = Some (Jal 1 joff_1382, 4%Z).
Hypothesis E_1382 : is_ecall (Z_to_bv 32 w_1382) = false.
Hypothesis D_1391 : decode_any (Z_to_bv 32 w_1391) = Some (Jal 1 joff_1391, 4%Z).
Hypothesis E_1391 : is_ecall (Z_to_bv 32 w_1391) = false.
Hypothesis D_1419 : decode_any (Z_to_bv 32 w_1419) = Some (Jal 0 joff_1419, 4%Z).
Hypothesis E_1419 : is_ecall (Z_to_bv 32 w_1419) = false.
Hypothesis ANCH_1364 : gw_anch (Z.shiftl (bv_signed hi_1363) 12 + (base + 5452) + bv_signed lo_1364)%Z G_10788.
Hypothesis LINK_1329 : gw_anch (base + 5316 + bv_signed joff_1329)%Z (e_addtf3 + 0)%Z.
Hypothesis LINK_1332 : gw_anch (base + 5328 + bv_signed joff_1332)%Z (e_subtf3 + 0)%Z.
Hypothesis LINK_1341 : gw_anch (base + 5364 + bv_signed joff_1341)%Z (e_extendsftf2 + 1120)%Z.
Hypothesis LINK_1345 : gw_anch (base + 5380 + bv_signed joff_1345)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1349 : gw_anch (base + 5396 + bv_signed joff_1349)%Z (e_divtf3 + 0)%Z.
Hypothesis LINK_1354 : gw_anch (base + 5416 + bv_signed joff_1354)%Z (e_getf2 + 0)%Z.
Hypothesis LINK_1365 : gw_anch (base + 5460 + bv_signed joff_1365)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_1370 : gw_anch (base + 5480 + bv_signed joff_1370)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1382 : gw_anch (base + 5528 + bv_signed joff_1382)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_1391 : gw_anch (base + 5564 + bv_signed joff_1391)%Z (e_letf2 + 0)%Z.
Hypothesis LINK_1419 : gw_anch (base + 5676 + bv_signed joff_1419)%Z (e_extendsftf2 + 1132)%Z.
Hypothesis CODE_e_errno_loc : code_at segs e_errno_loc errno_loc_code.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
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
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_27))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_28))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_29))).
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
Definition S_F3 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_F3 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_F3 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_F3 segs base got_ssp RATP STRING_READ ssp_guard) S_F3 gw_tbl_38).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis divtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQRC.divtf3_spec segs e_divtf3) 9%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).
Hypothesis getf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq1.getf2_spec segs e_getf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).  Arguments getf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis fabsl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.fabsl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).  Arguments fabsl_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis scalbnl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.scalbnl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).
Definition extenddftf2_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.extenddftf2_callv) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.extenddftf2_callv)).

Ltac show_goal := match goal with |- ?g => idtac g end.
Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
Ltac fixw2 := rewrite ?swrap32_landW, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.

Definition errno_loc_spec : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.errno_loc_spec) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.errno_loc_spec)).
Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition div_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.div_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.div_callE)).
Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition sub_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.sub_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.sub_callE)).
Definition letf2_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.letf2_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.letf2_callE)).
Definition getf2_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.getf2_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.getf2_callE)).
Definition fabsl_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.fabsl_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.fabsl_callE)).
Definition L_SCL : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.L_SCL) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.L_SCL)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Notation F_floatscan_common__L_SCL := L_SCL (only parsing).
Notation F_floatscan_common__S_F3 := S_F3 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="G_10788 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1329 E_1329 D_1332 E_1332 D_1341 E_1341 D_1345 E_1345 D_1349 E_1349 D_1354 E_1354 D_1363 E_1363 D_1364 E_1364 D_1365 E_1365 D_1370 E_1370 D_1382 E_1382 D_1391 E_1391 D_1419 E_1419 ANCH_1364 LINK_1329 LINK_1332 LINK_1341 LINK_1345 LINK_1349 LINK_1354 LINK_1365 LINK_1370 LINK_1382 LINK_1391 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec divtf3_spec getf2_spec fabsl_spec scalbnl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1363 lo_1364 joff_1329 joff_1332 joff_1341 joff_1345 joff_1349 joff_1354 joff_1365 joff_1370 joff_1382 joff_1391 joff_1419 G_10788 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1329 E_1329 D_1332 E_1332 D_1341 E_1341 D_1345 E_1345 D_1349 E_1349 D_1354 E_1354 D_1363 E_1363 D_1364 E_1364 D_1365 E_1365 D_1370 E_1370 D_1382 E_1382 D_1391 E_1391 D_1419 E_1419 ANCH_1364 LINK_1329 LINK_1332 LINK_1341 LINK_1345 LINK_1349 LINK_1354 LINK_1365 LINK_1370 LINK_1382 LINK_1391 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec divtf3_spec getf2_spec fabsl_spec scalbnl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation L_SCL := (@F_floatscan_common__L_SCL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPLO SPF SPT SG1 SG3 Q1).
Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_F3 := (@F_floatscan_common__S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Ltac b2z_01 := rewrite ?b2z_land; lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.

Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

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

#[using="Type"] Lemma land31_eq : forall v, Z.land (u32 v) INT_MAX_ = Z.land (Z.land v 18446744073709551615) 2147483647.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros v. unfold u32, INT_MAX_. change (2^32)%Z with (2^32)%Z. rewrite <- (Z.land_ones v 32) by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1382 joff_1419 e_errno_loc e_extendsftf2 CODE BASE4 BASER D_1382 E_1382 D_1419 E_1419 LINK_1382 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_E9FC : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y e2 : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1598)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1382 joff_1419 e_errno_loc e_extendsftf2 CODE BASE4 BASER D_1382 E_1382 D_1419 E_1419 LINK_1382 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros until e2. intros DI RJ Hk FOK FRM' He2 Hy.
dest_dfinv DI. gw_expose ssp_guard.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1382 joff_1391 joff_1419 e_errno_loc e_letf2 e_extendsftf2 CODE BASE4 BASER D_1382 E_1382 D_1391 E_1391 D_1419 E_1419 LINK_1382 LINK_1391 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec letf2_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F9F0 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR e2 dn : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^25 <= e2 < 2^25)%Z -> (0 <= dn <= 1)%Z ->
yR = m_scalbnl Y e2 ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 dn) (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 FR)) x23 x24 x25 x26 (Z_to_bv 64 (hi64 FR)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x158c)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1382 joff_1391 joff_1419 e_errno_loc e_letf2 e_extendsftf2 CODE BASE4 BASER D_1382 E_1382 D_1391 E_1391 D_1419 E_1419 LINK_1382 LINK_1391 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO scalbnl_spec letf2_spec fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros until dn. intros DI RJ Hk FOK FRM' He2 Hdn Hy.
pose proof DI as DI0. dest_dfinv DI. gw_expose ssp_guard.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR).
zs. fixw2. zs. zs. brs K3.
-  zs. brf K4.
+ eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
+ zs. zs. zs. zs. zs. callx (eapply letf2_callE with (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range FR 0) as RLE.
zs. brf K5.
* eapply L_E9FC; try eassumption; try lia; try mk_dfinv.
* eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
- eapply L_E9FC; try eassumption; try lia; try exact DI0.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1363 lo_1364 joff_1329 joff_1332 joff_1341 joff_1345 joff_1349 joff_1354 joff_1365 joff_1370 joff_1382 joff_1391 joff_1419 G_10788 e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1329 E_1329 D_1332 E_1332 D_1341 E_1341 D_1345 E_1345 D_1349 E_1349 D_1354 E_1354 D_1363 E_1363 D_1364 E_1364 D_1365 E_1365 D_1370 E_1370 D_1382 E_1382 D_1391 E_1391 D_1419 E_1419 ANCH_1364 LINK_1329 LINK_1332 LINK_1341 LINK_1345 LINK_1349 LINK_1354 LINK_1365 LINK_1370 LINK_1382 LINK_1391 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec divtf3_spec getf2_spec fabsl_spec scalbnl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F3 : S_F3.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_1363 lo_1364 joff_1329 joff_1332 joff_1341 joff_1345 joff_1349 joff_1354 joff_1365 joff_1370 joff_1382 joff_1391 joff_1419 G_10788 e_errno_loc e_extenddftf2 e_letf2 e_getf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1329 E_1329 D_1332 E_1332 D_1341 E_1341 D_1345 E_1345 D_1349 E_1349 D_1354 E_1354 D_1363 E_1363 D_1364 E_1364 D_1365 E_1365 D_1370 E_1370 D_1382 E_1382 D_1391 E_1391 D_1419 E_1419 ANCH_1364 LINK_1329 LINK_1332 LINK_1341 LINK_1345 LINK_1349 LINK_1354 LINK_1365 LINK_1370 LINK_1382 LINK_1391 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard RNG_G_10788 ROM_G_10788 LAY_got_ssp_RERRNO floatsitf_spec extenddftf2_spec divtf3_spec getf2_spec fabsl_spec scalbnl_spec letf2_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m. intros until bits'. intros _ DI RJ Hk FOK FRM' Hsg He2 Hb HK.
dest_dfinv DI. unfold FS_DEPTH in SPLO. gw_expose ssp_guard.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
unfold fin_K3 in HK. rewrite land31_eq in HK. change (1024 - 5)%Z with 1019%Z in HK. change LDBL_MANT_DIG_ with 113%Z in HK.
pose proof (land_mask_range (Z.land (e2 + 113) 18446744073709551615) 2147483647 ltac:(lia)) as R31.

zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE; [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
rename PC into FRM1.
set (Y1 := f128_add Y FR) in *. pose proof (lo64_range Y1). pose proof (hi64_range Y1).

zs. zs. zs.
call_split 48%Z (eapply sub_callE; [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
rename PC into FRM2.
set (Y2 := f128_sub Y1 BI) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs. zs. zs. zs. brs K.
-
replace (1019 <? Z.land (Z.land (e2 + 113) 18446744073709551615) 2147483647)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
injection HK as HK'.
zs. zs.
eapply L_SCL; try eassumption; try lia; try (symmetry; exact HK'); try mk_finv; try mk_framL.
- replace (1019 <? Z.land (Z.land (e2 + 113) 18446744073709551615) 2147483647)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).

zs. zs. zs. callx (eapply fabsl_callE; [eassumption | reflexivity | reflexivity]).
set (AY := m_fabsl Y2) in *. pose proof (lo64_range AY). pose proof (hi64_range AY).
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
pose proof (lo64_range (f128_of_i32 2)). pose proof (hi64_range (f128_of_i32 2)).
zs. zs. zs. zs.
call_split 112%Z (eapply div_callE with (Y := C_LDBL_EPS); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (LIM := f128_div (f128_of_i32 2) C_LDBL_EPS) in *. pose proof (lo64_range LIM). pose proof (hi64_range LIM).
zs. zs. zs. zs. zs. callx (eapply getf2_callE; [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_ge_range AY LIM) as RGE.
zs. zs. brs K2.
+
replace (0 <=? f128_ge AY LIM)%Z with false in HK by (symmetry; apply Z.leb_gt; lia). injection HK as HK'.
zs. zs.
let v := getreg 8%Z in lazymatch v with Z_to_bv 64 ?dv =>
eapply L_F9F0 with (dn := dv); try eassumption; try lia; try (symmetry; exact HK'); try mk_dfinv end.
all: try (lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end).
+
replace (0 <=? f128_ge AY LIM)%Z with true in HK by (symmetry; apply Z.leb_le; lia). injection HK as HK'.
zs. zs. zs. zs. zs. zs. zs. zs.
zs. callx (eapply extenddftf2_callv with (D := 0x3FE0000000000000%Z); [eassumption | lia]).
zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (Y := f128_of_d 0x3FE0000000000000); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs. zs. fixw2. zs.
let v := getreg 8%Z in lazymatch v with Z_to_bv 64 ?dv =>
eapply L_F9F0 with (dn := dv); try eassumption; try lia; try (symmetry; exact HK'); try mk_dfinv end.
all: try fok; try b2z_01. all: show_goal.
Qed.

End Floatscan.

End G.
