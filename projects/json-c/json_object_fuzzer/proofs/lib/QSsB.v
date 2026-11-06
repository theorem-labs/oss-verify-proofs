(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Qx2n Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx QhAd QVbl QQLG QQRC Q91D QCa8 QkTt Qy8Z Q8l1 QROt QZxv Q5m9 QXfH QzQg Q6Iq Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwFold.
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

Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_0)))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_1)))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_2)))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_3)))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_4)).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_5)).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_6)).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_7)).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_8)).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_9)).
Definition FLOATSCAN := (base + 0)%Z.
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.FLOATSCAN base) FLOATSCAN gw_tbl_10).
Definition SWSn : ltac:(gw_rebind_ty (@Q6Iq.Mq3.SWSn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.SWSn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@Q6Iq.Mq3.SWSn segs base got_ssp RATP STRING_READ ssp_guard) SWSn gw_tbl_11).
Definition S_WS : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_WS segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_WS segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@Q6Iq.Mq3.S_WS segs base got_ssp RATP STRING_READ ssp_guard) S_WS gw_tbl_12).
Definition S_AWS : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_AWS segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_AWS segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@Q6Iq.Mq3.S_AWS segs base got_ssp RATP STRING_READ ssp_guard) S_AWS gw_tbl_13).
Definition S_I1 : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_I1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_I1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@Q6Iq.Mq3.S_I1 segs base got_ssp RATP STRING_READ ssp_guard) S_I1 gw_tbl_14).
Definition S_N1 : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_N1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_N1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@Q6Iq.Mq3.S_N1 segs base got_ssp RATP STRING_READ ssp_guard) S_N1 gw_tbl_15).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
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

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb8_c8_in) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb8_c8_in)).
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
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsH0__S_AWS := S_AWS (only parsing).
Notation F_fsH0__S_I1 := S_I1 (only parsing).
Notation F_fsH0__S_N1 := S_N1 (only parsing).
Notation F_fsH0__S_WS := S_WS (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
Ltac mk_winv2 := norm_m1074; unfold F_floatscan_common__winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
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
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| [CB 8 _] => fail
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l' end in
lazymatch cs with ?c0 :: ?l => go constr:([c0]) l end end.

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

Local Notation S_WS := (@F_fsH0__S_WS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_AWS := (@F_fsH0__S_AWS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_I1 := (@F_fsH0__S_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N1 := (@F_fsH0__S_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).

Hypothesis HS_I1 : S_I1.
Hypothesis HS_N1 : S_N1.

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1"] Lemma L_AWS : S_AWS.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ WI RJ Hk Hst Hr1 Rcb Hns HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold FS_sign in HK.

assert (GOI : forall m2 (x8' x10' x11' x12' : word) sg c2 (f2 : shfile) k2,
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f2 -> RFJ' k2 c2 f2 -> (1 <= k2)%Z -> sh_stdio f2 = sh_stdio f0 ->
(sg = 1 \/ sg = -1)%Z -> (0 <= c2 < 256)%Z -> (c2 <> (-1)%Z -> 1 <= sh_rpos f2)%Z ->
FS_infk' sg 0 c2 f2 = Some (fR, yR) ->
forall K : Prop, ((Z.land c2 18446744073709551583 = 73%Z /\ K = (evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8' (Z_to_bv 64 sg) x10' x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x134)) fc None m2 (seg_rom segs))))
\/ (Z.land c2 18446744073709551583 <> 73%Z /\ K = (evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8' (Z_to_bv 64 sg) (Z_to_bv 64 c2) (Z_to_bv 64 (Z.land c2 18446744073709551583)) x12' x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x16c)) fc None m2 (seg_rom segs))))) -> K).
{ intros m2 x8' x10' x11' x12' sg c2 f2 k2 WI2 RJ2 Hk2 Hst2 Hsg Rc2 Hr2 HK2 K [[E73 ->] | [N73 ->]].
- and33y E73 c2 Rc2 73%Z E1. rewrite FS_infk_step in HK2 by lia. change (znth str_infinity 0) with 105%Z in HK2.
rewrite E1, Z.eqb_refl in HK2. change (0 <? 7)%Z with true in HK2. cbv iota in HK2.
stmt HS_I1. eapply NX; try eassumption; try flia.
- and33n N73 c2 Rc2 73%Z N1. rewrite FS_infk_step in HK2 by lia. change (znth str_infinity 0) with 105%Z in HK2.
replace (Z.lor c2 32 =? 105)%Z with false in HK2 by (symmetry; apply Z.eqb_neq; exact N1). rewrite FS_inf_0 in HK2.
stmt HS_N1. eapply NX; try eassumption; try flia. }
assert (SGN : forall x11', (c = 43%Z \/ c = 45%Z) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 32) (Z_to_bv 64 c) x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x100)) fc None m (seg_rom segs))).
{ intros x11' Hc.
assert (Hc0 : c <> 0%Z) by lia.
replace ((c =? 43) || (c =? 45))%Z with true in HK by (destruct Hc as [-> | ->]; reflexivity).
set (sg := (1 - 2 * b2z (c =? 45))%Z) in HK. assert (Hsg : (sg = 1 \/ sg = -1)%Z) by (subst sg; destruct (c =? 45)%Z; cbn; lia).
rewrite (surjective_pairing (sh_getc f)) in HK. cbv beta iota zeta in HK.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 sg) by (subst sg; destruct Hc as [-> | ->]; apply Z_to_bv_eqm; reflexivity).
zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf Kc.
+ eapply (GOI _ x8 (Z_to_bv 64 c'') (Z_to_bv 64 (Z.land c'' 18446744073709551583)) (Z_to_bv 64 73) sg c'' (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) (kmin + 1)%Z);
only 9: (right; split; [clear - Kc Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rch) in Kc; exact Kc | reflexivity]);
[mk_winv2 | exact RJ1 | flia | exact Hst1 | exact Hsg | exact Rch | cbn [sh_rpos]; intros _; flia | exact HK].
+ eapply (GOI _ x8 (Z_to_bv 64 c'') (Z_to_bv 64 (Z.land c'' 18446744073709551583)) (Z_to_bv 64 73) sg c'' (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) (kmin + 1)%Z);
only 9: (left; split; [clear - Kc Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rch) in Kc; exact Kc | reflexivity]);
[mk_winv2 | exact RJ1 | flia | exact Hst1 | exact Hsg | exact Rch | cbn [sh_rpos]; intros _; flia | exact HK]. }
zs. zs. brf Ka.
-
assert (E45 : c = 45%Z) by (clear - Ka Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
apply SGN. right. exact E45.
- assert (N45 : c <> 45%Z) by (clear - Ka Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
zs. zs. brf Kb.
+
assert (N43 : c <> 43%Z) by (clear - Kb Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
replace ((c =? 43) || (c =? 45))%Z with false in HK by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N43), (proj2 (Z.eqb_neq _ _) N45); reflexivity).
zs. zs. zs. zs. brf Kc.
* eapply (GOI m x8 (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) (Z_to_bv 64 73) 1%Z c f kmin);
only 9: (left; split; [clear - Kc Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rcb) in Kc; exact Kc | reflexivity]); try eassumption; try flia.
* eapply (GOI m x8 (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) (Z_to_bv 64 73) 1%Z c f kmin);
only 9: (right; split; [clear - Kc Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rcb) in Kc; exact Kc | reflexivity]); try eassumption; try flia.
+ assert (E43 : c = 43%Z) by (clear - Kb Rcb w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
apply SGN. left. exact E43.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1"] Lemma L_WS : S_WS.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ WI RJ Hk Hc0 Hst HL HK; [discriminate HL|].
pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite fs_ws_loop_S in HL.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *. cbv beta iota zeta in HL.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isspace_iff c'' Rch) as SPI.
assert (LOOP : forall m2 (x10' x11' : word), m_isspace c'' = true ->
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 5) (Z_to_bv 64 32) x10' x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xcc)) fc None m2 (seg_rom segs))).
{ intros m2 x10' x11' SP WI2. rewrite SP in HL.
assert (Hc1 : c'' <> 0%Z) by (intros E0; rewrite E0 in SP; discriminate SP).
eapply (IH m2); try eassumption; try flia. }
zs. zs. brf K1.
-
eapply LOOP; [| mk_winv2]. apply (proj2 SPI). right. clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc. rewrite ?land_W64 in K1. Z.div_mod_to_equations; lia.
- zs. brf K2.
+
eapply LOOP; [| mk_winv2]. apply (proj2 SPI). left. clear - K2 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia.
+
assert (NSP : m_isspace c'' = false).
{ destruct (m_isspace c''); [|reflexivity]. exfalso. pose proof (proj1 SPI eq_refl) as SPD. clear - K1 K2 Rch SPD w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc. rewrite ?land_W64 in K1. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia. }
rewrite NSP in HL. injection HL as <- <-.
stmt L_AWS. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia. mk_winv2. cbn [sh_rpos]. intros _. flia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_I1 HS_N1"] Lemma L_ENTRYh : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev : word),
let _ := ctx_all in
floatscan_h fuelc f0 1 pok = Some (fR, yR) ->
stk segs m0 (q - FS_DEPTH) q -> mem_inv segs m0 ->
rw_cells segs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (0 <= kmin0)%Z -> c0 <> 0%Z -> sh_stdio f0 = sh_stdio f0 ->
bytes_at segs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells segs m0 RERRNO [C4 ev] ->
evt segs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 1) (Z_to_bv 64 pok) a3 a4 a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (Z_to_bv 64 FLOATSCAN) fc None m0 (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_I1 HS_N1 segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 SE_T SG2 SG3 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; try gw_hide SE_T; try gw_hide SG2; try gw_hide SG3; first [clear FRM | gw_hide FRM | idtac].
intros until ev. intros _ HMh ST MI FC RJ Hk0 Hc0 Hst BY [SSP1 SSP2] ERR.
pose proof (munch_refl Wfs m0) as MU. pose proof (wmono_refl segs m0) as WM. unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU. unfold FS_DEPTH in ST.
gw_expose got_ssp; gw_expose ssp_guard. unfold RERRNO in ERR.
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T.
pose proof zbytes_len as LTX. unfold zlength in *. bury_disj.
site_facts FC RJ kmin0 c0 f0.

pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0) as RJ1.
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

rewrite floatscan_h_1 in HMh. destruct (fs_ws_loop fuelc f0) as [[c1 f1]|] eqn:HWS; [|discriminate HMh].
eapply (L_WS fuelc) with (kmin := kmin0) (c := c0) (f := f0); try eassumption; try flia.
mk_winv2.
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
Variables (joff_676 joff_683 joff_690 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_errno_loc e_197bc e_multf3 e_floatsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_676 : decode_any (Z_to_bv 32 w_676) = Some (Jal 1 joff_676, 4%Z).
Hypothesis E_676 : is_ecall (Z_to_bv 32 w_676) = false.
Hypothesis D_683 : decode_any (Z_to_bv 32 w_683) = Some (Jal 1 joff_683, 4%Z).
Hypothesis E_683 : is_ecall (Z_to_bv 32 w_683) = false.
Hypothesis D_690 : decode_any (Z_to_bv 32 w_690) = Some (Jal 1 joff_690, 4%Z).
Hypothesis E_690 : is_ecall (Z_to_bv 32 w_690) = false.
Hypothesis LINK_676 : gw_anch (base + 2704 + bv_signed joff_676)%Z (e_extendsftf2 + 0)%Z.
Hypothesis LINK_683 : gw_anch (base + 2732 + bv_signed joff_683)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_690 : gw_anch (base + 2760 + bv_signed joff_690)%Z (e_floatsitf + 0)%Z.
Hypothesis CODE_e_errno_loc : code_at segs e_errno_loc errno_loc_code.
Hypothesis CODE_e_extendsftf2 : code_at segs e_extendsftf2 extendsftf2_code.
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
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_3)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_4)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_5)))).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_6)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_7)))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_8)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_9)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_10)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_11)))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_12)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_13)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_14)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_15)))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_16)))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_17)))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_18)))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_19)).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_20)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_21)))))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_22)).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_23)).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_24)).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_25)).
Definition ERRNO_LOC : ltac:(gw_rebind_ty (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.ERRNO_LOC e_errno_loc) ERRNO_LOC gw_tbl_26).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_27)))).
Definition S_I1 : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_I1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_I1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@Q6Iq.Mq3.S_I1 segs base got_ssp RATP STRING_READ ssp_guard) S_I1 gw_tbl_28).
Definition S_ERR : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_ERR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_ERR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@Q6Iq.Mq3.S_ERR segs base got_ssp RATP STRING_READ ssp_guard) S_ERR gw_tbl_29).
Definition S_A38 : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_A38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_A38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@Q6Iq.Mq3.S_A38 segs base got_ssp RATP STRING_READ ssp_guard) S_A38 gw_tbl_30).

Hypothesis shlim_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq3.gw_all) (@QQRC.Mq3.shlim_spec) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).

Hypothesis RFI_ok : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_ok) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_ok _%_Z_scope _%_list_scope _%_Z_scope _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
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

Definition errno_loc_spec : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.errno_loc_spec) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.errno_loc_spec)).
Definition L_RET30 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.L_RET30) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.L_RET30)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Notation F_floatscan_common__L_RET30 := L_RET30 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsH0__S_A38 := S_A38 (only parsing).
Notation F_fsH0__S_ERR := S_ERR (only parsing).
Notation F_fsH0__S_I1 := S_I1 (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_multf3 e_floatsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_676 E_676 D_683 E_683 D_690 E_690 LINK_676 LINK_683 LINK_690 CODE_e_errno_loc CODE_e_extendsftf2 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 joff_683 joff_690 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_multf3 e_floatsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_676 E_676 D_683 E_683 D_690 E_690 LINK_676 LINK_683 LINK_690 CODE_e_errno_loc CODE_e_extendsftf2 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec.

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

Local Notation Fok := (@QzQg.Mq0.Fok F).
Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Local Notation L_RET30 := (@F_floatscan_common__L_RET30 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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

Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
Ltac mk_winv2 := norm_m1074; unfold F_floatscan_common__winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
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

Local Notation S_I1 := (@F_fsH0__S_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_ERR := (@F_fsH0__S_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A38 := (@F_fsH0__S_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO Hp SE_T SPF SPT SG1 SG3"] Lemma L_A38 : S_A38.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO Hp SE_T SPF SPT SG1 SG3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until v. intros _ WI RJ Hk FOK FRM' SP E10. pose proof WI as WI0. dest_winv WI. bury_disj.
zs.
zs. match goal with |- context [reg_get Ft ?i] => rewrite (E10 i) by (vm_compute; reflexivity) end.
destruct SP as [[-> Hy] | [[-> Hy] | [-> Hy]]];
match goal with |- context [sx32 ?v] => let w := eval vm_compute in (bv_swrap 32 (bv_unsigned v)) in change (sx32 v) with (Z_to_bv 64 w) end;
(do 5 zs; (brf K1; [ exfalso; lia | ]); zs; zs; (brf K2; [ exfalso; lia | ]); do 11 zs);
(let a := getreg 10%Z in let b := getreg 11%Z in
lazymatch type of Hy with yR = ?r =>
replace a with (Z_to_bv 64 (lo64 r)) by reflexivity; replace b with (Z_to_bv 64 (hi64 r)) by reflexivity end);
eapply L_RET30; try eassumption; try lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO fc pre post pok fuelc f0 kmin0 c0 Hp SE_T SPF SPT SG1 SG3"] Lemma L_INFR : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c sign,
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> yR = sINF sign ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xa80)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO fc pre post pok fuelc f0 kmin0 c0 Hp SE_T SPF SPT SG1 SG3 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until sign. intros WI RJ Hk FOK FRM' Hsg Hy.
destruct Hsg as [-> | ->]; unfold sINF in Hy; cbn in Hy;
(zs; zs; zs; zs; stmt L_A38; eapply NX; try eassumption; try lia;
[ fok | | intros r Hr; apply freg_get_same; rewrite Hr; vm_compute; reflexivity]);
[left | right; left]; (split; [apply bv_eq; vm_compute; reflexivity | exact Hy]).
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_683 joff_690 e_errno_loc e_floatsitf CODE BASE4 BASER D_683 E_683 D_690 E_690 LINK_683 LINK_690 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq floatsitf_spec Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_ERR : S_ERR.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_683 joff_690 e_errno_loc e_floatsitf CODE BASE4 BASER D_683 E_683 D_690 E_690 LINK_683 LINK_690 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq floatsitf_spec Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul SPLO SG2 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hst HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
assert (L0 : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat).
{ destruct FC as [[Hwf _] _]. cbn in Hwf. tauto. }
destruct L0 as [L0 L1].
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq f Hsn) in RJu, HfR.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FC2 : rw_cells segs mm Fp (rf_cells T p true (mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) J))
by (unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite Hsn, Hns; unfold M64; hyp_cells) end.
rewrite rf_cells_raw_eq in FC2.
pose proof (gw_unhyp shlim_spec) as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (J := J);
[exact FC2 | exact (RFI_ok T txt p J _ _ _ RJu) | exact L0 | exact L1 | flia | flia | unfold zlength in *; flia | assumption]).
match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ _ (sh_lim0 _) _) |- _ => rename H into FC3 end. rewrite <- HfR in FC3.
zs. zs. callx (eapply floatsitf_callp; [eassumption | flia]).
rewrite <- Hy. eapply L_RET30; try eassumption; try flia; try mk_finv; try mk_framL.
all: try (rewrite HfR; eapply RFJ_lim0; exact RJu). all: try flia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_IEX : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (i s0v : Z),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i - 2 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(3 <= i <= 7)%Z -> (0 <= s0v < 256)%Z -> ((i = 3 /\ s0v <> 73) \/ (4 <= i /\ s0v = 73))%Z ->
fR = fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f) -> yR = sINF sign ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 s0v) (Z_to_bv 64 sign) (Z_to_bv 64 (- i)) x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xa50)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok f0 fR yR Hpok ST0 BYT Hnul SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros until s0v. intros WI RJ Hk Hst Hsg Ri Rs0 Hs0 HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
assert (RJR : RFJ' (kmin - 1 - (i - 3)) c fR).
{ rewrite HfR. replace (i - 3)%Z with (Z.of_nat (Z.to_nat (i - 3))) at 1 by lia. apply RFJ_ungetn; [| rewrite (rf_unget_eq f Hsn); exact Hsn | lia].
exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)). }
assert (Hsn2 : sh_shlim_neg (sh_unget f) = false) by (rewrite (rf_unget_eq f Hsn); exact Hsn).
rewrite (fs_unget_loop_eq (Z.to_nat (i - 3)) (sh_unget f) Hsn2) in HfR. rewrite (rf_unget_eq f Hsn) in HfR. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in HfR.
specialize (KM Hsn).
ufc FC. rewrite Hsn, Hns in FC. rewrite Hpok1.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. brf K3.
-
assert (Ei : i = 3%Z) by (clear - K3 Hs0 Rs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq segs base ssp_guard; rewrite ?land_W64 in K3; Z.div_mod_to_equations; lia).
subst i. change (Z.of_nat (Z.to_nat (3 - 3))) with 0%Z in HfR. replace (sh_rpos f - 1 - 0)%Z with (sh_rpos f - 1)%Z in HfR by lia.
eapply L_INFR; try eassumption; try flia.
+ unfold F_floatscan_common__winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
rewrite HfR. unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite Hns. unfold M64. hyp_cells.
+ apply Fok_refl.
- assert (Es : s0v = 73%Z) by (clear - K3 Hs0 Rs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq segs base ssp_guard; rewrite ?land_W64 in K3; Z.div_mod_to_equations; lia).
zs. zs. zs. zs0.
replace (Z.of_nat (Z.to_nat (i - 3))) with (i - 3)%Z in HfR by lia.
eapply L_INFR; try eassumption; try flia.
+ unfold F_floatscan_common__winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
rewrite HfR. unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite Hns. unfold M64. hyp_cells.
+ apply Fok_refl.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_IEX4 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (i : Z),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i - 2 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(4 <= i <= 7)%Z ->
fR = fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f) -> yR = sINF sign ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) (Z_to_bv 64 (- i)) x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xa4c)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok f0 fR yR Hpok ST0 BYT Hnul SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros until i. intros WI RJ Hk Hst Hsg Ri HfR Hy. pose proof WI as WI0. dest_winv WI.
rewrite Hpok1. zs. (brf K; [ exfalso; lia | ]). rewrite <- Hpok1.
eapply L_IEX; try eassumption; try lia.
Qed.

Ltac inf_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I7 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (4 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 7 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x9d0)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 7) with 121%Z in HK. change (7 <? 7)%Z with false in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
-
and33y K1 c'' Rch 89%Z E1. rewrite E1, Z.eqb_refl in HK. rewrite FS_infk_8, FS_inf_8 in HK. injection HK as EfR EyR.
eapply L_INFR; [rewrite <- EfR; mk_winv2 | rewrite <- EfR; exact RJ1 | flia | apply Fok_refl | exact FRM | exact Hsg | symmetry; exact EyR].
- and33n K1 c'' Rch 89%Z N1. replace (Z.lor c'' 32 =? 121)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. change (Z_to_bv 64 (-7)) with (Z_to_bv 64 (- 7)).
eapply L_IEX4 with (i := 7%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I6 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (3 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 6 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x854)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 6) with 116%Z in HK. change (6 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
- and33n K1 c'' Rch 84%Z N1. replace (Z.lor c'' 32 =? 116)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-6)) with (Z_to_bv 64 (- 6)).
eapply L_IEX4 with (i := 6%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 84%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I7; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I5 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (2 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 5 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x374)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 5) with 105%Z in HK. change (5 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
- and33n K1 c'' Rch 73%Z N1. replace (Z.lor c'' 32 =? 105)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-5)) with (Z_to_bv 64 (- 5)).
eapply L_IEX4 with (i := 5%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 73%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I6; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I4 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 4 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x350)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 4) with 110%Z in HK. change (4 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-4)) with (Z_to_bv 64 (- 4)).
eapply L_IEX4 with (i := 4%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I5; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I3 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 3 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x32c)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 e_extendsftf2 CODE BASE4 BASER D_676 E_676 LINK_676 CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 3) with 105%Z in HK. change (3 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 73%Z N1. replace (Z.lor c'' 32 =? 105)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_3 _ _ _ _ _ _ _ Hpok1) in HK. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-3)) with (Z_to_bv 64 (- 3)).
rewrite ?land_W64 in *. rewrite ?(Z.mod_small _ _ Rch) in *.
eapply L_IEX with (i := 3%Z) (s0v := Z.land c'' 18446744073709551583); try eassumption; try flia; try (symmetry; assumption);
try mk_winv2; try (apply and33_range; exact Rch); try (left; split; [reflexivity | exact K1]).
- and33y K1 c'' Rch 73%Z E1. rewrite E1, Z.eqb_refl in HK.
rewrite ?land_W64 in *. rewrite ?(Z.mod_small _ _ Rch) in *. rewrite K1.
eapply L_I4; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 joff_683 joff_690 e_errno_loc e_floatsitf e_extendsftf2 CODE BASE4 BASER D_676 E_676 D_683 E_683 D_690 E_690 LINK_676 LINK_683 LINK_690 CODE_e_errno_loc CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I2 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 2 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x26c)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 joff_683 joff_690 e_errno_loc e_floatsitf e_extendsftf2 CODE BASE4 BASER D_676 E_676 D_683 E_683 D_690 E_690 LINK_676 LINK_683 LINK_690 CODE_e_errno_loc CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 2) with 102%Z in HK. change (2 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 70%Z N1. replace (Z.lor c'' 32 =? 102)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_inf_err in HK by lia. injection HK as EfR EyR.
stmt L_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 70%Z E1. rewrite E1, Z.eqb_refl in HK.
zs.
eapply L_I3; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 joff_683 joff_690 e_errno_loc e_floatsitf e_extendsftf2 CODE BASE4 BASER D_676 E_676 D_683 E_683 D_690 E_690 LINK_676 LINK_683 LINK_690 CODE_e_errno_loc CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I1 : S_I1.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_676 joff_683 joff_690 e_errno_loc e_floatsitf e_extendsftf2 CODE BASE4 BASER D_676 E_676 D_683 E_683 D_690 E_690 LINK_676 LINK_683 LINK_690 CODE_e_errno_loc CODE_e_extendsftf2 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq floatsitf_spec Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 SPLO SG2 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros _ WI RJ Hk Hst Hsg Hci HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in Hci; discriminate Hci).
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 1) with 110%Z in HK. change (1 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I2; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_inf_err in HK by lia. injection HK as EfR EyR.
zs.
stmt L_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
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

Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_0)))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_1)))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_2)))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_3)).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_4)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_5)))))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_6)).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_7)).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_8)).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_9)).
Definition S_N1 : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_N1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_N1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@Q6Iq.Mq3.S_N1 segs base got_ssp RATP STRING_READ ssp_guard) S_N1 gw_tbl_10).
Definition S_Z : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_Z segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_Z segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@Q6Iq.Mq3.S_Z segs base got_ssp RATP STRING_READ ssp_guard) S_Z gw_tbl_11).
Definition S_ERR : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_ERR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_ERR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@Q6Iq.Mq3.S_ERR segs base got_ssp RATP STRING_READ ssp_guard) S_ERR gw_tbl_12).
Definition S_A38 : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_A38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_A38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@Q6Iq.Mq3.S_A38 segs base got_ssp RATP STRING_READ ssp_guard) S_A38 gw_tbl_13).
Definition SPARn : ltac:(gw_rebind_ty (@Q6Iq.Mq3.SPARn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.SPARn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@Q6Iq.Mq3.SPARn segs base got_ssp RATP STRING_READ ssp_guard) SPARn gw_tbl_14).
Definition S_PAR : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_PAR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_PAR segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@Q6Iq.Mq3.S_PAR segs base got_ssp RATP STRING_READ ssp_guard) S_PAR gw_tbl_15).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
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

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsH0__S_A38 := S_A38 (only parsing).
Notation F_fsH0__S_ERR := S_ERR (only parsing).
Notation F_fsH0__S_N1 := S_N1 (only parsing).
Notation F_fsH0__S_PAR := S_PAR (only parsing).
Notation F_fsH0__S_Z := S_Z (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq.

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

Local Notation Fok := (@QzQg.Mq0.Fok F).
Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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

Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
Ltac mk_winv2 := norm_m1074; unfold F_floatscan_common__winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
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

Local Notation S_N1 := (@F_fsH0__S_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_Z := (@F_fsH0__S_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_ERR := (@F_fsH0__S_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A38 := (@F_fsH0__S_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_PAR := (@F_fsH0__S_PAR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Notation FS_nank' := (FS_nank fuelc 53 (-1074) pok).
Notation FS_nan' := (FS_nan fuelc 53 (-1074) pok).

Hypothesis HS_Z : S_Z.
Hypothesis HS_ERR : S_ERR.
Hypothesis HS_A38 : S_A38.

Ltac nan_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.
Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE fc pre post pok fuelc f0 kmin0 c0 HS_A38"] Lemma L_NANR : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c,
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> yR = C_NAN ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x834)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE fc pre post pok fuelc f0 kmin0 c0 HS_A38 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_Z HS_ERR. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_Z | gw_hide HS_Z | idtac]; first [clear HS_ERR | gw_hide HS_ERR | idtac].
intros until c. intros WI RJ Hk FOK FRM' Hy.
zs. zs. zs.
stmt HS_A38. eapply NX; try eassumption; try lia;
[ fok | right; right; split; [reflexivity | exact Hy] | intros r Hr; apply freg_get_same; rewrite Hr; vm_compute; reflexivity ].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq fc pre post pok fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38"] Lemma L_PUNG : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
fR = sh_unget f -> yR = C_NAN ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x820)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos RFI_unget rf_unget_eq fc pre post pok fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary fR yR Hpok Hpok1 ST0 BYT Hnul SE_T SPLO SG2 SG3 Q1 FRM HS_Z HS_ERR. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_Z | gw_hide HS_Z | idtac]; first [clear HS_ERR | gw_hide HS_ERR | idtac].
intros until f. intros WI RJ Hk FOK FRM' HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq f Hsn) in RJu, HfR.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0.
eapply L_NANR; try eassumption; try flia.
rewrite HfR. unfold F_floatscan_common__winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite ?Hns, ?Hsn. unfold M64. hyp_cells.
rewrite HfR. exact RJu. flia.
Qed.

Definition alnumb (c : Z) : bool := ((u32 (c - 48) <? 10) || (u32 (c - 65) <? 26) || (u32 (c - 97) <? 26) || (c =? 95))%Z.
#[using="Type"] Lemma alnumb_iff : forall c, (0 <= c < 256)%Z ->
(alnumb c = true <-> (48 <= c <= 57 \/ 65 <= c <= 90 \/ 97 <= c <= 122 \/ c = 95))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_Z HS_ERR HS_A38. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_Z | gw_hide HS_Z | idtac]; first [clear HS_ERR | gw_hide HS_ERR | idtac]; first [clear HS_A38 | gw_hide HS_A38 | idtac].
clear. intros c Hc.
pose proof (forallb_range (fun c => Bool.eqb (alnumb c) (((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)) || (c =? 95)))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply Bool.eqb_prop in E. rewrite E.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le, Z.eqb_eq. tauto.
Qed.
Ltac kswrap K := rewrite swrap32_small in K by lia; rewrite land_W64 in K.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38"] Lemma L_PAR : S_PAR.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 SE_T SPLO SG2 SG3 Q1 FRM HS_Z HS_ERR. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_Z | gw_hide HS_Z | idtac]; first [clear HS_ERR | gw_hide HS_ERR | idtac].
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ WI RJ Hk FOK FRM' Hc0 Hst Ri HL HR; [discriminate HL|].
pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
rewrite fs_par_loop_S in HL. unfold fs_par_body in HL.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
fold (alnumb c'') in HL. pose proof (alnumb_iff c'' Rch) as AIF. destruct (alnumb c'') eqn:AL.
-
pose proof (proj1 AIF eq_refl) as RANGE. clear AIF.
assert (CONT : forall m2 (x11' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 i) (Z_to_bv 64 10) (Z_to_bv 64 c'') x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 26) (Z_to_bv 64 95) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x46c)) fct None m2 (seg_rom segs))).
{ intros m2 x11' WI2.
assert (Hc1 : c'' <> 0%Z) by (clear - RANGE w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq; lia).
pose proof WI2 as WI3. destruct WI3 as (FI3 & FL3 & XW3 & LW3 & FC3). pose proof FI3 as FI4. dest_finv FI4.
zs.
eapply (IH m2); try eassumption; try flia. cbn [sh_rpos]. flia. }
zs. zs. brf K1; kswrap K1.
+ zs. zs. brf K2; kswrap K2.
* eapply CONT. mk_winv2.
* zs. brf K3.
-- eapply CONT. mk_winv2.
-- zs. zs. brf K4; kswrap K4.
++ eapply CONT. mk_winv2.
++ exfalso. clear - K1 K2 K3 K4 RANGE Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq. Z.div_mod_to_equations. lia.
+ zs. eapply CONT. mk_winv2.
-
assert (NR : ~ (48 <= c'' <= 57 \/ 65 <= c'' <= 90 \/ 97 <= c'' <= 122 \/ c'' = 95)%Z) by (intros X; apply (proj2 AIF) in X; discriminate X). clear AIF.
injection HL as <- <- <-.
zs. zs. brf K1; kswrap K1; [| exfalso; clear - K1 NR Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq; Z.div_mod_to_equations; lia].
zs. zs. brf K2; kswrap K2; [exfalso; clear - K1 K2 NR Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq; Z.div_mod_to_equations; lia |].
zs. brf K3; [exfalso; clear - K3 NR Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq; lia|].
zs. zs. brf K4; kswrap K4; [exfalso; clear - K1 K2 K3 K4 NR Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq; Z.div_mod_to_equations; lia|].
zs. zs. brf K5.
+
assert (E41 : c'' = 41%Z) by (clear - K5 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq; rewrite ?land_W64 in K5; Z.div_mod_to_equations; lia).
rewrite E41, Z.eqb_refl in HR. injection HR as EfR EyR.
eapply L_NANR with (k := (kmin + 1)%Z) (c := c''); [ rewrite EfR; mk_winv2 | rewrite EfR; exact RJ1 | flia | exact FOK | exact FRM' | exact EyR ].
+ assert (N41 : c'' <> 41%Z) by (clear - K5 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq; rewrite ?land_W64 in K5; Z.div_mod_to_equations; lia).
replace (c'' =? 41)%Z with false in HR by (symmetry; apply Z.eqb_neq; exact N41). injection HR as EfR EyR.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
assert (Hsn2 : sh_shlim_neg (sh_unget (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) = false).
{ unfold sh_unget. cbn [sh_shlim_neg]. rewrite Hsn. reflexivity. }
rewrite (fs_unget_loop_eq (Z.to_nat i) _ Hsn2) in EfR. unfold sh_unget in EfR. cbn [sh_shlim_neg] in EfR. rewrite Hsn in EfR.
cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb] in EfR.
assert (RJR : RFJ' (kmin + 1 - 1 - Z.of_nat (Z.to_nat i)) c'' fR).
{ rewrite EfR.
pose proof (RFI_unget T txt p J Hp _ _ _ RJ1 ltac:(flia)) as RJu. unfold sh_unget in RJu. cbn [sh_shlim_neg] in RJu. rewrite Hsn in RJu.
cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb] in RJu.
pose proof (RFJ_ungetn (Z.to_nat i) _ _ _ RJu ltac:(reflexivity) ltac:(lia)) as RJv.
rewrite fs_unget_loop_eq in RJv by reflexivity. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJv.
replace (sh_rpos f + 1 - 1 - Z.of_nat (Z.to_nat i))%Z with (sh_rpos f + 1 - 1 - Z.of_nat (Z.to_nat i))%Z by lia. exact RJv. }
unfold rf_rend in FC. rewrite ?Hsn, ?Hns in FC. unfold M64 in FC. rewrite Hpok1.
zs. zs. (brf K6; [ exfalso; lia | ]). zs. zs. zs0. zs. (brf K7; [ exfalso; lia | ]). zs. (brf K8; [ exfalso; lia | ]). zs. (brf K9; [ exfalso; lia | ]). zs. zs. zs. zs0.
eapply L_NANR; try eassumption; try flia.
rewrite EfR. unfold F_floatscan_common__winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite ?Hns, ?Hsn. unfold M64. hyp_cells.
all: flia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK3 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nan' sign 3 c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x438)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SE_T SPLO SG2 SG3 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
unfold FS_nan in HK. change (3 =? 3)%Z with true in HK. replace (negb (nz pok)) with false in HK by (rewrite Hpok1; reflexivity). cbv iota in HK.
nan_read FC RJ kmin c f Hc0. cbv beta iota zeta in HK.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K1.
-
assert (N40 : c'' <> 40%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq segs base ssp_guard; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c'' =? 40)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N40). cbn [negb] in HK. injection HK as EfR EyR.
eapply L_PUNG with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; eassumption); try mk_winv2; try apply Fok_refl.
- assert (E40 : c'' = 40%Z) by (clear - K1 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq segs base ssp_guard; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E40, Z.eqb_refl in HK. cbn [negb] in HK.
destruct (fs_par_loop fuelc _) as [[[i' c'] f']|] eqn:HL; [|discriminate HK].
zs. zs. zs. zs. zs.
eapply (L_PAR fuelc) with (kmin := (kmin + 1)%Z) (i := 1%Z) (c := c''); try eassumption; try flia;
try mk_winv2; try apply Fok_refl; try (cbn [sh_rpos]; flia); try (rewrite E40; lia).
destruct (c' =? 41)%Z; cbv zeta iota in HK; injection HK as <- <-; reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK2 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nank' sign 2 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x2f0)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SE_T SPLO SG2 SG3 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_nank_step in HK by lia. change (znth str_nan 2) with 110%Z in HK. change (2 <? 2)%Z with false in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_err in HK by lia. injection HK as EfR EyR.
stmt HS_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK. rewrite FS_nank_3 in HK.
zs.
eapply L_NK3; only 6: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK1 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nank' sign 1 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x174)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary pok fuelc f0 fR yR Hpok ST0 SE_T SPLO SG2 SG3 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_nank_step in HK by lia. change (znth str_nan 1) with 97%Z in HK. change (1 <? 2)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 65%Z N1. replace (Z.lor c'' 32 =? 97)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_err in HK by lia. injection HK as EfR EyR.
stmt HS_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 65%Z E1. rewrite E1, Z.eqb_refl in HK.
zs.
eapply L_NK2; only 6: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_N1 : S_N1.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok ST0 SE_T SPLO SG2 SG3 Q1. try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac].
intros m; intros until f. intros _ WI RJ Hk Hst Hsg Hr1 Rc0 Hni HK. pose proof WI as WI0. dest_winv WI. bury_disj.
rewrite FS_nank_step in HK by lia. change (znth str_nan 0) with 110%Z in HK. change (0 <? 2)%Z with true in HK. cbv iota in HK.
zs. zs. brf K1.
- and33n K1 c Rc0 78%Z N1. replace (Z.lor c 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_0 in HK.
stmt HS_Z. eapply NX; try eassumption; try flia. apply Fok_refl.
- and33y K1 c Rc0 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_NK1; only 6: exact HK; [exact WI0 | exact RJ | flia | intros E0; rewrite E0 in E1; discriminate E1 | exact Hst].
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

Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_0)))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_1)))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_2)))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_3)).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_4)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_5)))))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_6)).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_7)).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_8)).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_9)).
Definition S_848 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) S_848 gw_tbl_10).
Definition S_6F8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_6F8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_6F8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.S_6F8 segs base got_ssp RATP STRING_READ ssp_guard) S_6F8 gw_tbl_11).
Definition S_Z : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_Z segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_Z segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@Q6Iq.Mq3.S_Z segs base got_ssp RATP STRING_READ ssp_guard) S_Z gw_tbl_12).
Definition hinv : ltac:(gw_rebind_ty (@Q6Iq.Mq3.hinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.hinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@Q6Iq.Mq3.hinv segs got_ssp RATP ssp_guard) hinv gw_tbl_13).
Definition S_HEX : ltac:(gw_rebind_ty (@Q6Iq.Mq3.S_HEX segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q6Iq.Mq3.S_HEX segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@Q6Iq.Mq3.S_HEX segs base got_ssp RATP STRING_READ ssp_guard) S_HEX gw_tbl_14).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
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

Definition frame_release : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.frame_release) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.frame_release)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__S_6F8 := S_6F8 (only parsing).
Notation F_floatscan_common__S_848 := S_848 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__frame_release := frame_release (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).
Notation F_fsH0__S_HEX := S_HEX (only parsing).
Notation F_fsH0__S_Z := S_Z (only parsing).
Notation F_fsH0__hinv := hinv (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).
Local Notation frame_release := (@F_floatscan_common__frame_release ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T txt pre canary).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

Local Notation S_848 := (@F_floatscan_common__S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_6F8 := (@F_floatscan_common__S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
Ltac mk_winv2 := norm_m1074; unfold F_floatscan_common__winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
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

Local Notation S_Z := (@F_fsH0__S_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_HEX := (@F_fsH0__S_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Hypothesis HS_848 : S_848.
Hypothesis HS_6F8 : S_6F8.
Hypothesis HS_HEX : S_HEX.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_848 HS_6F8 HS_HEX"] Lemma L_Z : S_Z.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_848 HS_6F8 HS_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 SE_T SPLO SG2 SG3 Q1 FRM. try gw_hide Hpok; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide SE_T; try gw_hide SPLO; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold FS_tail_h in HK.
zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N48 : c <> 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; Z.div_mod_to_equations; lia).
replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N48).
stmt HS_6F8. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E48 : c = 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc; Z.div_mod_to_equations; lia).
rewrite E48, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E48 in RJ.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
unfold FS_zero in HK.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
(Z.lor (fst (sh_getc f)) 32 =? 120)%Z = false ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8 (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x3e4)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2 NX120. rewrite NX120 in HK.
stmt HS_848. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf K3; rewrite ?land_W64 in K3.
+
eapply JOIN. { mk_winv2. }
apply Z.eqb_neq. intros E. apply (proj2 (and33_lor c'' 88 Rch ltac:(lia))) in E. clear - K3 E Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc. Z.div_mod_to_equations; lia.
+
assert (E120 : Z.lor c'' 32 = 120%Z).
{ apply (proj1 (and33_lor c'' 88 Rch ltac:(lia))). clear - K3 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc. pose proof (and33_range c'' Rch). Z.div_mod_to_equations; lia. }
rewrite E120, Z.eqb_refl in HK.
gw_expose ssp_guard. zs. zs. zs. zs. zs. (brf K4; [ | exfalso; lia ]).
zs. zs. zs. zs. zs. zs. zs. zs.
do 14 zs. zs. zs.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (WI9 : winv mm j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws
(mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) by mk_winv2 end.
destruct WI9 as (FI9 & FL9 & XW9 & LW9 & FC9).
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI9 FL9 XW9 LW9) as STK.
stmt HS_HEX. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia.
* destruct FI9 as (MI9 & MU9 & WM9 & FRhi9 & ST9 & BY9 & SSA & SSB). destruct FL9 as [LOW9 ERR9].
unfold F_fsH0__hinv. split; [exact MI9|]. split; [exact MU9|]. split; [exact WM9|]. split; [exact STK|]. split; [exact BY9|].
split; [exact SSA|]. split; [exact SSB|]. split; [exact ERR9|]. exact FC9.
* intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
-- rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
-- rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.
End Floatscan.

End G.
End Mq3.

Module Mq4.

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
Local Definition gw_tbl_1 := (gw_ent (@Q6Iq.Mq3.ssJ STRING_READ) ssJ (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_0)))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q6Iq.Mq3.RFJ STRING_READ) RFJ (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_1)))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q6Iq.Mq3.RFI STRING_READ) RFI (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_2)))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Q6Iq.Mq3.RERRNO RATP) RERRNO (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_3)).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q6Iq.Mq3.Wfs RATP) Wfs (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_4)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Q6Iq.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_5)))))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Q6Iq.Mq3.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_6)).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Q6Iq.Mq3.finv segs got_ssp RATP ssp_guard) finv (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_7)).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q6Iq.Mq3.framL segs RATP) framL (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_8)).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Q6Iq.Mq3.winv segs got_ssp RATP ssp_guard) winv (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_9)).

Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
Notation rfj := G.T_rfj.rfj.

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard rf_getc_slow RFI_unget rf_unget_eq"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard rf_getc_slow RFI_unget rf_unget_eq.

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

Local Notation ctx_all := (@QzQg.Mq0.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Wfs := (@F_floatscan_common__Wfs q Fp).

Local Notation Fok := (@QzQg.Mq0.Fok F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).

Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.

Ltac lia_goal P := lazymatch P with
| (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
| (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
| ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
| ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
end.
Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].

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

Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation SC0 := (f128_of_i32 1).
Notation HX_alz' := (HX_alz fuelc 53 (-1074)).
Notation HX_rz' := (HX_rz fuelc 53 (-1074)).
Notation HX_dig' := (HX_dig fuelc 53 (-1074)).
Notation HX_tail' := (HX_tail fuelc 53 (-1074)).
Notation HX_e2' := (HX_e2 53 (-1074)).
Notation HX_fin' := (HX_fin 53 (-1074)).

Definition hxfr (w0 w8 w16 w24 w32 w40 w48 w56 : word) (m : word -> option byte) : Prop :=
rw_cells segs m (q + -176) [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 (reg_get F 8);
C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition hxinv (m : word -> option byte) (ev : word) (f : shfile) : Prop :=
mem_inv segs m /\ munch Wfs m0 m /\ wmono segs m0 m
/\ stk segs m (q - FS_DEPTH) (q + -176)
/\ bytes_at segs m T (zbytes txt)
/\ rw_cells segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells segs m ssp_guard [C8 canary]
/\ rw_cells segs m RERRNO [C4 ev]
/\ rw_cells segs m Fp (rf_cells T p true f J).

Definition kminH (kmin gd gr : Z) : Prop := (1 <= kmin)%Z /\ (gd = 0%Z -> 2 + gr <= kmin)%Z.

Definition SHLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin (f : shfile) (gd gd' c' : Z) (f' : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin 48 f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
df_lz_loop n (gd, 48, f)%Z = Some (gd', c', f') -> HX_alz' sign pok gd' c' f' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 0) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x17b4)) fct None m (seg_rom segs)).
Definition S_HLZ : Prop := forall n, SHLZn n.

Definition S_H778 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> (3 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
HX_alz' sign pok 1 c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 (Z_to_bv 64 0) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 0) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x17d0)) fct None m (seg_rom segs)).

Definition S_H720 : Prop := forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile) (gd : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> c <> 0%Z ->
(0 <= gd <= 1)%Z ->
HX_rz' sign pok gd 0 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) x9 (Z_to_bv 64 (T + sh_rpos f)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1778)) fct None m (seg_rom segs)).

Definition SHRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin (f : shfile) (gd rp gd' rp' c' : Z) (f' : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin 48 f -> (3 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(- sh_rpos f <= rp <= 0)%Z ->
df_rz_loop n (gd, rp, 48, f)%Z = Some (gd', rp', c', f') -> HX_dig' sign pok (mkHX c' f' 0 Y0 SC0 0 1 gd' rp' 0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 (Z_to_bv 64 48) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1814)) fct None m (seg_rom segs)).
Definition S_HRZ : Prop := forall n, SHRZn n.

Definition S_H7F0 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile) (gd gr rp : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
(0 <= gd <= 1)%Z -> (0 <= gr <= 1)%Z -> (- sh_rpos f <= rp <= 0)%Z ->
HX_dig' sign pok (mkHX c f 0 Y0 SC0 0 gr gd rp 0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1848)) fct None m (seg_rom segs)).

Definition hxI (f : shfile) (c x gt gr gd rp dc : Z) : Prop :=
(0 <= c < 256)%Z /\ (0 <= x < 2^32)%Z /\ (0 <= gt <= 1)%Z /\ (0 <= gr <= 1)%Z /\ (0 <= gd <= 1)%Z /\
(0 <= dc <= sh_rpos f)%Z /\ (- sh_rpos f <= rp <= sh_rpos f)%Z.

Definition SHDn (n : nat) : Prop := forall (pc : Z) m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc : Z) (s' : st_hex),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc ->
hx_dig_loop n (mkHX c f x y sc gt gr gd rp dc) = Some s' -> HX_tail' sign pok (hx_c s') (hx_f s') (hx_x s') (hx_y s') (hx_gr s') (hx_gd s') (hx_rp s') (hx_dc s') = Some (fR, yR) ->
((pc = (base + 0x18ac)%Z /\ isdigitc c = true) \/ (pc = (base + 0x19a8)%Z /\ isdigitc c = false)) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) (Z_to_bv 64 (bv_swrap 32 (c + -48))) (Z_to_bv 64 c) x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 pc) fct None m (seg_rom segs)).
Definition S_HD : Prop := forall n, SHDn n.

Definition S_HTL : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc ->
HX_tail' sign pok c f x y gr gd rp dc = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x19bc)) fct None m (seg_rom segs)).

Definition S_HE2 : Prop := forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y rp e2 : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 < x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z -> (-2^60 <= e2 <= 2^60)%Z ->
HX_e2' sign fR x y (4 * rp + e2 - 32) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 e2) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1a6c)) fct None m (seg_rom segs)).

Definition SHNLn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y e2 x' y' e2' : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> reg_get Ft 8 = D_05 ->
(0 < x < 2^31)%Z -> (-1340 + Z.of_nat n <= e2 <= 1074)%Z ->
hx_norm_loop n (x, y, e2) = Some (x', y', e2') -> HX_fin' sign fR x' y' e2' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1bb8)) fct None m (seg_rom segs)).
Definition S_HNL : Prop := forall n, SHNLn n.

Definition S_HFIN : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y e2 : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(2^31 <= x < 2^32)%Z -> (-1500 <= e2 <= 1074)%Z ->
HX_fin' sign fR x y e2 = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1c04)) fct None m (seg_rom segs)).

Definition S_HZR : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w48 w56 : word) sign k c,
let _ := ctx_all in
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> yR = hx_zero sign ->
evt segs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1b0c)) fct None m (seg_rom segs)).

#[using="Type"] Lemma HX_fin_f : forall sign f x y e2 f' y', HX_fin' sign f x y e2 = Some (f', y') -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros until y'. unfold HX_fin.
match goal with |- context [match ?X with pair _ _ => _ end] => destruct X as [[bias x2] y2] end. intros H; injection H as <- _; reflexivity.
Qed.
#[using="Type"] Lemma HX_e2_f : forall sign f x y e2 f' y', HX_e2' sign f x y e2 = Some (f', y') -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros until y'. unfold HX_e2.
destruct (x =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (- (-1074) <? e2)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (e2 <? -1074 - 2 * LDBL_MANT_DIG_)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (hx_norm_loop 33 _) as [[[x3 y3] e3]|]; [apply HX_fin_f | discriminate].
Qed.
End Floatscan.

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 QqdR QYTG G.T_shp G.T_pe Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

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
Import Q6Iq.Mq4.

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

Definition snprintf_code (w_4 w_5 w_15 w_23 : Z) : list Z :=
[0xfb010113; 0x00113c23; 0x00813823; 0x05113423; w_4; w_5; 0x02d13423; 0x02e13823; 0x02f13c23; 0x05013023; 0x00043683; 0x02810713; 0x00d13423; 0x00e13023; 0x02810693; w_15; 0x00043583; 0x00813603; 0x00c59a63; 0x01813083; 0x01013403; 0x05010113; 0x00008067; w_23]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_4 w_5 w_15 w_23 : Z).
Variables (hi_4 : bv 20).
Variables (lo_5 : bv 12).
Variables (joff_15 : bv 21).
Variables (got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_197bc e_vsnprintf e_sn_write e_memset : Z).
Hypothesis CODE : code_at segs base (snprintf_code w_4 w_5 w_15 w_23).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 96.
Hypothesis D_4 : decode_any (Z_to_bv 32 w_4) = Some (Auipc 17 hi_4, 4%Z).
Hypothesis E_4 : is_ecall (Z_to_bv 32 w_4) = false.
Hypothesis D_5 : decode_any (Z_to_bv 32 w_5) = Some (Load SZ8 true 8 17 lo_5, 4%Z).
Hypothesis E_5 : is_ecall (Z_to_bv 32 w_5) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Jal 1 joff_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis ANCH_5 : gw_anch (Z.shiftl (bv_signed hi_4) 12 + (base + 16) + bv_signed lo_5)%Z got_ssp.
Hypothesis LINK_15 : gw_anch (base + 60 + bv_signed joff_15)%Z (e_vsnprintf + 0)%Z.
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

Local Definition gw_tbl_0 := tt.

Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QZxv.Mqi.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqh.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq7.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqg.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqf.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqe.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqj.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq9.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq8.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq5.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq4.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq0.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq2.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq3.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq1.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq1.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq0.arg_ok segs) arg_ok (gw_ent (@QK0e.arg_ok segs) arg_ok (gw_ent (@QEN3.arg_ok segs) arg_ok (gw_ent (@Q6Iq.Mq4.arg_ok segs) arg_ok (gw_ent (@QzQg.Mq1.arg_ok segs) arg_ok (gw_ent (@Q5m9.Mq0.arg_ok segs) arg_ok (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_0)))))))))))))))))))))))).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QZxv.Mqi.args_ok segs) args_ok (gw_ent (@QZxv.Mqh.args_ok segs) args_ok (gw_ent (@QEN3.Mq7.args_ok segs) args_ok (gw_ent (@QZxv.Mqg.args_ok segs) args_ok (gw_ent (@QZxv.Mqf.args_ok segs) args_ok (gw_ent (@QZxv.Mqe.args_ok segs) args_ok (gw_ent (@QZxv.Mqj.args_ok segs) args_ok (gw_ent (@QZxv.Mq9.args_ok segs) args_ok (gw_ent (@QZxv.Mq8.args_ok segs) args_ok (gw_ent (@QEN3.Mq5.args_ok segs) args_ok (gw_ent (@QEN3.Mq4.args_ok segs) args_ok (gw_ent (@QEN3.Mq0.args_ok segs) args_ok (gw_ent (@QZxv.Mq2.args_ok segs) args_ok (gw_ent (@QZxv.Mq3.args_ok segs) args_ok (gw_ent (@QEN3.Mq1.args_ok segs) args_ok (gw_ent (@QZxv.Mq1.args_ok segs) args_ok (gw_ent (@QZxv.Mq0.args_ok segs) args_ok (gw_ent (@QK0e.args_ok segs) args_ok (gw_ent (@QEN3.args_ok segs) args_ok (gw_ent (@Q6Iq.Mq4.args_ok segs) args_ok (gw_ent (@QzQg.Mq1.args_ok segs) args_ok (gw_ent (@Q5m9.Mq0.args_ok segs) args_ok (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_1)))))))))))))))))))))))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QZxv.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqc.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqk.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqb.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqd.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqi.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqh.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqg.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqf.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqe.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqj.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq9.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QK0e.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqa.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q6Iq.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_2))))))))))))))))))))))))))))))))))))))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QZxv.Mq6.va_area segs) va_area (gw_ent (@QZxv.Mq5.va_area segs) va_area (gw_ent (@QZxv.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mqc.va_area segs) va_area (gw_ent (@QEN3.Mq3.va_area segs) va_area (gw_ent (@QZxv.Mqk.va_area segs) va_area (gw_ent (@QZxv.Mqb.va_area segs) va_area (gw_ent (@QZxv.Mqd.va_area segs) va_area (gw_ent (@QZxv.Mq4.va_area segs) va_area (gw_ent (@QZxv.Mqi.va_area segs) va_area (gw_ent (@QZxv.Mqh.va_area segs) va_area (gw_ent (@QEN3.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mqg.va_area segs) va_area (gw_ent (@QZxv.Mqf.va_area segs) va_area (gw_ent (@QZxv.Mqe.va_area segs) va_area (gw_ent (@QZxv.Mqj.va_area segs) va_area (gw_ent (@QZxv.Mq9.va_area segs) va_area (gw_ent (@QZxv.Mq8.va_area segs) va_area (gw_ent (@QEN3.Mq2.va_area segs) va_area (gw_ent (@QEN3.Mq5.va_area segs) va_area (gw_ent (@QEN3.Mq4.va_area segs) va_area (gw_ent (@QEN3.Mq0.va_area segs) va_area (gw_ent (@QZxv.Mq2.va_area segs) va_area (gw_ent (@QEN3.Mq8.va_area segs) va_area (gw_ent (@QZxv.Mq3.va_area segs) va_area (gw_ent (@QEN3.Mq1.va_area segs) va_area (gw_ent (@QZxv.Mq1.va_area segs) va_area (gw_ent (@QZxv.Mq0.va_area segs) va_area (gw_ent (@QK0e.va_area segs) va_area (gw_ent (@QEN3.va_area segs) va_area (gw_ent (@QZxv.Mqa.va_area segs) va_area (gw_ent (@QEN3.Mq6.va_area segs) va_area (gw_ent (@Q6Iq.Mq4.va_area segs) va_area (gw_ent (@QzQg.Mq1.va_area segs) va_area (gw_ent (@QROt.Mq1.va_area segs) va_area (gw_ent (@Q5m9.Mq0.va_area segs) va_area (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_3))))))))))))))))))))))))))))))))))))))).
Definition vsnprintf_post : ltac:(gw_rebind_ty (@Q6Iq.Mq4.vsnprintf_post segs got_ssp ssp_guard) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q6Iq.Mq4.vsnprintf_post segs got_ssp ssp_guard) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q6Iq.Mq4.vsnprintf_post segs got_ssp ssp_guard) vsnprintf_post gw_tbl_4).
Definition vsnprintf_stmt : ltac:(gw_rebind_ty (@Q6Iq.Mq4.vsnprintf_stmt segs e_vsnprintf got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q6Iq.Mq4.vsnprintf_stmt segs e_vsnprintf got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Q6Iq.Mq4.vsnprintf_stmt segs e_vsnprintf got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) vsnprintf_stmt gw_tbl_5).

Hypothesis args_ok_nos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q6Iq.Mq4.gw_all) (@Q6Iq.Mq4.args_ok_nos) e_vsnprintf)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in exact T).
Hypothesis vsnprintf_proof : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q6Iq.Mq4.gw_all) (@Q6Iq.Mq4.vsnprintf_proof) e_vsnprintf)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in exact T).
Notation mem := (word -> option byte).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Notation parg := G.T_printf.parg.

#[using="got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_vsnprintf e_sn_write e_memset CODE BASE4 BASER D_4 E_4 D_5 E_5 D_15 E_15 ANCH_5 LINK_15 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP args_ok_nos vsnprintf_proof"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_4 w_5 w_15 w_23 hi_4 lo_5 joff_15 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_vsnprintf e_sn_write e_memset CODE BASE4 BASER D_4 E_4 D_5 E_5 D_15 E_15 ANCH_5 LINK_15 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP args_ok_nos vsnprintf_proof.

Local Ltac transport_chunks segs_ m a bs ::= transport_chunks_fast segs_ m a bs.
Local Ltac footprint_after_store segs_ m a bs ::= footprint_after_store_fast segs_ m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs_ m m' MU WM ::= transport_after_call_fast segs_ m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
(try g_ret_pc) end.

Definition snprintf_entry : Z := (base + 0x0).

Definition SNPRINTF_DEPTH : Z := 5936.

Definition snprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D : Z) (dn : nat) (o : list Z) (r : Z) (junkd : list byte) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
/\ ssp_cells m' canary.

Definition snprintf_gen_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(n A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in let D := bv_unsigned a0 in
a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
rw_cells segs m D [CB dn junkd] ->
bytes_at segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
Forall no_s args -> args_ok 0 0 0 m lo q 0 [a3; a4; a5; a6; a7] args ->
printf_model OUT_sn OUTFP_sn fmt args [] = QlEo_c1.Mq0.Ret (Ok (r, o)) ->
Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
(length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
stk segs m lo q -> (lo <= q - SNPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv segs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
evt segs (snprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn o r junkd lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom segs)).

#[using="Type"] Lemma rwc_eq' : forall m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. clear - segs. intros m A A' cs H <-. exact H. Qed.

#[using="w_4 w_5 w_15 w_23 hi_4 lo_5 joff_15 e_vsnprintf CODE BASE4 BASER D_4 E_4 D_5 E_5 D_15 E_15 ANCH_5 LINK_15 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP args_ok_nos vsnprintf_proof"] Theorem snprintf_gen_proof : snprintf_gen_stmt.
Proof. clear - w_4 w_5 w_15 w_23 hi_4 lo_5 joff_15 e_vsnprintf CODE BASE4 BASER D_4 E_4 D_5 E_5 D_15 E_15 ANCH_5 LINK_15 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP args_ok_nos vsnprintf_proof.
unfold snprintf_gen_stmt, snprintf_entry. intros until o. cbv zeta.
intros -> -> DST BY HF P1 NOS AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA DD1 GD.
gw_expose GLOBALS_TOP; gw_expose STATIC_SPLIT; unfold SNPRINTF_DEPTH in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
set (D := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 D) by (unfold D; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct SSP as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
carve_frame 80%nat ST.
do 16 zs.

apply (proj1 (rw_cells_app segs _ _ [_;_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -80 + Z.of_nat 40)%Z with (bv_unsigned sp + -40)%Z in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a3; a4; a5; a6; a7]) in VAA.

pose proof (gw_unhyp vsnprintf_proof) as VS. unfold vsnprintf_stmt in VS. cbv zeta in VS.
eapply evt_cut.
{ eapply VS with (D := D) (n := n) (A := A) (VA := bv_unsigned sp + -40) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := [a3; a4; a5; a6; a7]) (args := args)
(lo := lo) (canary := canary) (r := r) (o := o);
clear VS; rewrite ?unsigned_lit by lia; gw_expose GLOBALS_TOP; gw_expose STATIC_SPLIT; unfold VSN_DEPTH, zlength; cbn [length].
all: try reflexivity.
all: try lia.
all: try eassumption.
- eapply args_ok_nos; [exact NOS | exact AOK].
- split; [exact SSP1 | exact SSP2]. }
cbv beta. intros ms' P.
unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard.

zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear - Kc w_4 w_5 w_15 w_23 hi_4 lo_5 joff_15 e_vsnprintf CODE BASE4 BASER D_4 E_4 D_5 E_5 D_15 E_15 ANCH_5 LINK_15 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP args_ok_nos vsnprintf_proof. apply Kc. reflexivity. }
zs. zs. zs. zs.
lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?c1, VAC : rw_cells _ ?mm (bv_unsigned sp + -40)%Z ?c2 |- _ =>
assert (FALL : rw_cells segs mm (bv_unsigned sp + -80) (c1 ++ c2));
[ apply (proj2 (rw_cells_app segs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq'; [exact VAC | lia]
| clear FR VAC ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold snprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split; [exact DST3|].
split; [exact SSP1 | exact SSP2].
Qed.

End G.
End Mq5.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QyjG QM7w QNAo QFs1 Q8QT QDXD QULt Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QM7w QNAo.Mq0 QFs1.Mq0.
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
Import QzQg.
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
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (ralloc_slot_entry : Z).
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
Hypothesis AL_ralloc_slot_entry : gw_al ralloc_slot_entry 4.
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
Notation gw_tbl_1 := (gw_ent (@QQRC.Mq4.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@QzQg.rimplT segs RC__) (@rimplT) gw_tbl_0))))).
Definition rta_fp : ltac:(gw_rebind_ty (@QzQg.rta_fp RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QzQg.rta_fp RATP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QzQg.rta_fp RATP) (@rta_fp) gw_tbl_1).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QzQg.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq4.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_2))))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QzQg.Mq3.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq4.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_3))))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QzQg.Mq3.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq4.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_4)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QzQg.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QzQg.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_5))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QzQg.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QzQg.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_6))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QzQg.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QzQg.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_7))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QzQg.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QzQg.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_8))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QzQg.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QzQg.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_9))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QzQg.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QzQg.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_10))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QzQg.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QzQg.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_11))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QzQg.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QzQg.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_12))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QzQg.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QzQg.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_13))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QzQg.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QzQg.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_14))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QzQg.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QzQg.rpres_except segs) (@rpres_except) gw_tbl_15))))))))).
Definition ras_post2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) gw_tbl_16).

Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).

Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).

Definition rauxv_ok_pres : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rauxv_ok_pres) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rauxv_ok_pres)).

Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Notation RISTF := (@ISTF_g ref_reserved).

#[using="ralloc_slot_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_ralloc_slot_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

#[using="LBK"] Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. clear - LBK st0 st stX LB sc req g k mr msk st' F ER SC RQ FIT TR HA GM MSK K0. first [clear K0 | gw_hide K0 | idtac]; first [clear MSK | gw_hide MSK | idtac]; first [clear GM | gw_hide GM | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear TR | gw_hide TR | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear F | gw_hide F | idtac]; try gw_hide st'; first [clear msk | gw_hide msk | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear k | gw_hide k | idtac]; first [clear g | gw_hide g | idtac]; first [clear req | gw_hide req | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear LB | gw_hide LB | idtac]; first [clear stX | gw_hide stX | idtac]; first [clear st | gw_hide st | idtac]; first [clear st0 | gw_hide st0 | idtac]. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

#[using="ref_reserved LB sc F ER SC RQ FIT TR GM MSK K0 LBK"] Lemma rta_slot_ok : exists b r,
m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
/\ slot_ok st' g b r k req
/\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
free_slot_addr st0 a).
Proof. clear - ref_reserved LB sc F ER SC RQ FIT TR GM MSK K0 LBK st0 st stX req g k mr msk st' HA. first [clear HA | gw_hide HA | idtac]; try gw_hide st'; try gw_hide msk; try gw_hide mr; try gw_hide k; try gw_hide g; first [clear req | gw_hide req | idtac]; first [clear stX | gw_hide stX | idtac]; try gw_hide st; try gw_hide st0.
pose proof (isf_mf _ _ F) as MF.
pose proof (gmf_cls _ _ _ GM) as GSC.
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).

destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
{ rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }

assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| gw_exact LBK]).
assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
{ apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
destruct (FM g b Hmem) as (FM1 & FM2 & _).
assert (KLI : k <= m_last_idx (get_meta_rec st g)).
{ destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; gw_exact TBst])) as FC.
cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
{ pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
assert (P2k : 0 < 2 ^ k <= msk).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. gw_exact LE'. }
exists b, r.
split; [gw_exact Hmem|]. split; [gw_exact Hr|].
split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); gw_exact Hr|]. split; [gw_exact Hk|].
split; [| split; [gw_exact ST'|]].
- pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; gw_exact ST').
constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
+ gw_exact Hmem.
+ unfold st'. cbn. rewrite (tr_regions _ _ _ TR). gw_exact Hr.
+ gw_exact Hk.
+ gw_exact B0.
+ gw_exact B16.
+ lia.
+ lia.
+ gw_exact SPAN.
+ unfold UNIT in S16. lia.
+ unfold UNIT in SMOD. gw_exact SMOD.
+ lia.
+ gw_exact RQ.
+ lia.
+ intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
+ unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). gw_exact K4.
+ intros off O0 OF.
assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
+ unfold st'. cbn. rewrite (tr_slots _ _ _ TR). gw_exact SSL.
+ unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| gw_exact MSL]. apply (tr_areas _ _ _ TR).
+ unfold msk, mr in *. lia.
+ unfold mr. lia.
+ lia.
+ lia.
+ left. lia.
- intros a Ha. rewrite ST' in Ha.
destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; gw_exact Hmem).
destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
exists g, b, r, k. split; [gw_exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); gw_exact Hr|]. split; [gw_exact Hk|]. split; [lia|].
split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
+ pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; gw_exact TB0].
+ assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End TASLOT.

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

#[using="segs RGOT_SSP ref_reserved RNG_RATP RC__ R k o s Q ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req errv ERR TP HK"] Lemma rerrno_lit : errno_addr tp = (RATP + -164).
Proof. clear - segs RGOT_SSP ref_reserved RNG_RATP RC__ R k o s Q ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req errv ERR TP HK RATP f bail tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 LB AR IS ER AC SC RQ FIT MR TK UA BL AUX ST CLO LO MI A0 A1 F0. gw_expose_fam RATP. first [clear F0 | gw_hide F0 | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear CLO | gw_hide CLO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear LB | gw_hide LB | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; try gw_hide tp; first [clear bail | gw_hide bail | idtac]; first [clear f | gw_hide f | idtac]. subst tp. gw_expose_fam RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved st0 LB errv AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK F0"] Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) ->
rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
(MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved st0 LB errv AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK F0 segs RATP R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo sc req ST MI A0 A1. gw_expose_fam RATP. first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ST | gw_hide ST | idtac]; try gw_hide req; try gw_hide sc; try gw_hide lo; try gw_hide st; try gw_hide m; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; try gw_hide t6; try gw_hide t5; try gw_hide t4; try gw_hide t3; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; try gw_hide t2; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; try gw_hide sp; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac].
intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
pose proof (isf_mf _ _ F0) as MF.
set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
subst msk.
destruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
fold st' in Hr', SO, STR, FSA.

pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).

assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
{ intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. gw_exact X.
- left. right. right. left. gw_exact X.
- left. do 3 right. destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. rewrite REGX. split; [gw_exact H0|]. split; [gw_exact K0|]. lia.
- do 3 right. left. destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
exists bq, gh0, rb. split; [gw_exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); gw_exact Hrb|]. split; [gw_exact Kb|].
pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [gw_exact PE| gw_exact FPC]).

assert (NIMG : forall a, 0x10000 <= a < RIMG_HI -> ~ ((RATP + 131968) <= a < (RATP + 132896)) -> ~ rta_fp st lo (bv_unsigned sp) a).
{ intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- unfold alloc_ceiling in CLO. lia.
- exact (Hc X).
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
apply HK. unfold ras_post2.
exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
split; [reflexivity|].
split; [gw_exact MI'|]. split; [gw_exact ST'|].
split. { eapply rpres_except_rw_cells; [gw_exact PE| gw_exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| gw_expose_fam RATP; lia]. }
split. { eapply rauxv_ok_pres; [gw_exact AUX| gw_exact PE| |].
- intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
+ lia. + gw_expose_fam RATP. unfold alloc_ceiling in CLO. lia.
+ destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). unfold alloc_ceiling in CLO. lia.
+ destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in *. lia.
- intros a Ha. apply NIMG; gw_expose_fam RATP; lia. }
split; [gw_exact MR'|].
split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | gw_exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
split. {
intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
{ revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; gw_exact Hc. }
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
refine (proj1 (PE (r_base rr + off) _ _)).
{ destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). unfold alloc_ceiling in RC. lia. }
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
- destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). gw_expose_fam RATP. lia.
- destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG0. exists bq, gh. split; [gw_exact Hbq|]. split; [gw_exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
split; [gw_exact PE'|].
split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. gw_exact BL. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split. {  constructor.
- intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
- intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). gw_exact Ha.
- unfold st'. cbn. apply (tr_tick _ _ _ TR).
- intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
exact (AC rid sh o' v t Esh Hc).
- intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
pose proof (mf_ctx _ _ MF) as (X & _). gw_exact X. }
right. split; [lia|]. exists g3, b, r.
split; [unfold st'; rewrite active_upd_meta; gw_exact HA|]. split; [gw_exact SO|]. split.
- intros a Ha. do 2 right. left. apply FSA. gw_exact Ha.
- intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.

End RC__1.

End G.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF Qe1A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QXxF.Mq0 QM7w QNAo.Mq0 QFs1.
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
Import QZxv.Mqm.
Import QzQg.Mq3.
Import Qe1A.Mq6.

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

Definition rag_regs : ltac:(gw_rebind_ty (@Qe1A.Mq6.rag_regs RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qe1A.Mq6.rag_regs RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qe1A.Mq6.rag_regs RATP) (@rag_regs) gw_tbl_0).
Definition rta_frame : ltac:(gw_rebind_ty (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qe1A.Mq6.rta_frame RC__) (@rta_frame) (gw_ent (@QZxv.Mqo.rta_frame RC__) (@rta_frame) (gw_ent (@QROt.Mq3.rta_frame RC__) (@rta_frame) gw_tbl_1))).
Definition rFRM : ltac:(gw_rebind_ty (@Qe1A.Mq6.rFRM RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Qe1A.Mq6.rFRM RC__) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qe1A.Mq6.rFRM RC__) (@rFRM) gw_tbl_2).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qe1A.Mq6.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QzQg.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq4.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_3)))))).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_4)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_5 := (gw_ent (@Qe1A.Mq6.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq4.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_4))))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qe1A.Mq6.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QzQg.Mq3.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq4.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_5)))))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qe1A.Mq6.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QzQg.Mq3.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq4.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_6))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qe1A.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@QzQg.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqm.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_7)))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qe1A.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QzQg.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqm.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_8)))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qe1A.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QzQg.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqm.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_9)))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qe1A.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QzQg.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqm.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_10)))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qe1A.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QzQg.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqm.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_11)))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Qe1A.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QzQg.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqm.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_12)))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Qe1A.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QzQg.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqm.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_13)))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@Qe1A.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QzQg.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqm.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_14)))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@Qe1A.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QzQg.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqm.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_15)))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@Qe1A.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QzQg.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqm.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_16)))))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Qe1A.Mq6.rpres_except segs) (@rpres_except) (gw_ent (@QzQg.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_17))))))))).
Definition rHAG_stmt : ltac:(gw_rebind_ty (@Qe1A.Mq6.rHAG_stmt segs base RATP RDEBRUIJN RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@Qe1A.Mq6.rHAG_stmt segs base RATP RDEBRUIJN RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)).
#[global] Arguments rHAG_stmt {R}%_type_scope f%_nat_scope k%_function_scope bail o s Q%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope a1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope m st0 st lo%_Z_scope sc%_Z_scope req%_Z_scope.
Notation gw_tbl_19 := (gw_ent (@Qe1A.Mq6.rHAG_stmt segs base RATP RDEBRUIJN RGOT_SSP ref_reserved RC__) (@rHAG_stmt) gw_tbl_18).
Definition ras_post2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@Qe1A.Mq6.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) (gw_ent (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) gw_tbl_19)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Ltac riprefixT := apply rimplT_from_evt.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Notation RISTF := (@ISTF_g ref_reserved).

Definition rcount_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqm.rcount_walk) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqm.rcount_walk)).
Definition rcnt2_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqm.rcnt2_walk) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqm.rcnt2_walk)).

#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

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

Definition rag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
rmrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv segs m3 /\ stk segs m3 lo (bv_unsigned sp + -144) /\
rw_cells segs m3 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rw_cells segs m3 (errno_addr tp) [C4 errv'] /\ rauxv_ok m3 (bv_unsigned sp) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
MS (mkR (Z_to_bv 64 (base + 0x1f8)) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
(wz (usage st2 sc)) (wz 4096) (wz (size_class sc * UNIT + 16)) (wz 2048) (wz (size_class sc * UNIT * cnt1)) (wz (size_class sc * UNIT * cnt1 + 16)) a6' a7'
a1 (wz cnt1) (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 pc) fc None m3 (seg_rom segs).

Definition rHMM_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
rimplT o (ag_mmap sc req k bail st2 mm cnt1) s' Q (rcnt_state (base + 0x2cc) st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Definition rHNEST_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
rimplT o (ag_nest f sc k bail st2 mm cnt1) s' Q (rcnt_state (base + 0x310) st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Hypothesis HMM : rHMM_stmt.
Hypothesis HNEST : rHNEST_stmt.

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_130 hi_136 hi_148 lo_131 lo_137 lo_149 CODE D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 ANCH_131 ANCH_137 ANCH_149 RNG_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT rmmap_entry LB AR SC RQ FIT HMM HNEST"] Lemma rhag_ok : rHAG_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_130 hi_136 hi_148 lo_131 lo_137 lo_149 CODE D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 ANCH_131 ANCH_137 ANCH_149 RNG_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT rmmap_entry LB AR SC RQ FIT HMM HNEST RATP RDEBRUIJN R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv IS ER AC MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK F0. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LO | gw_hide LO | idtac]; try gw_hide CLO; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear errv | gw_hide errv | idtac]; try gw_hide req; try gw_hide sc; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; try gw_hide st0; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; try gw_hide sp; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; try gw_hide bail; try gw_hide k; try gw_hide f.
intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
assert (CTXT : rag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.
pose proof (QULt.Mq1.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
pose proof (size_class_range sc SC) as SZR.
rewrite (ag_body_eq f sc req k bail st2 mm).
riprefixT. unfold rag_regs.
eapply evt_cut.
{ eapply (rcount_walk st2 m3 sc MR3 SC UR). gw_exact MI3. }
cbv beta. intros ms' (a2'' & a3'' & a4'' & ->).
set (size := size_class sc * UNIT).
set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
assert (C0R : 1 <= cnt0 <= 32).
{ pose proof (rcnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
subst cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
destruct (negb _); [lia|]. destruct (negb _); lia.
- apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
eapply evt_cut.
{ eapply (rcnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| gw_exact MI3]. }
cbv beta. intros ms' ->. unfold rcnt_regs.
set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
assert (EC : ag_cnt1 sc st2 = cnt1).
{ unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
apply evt_done.
destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
- pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. gw_exact X.
- pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. gw_exact X.
Qed.
End LEVEL.

End RC__1.

End G.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE Qatc QSfG QaiD Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq4 QytA Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1 QPjm.Mq4 QULt.Mq2 QFkE.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QCa8.Mq4.
Import Qy8Z.Mq3.
Import QQRC.Mqa.
Import QDXD.Mq3.
Import Qe1A.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Ql2m.Mq3 QGeV Qatc QSfG.Mq2 Q7S0 QSfG QdBa.Mq2 QaiD.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition is_allzero_code (w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 : Z) : list Z :=
[0x00f57593; 0x00058463; 0x00000023; 0xffc54603; 0xffd54683; 0xffe55583; 0x00060e63; 0x00058463; 0x00000023; 0xff856583; 0x0105d613; 0x00061463; 0x00000023; 0x00459613; 0x40c50533; 0xff053703; 0x01073603; 0xff050513; 0x01f6f693; 0x00a60463; 0x00000023; 0x02073503; 0x01f57613; 0x00d67463; 0x00000023; 0x01872803; 0x00100793; 0x00d797bb; 0x00f87833; 0x00080463; 0x00000023; 0x01c72803; 0x00f877b3; 0x00078463; 0x00000023; 0xfffff7b7; 0x00f77733; w_37; 0x00073703; w_39; 0x00f70463; 0x00000023; 0x03451713; 0x03a75713; 0x02f00793; 0x02e7ea63; 0x00171793; w_47; w_48; 0x00f807b3; 0x0007d783; 0x02d78833; 0x0105f463; 0x00000023; 0x00168693; 0x02f686b3; 0x00d5f863; 0x0100006f; 0x03f00693; 0x00d70463; 0x00000023; 0x00c55693; 0x00068a63; 0x00869793; 0xfff78793; 0x00b7f463; 0x00000023; 0x00300593; 0x00a59593; 0x00b577b3; 0x00b79663; 0x00100513; 0x00008067; 0x02068a63; 0x02061863; 0x00171713; w_76; w_77; 0x00e585b3; 0x0005d603; 0xfffff5b7; 0x00b57533; 0xff050593; 0x00461513; 0x00a5b533; 0x00008067; 0x00171713; w_87; w_88; 0x00e50533; 0x00055503; 0x00451513; 0x00a53533; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 : Z).
Variables (hi_37 hi_47 hi_76 hi_87 : bv 20).
Variables (lo_39 lo_48 lo_77 lo_88 : bv 12).
Hypothesis CODE : code_at segs base (is_allzero_code w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 376.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Auipc 15 hi_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_39 : decode_any (Z_to_bv 32 w_39) = Some (Load SZ8 true 15 15 lo_39, 4%Z).
Hypothesis E_39 : is_ecall (Z_to_bv 32 w_39) = false.
Hypothesis D_47 : decode_any (Z_to_bv 32 w_47) = Some (Auipc 16 hi_47, 4%Z).
Hypothesis E_47 : is_ecall (Z_to_bv 32 w_47) = false.
Hypothesis D_48 : decode_any (Z_to_bv 32 w_48) = Some (OpImm ALU_ADD 16 16 lo_48, 4%Z).
Hypothesis E_48 : is_ecall (Z_to_bv 32 w_48) = false.
Hypothesis D_76 : decode_any (Z_to_bv 32 w_76) = Some (Auipc 11 hi_76, 4%Z).
Hypothesis E_76 : is_ecall (Z_to_bv 32 w_76) = false.
Hypothesis D_77 : decode_any (Z_to_bv 32 w_77) = Some (OpImm ALU_ADD 11 11 lo_77, 4%Z).
Hypothesis E_77 : is_ecall (Z_to_bv 32 w_77) = false.
Hypothesis D_87 : decode_any (Z_to_bv 32 w_87) = Some (Auipc 10 hi_87, 4%Z).
Hypothesis E_87 : is_ecall (Z_to_bv 32 w_87) = false.
Hypothesis D_88 : decode_any (Z_to_bv 32 w_88) = Some (OpImm ALU_ADD 10 10 lo_88, 4%Z).
Hypothesis E_88 : is_ecall (Z_to_bv 32 w_88) = false.
Hypothesis ANCH_39 : gw_anch (Z.shiftl (bv_signed hi_37) 12 + (base + 148) + bv_signed lo_39)%Z (RATP + 131968).
Hypothesis ANCH_48 : gw_anch (Z.shiftl (bv_signed hi_47) 12 + (base + 188) + bv_signed lo_48)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_77 : gw_anch (Z.shiftl (bv_signed hi_76) 12 + (base + 304) + bv_signed lo_77)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_88 : gw_anch (Z.shiftl (bv_signed hi_87) 12 + (base + 348) + bv_signed lo_88)%Z (RDEBRUIJN + 32).
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

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qe1A.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0)))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qe1A.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1)))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qe1A.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2)))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qe1A.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3)))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qe1A.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4)))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qe1A.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5)))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qe1A.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6)))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qe1A.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7)))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qe1A.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8)))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qe1A.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9)))))))).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qe1A.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_10)).
Definition rblock_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qe1A.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@QDXD.Mq3.rblock_range RIMG_HI RC__) (@rblock_range) gw_tbl_11)).

Hypothesis land_pow2_testbit : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.land_pow2_testbit) (base + -5412)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_12))) in let T := gw_fold_pcs T base (-5412)%Z [0; 244]%Z in exact T).
Hypothesis sllw1_word' : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.sllw1_word') (base + -5412)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_12))) in let T := gw_fold_pcs T base (-5412)%Z [0; 244]%Z in exact T).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rmrep_shadow_read2 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read2) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read2)).
Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_group_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_group_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_group_read)).
Definition rmrep_area_check_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_area_check_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_area_check_read)).
Definition rmrep_ctx_secret_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_ctx_secret_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_ctx_secret_read)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition RHEAP_block_range_proof : ltac:(gw_ctx_fold_ty2 (@Qe1A.RHEAP_block_range_proof) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.RHEAP_block_range_proof)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ land_pow2_testbit sllw1_word'"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ land_pow2_testbit sllw1_word' | clear - hs segs base w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay land_pow2_testbit sllw1_word'].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rallzerop_entry : Z := (base + 0x0).

Definition raz_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (res : bool) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m0 (seg_rom segs)
/\ (bv_unsigned a0 <> 0 -> res = true).
End RC__1.

Ltac st1 := step; fix_lit_store; try nrm.
Section RC__2.

#[using="w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 land_pow2_testbit sllw1_word'"] Lemma raz_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m0 : mem)
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let stride := if (maplen =? 0) || negb (last_idx =? 0) then 16 * size_class sc else maplen * 4096 - 16 in
let res := (48 <=? sc) || (stride <? 16 * size_class sc) in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes segs m0 (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes segs m0 (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes segs m0 (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes segs m0 (wa B) 8 = Some (le8 (wz G)) ->
rw_cells segs m0 G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes segs m0 (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes segs m0 (wa (RATP + 131968)) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes segs m0 (wa ((RDEBRUIJN + 32) + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
(maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
evt segs (raz_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 res)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rallzerop_entry) fc None m0 (seg_rom segs)).
Proof. clear - w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 land_pow2_testbit sllw1_word' segs RATP RDEBRUIJN base. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN.
intros until next. intros idx mword stride res HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml SC48.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
unfold rallzerop_entry.

st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }

st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.
assert (RG' : ov_read_bytes segs m0 (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. gw_exact RG. }
st1.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }

st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); gw_exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); gw_exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. gw_expose_fam RATP. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. rewrite MW2. st1.
assert (MW12 : Z.shiftr mword 12 = maplen).
{ subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia. }
assert (MWP : mword - mword mod 4096 = 4096 * maplen).
{ subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia. }
assert (L3072 : forall x, 0 <= x -> Z.land x 3072 = x mod 4096 - x mod 1024).
{ intros x Hx. assert (E : 3072 = Z.ldiff (Z.ones 12) (Z.ones 10)) by first [reflexivity | (cbn; lia)]. rewrite E.
rewrite land_ldiff_distr. rewrite !Z.land_ones by lia. rewrite Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^12) with 4096. change (2^10) with 1024.
pose proof (Z.div_mod (x mod 4096) 1024 ltac:(lia)).
replace ((x mod 4096) mod 1024) with (x mod 1024) in H; [lia|].
change 4096 with (2^12). change 1024 with (2^10). rewrite mod_mod_pow2 by lia. reflexivity. }
assert (MWC : Z.land mword 3072 = 3072 <-> 48 <= sc).
{ rewrite L3072 by lia. subst mword.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.mod_add, (Z.mod_small _ 4096) by lia.
replace (last_idx + 32 * freeable + 64 * sc + maplen * 4096) with ((last_idx + 32 * freeable + 64 * (sc mod 16)) + (sc / 16 + 4 * maplen) * 1024)
by (Z.div_mod_to_equations; lia).
rewrite Z.mod_add, (Z.mod_small _ 1024) by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia. }

assert (Kc8 : forall a3v a5v a6v,
evt segs (raz_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 res)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) (wz off16) (Z_to_bv 64 last_idx) a3v (Z_to_bv 64 sc) a5v a6v a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xf4)) fc None m0 (seg_rom segs))).
{ intros a3v a5v a6v.

assert (Ke0 : forall a5w,
evt segs (raz_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 res)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) (wz off16) (Z_to_bv 64 last_idx) (Z_to_bv 64 maplen) (Z_to_bv 64 sc) a5w a6v a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x10c)) fc None m0 (seg_rom segs))).
{ intros a5w.

st1. st1. st1. rewrite ?wz_unsigned by lia. st1. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by lia.
2:{
st1. st1. apply evt_done. unfold raz_post. do 7 eexists. split; [reflexivity|].
intros _. unfold res. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; apply MWC; gw_exact K8). reflexivity. }
assert (SC48' : sc < 48) by (destruct (Z.lt_ge_cases sc 48) as [Hl|Hl]; [gw_exact Hl| exfalso; apply K8, MWC, Hl]).
specialize (RS SC48'). pose proof (size_class_range sc ltac:(lia)) as SZ.

assert (K2c : evt segs (raz_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 res)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) (Z_to_bv 64 3072) (Z_to_bv 64 last_idx) (Z_to_bv 64 maplen) (Z_to_bv 64 sc)
(Z_to_bv 64 (Z.land mword 3072)) a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x158)) fc None m0 (seg_rom segs))).
{
st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1.
replace ((RDEBRUIJN + 32) + sc * 2) with ((RDEBRUIJN + 32) + 2 * sc) by (gw_expose_fam RDEBRUIJN; lia).
change (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) with (wa ((RDEBRUIJN + 32) + 2 * sc)).
st1. st1. st1. st1. apply evt_done. unfold raz_post. do 7 eexists. split; [reflexivity|].
intros NZ. exfalso. apply NZ. zsimp. rewrite ?wz_unsigned, ?unsigned_lit by lia. unfold b2z. rewrite Z.ltb_irrefl. reflexivity. }
st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia; [gw_exact K2c|].
st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia; [gw_exact K2c|].

st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1.
replace ((RDEBRUIJN + 32) + sc * 2) with ((RDEBRUIJN + 32) + 2 * sc) by (gw_expose_fam RDEBRUIJN; lia).
change (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) with (wa ((RDEBRUIJN + 32) + 2 * sc)).
st1. st1. st1. rewrite land_pgmask by lia. rewrite ?(wz_unsigned mword), MWP by lia. st1. st1.
rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. st1. st1.
apply evt_done. unfold raz_post. do 7 eexists. split; [reflexivity|].
intros NZ. unfold res. apply orb_true_intro. right. apply Z.ltb_lt.
unfold stride. replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite (proj2 (Z.eqb_eq _ _) Kl). cbn [orb negb].
revert NZ. zsimp. rewrite ?unsigned_lit by lia. unfold b2z. destruct (Z.ltb_spec (4096 * maplen + -16) (size_class sc * 16)); [lia|].
intros NZ. exfalso. apply NZ. reflexivity. }

st1. rewrite ?wz_unsigned, MW12 by lia. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- apply Ke0.
-
st1. st1. st1. if_cases Ko; zify_cond Ko.
2:{ exfalso. specialize (Hml Km). rewrite Z.shiftl_mul_pow2 in Ko by lia. change (2^8) with 256 in Ko. change 18446744073709551615 with (Z.ones 64) in Ko.
rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in Ko by lia. rewrite Z.mod_small in Ko by lia. lia. }
apply Ke0. }

st1. if_cases K8; zify_cond K8.
-  specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
apply Kc8.
- specialize (RS ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).

st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1.
replace ((RDEBRUIJN + 32) + sc * 2) with ((RDEBRUIJN + 32) + 2 * sc) by (gw_expose_fam RDEBRUIJN; lia).
change (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) with (wa ((RDEBRUIJN + 32) + 2 * sc)).
pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }

st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. apply Kc8.
Qed.

#[using="RDEBRUIJN w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RDEBRUIJN ROM_RSIZE_CLASSES land_pow2_testbit sllw1_word'"] Lemma raz_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m0 : mem)
st (p : aptr) r g gh ar (b3 lo8 hi : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo8 + 256 * hi in
let idx := Z.land b3 31 in
let base_ := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
rmrep st m0 -> mem_inv segs m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base_ = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base_ ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
(m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
evt segs (raz_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 (is_allzero_ctrl mr))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rallzerop_entry) fc None m0 (seg_rom segs)).
Proof. clear - RDEBRUIJN w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RDEBRUIJN ROM_RSIZE_CLASSES land_pow2_testbit sllw1_word' segs.
intros until hi. cbv zeta. intros MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48.
set (po := snd p) in *. set (off16 := lo8 + 256 * hi) in *. set (idx := Z.land b3 31) in *.
set (base_ := aadd p (- (UNIT * off16) - UNIT)) in *. set (mr := get_meta_rec st g) in *.
set (strideW := if (m_maplen mr =? 0) || negb (m_last_idx mr =? 0) then 16 * size_class (m_sizeclass mr) else m_maplen mr * 4096 - 16).
assert (STR : get_stride mr = strideW).
{ unfold strideW, get_stride, UNIT. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn; lia. }
assert (RES : is_allzero_ctrl mr = (48 <=? m_sizeclass mr) || (strideW <? 16 * size_class (m_sizeclass mr))).
{ unfold is_allzero_ctrl. rewrite STR. unfold UNIT. reflexivity. }
rewrite RES.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). unfold alloc_ceiling in BC.

destruct (rmrep_shadow_read st m0 (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
destruct (rmrep_shadow_read st m0 (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
destruct (rmrep_shadow_read2 st m0 (fst p) r (po - 2) lo8 hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; gw_exact C1)) as (R2 & LO & HI).
rewrite <- le2_lohi in R2 by lia.

destruct (rmrep_group_read st m0 base_ gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.

pose proof (rmrep_meta_chunk st m0 g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.

pose proof (rmrep_area_check_read st m0 (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
pose proof (rmrep_ctx_secret_read st m0 MR) as RC.

destruct (WG base_ gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base_ aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
assert (HB : conc st base_ = (r_base r + po) - 16 * off16 - 16).
{ unfold base_. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
destruct MS as (aa & ara & k & Ha & Hkk & Eg).
destruct (WA aa ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
assert (HG : conc st g = r_base rg + snd aa + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st aa rg Hrg). reflexivity. }
destruct (WR (fst aa) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
assert (Hm : (r_base rg + snd aa + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd aa + (24 + 40 * k)) with ((24 + 40 * k) + (snd aa / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst aa) _ rg Hrg).
replace ((snd aa + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd aa + (24 + 40 * k)) with ((24 + 40 * k) + (snd aa / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
assert (MW : meta_word mr = m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) by first [reflexivity | (cbn; lia)].
unfold UNIT, IB in *.
pose proof (raz_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0
(r_base r + po) (conc st g) (conc st base_) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
(pw st (m_prev mr)) (pw st (m_next mr))) as W.
cbv zeta in W. rewrite <- MW in W. fold strideW in W. apply W; clear W; try eassumption; try lia.
all: try (replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia; gw_exact R4).
all: try (replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia; gw_exact R3).
all: try (replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia; gw_exact R2).
all: try (intros Hlt; apply rsize_classes_read; [gw_exact MI | lia]).
all: try (pose proof (round_up_pg_ge (r_len r)); lia).
Qed.

Definition razH_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (s : PState) (c : cptr) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m0 (seg_rom segs)
/\ (bv_unsigned a0 <> 0 -> exists g idx, (s_slots (ps_m s)) !! c = Some (g, idx) /\ is_allzero_ctrl (get_meta_rec (ps_m s) g) = true).

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RDEBRUIJN LAY_win_1 LAY_win_2 ROM_RSIZE_CLASSES LAY_ref_reserved land_pow2_testbit sllw1_word'"] Lemma raz_heap : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
(s : PState) (LB : list block) (c : cptr) (pid A n0 : Z),
RHEAP s LB m -> In ((c, pid), A, n0) LB -> mem_inv segs m -> a0 = Z_to_bv 64 A ->
evt segs (razH_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s c)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RDEBRUIJN LAY_win_1 LAY_win_2 ROM_RSIZE_CLASSES LAY_ref_reserved land_pow2_testbit sllw1_word' segs.
intros until n0. intros HP Hin MI A0.
pose proof (RHEAP_block_range_proof _ _ _ _ HP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR.
destruct BR as (A0p & A16 & N00 & AC & AIMG). pose proof AC as ACv. unfold alloc_ceiling in ACv.
destruct HP as (st & LB0 & PERM & Hst & RM & [BL AR]).
assert (Hin0 : In ((c, pid), A, n0) LB0) by (eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; gw_exact PERM| gw_exact Hin]).
pose proof (QNAo.Mq2.areach_cinv_proof _ _ AR) as C.
destruct (Q3o5.Mq1.areach_inv _ st LB0 AR) as (L & LS & BL0 & INV & LIVE & RESV & SEC & CR).
destruct (Q3o5.Mq1.Forall2_In_l _ _ _ _ CR Hin0) as (k & Hk & (K1 & K2 & K3)).
destruct k as [[c' off] n0']. cbn [blk_slot blk_size blk_addr bslot bsize boff fst snd] in K1, K2, K3. subst n0' c'.
destruct (block_facts x0 st L BL0 LS INV c off n0 Hk) as (g & bm & i & ai & aa & ar & ka & BF).
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) ((c, pid), A, n0) Hin0) as BK.
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) ((c, pid), A, n0) Hin0) as BC.
destruct BK as [(g' & i' & b & SL & HB & FB & Ii & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
cbn [blk_slot blk_size blk_addr fst snd] in SL, HB, FB, NFR, OA, OS, OK, HK, NG, SZ.
assert (Eg : g' = g /\ i' = i) by (rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) in SL; inversion SL; auto). destruct Eg as [-> ->].
assert (off' = off) as -> by (rewrite K3 in OA; unfold UNIT in OA; lia).
clear OA.
set (pf := aadd c (UNIT * off)) in *.
pose proof (ci_gmetas _ _ C b g HB) as GO.
destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
pose proof RM as (WF & CX & GL & ARr & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
destruct (ki_slts _ _ _ (KINV_of_CINV _ _ C) _ _ _ SL) as (GMg & Ec & _).
destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). cbn [aadd fst snd] in C3, C2, C1, OFF.
assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; gw_exact FB).
assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; rewrite <- FB; gw_exact Hr).
assert (Sp : snd pf = snd c + 16 * off) by (unfold pf, UNIT; cbn; lia).
assert (HAp : A = r_base r + snd pf) by (rewrite K3, Cc, Sp; unfold UNIT; lia).
assert (Sc : snd c = snd b + 16 + get_stride (get_meta_rec st g) * i).
{ rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
{ unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
assert (P16m : snd pf mod 16 = 0).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 O0 RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RDEBRUIJN LAY_win_1 LAY_win_2 ROM_RSIZE_CLASSES LAY_ref_reserved land_pow2_testbit sllw1_word' segs. Z.div_mod_to_equations. lia. }
assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
unfold UNIT, IB in *.
assert (16 * off + 16 <= stq) by (clear - OS SZ SM O0 S16 RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_37 w_39 w_47 w_48 w_76 w_77 w_87 w_88 hi_37 hi_47 hi_76 hi_87 lo_39 lo_48 lo_77 lo_88 CODE D_37 E_37 D_39 E_39 D_47 E_47 D_48 E_48 D_76 E_76 D_77 E_77 D_87 E_87 D_88 E_88 ANCH_39 ANCH_48 ANCH_77 ANCH_88 RNG_RDEBRUIJN LAY_win_1 LAY_win_2 ROM_RSIZE_CLASSES LAY_ref_reserved land_pow2_testbit sllw1_word' segs; Z.div_mod_to_equations; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
clear SIM SM B16 RBAL. change (frozen (snd pf mod 16 = 0)) in P16m.
assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
{ unfold aadd. apply injective_projections; cbn; [gw_exact Fp| unfold UNIT in *; lia]. }
destruct HB as [gai Hgh].
set (stride := get_stride (get_meta_rec st g)) in *.
eapply evt_mono.
{ eapply (raz_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
st pf r g (mkGhdr (Some g) gai) ar v3 lo8 hi);
first [gw_exact RM | gw_exact MI | gw_exact Kr | idtac].
all: rewrite ?EB, ?V31.
- rewrite Fp. gw_exact Hr.
- rewrite A0, HAp. apply unsigned_lit. unfold alloc_ceiling in RBC. pose proof (round_up_pg_ge (r_len r)). lia.
- gw_exact P16m.
- rewrite Sp, Sc. lia.
- unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
- gw_exact PHI.
- replace (snd pf - 4) with (snd c + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. gw_exact OK.
- replace (snd pf - 3) with (snd c + UNIT * off + - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. gw_exact C3.
- replace (snd pf - 2) with (snd c + UNIT * off + - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. gw_exact C2.
- replace (snd pf - 1) with (snd c + UNIT * off + - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. gw_exact C1.
- gw_exact Hgh.
- reflexivity.
- exact (go_slot _ _ _ GO).
- destruct (go_slot _ _ _ GO) as (a9 & ara & k9 & Ha & Hk9 & ->). destruct (WA a9 ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
- exact (go_mem _ _ _ GO).
- destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em). rewrite Em, (area_of_mslot aa ka Hal Hka). gw_exact Ha.
- destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em). gw_exact Hck.
- exact (go_avail _ _ _ GO).
- exact (go_freed _ _ _ GO).
- exact (proj2 (proj2 (proj2 (ki_cx _ _ _ (KINV_of_CINV _ _ C))))).
- lia.
- rewrite (go_freeable _ _ _ GO). lia.
- pose proof (go_sc _ _ _ GO). lia.
- pose proof (go_maplen _ _ _ GO). lia.
- lia.
- exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF).
- exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF).
-
intros Hsc. destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc' & Hle & Hst')| E63].
2:{ change (Qatc.MR st g) with (get_meta_rec st g) in E63. lia. }
change (Qatc.MR st g) with (get_meta_rec st g) in Hsc', Hle, Hst'. fold stride in Hle, Hst'.
pose proof (size_class_bound _ Hsc') as SCB.
pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFFb.
assert (Aq : stride = 16 * size_class (m_sizeclass (get_meta_rec st g)) \/ m_last_idx (get_meta_rec st g) = 0) by (unfold UNIT in Hst'; tauto).
assert (Bq : stride <= 16 * size_class (m_sizeclass (get_meta_rec st g)) \/ 292 <= size_class (m_sizeclass (get_meta_rec st g))).
{ destruct Hle as [Hle|H28]; [left; unfold UNIT in Hle; gw_exact Hle| right; apply size_class_28; lia]. }
unfold pf in OFF. cbn [aadd snd] in OFF. unfold UNIT, IB in OS. fold stride in OS.
eapply (guard16_arith _ stride i off n0 (lo8 + 256 * hi) (m_last_idx (get_meta_rec st g))); try eassumption; lia.
- intros H48. pose proof (go_sc _ _ _ GO). lia.
- intros NM. destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [Bz GE].
unfold gend, cnt_of, sstart, gbase in GE. change (Qatc.MR st g) with (get_meta_rec st g) in GE, Bz. rewrite (go_mem _ _ _ GO) in GE.
cbn [default id snd] in GE. fold stride in GE.
pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFFb.
replace (m_maplen (get_meta_rec st g) * 256) with (m_maplen (get_meta_rec st g) * 4096 / 16) by (rewrite <- (Z.div_mul (m_maplen (get_meta_rec st g) * 256) 16) by lia; f_equal; lia).
unfold UNIT in S16. unfold pf in OFF. cbn [aadd snd] in OFF. unfold UNIT, IB in OS. fold stride in OS.
eapply (guard17_arith stride i off n0 (lo8 + 256 * hi) (m_last_idx (get_meta_rec st g))); try lia.
unfold UNIT in GE. lia.
- intros HC. pose proof (go_sc _ _ _ GO). lia. }
cbv beta. intros ms' (w0 & w1 & w2 & w3 & w4 & w5 & w6 & -> & RES).
unfold razH_post. do 7 eexists. split; [reflexivity|].
intros NZ. exists g, i. rewrite <- Hst. split; [rewrite s_slots_strip; gw_exact SL| exact (RES NZ)].
Qed.

End RC__2.

End G.
End Mq8.
From Stdlib Require Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Q2qa.Mq1 Qy5Y.Mq4 Q4J3.Mq3 QPjm.Mq4 QULt.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Ql2m.Mq3 QGeV QSfG.Mq2.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq3.
Import Qe1A.
Import QkTt.Mq6.
Import Q91D.Mq8.
Import QVbl.Mq3.
Import QkTt.Mq2.
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

Definition realloc_code (w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 : Z) : list Z :=
[0x0040006f; 0x04050863; 0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x01613023; 0xffffe637; 0xfff6061b; 0x00165613; 0x02c5e263; w_15; 0x00050593; 0x00000513; 0x00c00613; 0x00c5a023; 0x3cc0006f; 0x00058513; 0x8ccff06f; 0x00f57613; 0x00060463; 0x00000023; 0xffc54603; 0xffd54883; 0xffe55803; 0x00060e63; 0x00080463; 0x00000023; 0xff856803; 0x01085613; 0x00061463; 0x00000023; 0x00481613; 0x40c506b3; 0xff06b483; 0x0104b603; 0xff068693; 0x01f8f293; 0x00d60463; 0x00000023; 0x0204b703; 0x01f77313; 0x00537463; 0x00000023; 0x0184a783; 0x00100693; 0x005696bb; 0x00d7f7b3; 0x00078463; 0x00000023; 0x01c4a783; 0x00d7f6b3; 0x00068463; 0x00000023; 0xfffff6b7; w_59; 0x00d4f6b3; 0x0006b683; w_62; 0x00f68463; 0x00000023; 0x03471693; 0x02f00e13; w_67; 0x03a6d693; 0x00169393; w_70; 0x02de6463; 0x00778e33; 0x000e5e03; 0x025e0eb3; 0x01d87463; 0x00000023; 0x00128e93; 0x03ce8e33; 0x01c87863; 0x0100006f; 0x03f00e13; 0x01c68463; 0x00000023; 0x00c75e13; 0x000e0c63; 0x008e1e13; 0xfffe0e13; 0x010e7463; 0x00000023; 0x1e030663; 0x007783b3; 0x0003d803; 0x00481813; 0x025802b3; 0x0a000e13; 0x005602b3; 0x01028313; 0x01030833; 0xffc80293; 0x0058d393; 0x03c8e663; 0x00500893; 0x01138463; 0x00000023; 0xff886383; 0x00400893; 0x0078e463; 0x00000023; 0xff784883; 0x00088463; 0x00000023; 0x40a288b3; 0x0078f463; 0x00000023; 0x40728933; 0x00094383; 0x00038463; 0x00000023; 0x0002c383; 0x00038463; 0x00000023; 0x000203b7; 0xfeb38e1b; 0x08be6c63; 0x08b8ea63; 0x00358613; 0x09d00713; 0x00465613; 0x18e5e063; 0x00160713; 0x077cb8b7; 0x0027531b; 0x00e36333; 0x0017571b; 0x00e36333; 0x0023531b; 0x00e36733; 0x00475313; 0x00e36733; 0x00875313; 0x00e36733; 0x00170313; 0xfff74713; 0x00e37733; w_145; 0x53188893; w_147; 0x03170733; 0x01b7571b; 0x00e30733; 0x00074703; 0x00271713; 0x07c74713; 0x07900893; 0x40e888b3; 0x00189893; 0x011788b3; 0x0008d883; 0x0f166463; 0x07a00893; 0x0e40006f; 0xfec3839b; 0x1075e063; 0x03000793; 0x0ef6ec63; 0x03f00793; 0x00f68463; 0x00000023; 0x00001a37; 0x406509b3; 0xfffff6b7; 0xfffa0a1b; 0x014587b3; 0x013787b3; 0x01478793; 0x00d7f433; 0x00d77733; 0x02870663; 0x00100693; 0x00050a93; 0x00060513; 0x00058b13; 0x00070593; 0x00040613; w_185; 0x000b0593; 0x00050613; 0x000a8513; 0xfff00693; 0x08d60a63; 0x0204b703; 0x01360533; 0x008606b3; 0x01050513; 0x014777b3; 0xffc68713; 0x00a585b3; 0x0087e7b3; 0x40b7083b; 0x00c4b823; 0x02f4b023; 0xfe068e23; 0x0c080863; 0x40b7063b; 0x40c005bb; 0x00b70733; 0x00500593; 0x00070023; 0x0cb64063; 0xfe068ba3; 0xfec6ac23; 0x0b80006f; 0xfffff837; 0x01077833; 0xff080813; 0xe19ff06f; 0x07800893; 0x40e88733; 0x00171893; 0x011787b3; 0x0007d783; 0x00f63633; 0x00164613; 0x00c76633; 0x0016061b; 0x04d65263; 0x00050493; 0x00058413; 0x00058513; 0xd8dfe0ef; 0x08050063; 0x409905b3; 0x00040613; 0x00b46463; 0x00058613; 0x00050413; 0x00048593; w_238; 0x00048513; 0xbd8fe0ef; 0x00040513; 0x0540006f; 0x00a585b3; 0x40b2863b; 0x02060463; 0x40b2863b; 0x40c005bb; 0x00b282b3; 0x00500593; 0x00028023; 0x00b64c63; 0xfe080ba3; 0xfec82c23; 0x0100006f; 0x00000593; 0x0080006f; 0x00060593; 0xffd54603; 0x01f67613; 0x00559593; 0x00c5e5b3; 0xfeb50ea3; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x00013b03; 0x04010113; 0x00008067]%Z.

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
Let rfree_entry := (base + -6248)%Z.
Let rmalloc_entry := (base + -3804)%Z.
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

Definition memcpy_post : ltac:(gw_rebind_ty (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QVbl.Mq3.memcpy_post segs) (@memcpy_post) gw_tbl_0).
Definition rclient_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_range RATP RGOT_SSP RIMG_HI RDATA_LO) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_range RATP RGOT_SSP RIMG_HI RDATA_LO) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq3.rclient_range RATP RGOT_SSP RIMG_HI RDATA_LO) (@rclient_range) gw_tbl_1).
Definition rclient_write_ok : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_write_ok RATP RGOT_SSP RIMG_HI RDATA_LO RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_write_ok RATP RGOT_SSP RIMG_HI RDATA_LO RC__) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qe1A.rclient_write_ok RATP RGOT_SSP RIMG_HI RDATA_LO RC__) (@rclient_write_ok) (gw_ent (@QDXD.Mq3.rclient_write_ok RATP RGOT_SSP RIMG_HI RDATA_LO RC__) (@rclient_write_ok) gw_tbl_2)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@Qe1A.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_3)))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qe1A.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_4)))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qe1A.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_5)))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qe1A.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_6)))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qe1A.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_7)))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qe1A.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_8)))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qe1A.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_9)))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qe1A.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_10)))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QkTt.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qe1A.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_11)))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QkTt.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qe1A.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_12)))))).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QkTt.Mq2.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@QkTt.Mq6.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@Qe1A.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_13)))).
Definition raddr_exposed : ltac:(gw_rebind_ty (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QkTt.Mq6.raddr_exposed segs RC__) (@raddr_exposed) (gw_ent (@QDXD.Mq3.raddr_exposed segs RC__) (@raddr_exposed) gw_tbl_14)).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QkTt.Mq2.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QkTt.Mq6.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_15)))).
Definition rblock_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@QkTt.Mq2.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@QkTt.Mq6.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@Qe1A.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@QDXD.Mq3.rblock_range RIMG_HI RC__) (@rblock_range) gw_tbl_16)))).
Definition ralloc_static : ltac:(gw_rebind_ty (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@QkTt.Mq2.ralloc_static RATP) (@ralloc_static) (gw_ent (@QkTt.Mq6.ralloc_static RATP) (@ralloc_static) (gw_ent (@QDXD.Mq3.ralloc_static RATP) (@ralloc_static) gw_tbl_17))).
Definition rclient_addr : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QkTt.Mq2.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) (gw_ent (@QkTt.Mq6.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) (gw_ent (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) gw_tbl_18))).
Definition rheap_pres : ltac:(gw_rebind_ty (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@QkTt.Mq2.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) (gw_ent (@QkTt.Mq6.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) (gw_ent (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) gw_tbl_19))).
Definition rmalloc_post : ltac:(gw_rebind_ty (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QkTt.Mq6.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) (gw_ent (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) gw_tbl_20)).
Definition rmalloc_impl_stmt : ltac:(gw_rebind_ty (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) (@rmalloc_impl_stmt) gw_tbl_21).
Definition rfree_post : ltac:(gw_rebind_ty (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@QkTt.Mq6.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rfree_post) (gw_ent (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rfree_post) gw_tbl_22)).
Definition rfree_impl_stmt : ltac:(gw_rebind_ty (@QkTt.Mq6.rfree_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_entry RC__) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QkTt.Mq6.rfree_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_entry RC__) constr:(gw_tbl_23)).
Notation gw_tbl_24 := (gw_ent (@QkTt.Mq6.rfree_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_entry RC__) (@rfree_impl_stmt) gw_tbl_23).
Definition rrealloc_post : ltac:(gw_rebind_ty (@QkTt.Mq2.rrealloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QkTt.Mq2.rrealloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_24)).
Notation gw_tbl_25 := (gw_ent (@QkTt.Mq2.rrealloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rrealloc_post) gw_tbl_24).

Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs e_memcpy) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in exact T).

Definition rimplM_membed_sbind : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplM_membed_sbind) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplM_membed_sbind)).
#[global] Arguments rimplM_membed_sbind {R}%_type_scope {S}%_type_scope T F%_function_scope s Q1%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rauxv_ok_frame : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_frame) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_frame)).

Definition rheap_pres_trans : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq3.rheap_pres_trans) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq3.rheap_pres_trans)).
Definition rheap_pres_weaken : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq3.rheap_pres_weaken) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq3.rheap_pres_weaken)).
Definition rheap_pres_rw_cells : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq3.rheap_pres_rw_cells) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq3.rheap_pres_rw_cells)).

Definition RHEAP_blocks_nodup_proof : ltac:(gw_ctx_fold_ty2 (@Qe1A.RHEAP_blocks_nodup_proof) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.RHEAP_blocks_nodup_proof)).
Definition RHEAP_block_range_proof : ltac:(gw_ctx_fold_ty2 (@Qe1A.RHEAP_block_range_proof) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.RHEAP_block_range_proof)).
Definition RHEAP_blocks_disjoint_proof : ltac:(gw_ctx_fold_ty2 (@Qe1A.RHEAP_blocks_disjoint_proof) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.RHEAP_blocks_disjoint_proof)).
Definition RHEAP_frame_proof : ltac:(gw_ctx_fold_ty2 (@Qe1A.RHEAP_frame_proof) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.RHEAP_frame_proof)).

Definition rmalloc_membed : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq6.rmalloc_membed) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq6.rmalloc_membed)).
Definition rfree_membed : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq6.rfree_membed) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq6.rfree_membed)).

Definition implM_membed_set_m : ltac:(gw_ctx_fold_ty2 (@Q91D.Mq8.implM_membed_set_m) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q91D.Mq8.implM_membed_set_m)).
#[global] Arguments implM_membed_set_m {R}%_type_scope t s cs Q%_function_scope ms _.

#[using="RDEBRUIJN rerrno_loc_entry rmremap_entry e_memcpy RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_15 E_15 D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 D_145 E_145 D_147 E_147 D_185 E_185 D_238 E_238 ANCH_62 ANCH_70 ANCH_147 LINK_15 LINK_185 LINK_238 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rfree_entry rmalloc_entry rmremap_entry memcpy_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="base rvm_wait_entry rfree_entry rmalloc_entry rmremap_entry"] Lemma rheap_pres_of_munch LB SP W m m' :
munch W m m' -> wmono segs m m' ->
(forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
rheap_pres LB SP m m'.
Proof. clear - base rvm_wait_entry rfree_entry rmalloc_entry rmremap_entry segs LB SP W m m'.
intros MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.

#[using="Type"] Lemma lb_remove_cons_neq p b LB : bptr_eqb (blk_id b) p = false -> lb_remove p (b :: LB) = b :: lb_remove p LB.
Proof. clear - p b LB. intros H. unfold lb_remove. cbn. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma bptr_eqb_false_of_neq (p q : bptr) : p <> q -> bptr_eqb p q = false.
Proof. clear - p q.
intros NE. destruct (bptr_eqb p q) eqn:E; [|reflexivity]. exfalso. apply NE.
unfold bptr_eqb in E. apply andb_prop in E. destruct E as [E1 E2].
apply aptr_eqb_eq in E1. apply Z.eqb_eq in E2. destruct p, q; cbn in *; congruence.
Qed.

#[using="Type"] Lemma In_lb_remove p b LB : In b (lb_remove p LB) -> In b LB /\ bptr_eqb (blk_id b) p = false.
Proof. clear - p b LB.
intros H. unfold lb_remove in H. apply (proj2 (list_elem_of_In _ _)) in H. apply list_elem_of_filter in H as [H1 H2].
split; [apply (proj1 (list_elem_of_In _ _)); gw_exact H2|]. destruct (bptr_eqb (blk_id b) p); [destruct H1| reflexivity].
Qed.

Definition rr_general (cs : mstate) (slot : cptr) (n : Z) : QUZl.M (mstate * option rr_where) :=
sbind (cmalloc cs n) (fun x__ => match x__ with (cs1, r) =>
match r with
| None => ret (cs1, @None rr_where)
| Some c => sbind (cfree cs1 (Some slot)) (fun cs2 => ret (cs2, Some (RRNew (c, fresh_off cs1 c n))))
end end).

Definition rr_conv (slot : cptr) (off : Z) (x : mstate * option rr_where) : option bptr :=
match snd x with
| None => None
| Some RRSame => Some (slot, off)
| Some (RRNew b) => Some b
end.

#[using="w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 CODE"] Lemma rr_epilogue : forall (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(ra v0 v1 v2 v3 v4 v5 v6 : word) F fc (m : mem) Q,
rw_cells segs m (bv_unsigned sp + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra] ->
Q (MS (mkR ra sp gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)) ->
evt segs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x41c)) fc None m (seg_rom segs)).
Proof. clear - w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 CODE segs base.
intros until Q. intros FR HQ. pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. step. step. step. step. step. step. step. step.
step. apply evt_done.  gw_exact HQ.
Qed.

Section GENERAL.
Hypothesis RMI : rmalloc_impl_stmt.
Hypothesis RFI : rfree_impl_stmt.

#[using="gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 joff_238 e_memcpy CODE BASE4 BASER D_238 E_238 LINK_238 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved memcpy_spec rfree_entry rmalloc_entry rmremap_entry RMI RFI"] Lemma rr_general_spec :
forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word)
(t0v t1v t2v a2v a3v a4v a5v a6v a7v t3v t4v s1v : word) (rax s0x s3x s4x s5x s6x t5x t6x : word)
(F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
(s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old junk0 : list byte),
RHEAP s LB m1 -> In (p, A, n0) LB ->
rw_cells segs m1 A [CB (Z.to_nat n0) (old ++ junk0)] ->
rauxv_ok m1 B -> bv_unsigned sp <= B ->
stk segs m1 lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
rw_cells segs m1 (errno_addr tp) [C4 errv] ->
mem_inv segs m1 ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
rw_cells segs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rheap_pres LB (bv_unsigned sp) m m1 ->
implM segs (membed (rr_general (ps_m s) (fst p) n)) s
(fun x s' ms' => evt segs (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m
(rr_conv (fst p) (real_off (ps_m s) (fst p) A) x) (set_m (fst x) s')) ms')
(MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0v t1v t2v s0x s1v a0 a1 a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 (A + n0)) s3x s4x s5x s6x s7 s8 s9 s10 s11 t3v t4v t5x t6x)
F (Z_to_bv 64 (base + 0x38c)) fc None m1 (seg_rom segs)).
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 joff_238 e_memcpy CODE BASE4 BASER D_238 E_238 LINK_238 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved memcpy_spec rfree_entry rmalloc_entry rmremap_entry RMI RFI segs base RATP. gw_expose_fam RATP.
intros until junk0. intros HP Hin OLD AV SB ST CLO LO ERR MI TP A0 A1 N FR PRES01. subst a0 a1.
unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RHEAP_block_range_proof _ _ _ _ HP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR.
destruct BR as (A0p & A16 & N00 & AC & AIMG). pose proof AC as ACv. unfold alloc_ceiling in ACv.
pose proof (rw_cells_CB_length _ _ _ _ _ OLD) as LOLD.
unfold rr_general.

eapply implM_evt.
{ step. step. step. step. apply evt_done. lazymatch goal with |- ?P ?ms => unify P (fun x : machine_state => x = ms) end. reflexivity. }
cbv beta. intros ms1 ->. change (Z_to_bv 64 rmalloc_entry) with (Z_to_bv 64 rmalloc_entry).

eapply rimplM_membed_sbind.
{ eapply (rmalloc_membed RMI); try eassumption; try reflexivity; rewrite ?unsigned_lit by lia; unfold RMALLOC_STACK; try lia.
replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST by lia. gw_exact ST. }
cbv beta. intros [cs1 r] s' ms' PM. cbn [fst snd] in PM.
eapply implM_evt; [gw_exact PM|]. cbv beta. clear PM. intros ms2 PM.
destruct PM as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> &
MI2 & ST2 & ERR2 & AUX2 & PRES2 & PSF2 & PSO2 & CASE).
rewrite unsigned_lit in ST2, PRES2 by lia.
try g_ret_pc_any.

assert (FR2 : rw_cells segs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [gw_exact PRES2| gw_exact FR|]. left. lia. }
assert (PRES02 : rheap_pres LB (bv_unsigned sp) m m2).
{ eapply rheap_pres_trans; [gw_exact PRES01|]. eapply rheap_pres_weaken; [gw_exact PRES2| lia| auto]. }
destruct r as [c'|].
-
cbn [cm_conv] in CASE. destruct CASE as (A' & junk & -> & BR' & HP2 & NEW & _).
pose proof BR' as (A'0 & A'16 & N0' & A'C & A'IMG). unfold alloc_ceiling in A'C.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ (c', fresh_off cs1 c' n, A', n) (p, A, n0) HP2 ltac:(left; reflexivity) ltac:(right; gw_exact Hin)) as DISJ.
cbn [blk_id blk_addr blk_size fst snd] in DISJ.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HP2) as ND. cbn [map blk_id fst] in ND.
assert (NEQ : (c', fresh_off cs1 c' n) <> p).
{ intros E. apply NoDup_cons_iff in ND as [NI _]. apply NI. rewrite E. apply in_map_iff. exists (p, A, n0). split; [reflexivity| gw_exact Hin]. }
specialize (DISJ ltac:(gw_exact NEQ)).

assert (OLD2 : rw_cells segs m2 A [CB (Z.to_nat n0) (old ++ junk0)]).
{ eapply rheap_pres_rw_cells; [gw_exact PRES2| gw_exact OLD|]. right; right. exists (p, A, n0). cbn -[Z.of_nat]. split; [gw_exact Hin| lia]. }
set (len := Z.min n n0).
assert (LEN : 0 <= len <= n /\ len <= n0) by (subst len; lia).

pose proof (rw_cells_split_CB segs m2 A [] (Z.to_nat n0) (old ++ junk0) [] [Z.to_nat len; Z.to_nat n0 - Z.to_nat len]%nat OLD2 ltac:(cbn; lia)) as OLDs.
cbn [app mk_CB_cells] in OLDs.
set (src := firstn (Z.to_nat len) (old ++ junk0)) in *.
assert (LSRC : length src = Z.to_nat len) by (subst src; rewrite firstn_length; lia).
pose proof (rw_cells_bytes_at _ _ _ _ OLDs) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
apply bytes_at_app in SRCB as [SRCB _].
pose proof (rw_cells_CB_length _ _ _ _ _ NEW) as LJ.
pose proof (rw_cells_split_CB segs m2 A' [] (Z.to_nat n) junk [] [Z.to_nat len; Z.to_nat n - Z.to_nat len]%nat NEW ltac:(cbn; lia)) as NEWs.
cbn [app mk_CB_cells] in NEWs.
change (rw_cells segs m2 A' ([CB (Z.to_nat len) (firstn (Z.to_nat len) junk)] ++ [CB (Z.to_nat n - Z.to_nat len) (firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk))])) in NEWs.
apply rw_cells_app in NEWs as [NEWs NEWt]. cbn [cells_size csize] in NEWt. rewrite Nat.add_0_r in NEWt.

eapply (implM_evt segs _ _ _ (fun msF => exists w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 m3,
msF = MS (mkR (Z_to_bv 64 (base + 0x3c4)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp w0 w1 w2 (Z_to_bv 64 A') (Z_to_bv 64 A)
(Z_to_bv 64 A) wa1 wa2 wa3 wa4 wa5 wa6 wa7 (Z_to_bv 64 (A + n0)) s3x s4x s5x s6x s7 s8 s9 s10 s11 w3 w4 w5 w6)
F (Z_to_bv 64 rfree_entry) fc None m3 (seg_rom segs)
/\ munch [(A', A' + len)] m2 m3 /\ wmono segs m2 m3 /\ mem_inv segs m3 /\ rw_cells segs m3 A' [CB (Z.to_nat len) src])).
{
assert (J : forall a1w a2w, a2w = Z_to_bv 64 len ->
evt segs (fun msF => exists w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 m3,
msF = MS (mkR (Z_to_bv 64 (base + 0x3c4)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp w0 w1 w2 (Z_to_bv 64 A') (Z_to_bv 64 A)
(Z_to_bv 64 A) wa1 wa2 wa3 wa4 wa5 wa6 wa7 (Z_to_bv 64 (A + n0)) s3x s4x s5x s6x s7 s8 s9 s10 s11 w3 w4 w5 w6)
F (Z_to_bv 64 rfree_entry) fc None m3 (seg_rom segs)
/\ munch [(A', A' + len)] m2 m3 /\ wmono segs m2 m3 /\ mem_inv segs m3 /\ rw_cells segs m3 A' [CB (Z.to_nat len) src])
(MS (mkR (Z_to_bv 64 (base + 0x39c)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 n) (Z_to_bv 64 A)
(Z_to_bv 64 A') a1w a2w ra3 ra4 ra5 ra6 ra7 (Z_to_bv 64 (A + n0)) s3x s4x s5x s6x s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 (base + 0x3b0)) fc None m2 (seg_rom segs))).
{ intros a1w a2w ->.

step. step. step.
eapply evt_cut.
{ eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 src (firstn (Z.to_nat len) junk));
rewrite ?unsigned_lit by lia.
- gw_exact SRCB.
- gw_exact LSRC.
- gw_exact NEWs.
- lia.
- gw_exact MI2. }
cbv beta. intros ms3 PC.
destruct PC as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & DST3 & _).
rewrite ?unsigned_lit in MU3, DST3 by lia.
try g_ret_pc_any.

step. step. apply evt_done. do 15 eexists. split; [reflexivity|]. auto. }

step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
step. rewrite ?unsigned_lit by lia. replace (A + n0 - A) with n0 by lia.
step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
- apply J. f_equal. subst len; lia.
- step. apply J. f_equal. subst len; lia. }
cbv beta. intros msF (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & DST3).
set (bnew := ((c', fresh_off cs1 c' n), A', n) : block) in *.
assert (HP3 : RHEAP (set_m cs1 s') (bnew :: LB) m3).
{ eapply RHEAP_frame_proof; [gw_exact HP2| gw_exact MU3| gw_exact WM3|]. constructor; [|constructor].
right; right. exists bnew. split; [left; reflexivity|]. cbn. lia. }
assert (DJW : forall a k, a + k <= A' \/ A' + len <= a -> disjoint_from [(A', A' + len)] a k) by (intros a9 k9 Hk9; cbn; lia).
assert (AUX3 : rauxv_ok m3 B).
{ eapply rauxv_ok_frame; [gw_exact AUX2| gw_exact MU3| gw_exact WM3|]. constructor; [|constructor]. cbn. gw_expose_fam RATP. lia. }
assert (ST3 : stk segs m3 lo (bv_unsigned sp - 64)).
{ eapply stk_transport_disjoint; [gw_exact ST2| gw_exact MU3| gw_exact WM3|]. apply DJW. lia. }
assert (ERR3 : rw_cells segs m3 (errno_addr tp) [C4 errv2]).
{ eapply rw_cells_transport; [gw_exact ERR2| gw_exact MU3| gw_exact WM3|]. apply DJW. rewrite TP. gw_expose_fam RATP. rewrite unsigned_lit by lia. cbn. lia. }
assert (FR3 : rw_cells segs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [gw_exact FR2| gw_exact MU3| gw_exact WM3|]. apply DJW. cbn. lia. }
assert (NEWt3 : rw_cells segs m3 (A' + len) [CB (Z.to_nat n - Z.to_nat len) (firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk))]).
{ replace (A' + len) with (A' + Z.of_nat (Z.to_nat len)) by lia. eapply rw_cells_transport; [gw_exact NEWt| gw_exact MU3| gw_exact WM3|]. apply DJW. cbn. lia. }

eapply rimplM_membed_sbind.
{ apply (implM_membed_set_m (cfree cs1 (Some (fst p))) s' cs1).
eapply (rfree_membed RFI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (set_m cs1 s') (bnew :: LB) p A n0 lo B errv2);
try eassumption; try reflexivity; rewrite ?unsigned_lit by lia; unfold RFREE_STACK; try lia.
all: first [right; gw_exact Hin | replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; gw_exact ST3]. }
cbv beta. intros cs2 s'' ms'' PFR.
cbn [membed]. apply implM_ret. eapply evt_cut; [gw_exact PFR|]. cbv beta. clear PFR. intros ms4 PFR.
destruct PFR as (v0 & v1 & v2 & fa0 & fa1 & fa2 & fa3 & fa4 & fa5 & fa6 & fa7 & v3 & v4 & v5 & v6 & m4 & -> &
MI4 & ST4 & ERR4 & AUX4 & PRES4 & _ & _ & HP4).
rewrite ?unsigned_lit in ST4, PRES4 by lia.
try g_ret_pc_any.
change (set_m cs2 (set_m cs1 s'')) with (set_m cs2 s'') in HP4.
rewrite (lb_remove_cons_neq p bnew LB) in HP4, PRES4 by (apply bptr_eqb_false_of_neq; gw_exact NEQ).
assert (FR4 : rw_cells segs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [gw_exact PRES4| gw_exact FR3|]. left. lia. }

apply evt_done. step. step. eapply rr_epilogue; [gw_exact FR4|].

unfold rrealloc_post. cbn [rr_conv fst snd].
exists v0, v1, v2, (Z_to_bv 64 A'), fa1, fa2, fa3, fa4, fa5, fa6, fa7, v3, v4, v5, v6, m4, errv2.
split; [reflexivity|]. split; [gw_exact MI4|].
split. { pose proof (stk_release segs m4 lo _ _ ST4 FR4 ltac:(lia)) as X. cbn [cells_size csize Nat.add] in X.
replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in X by lia. gw_exact X. }
split; [gw_exact ERR4|]. split; [gw_exact AUX4|].
split; [destruct (ps_fa s), (ps_fa (set_m cs2 s'')); reflexivity|]. split; [destruct (ps_so s), (ps_so (set_m cs2 s'')); reflexivity|].
exists A', (firstn (Z.to_nat len - length old) junk0 ++ firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk)).
split; [reflexivity|]. split; [gw_exact BR'|]. split; [gw_exact HP4|].
split.
+
eapply rheap_pres_trans; [| eapply rheap_pres_weaken; [gw_exact PRES4| lia| intros b Hb; right; gw_exact Hb]].
eapply rheap_pres_trans; [eapply rheap_pres_weaken; [gw_exact PRES02| lia|]|].
{ intros b Hb. apply In_lb_remove in Hb. tauto. }
eapply rheap_pres_of_munch; [gw_exact MU3| gw_exact WM3|]. intros a Ha HC. cbn. split; [|exact I].
destruct HC as [HC|[HC|(b & Hb & HC)]].
* lia.
* unfold ralloc_static in HC. lia.
* apply In_lb_remove in Hb as [Hb Hpb].
assert (NE2 : blk_id bnew <> blk_id b).
{ intros E. apply NoDup_cons_iff in ND as [NI _]. apply NI. cbn [bnew blk_id fst] in E |- *. rewrite E. apply in_map_iff. exists b. auto. }
pose proof (RHEAP_blocks_disjoint_proof _ _ _ bnew b HP2 ltac:(left; reflexivity) ltac:(right; gw_exact Hb) NE2) as D.
cbn [bnew blk_addr blk_size fst snd] in D. lia.
+
assert (M3 : rw_cells segs m3 A' ([CB (Z.to_nat len) src] ++ [CB (Z.to_nat n - Z.to_nat len) (firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk))])).
{ apply (proj2 (rw_cells_app segs m3 A' [CB (Z.to_nat len) src] [CB (Z.to_nat n - Z.to_nat len) (firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk))])).
split; [gw_exact DST3|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
replace (A' + Z.of_nat (Z.to_nat len)) with (A' + len) by lia. gw_exact NEWt3. }
assert (M4 : rw_cells segs m4 A' ([CB (Z.to_nat len) src] ++ [CB (Z.to_nat n - Z.to_nat len) (firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk))])).
{ eapply rheap_pres_rw_cells; [gw_exact PRES4| gw_exact M3|]. right; right. exists bnew. split; [left; reflexivity|]. cbn -[Z.of_nat]. lia. }
pose proof (rw_cells_merge segs m4 A' [] [CB (Z.to_nat len) src; CB (Z.to_nat n - Z.to_nat len) (firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk))] [] M4) as M.
cbn [app cells_size cells_bytes csize cbytes] in M. rewrite app_nil_r, Nat.add_0_r in M.
replace (Z.to_nat len + (Z.to_nat n - Z.to_nat len))%nat with (Z.to_nat n) in M by lia.
match type of M with rw_cells _ _ _ [CB _ ?bs] => replace bs with (firstn (Z.to_nat (Z.min n n0)) old ++ firstn (Z.to_nat len - length old) junk0 ++ firstn (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk)) in M end.
{ gw_exact M. }
subst src. rewrite firstn_app, <- app_assoc. reflexivity.
-
cbn [cm_conv] in CASE. destruct CASE as (-> & E12 & HP2).
cbn [membed]. apply implM_ret. apply evt_done.

step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
eapply rr_epilogue; [gw_exact FR2|].
unfold rrealloc_post. cbn [rr_conv fst snd].
exists u0, u1, u2, (Z_to_bv 64 0), ra1, ra2, ra3, ra4, ra5, ra6, ra7, u3, u4, u5, u6, m2, errv2.
split; [reflexivity|]. split; [gw_exact MI2|].
split. { pose proof (stk_release segs m2 lo _ _ ST2 FR2 ltac:(lia)) as X. cbn [cells_size csize Nat.add] in X.
replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in X by lia. gw_exact X. }
split; [gw_exact ERR2|]. split; [gw_exact AUX2|].
split; [destruct (ps_fa s), (ps_fa (set_m cs1 s')); reflexivity|]. split; [destruct (ps_so s), (ps_so (set_m cs1 s')); reflexivity|].
split; [reflexivity|]. split; [gw_exact E12|]. split; [gw_exact HP2| gw_exact PRES02].
Qed.
End GENERAL.

End RC__1.

End G.
End Mq9.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8l1.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe1A.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rmalloc_sym rmalloc_entry ralloc_slot_entry : Z).
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

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@Qe1A.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qe1A.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qe1A.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qe1A.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qe1A.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qe1A.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qe1A.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qe1A.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qe1A.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qe1A.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QROt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Q8l1.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq7.rpres_except segs) (@rpres_except) gw_tbl_10)))))))))).
Definition renf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq7.renf_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq7.renf_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mq7.renf_post segs RATP RGOT_SSP ref_reserved RC__) (@renf_post) gw_tbl_11).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QkTt.Mq6.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QROt.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Q8l1.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_12)))))))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QROt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Q8l1.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq8.ralloc_fp RATP) (@ralloc_fp) gw_tbl_13)))))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QROt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Q8l1.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_14))))).
Definition ras_post : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@QROt.Mq5.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@Q8l1.Mq8.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) gw_tbl_15))).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_17 := (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@QROt.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@Q8l1.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq7.rimplT segs RC__) (@rimplT) gw_tbl_16))))))).
Definition ralloc_slot_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) (gw_ent (@QROt.Mq5.ralloc_slot_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@ralloc_slot_stmt) (gw_ent (@Q8l1.Mq8.ralloc_slot_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@ralloc_slot_stmt) gw_tbl_17))).
Definition rcoreQ : ltac:(gw_rebind_ty (@QROt.Mq5.rcoreQ segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq5.rcoreQ segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QROt.Mq5.rcoreQ segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@rcoreQ) gw_tbl_18).
Definition rbig_stmt : ltac:(gw_rebind_ty (@QROt.Mq5.rbig_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq5.rbig_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@QROt.Mq5.rbig_stmt segs rmalloc_entry RATP RGOT_SSP ref_reserved RC__) (@rbig_stmt) gw_tbl_19).
Definition RMALLOC_SYM : ltac:(gw_rebind_ty (@QDXD.Mq3.RMALLOC_SYM rmalloc_sym) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RMALLOC_SYM rmalloc_sym) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QDXD.Mq3.RMALLOC_SYM rmalloc_sym) (@RMALLOC_SYM) gw_tbl_20).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@QkTt.Mq6.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@Qe1A.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_21))).
Definition raddr_exposed : ltac:(gw_rebind_ty (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@QkTt.Mq6.raddr_exposed segs RC__) (@raddr_exposed) (gw_ent (@QDXD.Mq3.raddr_exposed segs RC__) (@raddr_exposed) gw_tbl_22)).
Definition rblock_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_23)).
Notation gw_tbl_24 := (gw_ent (@QkTt.Mq6.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@Qe1A.rblock_range RIMG_HI RC__) (@rblock_range) (gw_ent (@QDXD.Mq3.rblock_range RIMG_HI RC__) (@rblock_range) gw_tbl_23))).
Definition ralloc_static : ltac:(gw_rebind_ty (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_24)).
Notation gw_tbl_25 := (gw_ent (@QkTt.Mq6.ralloc_static RATP) (@ralloc_static) (gw_ent (@QDXD.Mq3.ralloc_static RATP) (@ralloc_static) gw_tbl_24)).
Definition rclient_addr : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_25)).
Notation gw_tbl_26 := (gw_ent (@QkTt.Mq6.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) (gw_ent (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) gw_tbl_25)).
Definition rheap_pres : ltac:(gw_rebind_ty (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_26)).
Notation gw_tbl_27 := (gw_ent (@QkTt.Mq6.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) (gw_ent (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) gw_tbl_26)).
Definition rmalloc_post : ltac:(gw_rebind_ty (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_27)).
Notation gw_tbl_28 := (gw_ent (@QkTt.Mq6.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) (gw_ent (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) gw_tbl_27)).
Definition rmalloc_stmt : ltac:(gw_rebind_ty (@QDXD.Mq3.rmalloc_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_sym RC__) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rmalloc_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_sym RC__) constr:(gw_tbl_28)).
Notation gw_tbl_29 := (gw_ent (@QDXD.Mq3.rmalloc_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_sym RC__) (@rmalloc_stmt) gw_tbl_28).
Definition rmalloc_impl_stmt : ltac:(gw_rebind_ty (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) constr:(gw_tbl_29)).
Notation gw_tbl_30 := (gw_ent (@QkTt.Mq6.rmalloc_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rmalloc_entry RC__) (@rmalloc_impl_stmt) gw_tbl_29).

Hypothesis renf_implT : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq7.gw_all) (@Qy8Z.Mq7.renf_implT) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_30))) in exact T).

Hypothesis rmalloc_fp_cases : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq8.gw_all) (@QQRC.Mq8.rmalloc_fp_cases) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_30))) in exact T).
Hypothesis rmalloc_fp_image : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq8.gw_all) (@QQRC.Mq8.rmalloc_fp_image) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_30))) in exact T).
Hypothesis rauxv_ok_malloc_fp : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq8.gw_all) (@QQRC.Mq8.rauxv_ok_malloc_fp) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_30))) in exact T).

Hypothesis rmalloc_core_implT : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QROt.Mq5.gw_all) (@QROt.Mq5.rmalloc_core_implT) rmalloc_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_30))) in exact T).
Hypothesis rmalloc_stmt_of_impl : gw_hyp (rmalloc_impl_stmt -> rmalloc_stmt).

Definition rwr_at_bytes_exist : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rwr_at_bytes_exist) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rwr_at_bytes_exist)).

Definition rimpl_bind_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimpl_bind_mono) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimpl_bind_mono)).
#[global] Arguments rimpl_bind_mono {A}%_type_scope {B}%_type_scope {C}%_type_scope t f1%_function_scope f2%_function_scope Q1%_function_scope Q2%_function_scope ms _ _%_function_scope.
Definition rimplM_membed_sbind : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplM_membed_sbind) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplM_membed_sbind)).
#[global] Arguments rimplM_membed_sbind {R}%_type_scope {S}%_type_scope T F%_function_scope s Q1%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rauxv_ok_weaken : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_weaken) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_weaken)).
Definition rpres_except_refl : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_refl) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_refl)).
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).

Definition rmalloc_fp_mono : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmalloc_fp_mono) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmalloc_fp_mono)).
Notation RMFACTS := (@MFACTS_g ref_reserved).

Definition rheap_pres_weaken : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq3.rheap_pres_weaken) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq3.rheap_pres_weaken)).

Definition rregion_addr_facts : ltac:(gw_ctx_fold_ty2 (@Qe1A.rregion_addr_facts) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.rregion_addr_facts)).
Definition rblock_inside : ltac:(gw_ctx_fold_ty2 (@Qe1A.rblock_inside) constr:(gw_tbl_30)) := ltac:(gw_ctx_fold_tm2 (@Qe1A.rblock_inside)).

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
#[using="rmalloc_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rmalloc_sym ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rmalloc_sym AL_rmalloc_entry AL_ralloc_slot_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT rmalloc_stmt_of_impl"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : QUZl.M R1) (t2 : QUZl.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
implM segs (membed t1) s Q1 ms ->
implM segs (membed t2) s
(fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof. clear - segs R1 R2 RR t1 t2.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [gw_exact H|]. intros ms' H1.
exists r1, []. cbn. auto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
impl segs (at_node segs) (QlEo_c1.Mq0.bind _ (Ret Unr) f) Qx msx = impl segs (at_node segs) (f Unr) Qx msx) by first [reflexivity | (cbn; lia)].
destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w|ma ol nl fl].
5:{ cbn [ev_step] in *. unfold munr in *. cbn [QlEo_c1.Mq0.bind] in *. gw_exact H. }
5:{ cbn [ev_step] in *. unfold munr in *. cbn [QlEo_c1.Mq0.bind] in *. gw_exact H. }
all: eapply rimpl_bind_mono; [gw_exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [gw_exact H1|];
eapply impl_epost_mono; [eapply IH; gw_exact H1|];
intros [r2' s2] ms2; cbn; intros (r1' & ans & F1 & F2 & HR & HQ);
exists r1', (z :: ans); cbn; auto.
Qed.

#[using="Type"] Lemma rraw_malloc_bridge2 : forall st s n (o : mem) Q1 Q ms,
strip st = ps_m s ->
rimplT o (malloc st n) s Q1 ms ->
(forall st' (p : optr) s' ms' (r : option bptr) ans o' cst c,
Q1 (st', p) s' ms' -> ptr_rel p r ->
follow (mrun o (malloc st n)) ans = Some (o', (st', p)) ->
follow (cmalloc (strip st) n) ans = Some (cst, c) ->
cst = strip st' ->
r = match c with Some slot => Some (slot, fresh_off cst slot n) | None => None end ->
Q r (set_m (strip st') s') ms') ->
implM segs (raw_malloc n) s Q ms.
Proof. clear - segs.
intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
eapply (implM_bind segs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind segs _ _ _ (fun r s' ms' => exists st' p ans o', Q1 (st', p) s' ms' /\ MREL (o', (st', p)) r
/\ follow (mrun o (malloc st n)) ans = Some (o', (st', p)) /\ follow (cmalloc (strip st) n) ans = Some r)).
{ rewrite <- Hst. unfold rimplT in H.
eapply implM_mono.
- eapply (rmembed_strel_follow MREL (mrun o (malloc st n)) (cmalloc (strip st) n)); [| gw_exact H].
unfold mrun. apply malloc_control. apply pans_mem_range.
- intros [cs c] s' ms' ([o1 [st' p]] & ans & F1 & F2 & HR & H1). cbn in H1.
exists st', p, ans, o1. auto. }
intros [cs c] s' ms' (st' & p & ans & o' & H1 & HR & F1 & F2). cbv beta iota.
eapply (implM_bind segs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
eapply (HQ st' p s' ms' _ ans o' (strip st') c H1); [| gw_exact F1| gw_exact F2| reflexivity| reflexivity].
destruct p as [pf|], c as [c|]; cbn in Hp |- *; try gw_exact Hp.
Qed.

#[using="Type"] Lemma rimplT_silent {R} o (t : QUZl.M R) o' (x : R) s Q ms :
mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt segs (Q x s) ms.
Proof. clear - segs R o t o' x s Q ms. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. gw_exact H. Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved rmalloc_fp_cases rmalloc_fp_image"] Lemma rheap_pres_of_fp st st' LB lo sp m m' :
RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
rheap_pres LB sp m m'.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved rmalloc_fp_cases rmalloc_fp_image st st' LB lo sp m m' RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [gw_exact Ha|]. intros Hfp.
destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
- destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); unfold alloc_ceiling in *; lia.
- destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold ralloc_static in *); lia.
- destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
unfold alloc_ceiling in *.
pose proof MR' as (WF' & _). pose proof WF' as (_ & WR' & DISJ' & _).
pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
pose proof (round_up_pg_mono _ _ L1) as RL1.
pose proof (lr_lo_group r1 ltac:(rewrite K1; gw_exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
+ lia.
+ rewrite unsigned_lit in H by lia. lia.
+ gw_expose_fam RATP. lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay"] Lemma ruser_chunk st' m' (p : aptr) r n :
rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
exists junk, rw_cells segs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay segs st' m' p r n.
intros MR Hr Hk P0 PN N0.
pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). unfold alloc_ceiling in RC.
rewrite (conc_region' st' p r Hr).
assert (W : wr_at segs m' (r_base r + snd p) n) by (eapply wr_at_sub; [gw_exact HW| lia| lia]).
destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; gw_exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; gw_exact W].
split; [gw_exact L| exact I].
Qed.

Definition malloc_core_allzero_stmt : Prop :=
forall st L BL LS n (o : mem) ans (o' : mem) st1 g idx,
Qatc.INVL Qatc.x0 st L BL LS -> 0 <= n ->
follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o', (st1, Some (g, idx))) ->
is_allzero_ctrl (Qatc.MR st1 g) = true ->
exists bg, m_mem (Qatc.MR st1 g) = Some bg /\
forall k, 0 <= k < get_stride (Qatc.MR st1 g) - IB ->
cell_read (get_shadow st1 (fst bg)) (Qatc.sstart (Qatc.MR st1 g) idx + k) = Known 0.

#[using="Type"] Lemma bytes_at_inj0 m a bs bs' : bytes_at segs m a bs -> bytes_at segs m a bs' -> length bs = length bs' -> bs = bs'.
Proof. clear - segs m a bs bs'.
intros (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs i)) by lia. rewrite (proj2 (nth_error_None bs' i)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rzeros_of_shadow st m rid r base (cnt : nat) :
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
0 <= base -> base + Z.of_nat cnt <= round_up_pg (r_len r) ->
(forall j, 0 <= j < Z.of_nat cnt -> cell_read (get_shadow st rid) (base + j) = Known 0) ->
bytes_at segs m (r_base r + base) (zeros cnt).
Proof. clear - segs st m rid r base cnt.
intros MR Hr Hk B0. pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH rid r Hr Hk) as [HW HB].
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & _). unfold alloc_ceiling in RBC.
induction cnt as [|cnt IH]; intros BC HC.
- cbn. apply bytes_at_nil. lia.
- replace (zeros (S cnt)) with (zeros cnt ++ [b8 0]) by (unfold zeros; rewrite <- repeat_cons; cbn; reflexivity).
apply bytes_at_app. split; [apply IH; [lia| intros j Hj; apply HC; lia]|].
unfold zeros. rewrite repeat_length. replace (r_base r + base + Z.of_nat cnt) with (r_base r + (base + Z.of_nat cnt)) by lia.
exact (proj1 (HB (base + Z.of_nat cnt) 0 ltac:(lia) (HC (Z.of_nat cnt) ltac:(lia)))).
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis MCZ : malloc_core_allzero_stmt.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
exists st2 r ans o1,
fst res = strip st2
/\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
/\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

#[using="gw_RTEXT_LO gw_RDATA2_LO ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_impl_spec_proof : rmalloc_impl_stmt.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT as_pre as_inv RAS MCZ AS_PRE RBIG segs RATP. gw_expose_fam RATP.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR0.
assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [gw_exact AUXB| unfold alloc_ceiling in *; lia]).
destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]). rename LB into LBc. rename LB0 into LB.
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; gw_exact HPERM| gw_exact Hb]).
pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
unfold raw_malloc.
eapply (implM_bind segs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0' s1' ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind segs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
{ rewrite <- Hst. unfold cmalloc.
eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
x = (strip st2, r)
/\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
- eapply implM_mono.
+ eapply (rmembed_strel_follow CREL).
* pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
* unfold rimplT in |- *.
pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
unfold rimplT in X. first [gw_exact X | (rewrite ?Z.add_0_r in X; rewrite ?Z.add_0_r; gw_exact X)].
+ intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
exists st2, r, ans, o1. split; [reflexivity|]. split; [gw_exact F1|]. split; [gw_exact F2| gw_exact CQ].
- intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [gw_exact F1|]. split; [gw_exact F2| gw_exact CQ]. }
intros [cs c] s' ms'' MQ. cbv beta iota.
destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
eapply (implM_bind segs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] sx msx [-> ->]. apply implM_ret.

assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
| Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
follow (cmalloc (strip st) n) ans = Some y).
{ intros y Hy. unfold cmalloc. eapply follow_sbind; [gw_exact F2| gw_exact Hy]. }
destruct r as [[g idx]|].
-
cbn [rcoreQ] in CQ.
destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
set (stride := get_stride (get_meta_rec st2 g)) in *.
set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
unfold alloc_ceiling in RC, CLO. unfold RMALLOC_STACK in LO.
pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
ltac:(intros a Ha; left; gw_exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; gw_exact Ha) CTR2 SO) as ENF.
pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
eapply evt_mono; [gw_exact EV|]. clear EV.
intros msf [_ EP]. unfold renf_post in EP.
destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF & UB).
destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; gw_exact Hr).
assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
{ rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
set (A := conc st' p) in *.

assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
{ unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [gw_exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
fold A in UCH.
unfold rmalloc_post. do 15 eexists. exists m', errv1.
split; [reflexivity|]. split; [gw_exact MI'|]. split; [gw_exact ST'|].
split. { eapply rpres_except_rw_cells; [gw_exact PE'| gw_exact ERR2|]. rewrite TP. gw_expose_fam RATP. rewrite unsigned_lit by lia.
change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
- lia.
- lia. }
assert (MRELf : mrel st st') by (eapply mrel_trans; [gw_exact MREL|]; apply mrel_same; assumption).
assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
{ eapply rpres_except_mono.
+ eapply rpres_except_trans; [gw_exact PE2|].
eapply rpres_except_mono; [gw_exact PE'|]. intros a [X|X]; [left; left; gw_exact X| apply SPANFP; subst lo_s hi_s stride; gw_exact X].
+ intros a Ha. eapply rmalloc_fp_mono; [|gw_exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [gw_exact MR| gw_exact MR'| gw_exact AUXB| gw_exact PEf| gw_exact CLO| gw_exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [gw_exact HPf| lia| gw_exact HIN]. }
split; [gw_exact PSF|]. split; [gw_exact PSO|].
exists A, ujunk.
split; [reflexivity|].
split. { unfold rblock_range, alloc_ceiling. rewrite EA.
split; [lia|]. split; [apply mod16_slot; [gw_exact RAL| gw_exact B16| gw_exact SMOD| lia]|]. subst lo_s hi_s.
specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
split. { exists st'. eexists. split; [apply Permutation.perm_skip; gw_exact HPERM|]. split; [gw_exact SE|]. split; [gw_exact MR'|]. split.
- apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. gw_exact BL2.
- gw_exact AR'. }
split; [gw_exact UCH|].
split.
2:{
intros g0 idx0 SL0 AZ. cbn [ps_m set_m fst] in SL0, AZ.
rewrite s_slots_strip in SL0. unfold slot_of, slot_start' in SL0. rewrite Hmem in SL0. cbn [default from_option id] in SL0.
unfold aadd in SL0. cbn [fst snd] in SL0.
replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + get_stride (get_meta_rec st2 g) * idx) in SL0 by (unfold UNIT; lia).
rewrite SSL in SL0. assert (g0 = g /\ idx0 = idx) as [-> ->] by (inversion SL0; auto). clear SL0.
change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g) in AZ.
destruct (Q3o5.Mq1.areach_inv _ st LB AR) as (L & LS & BL0 & INV & _).
destruct (MCZ st L BL0 LS n m ans m st2 g idx INV ltac:(lia) F1 AZ) as (bg & Hbg & CZ).
change (Qatc.MR st2 g) with (get_meta_rec st2 g) in Hbg, CZ. rewrite Hmem in Hbg. assert (bg = b) as -> by congruence.
unfold Qatc.sstart, Qatc.gbase in CZ. rewrite Hmem in CZ. cbn [default id snd] in CZ. fold stride in CZ.
assert (Z0 : bytes_at segs m1 A (zeros (Z.to_nat n))).
{ rewrite EA. replace (r_base rg + snd b + 16 + stride * idx + 16 * off) with (r_base rg + (snd b + 16 + stride * idx + 16 * off)) by lia.
apply (rzeros_of_shadow st2 m1 (fst b) rg); [gw_exact MR2| gw_exact Hr| gw_exact Hk| lia| |].
- rewrite Ep in *. cbn [snd] in *. subst stride. lia.
- intros j Hj. replace (snd b + 16 + stride * idx + 16 * off + j) with (snd b + UNIT + stride * idx + (16 * off + j)) by (unfold UNIT; lia).
apply CZ. unfold IB. lia. }
pose proof (UB (zeros (Z.to_nat n)) Z0 ltac:(unfold zeros; rewrite repeat_length; lia)) as Z1.
pose proof (rw_cells_bytes_at _ _ _ _ UCH) as UJ. cbn [cells_bytes cbytes] in UJ. rewrite app_nil_r in UJ.
pose proof (proj1 (proj1 UCH)) as WFJ. cbn in WFJ. destruct WFJ as [LJ _].
apply (bytes_at_inj0 m' A); [gw_exact UJ| gw_exact Z1| unfold zeros; rewrite repeat_length; lia]. }

intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
{ apply EXPO. destruct AE as [AE|AE]; [left; gw_exact AE| right].
pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. gw_exact E0. }
unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
unfold fresh_off. cbn [s_slots strip].
replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
-
cbn [rcoreQ] in CQ.
destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO & E12).
apply evt_done. unfold rmalloc_post. do 15 eexists. exists m1, errv1.
pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
split; [reflexivity|]. split; [gw_exact MI2|]. split; [gw_exact ST2|]. split; [gw_exact ERR2|].
split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [gw_exact MR| gw_exact MR2| gw_exact AUXB| gw_exact PE2| gw_exact CLO| gw_exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [gw_exact HPf| lia| gw_exact HIN]. }
split; [gw_exact PSF|]. split; [gw_exact PSO|].
split; [reflexivity|]. split; [gw_exact E12|].
exists st2, LB. split; [gw_exact HPERM|]. split; [reflexivity|]. split; [gw_exact MR2|].
split.
+ apply (proj1 (brk_link_ps_iff st2 _)). cbn. gw_exact BL2.
+ eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [gw_exact F1|]. intros ans'. reflexivity.
Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO rmalloc_entry ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT rmalloc_stmt_of_impl as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO rmalloc_entry ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ref_wview_overlay ref_mrd_overlay renf_implT rmalloc_fp_cases rmalloc_fp_image rauxv_ok_malloc_fp rmalloc_core_implT rmalloc_stmt_of_impl as_pre as_inv RAS MCZ AS_PRE RBIG. exact (rmalloc_stmt_of_impl rmalloc_impl_spec_proof). Qed.

End TOPLEVEL.

End RC__1.

End G.
