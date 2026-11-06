(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Spec LibWritev Js0StdioDefs Js0Exit_run1 Js0Exit_run2 Js0Exit_run3 Js0StdioWrite_run1 Js0StdioWrite_run2 Js0StdioWrite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Exit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0ExitBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1list"; "1nil"; "1option"; "1prod"; "2I"; "2eq"; "3Z"; "4Fs"; "5mkCfg"; "6FdChannel"; "6FdEntry"; "6Model"; "6event"; "6fd_lookup"]; ["6m_fds"; "6m_fs"; "6m_halted"; "6m_vm_lazy"; "7bvmap"; "8file_clean"; "9exit_common"; "9exit_pre"; "9stdout_pending"; ":mkst"; ":seg_rom"; ";t_emit"; ";t_eq"; ";t_exit"; "<W"; "=srealizes"]; [">loaded_segments"; "0bufp"; "0bufsz"; "0can"; "0code"; "0fs"; "0fx"; "0mem"; "0model"; "0pending"; "0regs"; "0rp1"; "0rp2"; "0scfg"; "0sp"; "?BV"]; ["?Z_to_bv"; "?bv"; "?bv_and"; "0tid"; "0tp"; "0wb"; "0wp"; "0wp1"; "0wp2"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RdnPeelKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
lazymatch goal with
| |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
| |- _ => rdn_hyp
end.
Local Ltac rdn_solve ::= rdn_solve_fast.
Ltac zaddr_rec H := zaddr H.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section SE.
Local Abbreviation SEC_T_ref_exit_clean := (ltac2:(TCodec.tc2 tcn__Js0Exit "RG&Dy5'QAyR0%211%5241'4y8%611%311p061'='8'Fr;r:r8r7r6r5r4r3%9887654321&E+fhV@r2%34<251'7%F1H&B%11@(0%11L%63531'2'5%12Q0Q0%311&Cr<%211(3%116%@3631'O&Q0vQ=(:&IvQ6r?(Q?+cRf@(6%33QC21/01QCr>&J%11=%;5:9431r=%>221&M&QB&Q@+WO%22QO1%43R0QD1&A%119%8231%K4JI:1p0M1p0Q81p0Q@1p0QE1pRHR81pS@R91pRJR:1pSBR;1pS8R41pR:R=1pS:R>1pRNR?1pRBR91pR@R;1pRFRA1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 1%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 3%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 4%nat 0%nat).
Variable code : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 5%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 6%nat 0%nat).
Variable wp2 : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 7%nat 0%nat).
Variable rp2 : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 8%nat 0%nat).
Variable wp1 : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 9%nat 0%nat).
Variable rp1 : ltac:(sec_ty2 constr:(SEC_T_ref_exit_clean) 10%nat 0%nat).
Theorem ref_exit_clean : ltac:(sec_stmt2 constr:(SEC_T_ref_exit_clean) 11%nat 0%nat).
Proof using Type regs mem model sp tp code tid wp2 rp2 wp1 rp1.
intros EC F1 Hh Hlazy.
destruct EC. destruct ec_ax as [ax AX].
destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: try (unfold mem_w1, ax_writes; destruct ax as [|[|?]]; first [store_ok_peel; exact ec_sok | rdn_solve]).
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3a regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; rdn_solve. }
1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve. }
1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
eapply rz_exit_at; [exact (ltac:(oF' 0x987e0%Z)) | exact (ltac:(oE' 0x987e0%Z)) | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_ref_exit_flush := (ltac2:(TCodec.tc2 tcn__Js0Exit "SD&Dy5'QAyR0%211%5241'4y8%611%311p061'='8'2%116'Fr@r?r=r<r;r:r9r8%9887654321'Hr7r6r5r4r3r2%78@9654321'7%L1N&B%11D(0%11Q2%63531'5%12Q5Q5%M11&CrA%211(3%116%?3631'<%Q<11&?&@rB%211&Q@+1%22QF1%7241(1(;%114%32=1%N3=51'O&Q0vQ=(:&IvQ6rE(Q?+cRf@(6%33R721/01R7rD&J%11=%;5:9431rC%>221&K&N%12LQI&M&QB+WO%Q12RE1%33RFR91&A%11;%7231%;291%N4ML=1p0Q01p0Q@1p0QJ1p0R21p0R;1pRDRF1pR8S11pRHS21pR6S31pR4S41pS>RM1pS<RN1pRJS71pSBS81pS8S11pR:S:1pS:S;1pRNS<1pRBS61pR@S81pRFS>1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 1%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 3%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 4%nat 0%nat).
Variable code : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 5%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 6%nat 0%nat).
Variable wp2 : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 7%nat 0%nat).
Variable rp2 : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 8%nat 0%nat).
Variable wb : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 9%nat 0%nat).
Variable wp : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 10%nat 0%nat).
Variable bufp : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 11%nat 0%nat).
Variable bufsz : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 12%nat 0%nat).
Variable rp1 : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 13%nat 0%nat).
Variable can : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 14%nat 0%nat).
Variable pending : ltac:(sec_ty2 constr:(SEC_T_ref_exit_flush) 15%nat 0%nat).
Theorem ref_exit_flush : ltac:(sec_stmt2 constr:(SEC_T_ref_exit_flush) 16%nat 0%nat).
Proof using Type regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending.
intros EC SP Hh Hlazy Hfd.
destruct EC. destruct ec_ax as [ax AX]. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: try (unfold mem_w1, ax_writes; destruct ax as [|[|?]]; first [store_ok_peel; exact ec_sok | rdn_solve]).
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct (w3b1 regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wb wp)
as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; rdn_solve. }
1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
replace (Z_to_bv 64 0x9e188) with (0x9e188 : word) in R3ra by (apply bv_eq; reflexivity).
unfold W. rewrite <- (app_nil_r pending).
set (mem3 := mem_w3a (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
eapply (ref_stdio_write scfg regs3 mem3 model (bv_unsigned sp - 32) 0xb60d0 wb wp 1
(Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x9e188 : word) pending []);
[ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
| lia | lia
|
subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; sok_stack ec_sok
| lia | lia
| split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve
| split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; rdn_solve
| lia | exact Hfd | exact Hh | exact Hlazy
| lia | lia | exact LEN
| cbn [length]; u_norm; reflexivity
| cbn [length]; lia
| lia | u_norm; lia | u_norm; lia
| subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; repeat rdn_peel1; exact BYTES
| reflexivity
| apply ret_ok_even; reflexivity
| apply t_emit_has_nil
| ].
intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
rewrite R3s0 in Q8.
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
eapply rz_exit_at; [exact (ltac:(oF' 0x987e0%Z)) | exact (ltac:(oE' 0x987e0%Z)) | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.
End SE.
#[using="Type"] Lemma t_emit_nil_exit : ltac2:(TCodec.tc2 tcn__Js0Exit "A'QAyR0%211&9&L&Mr2r1%3221&K(3'>%211%4215%:261pR<<1pR:>1").
Proof.
intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.
Section SE.
Local Abbreviation SEC_T_ref_exit := (ltac2:(TCodec.tc2 tcn__Js0Exit "QJ&Dy5'QAyR0%211%5241'4y8%611%311p061'='2%115&Gr5r4r3r2r1%6554321'O&Q0vQ=(:&IvQ6r6(Q?+cRf@(6%33L21/01L&J%11<%:5983D1%<21D&K&N+1%221F&M&QB&Q@+WO%22Q:1%43Q;M1&A%11Q0%8231%=2:1%N4ML?1p0Q01pRDQ81pR:QB1pRBQ<1pR@Q>1pRFQD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_ref_exit) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_ref_exit) 1%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_ref_exit) 2%nat 0%nat).
Variable code : ltac:(sec_ty2 constr:(SEC_T_ref_exit) 3%nat 0%nat).
Variable pending : ltac:(sec_ty2 constr:(SEC_T_ref_exit) 4%nat 0%nat).
Theorem ref_exit : ltac:(sec_stmt2 constr:(SEC_T_ref_exit) 5%nat 0%nat).
Proof using Type regs mem model code pending.
intros (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
- eapply srz_conseq; [ | apply t_emit_nil_exit ].
eapply ref_exit_clean; eassumption.
- eapply ref_exit_flush; eassumption.
Qed.
End SE.
#[using="Type"] Corollary ref_exit_Z : ltac2:(TCodec.tc2 tcn__Js0Exit "QG&Dy5'QAyR0%211%5241'4y8%611%311p061'='2%115&Gr5r4r3r2r1%6554321'O&Q0vQ=(:&IvQ6r6&Q@+cRf@%22K1&J%11:%85763B1%:21B&K&N+1%221D&M&QB+WO%>2Q71%33Q8J1&A%11M%7231%<291%K4JI>1p0M1pRDQ51pR:Q?1pRBQ91pR@Q;1pRFQA1").
Proof.
intros. replace (Z_to_bv 64 0x98ad0) with (0x98ad0 : word) by (apply bv_eq; reflexivity).
apply ref_exit; assumption.
Qed.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
