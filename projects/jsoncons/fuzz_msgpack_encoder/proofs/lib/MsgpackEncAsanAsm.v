(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0276. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NarFamTop NraMainPhaseA NraInstAX. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnALibOk. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnALayFacts MsgpackEncFinalS MsgpackEncAsanTop. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.HeapIfaceAMxI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123.NarIfaceInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0276.NarIfaceLayoutPM OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123.NarIfaceMcmp OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289.NarFam OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NarFamTop OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraMainPhaseA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0276.NraInstA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraInstAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266.NraDiagArms OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266.NraUsageArm OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnALibOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.NTopAsmA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsTsw OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.PnATsVPot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnALayFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncFinalS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncAsanTop OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0276.NarIfaceSnp.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma na0_inst : inst_ok_stmt cfg0 art_L art_C BUDGET0.           Proof. exact (as0_inst_ok cfg0 BUDGET0 eq_refl). Qed.
Lemma na0_free_null : free_null_stmt cfg0 art_L BUDGET0.           Proof. exact (as0_free_null cfg0 BUDGET0). Qed.
Lemma na0_h4e : h4e_stmt BUDGET0.                                  Proof. exact (as0_h4e BUDGET0). Qed.
Lemma na0_icpt : icpt_ok_stmt cfg0 art_L art_IL BUDGET0.           Proof. exact (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok). Qed.
Lemma na0_ext : ext_ok_stmt cfg0 art_L PMA.EXT BUDGET0.            Proof. exact (as0_ext_ok_pma cfg0 BUDGET0 eq_refl). Qed.
Lemma na0_gap : gap_ok_stmt BUDGET0.                               Proof. exact (as0_gap_ok BUDGET0). Qed.
Lemma na0_dla : dla_ok_stmt cfg0 art_L art_C art_IL.               Proof. exact (as0_dla_ok cfg0 art_IL art_IL_ok). Qed.
Lemma na0_consts : drv_consts_stmt art_L art_C art_IL.             Proof. exact (as0_drv_consts art_IL art_IL_ok). Qed.
Lemma na0_usage : usage_stmt cfg0.
Proof. exact (as0_usage_closed cfg0 art_L art_C art_IL BUDGET0 BUDGET0_lo BUDGET0_hi na0_inst na0_free_null na0_h4e na0_icpt na0_dla na0_consts). Qed.

(* [comment removed for export] *)
Lemma na0_fam : forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static Asan.M.loaded_segments MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET0 NarInv.LENMAX NarInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x693b00 -> rn_key rn = 0 -> rn_tsd rn = 0x6b4fb8 -> rn_loff rn = 0x10 ->
    @NTASMA.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR (rn_ar rn) (fun D => art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET0 art_fsinv (art_rn_k rn D)).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE rn STATIC ROK Htp Hkey0 Htsd Hloff.
  exact (art_fam_top MAPS0 RESV0 NOACC0 BASE BUDGET0 rn cfg0 art_IL eq_refl asegs_wx STATIC Htp Hkey0 Htsd Hloff art_IL_ok).
Qed.

(* [comment removed for export] *)
Section Tgt.
Variable RES : credit.
Hypothesis ROK : RES_ok RES.
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis RESGE : PMSP.credit_le (PQATSPV.T12VMAX art_L PQATSTW.TSWMAX NTASMA.TSPVMAX) RES.
Hypothesis OPENA : forall (ar : asan_run) (HIk : list (list Z) -> asan_iface),
    @NTASMA.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR ar HIk -> @NTASMA.open_A art_L art_C art_IL art_LR ar HIk RES.

Lemma na0_drv : drv_main_stmt cfg0 art_L art_C art_IL (PQHAS.LayA RES art_L)
                  (fun _ => PQSTA.TopLSA Asan.M.loaded_segments PnLayoutA.ADDR_A PnLayoutA.AADDR_A PnLayoutQA.QADDR_A).
Proof. exact (as0_drv_main_closed cfg0 art_L art_C art_IL (PQHAS.LayA RES art_L) _ (pm_lib_layout RES ROK) (pm_lib_cells RES) (pm_lib_budget RES ROK)). Qed.

Lemma na0_lib : @PQALO.lib_ok_stmtF ScfgP_cfg0 art_L art_C art_IL art_LR (PQHAS.LayA RES art_L)
                  (PQSTA.TopLSA Asan.M.loaded_segments PnLayoutA.ADDR_A PnLayoutA.AADDR_A PnLayoutQA.QADDR_A).
Proof. exact (@PQALO.lib_okF ScfgP_cfg0 art_L art_C art_IL art_LR RES art_pma_layout art_IL_ok art_mcmp_cells art_snp_cells RESGE OPENA). Qed.

(* [comment removed for export] *)
Theorem na0_tgt : as0_tgt_stmt cfg0.
Proof.
  apply as0_tgt_of_run.
  intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs.
  exact (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL (PQHAS.LayA RES art_L)
           (fun _ => PQSTA.TopLSA Asan.M.loaded_segments PnLayoutA.ADDR_A PnLayoutA.AADDR_A PnLayoutQA.QADDR_A)
           PMA.EXT BUDGET0 BUDGET0_lo BUDGET0_hi na0_inst na0_free_null na0_h4e na0_icpt na0_ext na0_gap
           (@NTASMA.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR) na0_lib na0_fam na0_dla na0_consts na0_drv na0_usage PQALO.lsxfa
           sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs).
Qed.
End Tgt.
