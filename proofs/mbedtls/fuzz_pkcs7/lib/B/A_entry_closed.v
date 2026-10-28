(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg ATopContract ATopContract24 A_main_top A_entry_bridge A_entry_pack.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_R0 A_link_top A_link_rates A_link_budgets A_link_adapt A_pk_parse_H A_pk_parse_G0 A_x509_crt_parse_A A_ecp_grp_id_list A_ecp_stmtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapR AHeapHIA AW_FreePhPZ AW_ModDieT AW_B12WalkP.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_entry_closed () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.AHeap.ACeil.arun"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.A_link_budgets.FSTKc"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.R0"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_parse_A.STKx"; "RocqVerifyHarness.AgentSubmission.B.A_link_adapt.STKcrt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_sp"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_envp"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_fits"; "RocqVerifyHarness.AgentSubmission.B.A_main_top.entry_bridgeA"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.main_entry_A"].


(* [comment removed for export] *)
Lemma FSTK_R0 : ltac2:(CDefT.buildp (gd_tbl_A_entry_closed ()) "PhAR,$0.PSTKLO,$1.(2.(3.=(4.(5.R2.R1.)(6.(5.R2.R1.)(7.(5.R2.R1.)))))(3.(4.(5.R2.R1.)(6.(5.R2.R1.)(7.(5.R2.R1.))))(8.+2.+16.)))")
(* [comment removed for export] *).
Proof. intros hAR STKLO. vm_compute. split; discriminate. Qed.

Lemma C24f_R0 : A_pk_parse_G0.PKP_C24 + 1 <= 65536.
Proof. vm_compute. discriminate. Qed.

Theorem entry_bridge_closed : ltac2:(CDefT.buildp (gd_tbl_A_entry_closed ()) "Psp,(9.&40.)Pbrk0,(9.&40.)Prdraw,$:.Pargv,(;.(;.(9.&8.)))Penvp,(;.(;.(9.&8.)))Pfs,$<.Puid,(9.&40.)Phw,(9.&40.)P,(=.R8.)P,(>.R6.)P,(?.R6.)P,(10.R;.R8.R7.)(11.(12.R<.R;.R:.R9.R8.R7.R6.R5.)R9.R7.R<.)")
(* [comment removed for export] *).
Proof.
  intros sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit.
  pose (STKLO := bv_unsigned sp - 2 ^ 23).
  pose (LO := @A_link_R0.a_layout_ok_R0 (A_entry_bridge.arun_of sp Hsp) STKLO).
  pose (HO := @A_link_R0.a_hia_ok_R0 (A_entry_bridge.arun_of sp Hsp) STKLO (A_entry_bridge.STKLO_OK_of sp Hsp) AW_B12WalkP.b12_walk AW_ModDieT.mod_die_walk
                (@AW_FreePhPZ.freeH (A_entry_bridge.arun_of sp Hsp) STKLO (A_entry_bridge.STKLO_OK_of sp Hsp))).
  refine (A_entry_pack.entry_bridge sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit
            (A_pk_parse_H.A_pk_sinv (arl_L (@R0 (A_entry_bridge.arun_of sp Hsp) STKLO)) (A_link_layout.alo_ids_lok _ LO) (A_link_layout.alo_mc_lok _ LO)) _
            A_link_rates.PHItop A_link_rates.FPHIc A_link_rates.PHItop_max
            _ (FSTK_R0 (A_entry_bridge.arun_of sp Hsp) STKLO)
            A_link_rates.FFRtop A_link_rates.FFFRc A_link_rates.FFRtop_max
            _ C24f_R0
            (A_link_top.fuzz_entryA24_cl (@R0 (A_entry_bridge.arun_of sp Hsp) STKLO) _ LO HO)
            A_link_rates.HVF_closed A_link_rates.HFRF_closed).
  (* [comment removed for export] *)
  intros a NO. rewrite A_pk_parse_H.A_pk_sinv_fp in NO.
  unfold A_ecp_grp_id_list.A_ECP_IDS_DONE, A_ecp_grp_id_list.A_ECP_IDS, A_ecp_stmtA.A_MUL_COUNT in NO. cbn [outside fst snd] in NO. lia.
Qed.

(* [comment removed for export] *)
