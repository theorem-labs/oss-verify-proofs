(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX Arr InNth.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0
     ECH_AImg ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C3 ECH_APF_C4 ECH_AStmt_C4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require Import I2ImgAsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit
  I2ANodeSig I2ANodeM I2ASound I2ACert I2AStart I2ASh0 I2ATop I2ACertE CertA_asanK.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require GenO3s0_0_asan GenO3s0_16_asan GenO3s1_0_asan GenO3s1_16_asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition S_O3 (save : Z) : ssrc :=
  SSrc [(4, ATP); (10, save)]
       [(A_malloc_impl, le8Z P_CRYPTO_malloc); (A_realloc_impl, le8Z P_CRYPTO_realloc); (A_free_impl, le8Z P_CRYPTO_free);
        (A_mem_inited, [1]);
        (AMUSL_TSD, le8Z A_tsd_main);
        (ASHBASE_CELL, le8Z ASHADOW_BASE); (AUAR_CELL, le4Z 1);
        (A_stopped, [0]); (A_base_once, le4Z 2); (A_base_ret, le4Z 1);
        (A_destructor_key, le4Z (LIBKEY0 + 1) ++ le4Z (2 ^ 32 - 1));
        (A_keys + 8 * LIBKEY0, le8Z P_nodtor ++ le8Z P_init_thread_destructor ++ le8Z P_nodtor);
        (A_keys, le8Z A_keys0_val);
        (A_next_key, le4Z (LIBKEY0 + 2)); (A_key_lock, le8Z 0 ++ le8Z 0); (A_td_cancelbuf, le8Z 0); (A_td_tsd_used, [1])]
       [(0x10000, 0x571000); (0x571000, 0x5ea000);
        (A_err_string_lock, A_err_string_lock + 8); (A_int_error_hash, A_int_error_hash + 8);
        (A_err_string_once, A_err_string_once + 4); (A_err_string_ret, A_err_string_ret + 4);
        (A_master_once, A_master_once + 4); (A_master_key, A_master_key + 4); (A_master_once_ret, A_master_once_ret + 1);
        (A_tevent_once, A_tevent_once + 4); (A_tevent_ret, A_tevent_ret + 4); (A_glob_tevent_reg, A_glob_tevent_reg + 8);
        (A_load_strings_once, A_load_strings_once + 4); (A_load_strings_ret, A_load_strings_ret + 4); (A_optsdone, A_optsdone + 8);
        (A_keys + 8 * (LIBKEY0 + 3), A_keys + 8 * (LIBKEY0 + 3) + 8);
        (A_tsd_main + 8 * (LIBKEY0 + 1), A_tsd_main + 8 * (LIBKEY0 + 1) + 8); (A_tsd_main + 8 * (LIBKEY0 + 3), A_tsd_main + 8 * (LIBKEY0 + 3) + 8)]
       [(AERRNO, 4, 32%uint63); (A_optsdone_lock, 8, 33%uint63); (ACANARYX, 8, 34%uint63)]
       [].

(* [comment removed for export] *)
Definition xregs_of3 (errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (i : Z) : word :=
  nth (Z.to_nat i) [errv; ra; sp; gp; tp; t0; t1; t2; s0; s1; a0; a1; a2; a3; a4; a5; a6; a7; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] w0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chks0_0_K : KA_ok GenO3s0_0_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_roc : K_roc_okA GenO3s0_0_asan.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_code_some : match build_code asegs GenO3s0_0_asan.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_code : code_ok asegs GenO3s0_0_asan.code.
Proof.
  unfold GenO3s0_0_asan.code_. pose proof chks0_0_code_some as Hs.
  destruct (build_code asegs GenO3s0_0_asan.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok asegs GenO3s0_0_asan.pcs C E).
Qed.
Lemma chks0_0_run : i2a_check2 IMX GenO3s0_0_asan.KA GenO3s0_0_asan.code GenO3s0_0_asan.fuel GenO3s0_0_asan.st0 GenO3s0_0_asan.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_shape : start_shape_okA GenO3s0_0_asan.KA IMX (I2AS (state_of GenO3s0_0_asan.d0) GenO3s0_0_asan.n0 GenO3s0_0_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_ho : ho_check2 IMX GenO3s0_0_asan.facts0 GenO3s0_0_asan.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_tags : forallb (fact_tags_lt GenO3s0_0_asan.n0) GenO3s0_0_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_facts : forallb (fact_okA GenO3s0_0_asan.K GenO3s0_0_asan.d0 (S_O3 0)) GenO3s0_0_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_xw : xw_in GenO3s0_0_asan.K ERR_XE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_sh0 : sh0_chk GenO3s0_0_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_pfc : forallb (fun r => row_inb r PFC_ERRINIT) (rowsZ (ka_pfc GenO3s0_0_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_pfo : forallb (fun r => row_inb r PF_EGS_FRESH) (rowsZ (ka_pfo GenO3s0_0_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_msum : (msum (ka_costs GenO3s0_0_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_0_fsum : (fsum (ka_costs GenO3s0_0_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chks0_16_K : KA_ok GenO3s0_16_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_roc : K_roc_okA GenO3s0_16_asan.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_code_some : match build_code asegs GenO3s0_16_asan.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_code : code_ok asegs GenO3s0_16_asan.code.
Proof.
  unfold GenO3s0_16_asan.code_. pose proof chks0_16_code_some as Hs.
  destruct (build_code asegs GenO3s0_16_asan.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok asegs GenO3s0_16_asan.pcs C E).
Qed.
Lemma chks0_16_run : i2a_check2 IMX GenO3s0_16_asan.KA GenO3s0_16_asan.code GenO3s0_16_asan.fuel GenO3s0_16_asan.st0 GenO3s0_16_asan.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_shape : start_shape_okA GenO3s0_16_asan.KA IMX (I2AS (state_of GenO3s0_16_asan.d0) GenO3s0_16_asan.n0 GenO3s0_16_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_ho : ho_check2 IMX GenO3s0_16_asan.facts0 GenO3s0_16_asan.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_tags : forallb (fact_tags_lt GenO3s0_16_asan.n0) GenO3s0_16_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_facts : forallb (fact_okA GenO3s0_16_asan.K GenO3s0_16_asan.d0 (S_O3 0)) GenO3s0_16_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_xw : xw_in GenO3s0_16_asan.K ERR_XE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_sh0 : sh0_chk GenO3s0_16_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_pfc : forallb (fun r => row_inb r PFC_ERRINIT) (rowsZ (ka_pfc GenO3s0_16_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_pfo : forallb (fun r => row_inb r PF_EGS_FRESH) (rowsZ (ka_pfo GenO3s0_16_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_msum : (msum (ka_costs GenO3s0_16_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks0_16_fsum : (fsum (ka_costs GenO3s0_16_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chks1_0_K : KA_ok GenO3s1_0_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_roc : K_roc_okA GenO3s1_0_asan.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_code_some : match build_code asegs GenO3s1_0_asan.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_code : code_ok asegs GenO3s1_0_asan.code.
Proof.
  unfold GenO3s1_0_asan.code_. pose proof chks1_0_code_some as Hs.
  destruct (build_code asegs GenO3s1_0_asan.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok asegs GenO3s1_0_asan.pcs C E).
Qed.
Lemma chks1_0_run : i2a_check2 IMX GenO3s1_0_asan.KA GenO3s1_0_asan.code GenO3s1_0_asan.fuel GenO3s1_0_asan.st0 GenO3s1_0_asan.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_shape : start_shape_okA GenO3s1_0_asan.KA IMX (I2AS (state_of GenO3s1_0_asan.d0) GenO3s1_0_asan.n0 GenO3s1_0_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_ho : ho_check2 IMX GenO3s1_0_asan.facts0 GenO3s1_0_asan.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_tags : forallb (fact_tags_lt GenO3s1_0_asan.n0) GenO3s1_0_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_facts : forallb (fact_okA GenO3s1_0_asan.K GenO3s1_0_asan.d0 (S_O3 1)) GenO3s1_0_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_xw : xw_in GenO3s1_0_asan.K ERR_XE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_sh0 : sh0_chk GenO3s1_0_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_pfc : forallb (fun r => row_inb r PFC_ERRINIT) (rowsZ (ka_pfc GenO3s1_0_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_pfo : forallb (fun r => row_inb r PF_EGS_FRESH) (rowsZ (ka_pfo GenO3s1_0_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_msum : (msum (ka_costs GenO3s1_0_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_0_fsum : (fsum (ka_costs GenO3s1_0_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chks1_16_K : KA_ok GenO3s1_16_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_roc : K_roc_okA GenO3s1_16_asan.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_code_some : match build_code asegs GenO3s1_16_asan.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_code : code_ok asegs GenO3s1_16_asan.code.
Proof.
  unfold GenO3s1_16_asan.code_. pose proof chks1_16_code_some as Hs.
  destruct (build_code asegs GenO3s1_16_asan.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok asegs GenO3s1_16_asan.pcs C E).
Qed.
Lemma chks1_16_run : i2a_check2 IMX GenO3s1_16_asan.KA GenO3s1_16_asan.code GenO3s1_16_asan.fuel GenO3s1_16_asan.st0 GenO3s1_16_asan.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_shape : start_shape_okA GenO3s1_16_asan.KA IMX (I2AS (state_of GenO3s1_16_asan.d0) GenO3s1_16_asan.n0 GenO3s1_16_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_ho : ho_check2 IMX GenO3s1_16_asan.facts0 GenO3s1_16_asan.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_tags : forallb (fact_tags_lt GenO3s1_16_asan.n0) GenO3s1_16_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_facts : forallb (fact_okA GenO3s1_16_asan.K GenO3s1_16_asan.d0 (S_O3 1)) GenO3s1_16_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_xw : xw_in GenO3s1_16_asan.K ERR_XE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_sh0 : sh0_chk GenO3s1_16_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_pfc : forallb (fun r => row_inb r PFC_ERRINIT) (rowsZ (ka_pfc GenO3s1_16_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_pfo : forallb (fun r => row_inb r PF_EGS_FRESH) (rowsZ (ka_pfo GenO3s1_16_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_msum : (msum (ka_costs GenO3s1_16_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chks1_16_fsum : (fsum (ka_costs GenO3s1_16_asan.KA) <=? ERRINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
