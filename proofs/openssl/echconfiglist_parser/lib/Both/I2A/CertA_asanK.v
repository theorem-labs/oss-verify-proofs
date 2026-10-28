(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX Arr InNth.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0
     ECH_AImg ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C3.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require Import I2ImgAsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit
  I2ANodeSig I2ASound I2ACert I2AStart I2ASh0 I2ATop I2ACertE.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2 Require GenA0_asan GenA16_asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition S_A : ssrc :=
  SSrc [(4, ATP)]
       [(A_malloc_impl, le8Z P_CRYPTO_malloc); (A_realloc_impl, le8Z P_CRYPTO_realloc); (A_free_impl, le8Z P_CRYPTO_free);
        (A_mem_inited, [1]);
        (AMUSL_TSD, le8Z A_tsd_main);
        (A_keys, le8Z A_keys0_val); (A_next_key, le4Z 0); (A_key_lock, le8Z 0 ++ le8Z 0); (A_td_tsd_used, [1]);
        (ASHBASE_CELL, le8Z ASHADOW_BASE); (AUAR_CELL, le4Z 1)]
       [(0x10000, 0x571000); (0x571000, 0x5ea000);
        (A_destructor_key, A_destructor_key + 8); (A_defctx_inited, A_defctx_inited + 1); (A_defctx, A_defctx + 328);
        (A_defctx_tlkey, A_defctx_tlkey + 4); (A_defctx_tlkey_once, A_defctx_tlkey_once + 4); (A_defctx_tlkey_ret, A_defctx_tlkey_ret + 4);
        (A_defctx_once, A_defctx_once + 4); (A_defctx_once_ret, A_defctx_once_ret + 4);
        (A_base_inited, A_base_inited + 1); (A_stopped, A_stopped + 1); (A_in_init_config_key, A_in_init_config_key + 4);
        (A_base_once, A_base_once + 4); (A_base_ret, A_base_ret + 4); (A_load_strings_once, A_load_strings_once + 4);
        (A_load_strings_ret, A_load_strings_ret + 4); (A_optsdone_lock, A_optsdone_lock + 8); (A_init_lock, A_init_lock + 8);
        (A_optsdone, A_optsdone + 8); (A_td_cancelbuf, A_td_cancelbuf + 8); (A_keys + 8, A_keys + 8 + (0x400 - 8));
        (A_tsd_main + 8, A_tsd_main + 16)]
       [(AERRNO, 4, 33%uint63); (ACANARYX, 8, 34%uint63)]
       [].

(* [comment removed for export] *)
Definition xregs_ofA (errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (i : Z) : word :=
  nth (Z.to_nat i) [errv; ra; sp; gp; tp; t0; t1; t2; s0; s1; a0; a1; a2; a3; a4; a5; a6; a7; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] w0.

(* [comment removed for export] *)
Definition zlist_eqb (a b : list Z) : bool := if list_eq_dec Z.eq_dec a b then true else false.
Definition row_inb (r : Z * list Z) (l : list (Z * list Z)) : bool :=
  existsb (fun r' => (fst r' =? fst r)%Z && zlist_eqb (snd r') (snd r)) l.
Lemma row_inb_In : forall r l, row_inb r l = true -> In r l.
Proof.
  intros [pc t] l Hb. unfold row_inb in Hb. apply existsb_exists in Hb as ([pc' t'] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1. unfold zlist_eqb in H2. destruct (list_eq_dec Z.eq_dec t' t); [|discriminate].
  subst. exact Hin.
Qed.
(* [comment removed for export] *)
Definition rowsZ (l : list (int * list int)) : list (Z * list Z) := map (fun e : int * list int => (to_Z (fst e), map to_Z (snd e))) l.
Lemma rows_closed : forall (TR : list (list Z)) (PFC : list (Z * list Z)) (l : list (int * list int)),
  forallb (fun r => row_inb r PFC) (rowsZ l) = true ->
  Forall (fun r : Z * list Z => trace_ok TR (fst r) (snd r)) PFC ->
  Forall (fun e : int * list int => trace_ok TR (to_Z (fst e)) (map to_Z (snd e))) l.
Proof.
  intros TR PFC l Hb HF. apply Forall_forall. intros e He. rewrite forallb_forall in Hb.
  specialize (Hb (to_Z (fst e), map to_Z (snd e)) ltac:(unfold rowsZ; apply in_map_iff; exists e; split; [reflexivity | exact He])).
  apply row_inb_In in Hb. exact (proj1 (Forall_forall _ _) HF _ Hb).
Qed.
Lemma rows_open : forall (TR : list (list Z)) (PF : list (Z * list Z)) (l : list (int * list int)) ra CH,
  forallb (fun r => row_inb r PF) (rowsZ l) = true -> pf_ok TR PF ra CH -> pf_ok TR (rowsZ l) ra CH.
Proof.
  intros TR PF l ra CH Hb HF. unfold pf_ok in *. apply Forall_forall. intros r Hr. rewrite forallb_forall in Hb.
  specialize (Hb r Hr). apply row_inb_In in Hb. exact (proj1 (Forall_forall _ _) HF _ Hb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chk0_K : KA_ok GenA0_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_roc : K_roc_okA GenA0_asan.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_code_some : match build_code asegs GenA0_asan.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_code : code_ok asegs GenA0_asan.code.
Proof.
  unfold GenA0_asan.code_. pose proof chk0_code_some as Hs.
  destruct (build_code asegs GenA0_asan.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok asegs GenA0_asan.pcs C E).
Qed.
Lemma chk0_run : i2a_check2 IMX GenA0_asan.KA GenA0_asan.code GenA0_asan.fuel GenA0_asan.st0 GenA0_asan.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_shape : start_shape_okA GenA0_asan.KA IMX (I2AS (state_of GenA0_asan.d0) GenA0_asan.n0 GenA0_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_ho : ho_check2 IMX GenA0_asan.facts0 GenA0_asan.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_tags : forallb (fact_tags_lt GenA0_asan.n0) GenA0_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_facts : forallb (fact_okA GenA0_asan.K GenA0_asan.d0 S_A) GenA0_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_xw : xw_in GenA0_asan.K (CTX_X ++ AERRNO_X) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_sh0 : sh0_chk GenA0_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_pfc : forallb (fun r => row_inb r PFC_CTXINIT) (rowsZ (ka_pfc GenA0_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_pfo : forallb (fun r => row_inb r PF_ctxinit) (rowsZ (ka_pfo GenA0_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_msum : (msum (ka_costs GenA0_asan.KA) <=? CTXINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk0_fsum : (fsum (ka_costs GenA0_asan.KA) <=? CTXINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chk16_K : KA_ok GenA16_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_roc : K_roc_okA GenA16_asan.K = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_code_some : match build_code asegs GenA16_asan.pcs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_code : code_ok asegs GenA16_asan.code.
Proof.
  unfold GenA16_asan.code_. pose proof chk16_code_some as Hs.
  destruct (build_code asegs GenA16_asan.pcs) as [C|] eqn:E; [|discriminate Hs]. exact (build_code_ok asegs GenA16_asan.pcs C E).
Qed.
Lemma chk16_run : i2a_check2 IMX GenA16_asan.KA GenA16_asan.code GenA16_asan.fuel GenA16_asan.st0 GenA16_asan.X = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_shape : start_shape_okA GenA16_asan.KA IMX (I2AS (state_of GenA16_asan.d0) GenA16_asan.n0 GenA16_asan.blk0 [] 0%uint63 0%uint63 0%uint63 []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_ho : ho_check2 IMX GenA16_asan.facts0 GenA16_asan.d0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_tags : forallb (fact_tags_lt GenA16_asan.n0) GenA16_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_facts : forallb (fact_okA GenA16_asan.K GenA16_asan.d0 S_A) GenA16_asan.facts0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_xw : xw_in GenA16_asan.K (CTX_X ++ AERRNO_X) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_sh0 : sh0_chk GenA16_asan.KA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_pfc : forallb (fun r => row_inb r PFC_CTXINIT) (rowsZ (ka_pfc GenA16_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_pfo : forallb (fun r => row_inb r PF_ctxinit) (rowsZ (ka_pfo GenA16_asan.KA)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_msum : (msum (ka_costs GenA16_asan.KA) <=? CTXINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk16_fsum : (fsum (ka_costs GenA16_asan.KA) <=? CTXINIT_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.

