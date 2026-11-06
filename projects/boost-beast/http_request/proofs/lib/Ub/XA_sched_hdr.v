(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt XRep XA_registry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition sched_hdr0 (ioc : Z) : svch := mkSVC VP_SCHED 0 0 ioc 0 0.

(* [comment removed for export] *)
Definition sched_hdr (ioc cfgb : Z) : svch := mkSVC VP_SCHED L_TYPEID_SCHED 0 ioc cfgb P_DESTROY_ALLOC_SCHED.

(* [comment removed for export] *)
Definition cfg_elt (ioc cfgb : Z) : svce := mkSE cfgb (cfg_hdr ioc) TI_NAME_CONFIG.

Lemma cfg_chain : forall LB m cfgb ioc,
  ConfigSvc LB m cfgb (cfg_hdr ioc) -> XStatics m -> 0 < cfgb -> cfgb + NEWSZ_CFG <= 2^64 -> 0 <= ioc < 2^64 ->
  SvcChain m cfgb [cfg_elt ioc cfgb].
Proof.
  intros LB m cfgb ioc (p & j4 & j7 & IN & CH & _) XS POS HI IOCR. cbn.
  split; [reflexivity|]. split; [exact POS|]. split; [unfold NEWSZ_CFG in HI; lia|].
  split. { apply (proj1 (rw_cells_app _ _ _ (SvcHdrCells _) _)) in CH. exact (proj1 (proj1 CH)). }
  split. { unfold svch_ok, cfg_hdr, VP_CONFIG_SVC, L_TYPEID_CONFIG, P_DESTROY_ALLOC_CONFIG; cbn; lia. }
  split. { intros _. split; [exact (XS_tiname_config _ XS)|]. unfold TI_NAME_CONFIG, L_TYPEID_CONFIG; lia. }
  reflexivity.
Qed.

Lemma cfg_find : forall ioc cfgb, find_svc L_TYPEID_CONFIG 0 TI_NAME_CONFIG [cfg_elt ioc cfgb] = cfgb.
Proof. intros. cbn [find_svc cfg_elt]. rewrite (keys_match_true_ti L_TYPEID_CONFIG 0 TI_NAME_CONFIG cfgb (cfg_hdr ioc) TI_NAME_CONFIG); [reflexivity| | | reflexivity]; unfold cfg_hdr, L_TYPEID_CONFIG; cbn; lia. Qed.

End HCW.
