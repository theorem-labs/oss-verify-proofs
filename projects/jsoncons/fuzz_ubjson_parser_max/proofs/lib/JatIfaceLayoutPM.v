(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA L5DefsA JatIfaceLaws JatIfaceInst JatIfaceLayout PmLayout PmLayoutA PmStatics PmSpecsAa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma art_pm_dep_not_static : forall a, PMST.dep PMA.AD a -> ~ hl_rt_static art_L a.
Proof.
intros a D. cbn [art_L hl_rt_static]. unfold art_static.
unfold PMST.dep, pm_foot, pm_initc in D. cbn [PMA.AD ADDR_A pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock app] in D.
destruct D as [(iv & Hiv & Hr) | [Hc | (iv & Hiv & Hr)]].
- cbn [In] in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
- lia.
- cbn [In] in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
Qed.
Theorem art_pma_layout : PMA.layout art_L art_C.
Proof.
constructor.
- exact art_as0_layout.
- reflexivity.
- intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
- cbn. split; [reflexivity | split; reflexivity].
- exact art_pm_dep_not_static.
- intros a Ha. cbn [art_L hl_rt_static]. unfold art_static. lia.
- intros a Ha. cbn [art_L hl_rt_ro] in Ha. unfold art_ro in Ha. lia.
- cbn [art_C art_statics_cells asc_cells]. split; apply in_or_app; right; cbn [art_cells_drv In]; tauto.
- intros a Ha. cbn [art_L hl_rt_static hl_tp] in *. unfold art_static. lia.
Qed.
