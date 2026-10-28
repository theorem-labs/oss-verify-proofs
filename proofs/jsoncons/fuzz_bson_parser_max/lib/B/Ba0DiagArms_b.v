(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg Spec HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvLib_b Ba0DrvStdio_b Ba0DrvG_b Ba0MainPhaseA_b Ba0DrvMain_b Ba0DiagArmRefuse_b Ba0DiagFwrite_b Ba0DiagArmMsg_b Ba0DiagStrK_b Ba0DiagArmOpen_b
  Ba0DrvLibL_b Ba0DrvLibInit_b Ba0DrvOpenFail_b Ba0DrvH_b Ba0DiagArmRead_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Existing Instance PropExec.fx0.

Theorem dg_refuse_ok : forall scfg L C IL, dg_refuse_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & _) Hsp Hal DL _] path fs0 fdata p0 p1 can A0 _ _.
  exact (refuse_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG M0 fdata path fs0 p0 p1 can [] A0).
Qed.

Theorem dg_short_ok : forall scfg L C IL, dg_short_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & _ & _ & HDGM) Hsp Hal DL M0def] fs0 fdata p0 p1 can A0 CAP crC HCAP HLEN Hs.
  exact (short_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDGM M0 M0def fs0 fdata p0 p1 can [] A0 CAP HCAP crC Hs).
Qed.

Theorem dg_overrun_ok : forall scfg L C IL, dg_overrun_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & _ & _ & HDGM) Hsp Hal DL M0def] fs0 fdata p0 p1 can A0 CAP crC HCAP HLEN Hge Hov.
  exact (overrun_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDGM M0 M0def fs0 fdata p0 p1 can [] A0 CAP HCAP crC HLEN Hge Hov).
Qed.

Theorem dg_openerr_ok : forall scfg L C IL, dg_openerr_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & HDGS & _) Hsp Hal DL _] path fs0 fdata p1 cr0 A0 [PLO STR NONUL PLEN PDEF] SAH.
  exact (open_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG HDGS M0 fdata path fs0 p1 [] cr0 A0 (STR_ATA ar sp0 M0 A0 p1 path PLO STR NONUL PLEN PDEF SAH)).
Qed.

Theorem dg_readerr_ok : forall scfg L C IL, dg_readerr_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & HDGS & _) Hsp Hal DL _] fs0 p0 p1 can cr0 A0 [PLO STR NONUL PLEN PDEF] SAH.
  exact (read_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG HDGS M0 fs0 p0 p1 can [] cr0 A0 (STR_ATA ar sp0 M0 A0 p1 dot_path PLO STR NONUL PLEN PDEF SAH)).
Qed.

Theorem dg_nofile_ok : forall scfg L C IL Lay LSt, dg_nofile_stmt scfg L C IL Lay LSt.
Proof. intros scfg L C IL Lay LSt. exact (dg_nofile_of_openerr scfg L C IL Lay LSt (dg_openerr_ok scfg L C IL)). Qed.

Theorem dg_dot_ok : forall scfg L C IL Lay LSt, drv_lib_layoutA Lay L -> drv_budgetA L Lay -> dg_dot_stmt scfg L C IL Lay LSt.
Proof. intros scfg L C IL Lay LSt DLL HBUD. exact (dg_dot_of scfg L C IL Lay LSt DLL HBUD (dg_openerr_ok scfg L C IL) (dg_readerr_ok scfg L C IL)). Qed.

(* [comment removed for export] *)
Theorem as0_drv_main_closed : forall scfg (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics),
  drv_lib_layoutA Lay L -> drv_lib_cellsA Lay -> drv_budgetA L Lay -> drv_main_stmt scfg L C IL Lay LSt.
Proof.
  intros scfg L C IL Lay LSt DLL DLC HBUD.
  exact (as0_drv_main scfg L C IL Lay LSt DLL DLC HBUD (dg_openerr_ok scfg L C IL) (dg_short_ok scfg L C IL) (dg_overrun_ok scfg L C IL) (dg_refuse_ok scfg L C IL)
           (dg_nofile_ok scfg L C IL Lay LSt) (dg_dot_ok scfg L C IL Lay LSt DLL HBUD)).
Qed.
