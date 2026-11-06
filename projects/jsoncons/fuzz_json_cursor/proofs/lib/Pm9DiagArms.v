(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec ShapeAlg SpinAlg Spec HeapIface HeapIfaceA IcptIfaceA LibIface PmLibIfaceA Pm9DrvLib Pm9DrvStdio Pm9DrvG Pm9MainPhaseA Pm9DrvMain Pm9DiagArmRefuse Pm9DiagFwrite Pm9DiagArmMsg Pm9DiagStrK Pm9DiagArmOpen
  Pm9DrvLibL Pm9DrvLibInit Pm9DrvOpenFail Pm9DrvH Pm9DiagArmRead.
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

Theorem as0_drv_main_closed : forall scfg (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics),
  drv_lib_layoutA Lay L -> drv_lib_cellsA Lay -> drv_budgetA L Lay -> drv_main_stmt scfg L C IL Lay LSt.
Proof.
  intros scfg L C IL Lay LSt DLL DLC HBUD.
  exact (as0_drv_main scfg L C IL Lay LSt DLL DLC HBUD (dg_openerr_ok scfg L C IL) (dg_short_ok scfg L C IL) (dg_overrun_ok scfg L C IL) (dg_refuse_ok scfg L C IL)
           (dg_nofile_ok scfg L C IL Lay LSt) (dg_dot_ok scfg L C IL Lay LSt DLL HBUD)).
Qed.
