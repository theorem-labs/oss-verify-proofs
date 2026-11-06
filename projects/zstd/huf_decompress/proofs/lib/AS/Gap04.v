(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MmapComplete.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Gap04 () := "C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib2AS5Gap04=alloc_top_minC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib<MmapCompleteIvm_gap_available_completeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib9PlacementFmmap_reserve_refusableC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib3Lib9PlacementDmmap_grant_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementJmmap_fixed_fresh_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC59OSSVerify5KrLib3Lib9PlacementKmmap_fixed_commit_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC59OSSVerify5KrLib3Lib9PlacementBmprotect_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9Placement@mmap_errnos_whenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosI47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib9PlacementDmprotect_errnos_whenC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnos".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition alloc_top_min : Z := 0x7fff7f800000.
Lemma alloc_top_min_eq : alloc_top_min = sp_window_lo - stack_max_size.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap04 ()) [] "p;2g0000j21Tg000Mj20Tg000gg001Eg002@'1'0o"). Qed.
Lemma alloc_top_ge_min : forall h, sp_window_lo <= bv_unsigned (vm_init_sp h) -> alloc_top_min <= alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap04 ()) [] "h04__x1h11Hh27__arithh34__ffh48__varmaph55__with61hp;1p;2p;4p;3p;8p;7g003=j10Tg003bj1MTg004@j1:Tg0059j2>Tg005cj24Tg006?j1QTg006_j1LTg007?j2CTg007]j1BTg008;j1ATg008fj11Tg009Kj16Tg009ij25Tg00:Lj2RTg00:oj4<Tg00;Zj1PTg00<<j3;Tg00<_j3KTg00=Bj8DTg00=fj2ETg000Mj2FTg00>Hj2GTg00?4j3HTg00?Nj3ITg00?mj4JTg00@_j2=Tg0000j2@Tg00A<j1NTg00B4j7OTf0R0#0#0p=7%10#1p=?%10#1#1#1p=2%00#0#0#0p=8%00#0#0#0#0#0#0#0p=3f1R1g00BXR2g00C7R3P3g00CWR4P0g00D7FOp=9g00DWg001Eg00ENR5#0#7R6#0#7R7#MR8%:0'>'4g000gR9g00F3R:#Q%L:1C91%B9%A9R:P2P3P3P4P9%?5#2#2#2R2#1#0#7#8#3#3#3#6R;,59g00F_R<1R95R5C<,9:%P3P9%02#2#2#0#7#8#3#3#6R2,59P<%66R6,59%87#6R7,59R<5;9=;9<9K95C<,9:GD1E:4P0f2R:g00GFR4g00GfR5'F1G0:=H45dg00HF=I91CJb3b4b5W014;01=67/=7,@1,42[^09P0%::,>8P1O2b2g00Hd%N1'4eW1W6o"). Qed.
Lemma alloc_top_lt_2_64 : forall h, alloc_top h < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap04 ()) [] "h02Hah14__x1h21Hh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91hp;1p;2p;3p;4p;7p;8g00I_j1KTg00A<j12Tg00JZj21Tg003=j10Tg009Kj14Tg00K6j2@Tg005cj23Tg00K^j2;Tg00L;j37Tg006?j16Tg006_j15Tg007?j28Tg007]j19Tg008;j1JTg00:Lj2ITg009ij2HTg003bj1?Tg00L_j3=Tg00:oj4>Tg00B4j7<Tg00;Zj1ATg00=Bj8BTg00=fj2:Tg000Mj2CTg00>Hj2DTg00?4j3ETg00?Nj3FTg00?mj4GTg00DWf0R0#K%20g00MB'1g00ENR1#0R2#4R3%02#0#0#0#0R2#4R4'@g00HFR5/1313541;34R6,15[[1353R7g00N;R8f1R99734UW01356\8^07g000gR7g00F3R8#6%581879%97%J7R8g00BXR4g00C7R:P:g00CWR;P8P4P:P:P;P71I71g00NW1H73%?25=7C>g00D7F<R2%A:P2GB1:8;P0f2R;g00GFR8g00GfR2'C1D0;=E82dAF759CGb4b7b8W111061196[^17P0f4#2f3O2b3b5b6%29/16eb2W9o"). Qed.

(* [comment removed for export] *)
Corollary mmap_reserve_not_refusable : forall m nZ (a : word),
  0 <= nZ ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a HnZ Hal Hpos Hce Hfree. unfold mmap_reserve_refusable.
  rewrite (vm_gap_available_complete (m_vmmaps m) nZ a HnZ Hal Hpos Hce Hfree). reflexivity.
Qed.

Corollary mmap_grant_not_refusable : forall flags m nZ (a : word),
  0 <= nZ ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a HnZ Hal Hpos Hce Hfree Hbud. unfold mmap_grant_refusable.
  rewrite (vm_gap_available_complete (m_vmmaps m) nZ a HnZ Hal Hpos Hce Hfree), Hbud. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_fresh_not_refusable : forall flags m nZ,
  mmap_noreserve_backed_ok flags m nZ = true -> mmap_fixed_fresh_refusable flags m nZ = false.
Proof. intros flags m nZ H. unfold mmap_fixed_fresh_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_commit_not_refusable : forall flags m addr n,
  mmap_fixed_rw_budget_ok flags m addr n = true -> mmap_fixed_commit_refusable flags m addr n = false.
Proof. intros flags m addr n H. unfold mmap_fixed_commit_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mprotect_not_refusable : forall m addr n,
  mprotect_budget_ok m addr n = true -> mprotect_refusable m addr n = false.
Proof. intros m addr n H. unfold mprotect_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof.
ltac2:(KReplay.run1 (kr_t_Gap04 ()) [] "p;1p;2g006_j12Tg006?j11Tg000Mj20Tg000gR0#2%10'0o"). Qed.

Lemma mprotect_errnos_when_false : mprotect_errnos_when false = [].
Proof.
ltac2:(KReplay.run1 (kr_t_Gap04 ()) [] "p;1p;2g006_j12Tg006?j11Tg000Mj20Tg000gR0#2%10'0o"). Qed.

Lemma mmap_destructive_errnos_nil : mmap_destructive_errnos = [].
Proof.
ltac2:(KReplay.run1 (kr_t_Gap04 ()) [] "p;1p;2g006_j12Tg006?j11Tg000Mj20Tg000gR0#2%10'0o"). Qed.

Lemma errno_from_nil_in : forall e, ~ In e (mmap_errnos_when false).
Proof. intros e H. exact H. Qed.

Lemma mmap_errnos_when_incl : forall b e, In e (mmap_errnos_when b) -> In e mmap_errnos.
Proof. intros [|] e H; [exact H | destruct H]. Qed.

Lemma mprotect_errnos_when_incl : forall b e, In e (mprotect_errnos_when b) -> In e mprotect_errnos.
Proof. intros [|] e H; [exact H | destruct H]. Qed.
