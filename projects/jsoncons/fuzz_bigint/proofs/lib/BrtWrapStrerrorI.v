(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 BrtInv BrtFsInv BrtWrapStrerror.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Theorem art_astrerror_r22 : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> forall (L : asan_layout) (IL : icpt_layout),
  hl_segs L = ASEGS -> hl_img_lo L = 0x10000 -> hl_img_hi L = 0x634000 -> hl_tp L = rn_tp rn ->
  rn_tp rn = 0x611908 -> rn_loff rn = 0x10 -> rn_key rn = 0 -> rn_tsd rn = 0x632cb0 ->
  (forall a, 0x611918 <= a < 0x61191c -> hl_rt_static L a) ->
  icl_strerror_r IL = 0x4de84 -> icl_scr_strerror IL = 4320 -> icl_strerror_cells IL = [(0x6118d8, 8, 0x631bd0); (0x631bf8, 8, 0)] ->
  icl_sro_lo IL = 0x10000 -> icl_sro_hi IL = 0xd8000 ->
  astrerror_r22_spec L (rn_ar rn) IL scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L IL HLsegs HLlo HLhi HLtp Htp Hloff Hkey0 Htsd HLlsan E1 E2 E3 E4 E5 fx R M model LB FF LK cr A Kt. cbv zeta.
  intros INV Hh HMI H10 H11 H12 H4 Hret AST SPT APP BUFW SHZ CELLS ROC KT0 POST. rewrite HLsegs, E1, E2, E3, E4, E5 in *. rewrite HLtp in H4.
  inversion CELLS as [|c1 l1 C1 CL1]; subst. inversion CL1 as [|c2 l2 C2 CL2]; subst. cbn [fst snd Z.to_nat Pos.to_nat] in C1, C2.
  apply (art_wrap_strerror22 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi Htp Hloff Hkey0 Htsd HLlsan R M model LB FF LK cr A Kt INV Hh HMI H10 H11 H12 H4 Hret AST SPT BUFW SHZ C1 C2 ROC KT0).
  intros fx' R' M' model' E10 RP MSG PRES SDEF GROW RT MI' RI'. exact (POST fx' R' M' model' E10 RP MSG PRES SDEF GROW RT MI' RI').
Qed.
