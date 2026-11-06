(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA PmHeapIfaceA ArtBridge Pm9ArtInv Pm9ArtFsInv Pm9ArtIfaceInst Pm9ArtIfaceInstFree Pm9ArtWrapSmallocI Pm9ArtWrapSfree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition art_LX : asan_layout_x := ALX (fun _ => 0x65888) 0x103a8.

Theorem art_pm_inst_ok : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, sc_alloc scfg = false -> wx_segs_nowrap ASEGS ->
  bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX ->
  rn_tp rn = 0x691d90 -> rn_key rn = 0 -> rn_tsd rn = 0x6b3248 -> rn_loff rn = 0x10 ->
  pm_asan_iface_ok art_L art_LX (rn_ar rn) art_C scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff. constructor.
  - exact (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff
             (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc Hwx STATIC Htp) (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx Htp)).
  - cbn [art_LX hlx_stack_free hlx_sfree_pat]. apply (art_asfree5 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L); try reflexivity. symmetry. exact Htp.
Qed.
