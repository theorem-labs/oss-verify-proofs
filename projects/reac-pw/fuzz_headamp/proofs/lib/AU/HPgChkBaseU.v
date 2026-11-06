(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgChkBase.v (its image-A block) for
   image B (fuzz_headamp.asan-ubsan, lib/AU/Img0U.v rsegs): the image's facts, the .got word 0x9c7f0 and the cell
   0xa5238, the regions at them, the entry state and the walk's prelude; everything image-independent is
   HPgChkBase's. *)
(* The image-B instance of the check-function walk plumbing (fuzz_headamp.asan-ubsan, unstripped sha256
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff; the pinned 53edda9bdeeb has the same loaded
   bytes except .note.gnu.build-id). Proves no function (kind: walk plumbing).

   Measured on the pinned file (pyelftools over PT_LOAD): the eight bytes at the .got word 0x9c7f0 hold 0xa5238,
   the address of __asan_shadow_memory_dynamic_address (the shadow-offset cell, .bss of the RW segment
   [0x9e4e8, 0x5f9ab0)); every image-B check function loads it by `auipc; ld` (= 0x9c7f0) and `ld aY,0(aX)`. The
   walks take HBgot : as_got_shadow B = 0x9c7f0 and HBcell : as_shadow_cell B = 0xa5238. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgChkBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image's code and segments ---- *)
Lemma hcu_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma hcu_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* ---- the shadow offset: the .got word and the cell ---- *)
Definition HCU_GOT_SH : Z := 0x9c7f0.
Definition HCU_SH_CELL : Z := 0xa5238.
Lemma hcu_got_img : forall x, HCU_GOT_SH <= x < HCU_GOT_SH + 8 -> in_img rsegs x.
Proof. apply hc_in_img_of_b. vm_compute. reflexivity. Qed.
Lemma hcu_cell_img : forall x, HCU_SH_CELL <= x < HCU_SH_CELL + 8 -> in_img rsegs x.
Proof. apply hc_in_img_of_b. vm_compute. reflexivity. Qed.

(* ---- the regions at image B's .got word and cell (the literal forms the walks unfold) ---- *)
Definition hcu_got_region : YP09.region :=
YP09.mkRegion None HCU_GOT_SH (HCU_GOT_SH + 8) 0 0 [YP09.mkChunk HCU_GOT_SH (CVal 8 (SLit HCU_SH_CELL))].
Definition hcu_cell_region : YP09.region :=
YP09.mkRegion None HCU_SH_CELL (HCU_SH_CELL + 8) 0 0 [YP09.mkChunk HCU_SH_CELL (CVal 8 hc_Bx)].
Definition hcu_base_regions : smem := [hc_stack_region; hcu_got_region; hcu_cell_region].
Definition ss_hcu (pc : Z) (ov : list (bv 5 * sv)) (rs : smem) (fs : list (nat * afact)) : sstate :=
mkSS pc (hc_sr ov) (hcu_base_regions ++ rs) None (hc_facts fs).
Lemma hcu_app_apart : forall p n, (forall x, p <= x < p + n -> ~ in_img rsegs x) -> 0 < n ->
(p + n <= HCU_GOT_SH \/ HCU_GOT_SH + 8 <= p) /\ (p + n <= HCU_SH_CELL \/ HCU_SH_CELL + 8 <= p).
Proof. intros p n H Hn. exact (hc_app_apart_at HCU_GOT_SH HCU_SH_CELL p n hcu_got_img hcu_cell_img H Hn). Qed.

Section ib. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state: the save slot, the .got word and the cell, then the walk's data regions rs and facts fs *)
Lemma hcu_entry : forall pc ov xs (rs : smem) fs (W : world rsegs) regs memc, 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs (hc_extra xs)) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 ->
rdword (aview rsegs (w_H W) memc) HCU_GOT_SH = Some HCU_SH_CELL ->
rdword (aview rsegs (w_H W) memc) HCU_SH_CELL = Some SHADOW_OFF ->
regions_wf (hcu_base_regions ++ rs) = true ->
Forall (region_ok rsegs (Ereg regs (hc_extra xs)) (mrestrict (w_H W) memc)) rs ->
zpairwise_disjoint (map (extent_of_region (Ereg regs (hc_extra xs))) (hcu_base_regions ++ rs)) ->
atoms_ok (Ereg regs (hc_extra xs)) ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF hc_SB hc_SB 0) :: fs) ->
st_ok rsegs (Ereg regs (hc_extra xs)) (ss_hcu pc ov rs fs)
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov xs rs fs W regs memc Hpc. apply (hc_entry_at HCU_GOT_SH HCU_SH_CELL); unfold HCU_GOT_SH, HCU_SH_CELL; lia.
Qed.
End ib.
Ltac hcu_prelude := hc_prelude_with hcu_wx hcu_segs_low.
