(* fuzz_preset image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43): PST_unowned, the B half of
   YCbqG's PST_ok at PST := prh_pst (PwAllocSurfB.v Section T :773, carried by PRW_AfnBridgeB.v Section w into
   pcc_fuzz_alloc_peak_reset_of_walk, afn_fuzz_alloc_fail_of_walk and the #102 record field
   pcc102_fuzz_alloc_peak_reset_of_walk): no byte of the seven harness statics of the kit's prh_pst (PRH_Base.v :448-451:
   alloc.c's g_live, g_peak, g_count, g_fail_at, g_ran_out, #102's g_most, and fuzz_preset.c's g_own_ran_out:
   prh_img_B's pi_g_<x> / pi_gz_<x>) is a byte of an owned static area of B.
   RELOCATED AND RE-FIT 2026-10-29 from the old-pin file (a working branch 5f6a2b85e1b9, blob eb94eafd686c,
   image f8f98a95, five statics over 91 owned rows): the code is unchanged; prh_pst now has seven cells and YF0m's
   Tfib_owned_static 93 rows, both generated for B' (lib/B/PRH_ImgB.v blob 3216eca68342, lib/Reusable/YF0m.v blob
   f82202ebccdf), and pst_off_owned_B decides the new lists. Section 2 gains the closed #102 record field at TfibB.
   rule 24: no function proved. This file proves an image fact and instantiates the bridge's entries with it.
   THE LAW IT USES: YF0m.TfibSyms B, field ts_owned (as_owned_static B = Tfib_owned_static), the image premise the
   bridge's own pcc_stack_malloc_of_fcapi (PRW_AfnBridgeB.v section 5) already takes. With it the statement is a
   computation: every static is disjoint from every row of Tfib_owned_static (pst_off_owned_B, decided over the WHOLE
   table and the whole prh_pst list, so a table that gains rows, in any order, keeps the proof). Each static's redzone
   row starts at its last byte + 1 ([g + width, next global): the asan globals' guard runs; on image B' rows 86-92
   (0-based) of YF0m's 93: (0xa6e08, 0x18), (0xa6e28, 0x18), (0x5ddd81, 0x1f), (0x5ddda8, 0x18), (0x5dddc8, 0x18),
   (0x5ddde8, 0x18), (0x5dde01, 0x1f)), so the disjointness is tight, not slack. For g_live 0x5ddda0, g_peak
   0x5dddc0, g_count 0x5ddde0, g_ran_out 0x5dde00 and g_most 0xa6e20 the owned row BELOW also touches the static
   ((0x5ddd81, 0x1f), (0x5ddda8, 0x18), (0x5dddc8, 0x18), (0x5ddde8, 0x18), (0xa6e08, 0x18) end exactly at its first
   byte): zero gap on BOTH sides. g_fail_at 0xa6e00 has 40 bytes below it (row 0 ends at 0xa6dd8), g_own_ran_out
   0x5ddd80 65584 bytes (row 3 ends at 0x5cdd50). Measured 2026-10-29 by evaluating line 1786 of YF0m.v against
   prh_img_B's seven cells (a Theorem Labs lane's internal file bridgeb-checks.md). THE MARGIN IS ZERO BY CONSTRUCTION, so
   ANY regeneration of YF0m's Tfib_owned_static or of PRH_ImgB's statics MUST re-run pst_off_owned_B's vm_compute:
   there is no slack.
   THE FINAL INSTANCE: the composition states the #102 callee record (PresetCfnB.v preset_callee_contracts :950-992)
   at B := YD2l.TfibB; YD2l.TfibB_syms (Qed, lib/Reusable/YD2l.v blob 95803a8b9493) is its TfibSyms, so the premise
   is satisfiable (the generic lemma is not vacuous) and the entries close at TfibB with no open hypothesis
   (section 2). The bridge's entries are unchanged: section 2 applies them, each at every run's data words DW.
   NUMERALS: none in code (no address, no width: the statics are prh_img_B's, the areas YF0m's). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YP08 YL0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwAllocSurfB PRW_AfnBridgeB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ==== 1. PST_unowned from TfibSyms B ==== *)
(* every range of P is disjoint from every range of O, decided over both whole lists *)
Definition pu_off_b (P O : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun o => (fst r + snd r <=? fst o) || (fst o + snd o <=? fst r)) O) P.
Lemma pu_off_sound : forall P O a, pu_off_b P O = true -> Exists (in_zr a) P -> ~ Exists (in_zr a) O.
Proof.
intros P O a H HP HO. apply Exists_exists in HP as (r & Hr & Ha). apply Exists_exists in HO as (o & Ho & Hb).
unfold pu_off_b in H. rewrite forallb_forall in H. specialize (H r Hr). rewrite forallb_forall in H.
specialize (H o Ho). unfold in_zr in Ha, Hb.
apply Bool.orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* the seven statics of image B' are off every owned static area of the image's symbol record *)
Lemma pst_off_owned_B : pu_off_b (@prh_pst prh_img_B) YF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Theorem pst_unowned_B : forall B : asyms, YF0m.TfibSyms B ->
  forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> ~ Exists (in_zr a) (as_owned_static B).
Proof. intros B TB a Ha. rewrite (YF0m.ts_owned _ TB). exact (pu_off_sound _ _ a pst_off_owned_B Ha). Qed.

(* at the final instance's symbol record (YD2l.TfibB), with no premise *)
Theorem pst_unowned_TfibB :
  forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> ~ Exists (in_zr a) (as_owned_static YD2l.TfibB).
Proof. exact (pst_unowned_B YD2l.TfibB YD2l.TfibB_syms). Qed.

(* ==== 2. the bridge's entries that carry PST_unowned, at B := TfibB, closed ==== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).

Theorem pcc_fuzz_alloc_peak_reset_of_walk_TfibB : forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) YD2l.TfibB PresetCfnB.A_fuzz_alloc_peak_reset
    (prwB_F_peak_reset YD2l.TfibB ctx fr bud DW).
Proof. exact (pcc_fuzz_alloc_peak_reset_of_walk YD2l.TfibB pst_unowned_TfibB). Qed.

Theorem afn_fuzz_alloc_fail_of_walk_TfibB : forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) YD2l.TfibB (SIGMA AS_fuzz_alloc_fail)
    (prwB_F_fail YD2l.TfibB ctx fr bud DW).
Proof. exact (afn_fuzz_alloc_fail_of_walk YD2l.TfibB pst_unowned_TfibB). Qed.

(* the #102 callee record's field pcc_fuzz_alloc_peak_reset (PresetCfnB.v :980-981) at B := TfibB, closed: the
   composition cites this one; the record's other three accessor fields walked here
   (PRW_AfnBridgeB.pcc102_fuzz_alloc_{live,count,peak}_of_walk) take no PST_unowned *)
Theorem pcc102_fuzz_alloc_peak_reset_TfibB : forall fy : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_peak_reset_specX fy rc CfParams_preset PresetCfnB.preset_prh_img
    (@prh_room_live_a8 CfParams_preset) B_prog_listing PI_prog_B YD2l.TfibB
    (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) YD2l.TfibB) PresetCfnB.preset_sink_head.
Proof. exact (pcc102_fuzz_alloc_peak_reset_of_walk YD2l.TfibB pst_unowned_TfibB). Qed.
End w.
