(* fuzz_preset image A' (asan, #102 pin 1be0f53d, unstripped twin bff8519b): PST_unowned, the B half of YCbqG's PST_ok
   at PST := prh_pst (PwAllocSurf.v Section T, carried by PRW_AfnBridge.v Section w into
   pcc_fuzz_alloc_peak_reset_of_walk, afn_fuzz_alloc_peak_reset_of_walk and afn_fuzz_alloc_fail_of_walk): no byte of
   alloc.c's seven statics (#102: g_live, g_peak, g_count, g_fail_at, g_ran_out, g_most, g_own_ran_out: prh_img_A's
   pi_g_<x> / pi_gz_<x>) is a byte of an owned static area of B.
   rule 24: no function proved. This file proves an image fact and instantiates the bridge's entries with it.
   THE LAW IT USES: AF0m.TfibSyms B, field ts_owned (as_owned_static B = Tfib_owned_static), the image premise the
   bridge's own pcc_stack_malloc_of_fcapi and every lib/A walk over B already take. With it the statement is a
   computation: every static is disjoint from every row of Tfib_owned_static (pst_off_owned_A, decided over the WHOLE
   table and the whole prh_pst list, so a table that gains rows, in any order, keeps the proof). Each static's redzone
   row starts AT THE NEXT BYTE after it, at g + width, with zero bytes between: [g + width, next global) is the asan
   globals' guard run. Measured on A' over lib/A/AF0m.v blob 97f423adf6eb (93 rows) and lib/A/PRH_Img.v blob
   934516a622e8: the gap ABOVE each of the seven statics is 0 (rows 86-92, 0-based); the gap BELOW is 0 for g_live
   0x5dd560, g_peak 0x5dd580, g_count 0x5dd5a0, g_ran_out 0x5dd5c0 and g_most 0xa65e0 (an owned row ends exactly at
   its first byte), 40 for g_fail_at 0xa65c0 and 65584 for g_own_ran_out 0x5dd540. THE MARGIN IS ZERO BY
   CONSTRUCTION, so ANY regeneration of AF0m's Tfib_owned_static or of PRH_Img's statics MUST re-run pst_off_owned_A's
   vm_compute: there is no slack. Image B is no different (h-pre-b1's lib/B/Prog/PwPstUnownedB.v,
   origin/cold/h-pre-b1-bridgeb cbf7b06fc3c).
   THE FINAL INSTANCE: B := AD2l.TfibB (lib/A/AD2l.v blob eb321db7a357), whose TfibSyms is AD2l.TfibB_syms (Qed), so the
   premise is satisfiable (the generic lemma is not vacuous) and the entries close at TfibB with no open hypothesis
   (section 2). The bridge's entries are unchanged: section 2 applies them at every RL : PrhRoomLive (Section w's
   Context, as B's twin PwPstUnownedB.v does); the #102 slot field pcc_fuzz_alloc_peak_reset is at RL :=
   prh_room_live_a8 (cp := CfParams_preset) (PRH_Base.v, a Definition, not an Instance, so it is passed explicitly).
   THE #102 RE-CUT (from commit 1faacee1304, blob 578ac794944c): section 1 is unchanged
   in text (prh_pst has seven cells on #102; the computation covers them); section 2 follows the bridge's #102 re-cut:
   pcc_fuzz_alloc_peak_reset_of_walk_TfibB states the slot field (the text at iface_ARx), the former afn_spec_cf
   entry is afn_fuzz_alloc_peak_reset_of_walk_TfibB, and afn_fuzz_alloc_fail_of_walk_TfibB is unchanged.
   NUMERALS: none in code (no address, no width: the statics are prh_img_A's, the areas AF0m's). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
AB1v Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m AD2l PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwAllocSurf PRW_AfnBridge.
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

(* the seven statics of image A' are off every owned static area of the image's symbol record *)
Lemma pst_off_owned_A : pu_off_b (@prh_pst prh_img_A) AF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Theorem pst_unowned_A : forall B : asyms, AF0m.TfibSyms B ->
  forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> ~ Exists (in_zr a) (as_owned_static B).
Proof. intros B TB a Ha. rewrite (AF0m.ts_owned _ TB). exact (pu_off_sound _ _ a pst_off_owned_A Ha). Qed.

(* at the final instance's symbol record, with no premise *)
Theorem pst_unowned_TfibB :
  forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> ~ Exists (in_zr a) (as_owned_static AD2l.TfibB).
Proof. exact (pst_unowned_A AD2l.TfibB AD2l.TfibB_syms). Qed.

(* ==== 2. the bridge's entries that carry PST_unowned, at B := TfibB, closed ==== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).

(* the #102 slot's field pcc_fuzz_alloc_peak_reset (PresetCfnA.v preset_callee_contracts) at TfibB *)
Theorem pcc_fuzz_alloc_peak_reset_of_walk_TfibB :
  @PRH_FnAlloc.tfuzz_alloc_peak_reset_specX fx rc CfParams_preset PresetCfnA.preset_prh_img
    (@prh_room_live_a8 CfParams_preset) A_prog_listing PI_prog_A AD2l.TfibB
    (PresetCfnA.iface_ARx (L := A_prog_listing) (PA := PI_prog_A) AD2l.TfibB) PresetCfnA.preset_sink_head.
Proof. exact (pcc_fuzz_alloc_peak_reset_of_walk AD2l.TfibB pst_unowned_TfibB). Qed.

Theorem afn_fuzz_alloc_peak_reset_of_walk_TfibB : forall ctx fr bud,
  PresetCfnA.afn_spec_cf (L := A_prog_listing) (PA := PI_prog_A) AD2l.TfibB
    (PresetCfnA.A_fuzz_alloc_peak_reset (L := A_prog_listing) (PA := PI_prog_A))
    (prwA_F_peak_reset AD2l.TfibB ctx fr bud).
Proof. exact (afn_fuzz_alloc_peak_reset_of_walk AD2l.TfibB pst_unowned_TfibB). Qed.

Theorem afn_fuzz_alloc_fail_of_walk_TfibB : forall ctx fr bud,
  PresetCfnA.afn_spec_cf (L := A_prog_listing) (PA := PI_prog_A) AD2l.TfibB (SIGMA AS_fuzz_alloc_fail)
    (prwA_F_fail AD2l.TfibB ctx fr bud).
Proof. exact (afn_fuzz_alloc_fail_of_walk AD2l.TfibB pst_unowned_TfibB). Qed.
End w.
