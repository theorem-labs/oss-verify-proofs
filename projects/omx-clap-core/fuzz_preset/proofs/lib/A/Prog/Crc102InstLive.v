(* fuzz_preset, image A' (the #102 asan image, pinned 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the walk
   of check_reject_clean (Wcrc102.v) at the seam's instance with its callee fuzz_alloc_live DISCHARGED (h-pre-b1's
   request through the lead, 19:06Z). rule 24: proves function check_reject_clean (ported; no #102 copy exists).
   check_reject_clean_holds_A102_inst_live is Crc102InstA.v's check_reject_clean_holds_A102_inst (B := AD2l.TfibB,
   ARx := c102_ARx = a Theorem Labs lane's ec_ARx body at CfParams_preset, PI := prh_img_A, PA := PI_prog_A) with:
   - LIVE closed by a Theorem Labs lane's A' walk of fuzz_alloc_live (commit f5123281fbe2,
     lib/A/Prog/PwAllocSurf.v, on the #102 integration line by path since 08db2cddc35): fuzz_alloc_live_holds_rl, the RL-generic form
     of fuzz_alloc_live_holds (which is it at RL := prh_room_live_a8 CfParams_preset, PwAllocSurf.v:796-798), against
     the tfuzz_alloc_live_specX (PRH_FnAlloc.v:71, blob 83fe93bc86e2) exactly. Its allocator relation is
     ARcf /\ xs_placed_cf at CfParams_preset over PI_prog_A's segments, which is c102_ARx by conversion; its only
     Section hypothesis, PST_unowned, is not used by that theorem (it serves fuzz_alloc_peak_reset / fail only);
   - SK fixed at a Theorem Labs lane's preset_sink_head (lib/A/PresetCfnA.v of the #102 interface, which builds on the #102 integration line since its
     d1659777b723: prh_ledger at thirteen arguments).
   The one premise left is BCMP: the bcmp row with the memnorm keep (Reusable/YGcallMxmn.v:265 abcmp_realizes_xm) at
   the listing's __wrap_bcmp; owner: the bcmp realizer's lane, c-libc-stdio (its po_memcmp_cf row with the nested bcmp
   row, Reusable/YGcallCmp.v:3-6). No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfParamsPreset PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crc102InstA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PwAllocSurf.
Import ListNotations.
Open Scope Z_scope.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Theorem check_reject_clean_holds_A102_inst_live :
  YGcallMxmn.abcmp_realizes_xm rsegs AD2l.TfibB c102_ARx (A_prog_sigma AS___wrap_bcmp) ->
  tcheck_reject_clean_specX (cp := CfParamsPreset.CfParams_preset) (PI := prh_img_A) (RL := RL) (PA := PI_prog_A)
    AD2l.TfibB c102_ARx PresetCfnA.preset_sink_head.
Proof.
intros BCMP.
exact (check_reject_clean_holds_A102_inst (RL := RL) PresetCfnA.preset_sink_head BCMP
  (PwAllocSurf.fuzz_alloc_live_holds_rl (SK := PresetCfnA.preset_sink_head) (RL := RL) AD2l.TfibB)).
Qed.
End L.

(* ---- the Qed report (unit rule 16:5xZ): the elaborated statement, every implicit shown, and the assumptions ---- *)
Set Printing Implicit.
Unset Printing Notations.
Print check_reject_clean_holds_A102_inst_live.
Unset Printing Implicit.
Set Printing Notations.
Print Assumptions check_reject_clean_holds_A102_inst_live.
