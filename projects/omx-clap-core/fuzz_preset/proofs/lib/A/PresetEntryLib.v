(* omx-clap-core/fuzz_preset (image A's interface; the AU twin lib/AU/PresetCfnB.v has the same LIVE_LIB body, :275 at
   d6318e886fd9, :270 on int102):
   THE HARNESS ENTRY'S LIVE BUDGET, row ENTRY-SUMS (h-pre-b2; statement owner c-omx-alloc, addition (a) of 00:23Z).
   Nothing here is a function's proof (rule 24); kind: model bound lemma.

   WHAT IT SAYS. At LLVMFuzzerTestOneInput's entry every earlier call is closed, so blocks_bytes S is at most the
   driver's blocks (DRV_BYTES), and the entry budget LIVE_LIB = 3 * 2 ^ 32 fits in CLOSED_ROOM = LIVE_MAX - DRV_BYTES
   (PresetLiveBytes.entry_sum_closed):
     live_lib_fits    0 <= LIVE_LIB <= CLOSED_ROOM
     lcut_fits        every budget within LIVE_LIB is within CLOSED_ROOM: the walk's cut budgets ec_lcut
                      (ec_lcut_ok, lib/A/Ent102CutsA.v:561 at d6318e886fd9: 0 <= ec_lcut E i <= LIVE_LIB) and its
                      witness sat_lcut (lib/A/Ent102PaySat.v:358 sat_lraw_le, at most 9,823,176,288, check_round_trip's
                      LIVE_check_round_trip <= 9,017,853,504 inside it, :226)
     live_lib_entry   the interface pre's conjunct lib/A/PresetCfnA.v:803 `blocks_bytes S + LIVE_LIB <= LIVE_MAX`
                      from its own :801 iface_room_at (iface_room_pos_entry :566) and Wf_cf (PresetCfnA.v lines at
                      d6318e886fd9; on int102 they are :803, :802 and :569).
   The walk's own copy of the conjunct, Ent102CutsA.v:397 (its LIVE_LIB :90 is the same 3 * 2 ^ 32), is
   entry_sum_closed at n := LIVE_LIB from ec_pre's :388 / :390 and live_lib_fits.
   A SEPARATE FILE so that lib/A/PresetEntrySums.v (the texts' arithmetic) does not Require the interface. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames YG01cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoomPos PresetLiveBytes.
Import ListNotations.
Local Open Scope Z_scope.

Lemma live_lib_fits : 0 <= PresetCfnA.LIVE_LIB <= PresetLiveBytes.CLOSED_ROOM.
Proof.
  assert (LL : PresetCfnA.LIVE_LIB = 12884901888) by reflexivity.
  assert (LM : LIVE_MAX = 17179869184) by reflexivity.
  unfold PresetLiveBytes.CLOSED_ROOM, PresetLiveBytes.DRV_BYTES. rewrite LL, LM. lia.
Qed.

Lemma lcut_fits : forall l, 0 <= l <= PresetCfnA.LIVE_LIB -> 0 <= l <= PresetLiveBytes.CLOSED_ROOM.
Proof. intros l H. pose proof live_lib_fits. lia. Qed.

Theorem live_lib_entry :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (H0 : list Z) (hist : list YG00.chunk) (S : astate),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  PresetCfnA.iface_room_at sm x os H0 hist S ->
  blocks_bytes S + PresetCfnA.LIVE_LIB <= LIVE_MAX.
Proof.
  intros U sm x os H0 hist S HW HA.
  pose proof (PresetCfnA.iface_room_pos_entry sm x os [] H0 hist S HA) as HP. rewrite app_nil_r in HP.
  exact (PresetLiveBytes.entry_sum_closed U sm x os _ H0 hist S _ HW HP eq_refl live_lib_fits).
Qed.

Locate live_lib_fits.
Print Assumptions live_lib_fits.
Locate lcut_fits.
Print Assumptions lcut_fits.
Locate live_lib_entry.
Print Assumptions live_lib_entry.
