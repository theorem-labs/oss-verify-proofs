(* A measurement file (BATCH-SAT joint witnesses): it proves no function. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YM05 YG00 YG01 YG0f YG0d YGcfNames YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YGcfRoom YGcfFrees YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YCej YI04 YP09 YK04 YA0n YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Img CfImgA AD2l ACej CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx PRH_FnPj K1BatchSat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt
  PresetLiveBounds PresetRoom.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import K1JBase K1J1a K1J1b K1J1c K1J1g K1J1e K1J2 K1J3 K1J4 K1J5.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
Local Open Scope Z_scope.
Lemma iface28 : PresetRoomPos.iface_room_pos K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6 28 [] hist28 S28.
Proof.
unfold PresetRoomPos.iface_room_pos.
(* the quarantined frees of this prefix are all its frees (every request is within kQuarantineMax), by computation *)
assert (Eq : PresetRunQ.hfrees_q (firstn 28 (PresetRun.hruns K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6)) =
  PresetRun.hfrees (firstn 28 (PresetRun.hruns K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6))) by (vm_compute; reflexivity).
rewrite Eq. refine (conj i28a (conj i28b (conj i28c (conj i28d (conj i28e _))))).
(* the count clause: S28 has no secondary map entry, so both meters read 0 *)
intros _. split; apply Z.leb_le; vm_compute; reflexivity.
Qed.
Lemma depot28 : st_depot S28 = [].
Proof. reflexivity. Qed.
Lemma nodup28 : List.NoDup (st_depot S28).
Proof. rewrite depot28. constructor. Qed.
Lemma room28 : forall U set k, (length set + k <= u_wmax U)%nat -> YCbqGwild.wild_room U set k (st_depot S28).
Proof. intros U set k H. rewrite depot28, <- YCbqGwild.init_depot_nil. exact (K1BatchSat.wr_init U set k H). Qed.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}.
(* (A) tx_put at its first GROW, jointly at ONE state (S28, position 28 = HMal 2, len0 = cap0 = n = 0, f0 = 0), with
   the depot (field 25's NoDup) and the admission of the grow's realloc trace that the guarded room gives *)
Theorem tx_put_joint_A :
  YGcfRoomLive.room_live_cf (cp := CfParamsPreset.CfParams_preset) S28 /\
  PresetRoomPos.iface_room_pos K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6 28 [] hist28 S28 /\
  YCbqGwild.wild_room (as_universe K1BatchSat.TA) [] (length (PRH_FnTx.prhtx_evs 0 0 [0])) (st_depot S28) /\
  prh_cons_from K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6 28 (length (PRH_FnTx.prhtx_evs 0 0 [0])) /\
  nth_error (PresetRun.hruns K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6) 28 = Some (PresetReqAt.HMal 2) /\
  blocks_bytes S28 + PRH_FnTx.LIVE_tx <= LIVE_MAX /\ 2 < @cf_malloc_max CfParamsPreset.CfParams_preset /\
  YM05.alloc_ceiling < ly_top ly28 /\
  PRH_FnTx.prhtx_trace (ci := CfImgA.CfImg_A) (PI := PRH_Img.prh_img_A) K1BatchSat.TA ly28 (W0 pa_segs) mem0 YM05.alloc_ceiling /\
  prh_ledger (PI := PRH_Img.prh_img_A) (cp := CfParamsPreset.CfParams_preset) K1BatchSat.TA ly28 S28 [] (W0 pa_segs) mem0 [] 0 0 0 0 0 0 /\
  List.NoDup (st_depot S28) /\
  (forall t ch, admits (as_universe K1BatchSat.TA)
     (unwind_of_chain (@cf_pc_realloc_ra0 CfImgA.CfImg_A) ((t, @pi_ret_tx_realloc PRH_Img.prh_img_A, t) :: ch)) S28).
Proof.
  destruct tx3_A as (R & C & E & Bb & Mm). destruct trace28_A as (Lt & Tr).
  refine (conj live28_A (conj iface28 (conj R (conj C (conj E (conj Bb (conj Mm (conj Lt (conj Tr
    (conj ledger28_A (conj nodup28 _))))))))))).
  intros t ch. apply (YCbqGwild.wild_room_admits _ [] (length (PRH_FnTx.prhtx_evs 0 0 [0])) S28); [exact nodup28 | exact R | |].
  - apply K1BatchSat.tx_chain_inU_A.
  - right. vm_compute. lia.
Qed.
End s.
Print Assumptions tx_put_joint_A.
