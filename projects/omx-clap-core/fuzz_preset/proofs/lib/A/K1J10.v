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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PRH_ImgB.
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
(* at mem0 every byte reads 0, so the slot word rdword reads is 0 *)
Lemma rd0 : forall {fx : YK11.FPState} segs a, rdword (YG0n.aview segs (YA0n.w_H (W0 segs)) mem0) a = Some 0.
Proof. intros fx segs a. unfold rdword, YG0n.aview, YP09.mbyte, YK04.mrestrict, mem0, W0. cbn [YA0n.w_H option_map]. reflexivity. Qed.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}.
Lemma ledger28_B : prh_ledger (PI := PRH_ImgB.prh_img_B) (cp := CfParamsPreset.CfParams_preset) K1BatchSat.TB ly28 S28 []
  (W0 pa_segs) mem0 [] 0 0 0 0 0 0.
Proof.
  unfold prh_ledger, prh_glob, prh_most, prh_own. cbn [W0 YA0n.w_H].
  split; [|split; [constructor | split; [constructor | cbn [map]; constructor]]].
  split; [apply vz|]. split; [apply vz|]. split; [apply vz|]. split; [apply vz|]. split; [apply vz|].
  split; [split; [apply vz | lia]|]. split; [split; [apply vz | left; reflexivity]|].
  change (Ledger.lsum []) with 0. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
Qed.
(* (A) the cursor texts jointly at ONE state on B', against the PINNED prh_cw_pj: CW = CWB2 (t0 + len) 0 - parse_items
   at arm 1 (its trace at the cursor's end), parse_string at arm 2 at the slot word rdword READS at S28's memory (0, rd0);
   with the depot's NoDup, the ADMISSION of both cursor frees' traces, option (b)'s cw_of at the same words, room_live_cf,
   iface_room_pos and the ledger. Not here: ARcfx (S28_not_ARcfx), the frame-window facts, the meter. *)
Theorem cursor_joint_B : forall regs t0 len, t0 + len <> 0x53964 ->
  YGcfRoomLive.room_live_cf (cp := CfParamsPreset.CfParams_preset) S28 /\
  PresetRoomPos.iface_room_pos K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6 28 [] hist28 S28 /\
  prh_cw_pj (PI := PRH_ImgB.prh_img_B) K1BatchSat.TB (K1BatchSat.CWB2 (t0 + len) 0) (W0 pa_segs) mem0 regs t0 len /\
  YCbqGwild.wild_room (as_universe K1BatchSat.TB) (K1BatchSat.CWB2 (t0 + len) 0) 0 (st_depot S28) /\
  List.NoDup (st_depot S28) /\
  admits (as_universe K1BatchSat.TB) (prh_trace 0x53964 0x87f34 [t0 + len]) S28 /\
  admits (as_universe K1BatchSat.TB) (prh_trace 0x53964 0x885e4 [0]) S28 /\
  YCbqGwild.wild_room (as_universe K1BatchSat.TB)
    (YCbqGwild.cw_of (u_wild (as_universe K1BatchSat.TB)) (t0 + len) 0) 0 (st_depot S28) /\
  prh_ledger (PI := PRH_ImgB.prh_img_B) (cp := CfParamsPreset.CfParams_preset) K1BatchSat.TB ly28 S28 [] (W0 pa_segs) mem0 [] 0 0 0 0 0 0.
Proof.
  intros regs t0 len Hw.
  assert (Rcw : YCbqGwild.wild_room (as_universe K1BatchSat.TB) (K1BatchSat.CWB2 (t0 + len) 0) 0 (st_depot S28))
    by (apply room28; rewrite K1BatchSat.wmaxB; cbn [length K1BatchSat.CWB2]; lia).
  refine (conj live28_A (conj iface28 (conj (K1BatchSat.cw_pj_B _ _ _ _ _ 0 (rd0 _ _)) (conj Rcw (conj nodup28 (conj _
    (conj _ (conj _ ledger28_B)))))))).
  - apply (YCbqGwild.wild_room_admits _ _ 0 S28 _ nodup28 Rcw); [|left; left; reflexivity].
    apply K1BatchSat.inU_cursor; [lia | vm_compute; repeat first [left; reflexivity | right]].
  - apply (YCbqGwild.wild_room_admits _ _ 0 S28 _ nodup28 Rcw); [|left; right; left; reflexivity].
    apply K1BatchSat.inU_cursor; [lia | vm_compute; repeat first [left; reflexivity | right]].
  - apply room28. rewrite YCbqGwild.cw_of_length, K1BatchSat.wmaxB. lia.
Qed.
(* CONTROL at the same state: the arm-1-for-both CW (CWB (t0 + len)) FAILS the pin, since the slot word read is 0 *)
Theorem cursor_joint_B_ctl : forall regs t0 len, t0 + len <> 0 -> t0 + len <> 0x8633c -> t0 + len <> 0x53964 ->
  ~ prh_cw_pj (PI := PRH_ImgB.prh_img_B) K1BatchSat.TB (K1BatchSat.CWB (t0 + len)) (W0 pa_segs) mem0 regs t0 len.
Proof. intros regs t0 len H1 H2 H3. apply (K1BatchSat.cw_pj_B_ctl _ _ _ _ _ 0); [apply rd0 | lia | exact H2 | lia | exact H3]. Qed.
End s.
Print Assumptions cursor_joint_B. Print Assumptions cursor_joint_B_ctl.
