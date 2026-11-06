(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Frame MState PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import SpecFrame SpecLeib WalkL Init.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module EF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Module MSt := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module APx := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Module SegL.
Definition IMGLO : Z := 0x10000.
Definition IMGHI : Z := 0x62f000.

Definition envW (R F : bvmap 5 word) (fc : bv 32) : env :=
  Env (fun k => if PrimInt63.eqb k 1%uint63 then rget (Core R F (Z_to_bv 64 0) fc None) (reg_of_r5 X2) else
                match r5_of_Z (to_Z k - 100) with
                | Some r => rget (Core R F (Z_to_bv 64 0) fc None) (reg_of_r5 r)
                | None => match r5_of_Z (to_Z k - 200) with Some r => reg_get F (reg_of_r5 r) | None => Z_to_bv 64 0 end
                end)
      (fun _ => []) (fun _ _ => Z_to_bv 8 0).

Lemma den_VPz : forall E k, den E (VP k wzero) = ev E k.
Proof. intros E k. apply bv_eq. apply (ValP.den_VP0 E k wzero eq_refl). Qed.

Definition FFP : rf sv := RF (VP 200%uint63 wzero) (VP 201%uint63 wzero) (VP 202%uint63 wzero) (VP 203%uint63 wzero) (VP 204%uint63 wzero) (VP 205%uint63 wzero) (VP 206%uint63 wzero) (VP 207%uint63 wzero) (VP 208%uint63 wzero) (VP 209%uint63 wzero) (VP 210%uint63 wzero) (VP 211%uint63 wzero) (VP 212%uint63 wzero) (VP 213%uint63 wzero) (VP 214%uint63 wzero) (VP 215%uint63 wzero) (VP 216%uint63 wzero) (VP 217%uint63 wzero) (VP 218%uint63 wzero) (VP 219%uint63 wzero) (VP 220%uint63 wzero) (VP 221%uint63 wzero) (VP 222%uint63 wzero) (VP 223%uint63 wzero) (VP 224%uint63 wzero) (VP 225%uint63 wzero) (VP 226%uint63 wzero) (VP 227%uint63 wzero) (VP 228%uint63 wzero) (VP 229%uint63 wzero) (VP 230%uint63 wzero) (VP 231%uint63 wzero).

Lemma FFP_ok : forall R F fc r, reg_get F (reg_of_r5 r) = den (envW R F fc) (rf_get FFP r).
Proof. intros R F fc r. destruct r; cbn [rf_get FFP f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31]; rewrite den_VPz; reflexivity. Qed.

Lemma ev1 : forall R F fc, ev (envW R F fc) 1%uint63 = rget (Core R F (Z_to_bv 64 0) fc None) (reg_of_r5 X2).
Proof. reflexivity. Qed.

Section S.
Variable it : itab.
Hypothesis HIT : itab_ok asegs it.
Variable RNG : EF.footprint.

Definition seg_post (fin : sstate -> bool) (E : env) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo hi : Z) : machine_state -> Prop :=
  fun ms' => exists st' mo' R' m',
    ms' = MSt.MS (SpecLeib.mkR_of R') F (Z_to_bv 64 (to_Z (s_pc st'))) fc None m' (APx.seg_rom asegs)
    /\ st_ok asegs WInit.OPSW E st' ms' mo' /\ fin st' = true /\ WalkL.winv asegs lo hi m m' /\ AM.mem_inv asegs m'.

Theorem fx_segment_L : forall (R F : bvmap 5 word) (pc : int) (fc : bv 32) (m : word -> option byte)
    (xf : rf sv) (facts : list fact) (next : int) (ROOM lo : Z) (stops : list int) (fuel : positive) (fin : sstate -> bool) (depth : nat),
  let E := envW R F fc in
  let ms := MSt.MS R F (Z_to_bv 64 (to_Z pc)) fc None m (APx.seg_rom asegs) in
  let sp := bv_unsigned (rget (core_of ms) (reg_of_r5 X2)) in
  WalkL.wcheck asegs it stops ROOM IMGLO IMGHI fuel fin depth (WInit.wstate ROOM pc xf FFP facts next) = true ->
  SpecLeib.shape R ->
  (forall st, fin st = true -> s_resv st = RNone) ->
  0 < ROOM < 2 ^ 40 ->
  rf_get xf X0 = VL wzero ->
  (forall r, rget (core_of ms) (reg_of_r5 r) = den E (rf_get xf r)) ->
  bv_unsigned fc < 32 ->
  facts_hold E facts ->
  AF.stk asegs m lo sp -> lo <= sp - ROOM -> 0x62f000 <= lo ->
  AM.mem_inv asegs m ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (AM.wa i) = None) ->
  EF.rng RNG (sp - ROOM) ROOM -> rng_aimg RNG ->
  EF.evtF asegs RNG (seg_post fin E F fc m (sp - ROOM) sp) ms.
Proof.
  intros R F pc fc m xf facts next ROOM lo stops fuel fin depth E ms sp HC SH FINR RR HX0 HR FC FH STK LO IMG MI RELRO RW RI.
  assert (E1 : bv_unsigned (ev E 1%uint63) = sp) by reflexivity.
  assert (HS : st_ok asegs WInit.OPSW E (WInit.wstate ROOM pc xf FFP facts next) ms WInit.MOW).
  { apply (WInit.init_ok ROOM RR E ms pc xf FFP facts next lo); try assumption; try reflexivity.
    intros r. apply FFP_ok. }
  assert (WLO : 0 <= bv_unsigned (ev E 1%uint63) - ROOM).
  { rewrite E1. destruct STK as (S0 & _). exact (Z.le_trans _ _ _ S0 LO). }
  destruct (WalkL.wcheck_sound asegs WInit.OPSW it stops ROOM IMGLO IMGHI fuel fin RNG HIT E WLO
              ltac:(rewrite E1; exact RW) ltac:(unfold IMGLO, IMGHI; exact RI) depth _ ms WInit.MOW HC HS)
    as (ms' & mo' & st' & STEPS & HS' & FIN & INV & (KF & KC & KS)).
  exists ms'. split; [exact STEPS|]. exists st', mo', (ms_regs ms'), (ms_mem ms').
  rewrite E1 in INV.
  split; [| split; [exact HS'| split; [exact FIN| split; [exact INV|]]]].
  - pose proof (so_resv _ _ _ _ _ _ HS') as RV. rewrite (FINR _ FIN) in RV. cbn [resv_ok] in RV.
    etransitivity; [apply (MSt.MS_eta ms' (so_svc _ _ _ _ _ _ HS'))|].
    f_equal.
    + exact (KS SH).
    + exact KF.
    + exact (so_pc _ _ _ _ _ _ HS').
    + exact KC.
    + exact RV.
    + exact (so_rom _ _ _ _ _ _ HS').
  - intros a b MB. pose proof (so_minv _ _ _ _ _ _ HS' a b MB) as W.
    unfold AM.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:FS; [| reflexivity].
    rewrite (W seg eq_refl). reflexivity.
Qed.
End S.
End SegL.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import ABase.TwinB.
Import SpecFrame.TwinB SpecLeib.TwinB WalkL.TwinB Init.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module EF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Module MSt := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module APx := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Module SegL.
Definition IMGLO : Z := 0x10000.
Definition IMGHI : Z := 0x631000.

Definition envW (R F : bvmap 5 word) (fc : bv 32) : env :=
  Env (fun k => if PrimInt63.eqb k 1%uint63 then rget (Core R F (Z_to_bv 64 0) fc None) (reg_of_r5 X2) else
                match r5_of_Z (to_Z k - 100) with
                | Some r => rget (Core R F (Z_to_bv 64 0) fc None) (reg_of_r5 r)
                | None => match r5_of_Z (to_Z k - 200) with Some r => reg_get F (reg_of_r5 r) | None => Z_to_bv 64 0 end
                end)
      (fun _ => []) (fun _ _ => Z_to_bv 8 0).

Lemma den_VPz : forall E k, den E (VP k wzero) = ev E k.
Proof. intros E k. apply bv_eq. apply (ValP.den_VP0 E k wzero eq_refl). Qed.

Definition FFP : rf sv := RF (VP 200%uint63 wzero) (VP 201%uint63 wzero) (VP 202%uint63 wzero) (VP 203%uint63 wzero) (VP 204%uint63 wzero) (VP 205%uint63 wzero) (VP 206%uint63 wzero) (VP 207%uint63 wzero) (VP 208%uint63 wzero) (VP 209%uint63 wzero) (VP 210%uint63 wzero) (VP 211%uint63 wzero) (VP 212%uint63 wzero) (VP 213%uint63 wzero) (VP 214%uint63 wzero) (VP 215%uint63 wzero) (VP 216%uint63 wzero) (VP 217%uint63 wzero) (VP 218%uint63 wzero) (VP 219%uint63 wzero) (VP 220%uint63 wzero) (VP 221%uint63 wzero) (VP 222%uint63 wzero) (VP 223%uint63 wzero) (VP 224%uint63 wzero) (VP 225%uint63 wzero) (VP 226%uint63 wzero) (VP 227%uint63 wzero) (VP 228%uint63 wzero) (VP 229%uint63 wzero) (VP 230%uint63 wzero) (VP 231%uint63 wzero).

Lemma FFP_ok : forall R F fc r, reg_get F (reg_of_r5 r) = den (envW R F fc) (rf_get FFP r).
Proof. intros R F fc r. destruct r; cbn [rf_get FFP f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31]; rewrite den_VPz; reflexivity. Qed.

Lemma ev1 : forall R F fc, ev (envW R F fc) 1%uint63 = rget (Core R F (Z_to_bv 64 0) fc None) (reg_of_r5 X2).
Proof. reflexivity. Qed.

Section S.
Variable it : itab.
Hypothesis HIT : itab_ok bsegs it.
Variable RNG : EF.footprint.

Definition seg_post (fin : sstate -> bool) (E : env) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo hi : Z) : machine_state -> Prop :=
  fun ms' => exists st' mo' R' m',
    ms' = MSt.MS (SpecLeib.TwinB.SpecLeib.mkR_of R') F (Z_to_bv 64 (to_Z (s_pc st'))) fc None m' (APx.seg_rom bsegs)
    /\ st_ok bsegs WInit.OPSW E st' ms' mo' /\ fin st' = true /\ WalkL.TwinB.WalkL.winv bsegs lo hi m m' /\ AM.mem_inv bsegs m'.

Theorem fx_segment_L : forall (R F : bvmap 5 word) (pc : int) (fc : bv 32) (m : word -> option byte)
    (xf : rf sv) (facts : list fact) (next : int) (ROOM lo : Z) (stops : list int) (fuel : positive) (fin : sstate -> bool) (depth : nat),
  let E := envW R F fc in
  let ms := MSt.MS R F (Z_to_bv 64 (to_Z pc)) fc None m (APx.seg_rom bsegs) in
  let sp := bv_unsigned (rget (core_of ms) (reg_of_r5 X2)) in
  WalkL.TwinB.WalkL.wcheck bsegs it stops ROOM IMGLO IMGHI fuel fin depth (WInit.wstate ROOM pc xf FFP facts next) = true ->
  SpecLeib.TwinB.SpecLeib.shape R ->
  (forall st, fin st = true -> s_resv st = RNone) ->
  0 < ROOM < 2 ^ 40 ->
  rf_get xf X0 = VL wzero ->
  (forall r, rget (core_of ms) (reg_of_r5 r) = den E (rf_get xf r)) ->
  bv_unsigned fc < 32 ->
  facts_hold E facts ->
  AF.stk bsegs m lo sp -> lo <= sp - ROOM -> 0x631000 <= lo ->
  AM.mem_inv bsegs m ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (AM.wa i) = None) ->
  EF.rng RNG (sp - ROOM) ROOM -> rng_aimg RNG ->
  EF.evtF bsegs RNG (seg_post fin E F fc m (sp - ROOM) sp) ms.
Proof.
  intros R F pc fc m xf facts next ROOM lo stops fuel fin depth E ms sp HC SH FINR RR HX0 HR FC FH STK LO IMG MI RELRO RW RI.
  assert (E1 : bv_unsigned (ev E 1%uint63) = sp) by reflexivity.
  assert (HS : st_ok bsegs WInit.OPSW E (WInit.wstate ROOM pc xf FFP facts next) ms WInit.MOW).
  { apply (WInit.init_ok ROOM RR E ms pc xf FFP facts next lo); try assumption; try reflexivity.
    intros r. apply FFP_ok. }
  assert (WLO : 0 <= bv_unsigned (ev E 1%uint63) - ROOM).
  { rewrite E1. destruct STK as (S0 & _). exact (Z.le_trans _ _ _ S0 LO). }
  destruct (WalkL.TwinB.WalkL.wcheck_sound bsegs WInit.OPSW it stops ROOM IMGLO IMGHI fuel fin RNG HIT E WLO
              ltac:(rewrite E1; exact RW) ltac:(unfold IMGLO, IMGHI; exact RI) depth _ ms WInit.MOW HC HS)
    as (ms' & mo' & st' & STEPS & HS' & FIN & INV & (KF & KC & KS)).
  exists ms'. split; [exact STEPS|]. exists st', mo', (ms_regs ms'), (ms_mem ms').
  rewrite E1 in INV.
  split; [| split; [exact HS'| split; [exact FIN| split; [exact INV|]]]].
  - pose proof (so_resv _ _ _ _ _ _ HS') as RV. rewrite (FINR _ FIN) in RV. cbn [resv_ok] in RV.
    etransitivity; [apply (MSt.MS_eta ms' (so_svc _ _ _ _ _ _ HS'))|].
    f_equal.
    + exact (KS SH).
    + exact KF.
    + exact (so_pc _ _ _ _ _ _ HS').
    + exact KC.
    + exact RV.
    + exact (so_rom _ _ _ _ _ _ HS').
  - intros a b MB. pose proof (so_minv _ _ _ _ _ _ HS' a b MB) as W.
    unfold AM.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:FS; [| reflexivity].
    rewrite (W seg eq_refl). reflexivity.
Qed.
End S.
End SegL.
End TwinB.
