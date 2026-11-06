(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC MemsetPre RangePre PubC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Definition PUBW : list (Z * Z) := [(0x60c140, 0x60cc00); (0x60ccc0, 0x62cf40); (0x62cf80, 0x62dc00); (0x62dc40, 0x62e000); (0x62e040, 0x62e540)].
Definition ZPBW : list (Z * Z) := [(0x800b9828, 0x800b9980); (0x800b9998, 0x800bd9e8); (0x800bd9f0, 0x800bdb80); (0x800bdb88, 0x800bdc05); (0x800bdc06, 0x800bdca8)].
Definition in_pubw (lo hi : Z) : Prop := exists w, In w PUBW /\ fst w <= lo /\ hi <= snd w.
Definition in_zpbw (s : Z) : Prop := exists w, In w ZPBW /\ fst w <= s < snd w.

Lemma in_pubw_bounds : forall lo hi, in_pubw lo hi -> 0x60c140 <= lo /\ hi <= 0x62e540.
Proof. intros lo hi (w & Hw & H1 & H2). unfold PUBW in Hw. cbn [In] in Hw. repeat (destruct Hw as [<-|Hw]; [cbn [fst snd] in *; lia|]). destruct Hw. Qed.
Lemma in_pubw_sub : forall lo hi lo' hi', in_pubw lo hi -> lo <= lo' -> hi' <= hi -> in_pubw lo' hi'.
Proof. intros lo hi lo' hi' (w & Hw & H1 & H2) L H. exists w. split; [exact Hw| lia]. Qed.

Lemma pubw_shadow : forall lo hi s, in_pubw lo hi -> ASHOFF + lo / 8 <= s < ASHOFF + (hi + 7) / 8 -> lo <= hi -> in_zpbw s.
Proof.
  intros lo hi s (w & Hw & H1 & H2) Hs LH. unfold PUBW in Hw. cbn [In] in Hw. unfold in_zpbw, ZPBW, ASHOFF in *.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in *.
  - exists (0x800b9828, 0x800b9980). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800b9998, 0x800bd9e8). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800bd9f0, 0x800bdb80). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800bdb88, 0x800bdc05). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800bdc06, 0x800bdca8). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
Qed.

Definition zpb_holds {rc : runConstT} (m : word -> option byte) : Prop :=
  forall s, in_zpbw s -> m (ALib.Mem.wa s) = Some (Z_to_bv 8 0) /\ wb asegs m s = true.

Lemma pub_window_rw {rc : runConstT} : forall (m : word -> option byte) a, in_pubw a (a + 1) ->
  wb asegs m a = true /\ rb asegs m a <> None /\ exists seg, find_segment asegs a 1 = Some seg.
Proof.
  intros m a (w & Hw & H1 & H2).
  assert (G : forall lo n, 0 <= lo -> 0 <= n -> OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.abs_writable asegs lo n = true -> lo <= a < lo + n ->
              wb asegs m a = true /\ rb asegs m a <> None /\ exists seg, find_segment asegs a 1 = Some seg).
  { intros lo n Hlo Hn AW Ha.
    destruct (MemP.abs_writable_sound asegs lo n Hlo Hn AW) as [RD WB].
    destruct (MemP.abs_readable_sound asegs lo n Hn RD) as [_ RS].
    destruct (WB (a - lo) ltac:(lia)) as [W (seg & FS & _)]. destruct (RS (a - lo) ltac:(lia)) as (b & rest & MR).
    replace (lo + (a - lo)) with a in * by lia.
    split; [exact (W m)|]. split; [exact (MemP.rb_rom asegs m a b rest MR)| exists seg; exact FS]. }
  unfold PUBW in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in *.
  - apply (G 0x60c140 (0x60cc00 - 0x60c140)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x60ccc0 (0x62cf40 - 0x60ccc0)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x62cf80 (0x62dc00 - 0x62cf80)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x62dc40 (0x62e000 - 0x62dc40)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x62e040 (0x62e540 - 0x62e040)); [lia| lia| vm_compute; reflexivity| lia].
Qed.

Definition pub_range_facts {rc : runConstT} (RNG : footprint) (m : amem) (A len : Z) : Prop :=
  in_pubw A (A + len)
  /\ (exists junk, AS.rw_cells asegs m A [CB (Z.to_nat len) junk])
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma pub_range_facts_ok {rc : runConstT} : forall (RNG : footprint) (m : amem) A len, zpb_holds m -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc4000 ->
  in_pubw A (A + len) -> 0 <= len -> pub_range_facts RNG m A len.
Proof.
  intros RNG m A len Z RI RS PW HN. pose proof (in_pubw_bounds _ _ PW) as [HA HH].
  split; [exact PW|].
  split.
  { apply (UnreggLib.mapped_chunk asegs m (Z.to_nat len) A); [lia| rewrite Z2Nat.id by lia; lia|].
    intros i Hi. rewrite Z2Nat.id in Hi by lia. destruct (pub_window_rw m (A + i) (in_pubw_sub A (A + len) (A + i) (A + i + 1) PW ltac:(lia) ltac:(lia))) as (W & R & _). split; assumption. }
  split; [split; [lia|]; left; unfold Shadow.KLOW; lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    assert (SG : ASHOFF + A / 8 <= ASHOFF + G < ASHOFF + (A + len + 7) / 8) by (clear - G1 G2; Z.div_mod_to_equations; lia).
    apply (proj1 (Z (ASHOFF + G) (pubw_shadow A (A + len) (ASHOFF + G) PW SG ltac:(lia)))). }
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].

  assert (HULLW : in_pubw (A / 64 * 64) ((A + len + 63) / 64 * 64)).
  { destruct PW as (w & Hw & H1 & H2). exists w. split; [exact Hw|]. unfold PUBW in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in *; Z.div_mod_to_equations; lia. }
  pose proof (in_pubw_bounds _ _ HULLW) as [HL1 HL2].
  exists (A / 64 * 64), ((A + len + 63) / 64 * 64).
  assert (H1 : A / 64 * 64 <= A) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + len <= (A + len + 63) / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (SE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  - split; [rewrite SE; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split; [rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    intros i Hi. apply (GlueA.wb_wviewA asegs).
    assert (SR : ASHOFF + (A / 64 * 64) / 8 <= shad (A / 64 * 64) + i < ASHOFF + ((A + len + 63) / 64 * 64 + 7) / 8).
    { rewrite !SE in *. clear - Hi. Z.div_mod_to_equations. lia. }
    apply (proj2 (Z (shad (A / 64 * 64) + i) (pubw_shadow (A / 64 * 64) ((A + len + 63) / 64 * 64) (shad (A / 64 * 64) + i) HULLW SR ltac:(lia)))).
  - apply (rng_sub _ _ _ _ _ RS); rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.

Lemma in_pub_win_spec : forall a len, PubC.in_pub_win a len = true -> to_Z len <= 4096 ->
  in_pubw (to_Z a) (to_Z a + to_Z len) /\ to_Z a + to_Z len < 2 ^ 62.
Proof.
  intros a len H NR. unfold PubC.in_pub_win, PubC.PUB_WINS in H. cbn [existsb fst snd] in H.
  pose proof (to_Z_bounded len) as LB. pose proof (to_Z_bounded a) as AB.
  rewrite !orb_true_iff, !andb_true_iff, !Uint63.leb_spec in H.
  change (to_Z 6340928%uint63) with 0x60c140 in H. change (to_Z 6343680%uint63) with 0x60cc00 in H.
  change (to_Z 6343872%uint63) with 0x60ccc0 in H. change (to_Z 6475584%uint63) with 0x62cf40 in H.
  change (to_Z 6475648%uint63) with 0x62cf80 in H. change (to_Z 6478848%uint63) with 0x62dc00 in H.
  change (to_Z 6478912%uint63) with 0x62dc40 in H. change (to_Z 6481216%uint63) with 0x62e540 in H.
  change (to_Z 6479872%uint63) with 0x62e000 in H. change (to_Z 6479936%uint63) with 0x62e040 in H.
  assert (AD : to_Z (PrimInt63.add a len) = to_Z a + to_Z len \/ to_Z a > 0x62e540).
  { destruct (Z_le_gt_dec (to_Z a) 0x62e540) as [L|G]; [left| right; exact G].
    rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  unfold in_pubw, PUBW.
  destruct H as [[[H1 H2] H3]|[[[H1 H2] H3]|[[[H1 H2] H3]|[[[H1 H2] H3]|[[[H1 H2] H3]|F]]]]]; [| | | | | discriminate F]; (destruct AD as [AD|AD]; [rewrite AD in H3| lia]).
  - split; [exists (0x60c140, 0x60cc00); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x60ccc0, 0x62cf40); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x62cf80, 0x62dc00); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x62dc40, 0x62e000); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x62e040, 0x62e540); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
Qed.

Lemma lit_pub_inv : forall st a len, PubC.lit_pub st a len = true -> to_Z len <= 4096 ->
  W64.wt a = false /\ in_pubw (to_Z (W64.wl a)) (to_Z (W64.wl a) + to_Z len)
  /\ (forall x, to_Z (W64.wl a) <= x < to_Z (W64.wl a) + to_Z len -> ~ in_priv (s_priv st) x)
  /\ find_op PubC.ZPB_ID (s_ops st) = Some [].
Proof.
  intros st a len H NR. unfold PubC.lit_pub in H.
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in H, Q0.
  destruct (find_op PubC.ZPB_ID (s_ops st)) as [[|? ?]|]; try discriminate Q.
  destruct (in_pub_win_spec _ _ Q1 NR) as [PW SM].
  split; [exact H|]. split; [exact PW|]. split; [| reflexivity].
  intros x Hx. apply (MemP.in_priv_b_false (s_priv st) (W64.wl a) len x Q0); [unfold W64.two63; lia| exact Hx].
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import StackSh.TwinB RangeC.TwinB MemsetPre.TwinB RangePre.TwinB PubC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Definition PUBW : list (Z * Z) := [(0x60e300, 0x60edc0); (0x60ee80, 0x62f100); (0x62f140, 0x62fdc0); (0x62fe00, 0x6301c0); (0x630200, 0x630700)].
Definition ZPBW : list (Z * Z) := [(0x800b9c60, 0x800b9db8); (0x800b9dd0, 0x800bde20); (0x800bde28, 0x800bdfb8); (0x800bdfc0, 0x800be03d); (0x800be03e, 0x800be0e0)].
Definition in_pubw (lo hi : Z) : Prop := exists w, In w PUBW /\ fst w <= lo /\ hi <= snd w.
Definition in_zpbw (s : Z) : Prop := exists w, In w ZPBW /\ fst w <= s < snd w.

Lemma in_pubw_bounds : forall lo hi, in_pubw lo hi -> 0x60e300 <= lo /\ hi <= 0x630700.
Proof. intros lo hi (w & Hw & H1 & H2). unfold PUBW in Hw. cbn [In] in Hw. repeat (destruct Hw as [<-|Hw]; [cbn [fst snd] in *; lia|]). destruct Hw. Qed.
Lemma in_pubw_sub : forall lo hi lo' hi', in_pubw lo hi -> lo <= lo' -> hi' <= hi -> in_pubw lo' hi'.
Proof. intros lo hi lo' hi' (w & Hw & H1 & H2) L H. exists w. split; [exact Hw| lia]. Qed.

Lemma pubw_shadow : forall lo hi s, in_pubw lo hi -> ASHOFF + lo / 8 <= s < ASHOFF + (hi + 7) / 8 -> lo <= hi -> in_zpbw s.
Proof.
  intros lo hi s (w & Hw & H1 & H2) Hs LH. unfold PUBW in Hw. cbn [In] in Hw. unfold in_zpbw, ZPBW, ASHOFF in *.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in *.
  - exists (0x800b9c60, 0x800b9db8). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800b9dd0, 0x800bde20). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800bde28, 0x800bdfb8). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800bdfc0, 0x800be03d). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
  - exists (0x800be03e, 0x800be0e0). split; [cbn [In]; tauto| cbn [fst snd]; Z.div_mod_to_equations; lia].
Qed.

Definition zpb_holds {rc : runConstT} (m : word -> option byte) : Prop :=
  forall s, in_zpbw s -> m (ALib.Mem.wa s) = Some (Z_to_bv 8 0) /\ wb bsegs m s = true.

Lemma pub_window_rw {rc : runConstT} : forall (m : word -> option byte) a, in_pubw a (a + 1) ->
  wb bsegs m a = true /\ rb bsegs m a <> None /\ exists seg, find_segment bsegs a 1 = Some seg.
Proof.
  intros m a (w & Hw & H1 & H2).
  assert (G : forall lo n, 0 <= lo -> 0 <= n -> OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.abs_writable bsegs lo n = true -> lo <= a < lo + n ->
              wb bsegs m a = true /\ rb bsegs m a <> None /\ exists seg, find_segment bsegs a 1 = Some seg).
  { intros lo n Hlo Hn AW Ha.
    destruct (MemP.abs_writable_sound bsegs lo n Hlo Hn AW) as [RD WB].
    destruct (MemP.abs_readable_sound bsegs lo n Hn RD) as [_ RS].
    destruct (WB (a - lo) ltac:(lia)) as [W (seg & FS & _)]. destruct (RS (a - lo) ltac:(lia)) as (b & rest & MR).
    replace (lo + (a - lo)) with a in * by lia.
    split; [exact (W m)|]. split; [exact (MemP.rb_rom bsegs m a b rest MR)| exists seg; exact FS]. }
  unfold PUBW in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in *.
  - apply (G 0x60e300 (0x60edc0 - 0x60e300)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x60ee80 (0x62f100 - 0x60ee80)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x62f140 (0x62fdc0 - 0x62f140)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x62fe00 (0x6301c0 - 0x62fe00)); [lia| lia| vm_compute; reflexivity| lia].
  - apply (G 0x630200 (0x630700 - 0x630200)); [lia| lia| vm_compute; reflexivity| lia].
Qed.

Definition pub_range_facts {rc : runConstT} (RNG : footprint) (m : amem) (A len : Z) : Prop :=
  in_pubw A (A + len)
  /\ (exists junk, AS.rw_cells bsegs m A [CB (Z.to_nat len) junk])
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma pub_range_facts_ok {rc : runConstT} : forall (RNG : footprint) (m : amem) A len, zpb_holds m -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc5000 ->
  in_pubw A (A + len) -> 0 <= len -> pub_range_facts RNG m A len.
Proof.
  intros RNG m A len Z RI RS PW HN. pose proof (in_pubw_bounds _ _ PW) as [HA HH].
  split; [exact PW|].
  split.
  { apply (UnreggLib.TwinB.mapped_chunk bsegs m (Z.to_nat len) A); [lia| rewrite Z2Nat.id by lia; lia|].
    intros i Hi. rewrite Z2Nat.id in Hi by lia. destruct (pub_window_rw m (A + i) (in_pubw_sub A (A + len) (A + i) (A + i + 1) PW ltac:(lia) ltac:(lia))) as (W & R & _). split; assumption. }
  split; [split; [lia|]; left; unfold Shadow.KLOW; lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    assert (SG : ASHOFF + A / 8 <= ASHOFF + G < ASHOFF + (A + len + 7) / 8) by (clear - G1 G2; Z.div_mod_to_equations; lia).
    apply (proj1 (Z (ASHOFF + G) (pubw_shadow A (A + len) (ASHOFF + G) PW SG ltac:(lia)))). }
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].

  assert (HULLW : in_pubw (A / 64 * 64) ((A + len + 63) / 64 * 64)).
  { destruct PW as (w & Hw & H1 & H2). exists w. split; [exact Hw|]. unfold PUBW in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in *; Z.div_mod_to_equations; lia. }
  pose proof (in_pubw_bounds _ _ HULLW) as [HL1 HL2].
  exists (A / 64 * 64), ((A + len + 63) / 64 * 64).
  assert (H1 : A / 64 * 64 <= A) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + len <= (A + len + 63) / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (SE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  - split; [rewrite SE; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split; [rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs).
    assert (SR : ASHOFF + (A / 64 * 64) / 8 <= shad (A / 64 * 64) + i < ASHOFF + ((A + len + 63) / 64 * 64 + 7) / 8).
    { rewrite !SE in *. clear - Hi. Z.div_mod_to_equations. lia. }
    apply (proj2 (Z (shad (A / 64 * 64) + i) (pubw_shadow (A / 64 * 64) ((A + len + 63) / 64 * 64) (shad (A / 64 * 64) + i) HULLW SR ltac:(lia)))).
  - apply (rng_sub _ _ _ _ _ RS); rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.

Lemma in_pub_win_spec : forall a len, PubC.TwinB.PubC.in_pub_win a len = true -> to_Z len <= 4096 ->
  in_pubw (to_Z a) (to_Z a + to_Z len) /\ to_Z a + to_Z len < 2 ^ 62.
Proof.
  intros a len H NR. unfold PubC.TwinB.PubC.in_pub_win, PubC.TwinB.PubC.PUB_WINS in H. cbn [existsb fst snd] in H.
  pose proof (to_Z_bounded len) as LB. pose proof (to_Z_bounded a) as AB.
  rewrite !orb_true_iff, !andb_true_iff, !Uint63.leb_spec in H.
  change (to_Z 6349568%uint63) with 0x60e300 in H. change (to_Z 6352320%uint63) with 0x60edc0 in H.
  change (to_Z 6352512%uint63) with 0x60ee80 in H. change (to_Z 6484224%uint63) with 0x62f100 in H.
  change (to_Z 6484288%uint63) with 0x62f140 in H. change (to_Z 6487488%uint63) with 0x62fdc0 in H.
  change (to_Z 6487552%uint63) with 0x62fe00 in H. change (to_Z 6489856%uint63) with 0x630700 in H.
  change (to_Z 6488512%uint63) with 0x6301c0 in H. change (to_Z 6488576%uint63) with 0x630200 in H.
  assert (AD : to_Z (PrimInt63.add a len) = to_Z a + to_Z len \/ to_Z a > 0x630700).
  { destruct (Z_le_gt_dec (to_Z a) 0x630700) as [L|G]; [left| right; exact G].
    rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  unfold in_pubw, PUBW.
  destruct H as [[[H1 H2] H3]|[[[H1 H2] H3]|[[[H1 H2] H3]|[[[H1 H2] H3]|[[[H1 H2] H3]|F]]]]]; [| | | | | discriminate F]; (destruct AD as [AD|AD]; [rewrite AD in H3| lia]).
  - split; [exists (0x60e300, 0x60edc0); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x60ee80, 0x62f100); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x62f140, 0x62fdc0); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x62fe00, 0x6301c0); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
  - split; [exists (0x630200, 0x630700); split; [cbn [In]; tauto| cbn [fst snd]; lia]| lia].
Qed.

Lemma lit_pub_inv : forall st a len, PubC.TwinB.PubC.lit_pub st a len = true -> to_Z len <= 4096 ->
  W64.wt a = false /\ in_pubw (to_Z (W64.wl a)) (to_Z (W64.wl a) + to_Z len)
  /\ (forall x, to_Z (W64.wl a) <= x < to_Z (W64.wl a) + to_Z len -> ~ in_priv (s_priv st) x)
  /\ find_op PubC.TwinB.PubC.ZPB_ID (s_ops st) = Some [].
Proof.
  intros st a len H NR. unfold PubC.TwinB.PubC.lit_pub in H.
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in H, Q0.
  destruct (find_op PubC.TwinB.PubC.ZPB_ID (s_ops st)) as [[|? ?]|]; try discriminate Q.
  destruct (in_pub_win_spec _ _ Q1 NR) as [PW SM].
  split; [exact H|]. split; [exact PW|]. split; [| reflexivity].
  intros x Hx. apply (MemP.in_priv_b_false (s_priv st) (W64.wl a) len x Q0); [unfold W64.two63; lia| exact Hx].
Qed.
End TwinB.
