(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step ValP MemP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Section WithSegs.
Variable segs : list Segment.

Definition range_untouched (r : region) (lo n : Z) : bool :=
  forallb (fun g => match IMap.find (of_Z g) (rg_cells r) with None => true | Some _ => false end)
          (map (fun i => lo / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1)))).
Definition range_in_image (lo n : Z) : bool :=
  forallb (fun i => match img_byte segs (lo + Z.of_nat i) with Some _ => true | None => false end) (seq 0 (Z.to_nat n)).

Lemma image_bytes_p : forall OPS E st ms m r lo n,
  st_ok segs OPS E st ms m -> IMap.find 0%uint63 (s_regs st) = Some r -> rg_bg r = BGImage ->
  0 <= lo -> lo + n < 2 ^ 62 ->
  in_priv_b (s_priv st) (of_Z lo) (of_Z n) = false ->
  range_untouched r lo n = true -> range_in_image lo n = true ->
  forall i, 0 <= i < n -> rb segs (ms_mem ms) (lo + i) = img_byte segs (lo + i).
Proof.
  intros OPS E st ms m r lo n HS Hr Hbg Hlo Hhi HP HU HI i Hi.
  pose proof (so_reg _ _ _ _ _ _ HS 0%uint63 r Hr) as RO. pose proof (so_zero _ _ _ _ _ _ HS) as Hz.
  assert (IMG : exists b, img_byte segs (lo + i) = Some b).
  { unfold range_in_image in HI. pose proof (proj1 (forallb_forall _ _) HI (Z.to_nat i) ltac:(apply in_seq; lia)) as Q. cbn beta in Q.
    rewrite Z2Nat.id in Q by lia. destruct (img_byte segs (lo + i)); [eexists; reflexivity | discriminate Q]. }
  destruct IMG as [b Hb].
  pose proof (St.ro_bg _ _ _ _ _ _ RO (lo + i)) as BG.
  assert (U : uncovered r (lo + i)).
  { intros g gr Hg Hf. exfalso. unfold range_untouched in HU.
    assert (Hgi : In ((lo + i) / 8) (map (fun j => lo / 8 + Z.of_nat j) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1))))).
    { apply in_map_iff. exists (Z.to_nat ((lo + i) / 8 - lo / 8)). split.
      - rewrite Z2Nat.id; [lia|]. apply Z.le_0_sub. apply Z.div_le_mono; lia.
      - apply in_seq. split; [lia|]. assert ((lo + i) / 8 <= (lo + n - 1) / 8) by (apply Z.div_le_mono; lia).
        assert (lo / 8 <= (lo + i) / 8) by (apply Z.div_le_mono; lia). lia. }
    pose proof (proj1 (forallb_forall _ _) HU _ Hgi) as Q. cbn beta in Q.
    assert (Hgk : of_Z ((lo + i) / 8) = g).
    { apply to_Z_inj. rewrite of_Z_spec, wB_two63, Z.mod_small.
      - unfold keyZ, Mem.keyZ in Hg. destruct (PrimInt63.ltb g bit62i) eqn:C; [lia|]. apply Bool.not_true_iff_false in C.
        exfalso. apply C. apply ltb_spec. change (to_Z bit62i) with (2 ^ 62). pose proof (int_range g).
        assert ((lo + i) / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia.
      - rewrite two63_eq. split; [apply Z.div_pos; lia|]. assert ((lo + i) / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia. }
    rewrite Hgk, Hf in Q. discriminate Q. }
  assert (P2 : 0 <= lo + i < two63 / 2 /\ (exists bs, memory_read segs (Z_to_bv 64 (lo + i)) 1 = Some bs) /\ ~ in_priv (s_priv st) (lo + i)).
  { split; [rewrite two63_eq; change (2 ^ 63 / 2) with (2 ^ 62); lia|]. split.
    - unfold img_byte, rom_of in Hb. destruct (memory_read segs (Z_to_bv 64 (lo + i)) 1) as [bs|]; [eexists; reflexivity | discriminate Hb].
    - assert (TL : to_Z (of_Z lo) = lo) by (rewrite of_Z_spec, wB_two63, Z.mod_small; [reflexivity| rewrite two63_eq; lia]).
      assert (TN : to_Z (of_Z n) = n) by (rewrite of_Z_spec, wB_two63, Z.mod_small; [reflexivity| rewrite two63_eq; lia]).
      apply (in_priv_b_false (s_priv st) (of_Z lo) (of_Z n) (lo + i) HP); rewrite ?TL, ?TN; [rewrite two63_eq; lia| lia]. }
  specialize (BG ltac:(intros K; discriminate K) (fun _ => P2) U).
  unfold bg_byte in BG. rewrite Hbg, Hb in BG. rewrite Hz in BG. change (bv_unsigned (Z_to_bv 64 0)) with 0 in BG.
  rewrite Z.add_0_l in BG. rewrite BG, Hb. reflexivity.
Qed.

Definition lit_cell0 (r : region) (A : Z) (w : w64) : bool :=
  match IMap.find (of_Z (A / 8)) (rg_cells r) with
  | Some gr => existsb (fun c => PrimInt63.eqb (c_idx c) 0%uint63 && PrimInt63.eqb (c_w c) 8%uint63 && sv_eqb (c_v c) (VL w)) (g_cells gr)
  | None => false
  end.

Lemma lit_cell0_bytes : forall OPS E st ms m r A w,
  st_ok segs OPS E st ms m -> IMap.find 0%uint63 (s_regs st) = Some r ->
  0 <= A < 2 ^ 62 -> A mod 8 = 0 ->
  lit_cell0 r A w = true ->
  forall i, 0 <= i < 8 -> rb segs (ms_mem ms) (A + i) = Some (byte_of (wbv w) i).
Proof.
  intros OPS E st ms m r A w HS Hr HA Hal H i Hi. unfold lit_cell0 in H.
  destruct (IMap.find (of_Z (A / 8)) (rg_cells r)) as [gr|] eqn:Hg; [|discriminate H].
  apply existsb_exists in H as (c & Hc & Q). apply andb_prop in Q as [Q Qv]. apply andb_prop in Q as [Qi Qw].
  apply Uint63.eqb_correct in Qi. apply Uint63.eqb_correct in Qw. apply sv_eqb_eq in Qv.
  pose proof (so_reg _ _ _ _ _ _ HS 0%uint63 r Hr) as RO. pose proof (so_zero _ _ _ _ _ _ HS) as Hz.
  destruct (St.ro_cells _ _ _ _ _ _ RO _ _ Hg) as [_ FC].
  pose proof (proj1 (Forall_forall _ _) FC c Hc) as (_ & _ & _ & C4).
  rewrite Qi, Qw, Qv in C4. change (to_Z 0%uint63) with 0 in C4. change (to_Z 8%uint63) with 8 in C4.
  specialize (C4 i Hi). rewrite Hz in C4. change (bv_unsigned (Z_to_bv 64 0)) with 0 in C4.
  assert (KG : keyZ (of_Z (A / 8)) = A / 8).
  { unfold keyZ, Mem.keyZ.
    assert (T : to_Z (of_Z (A / 8)) = A / 8).
    { rewrite of_Z_spec, wB_two63, Z.mod_small; [reflexivity|]. rewrite two63_eq. split; [apply Z.div_pos; lia|].
      assert (A / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia. }
    destruct (PrimInt63.ltb (of_Z (A / 8)) bit62i) eqn:C; [exact T|].
    exfalso. apply Bool.not_true_iff_false in C. apply C. apply ltb_spec. rewrite T. change (to_Z bit62i) with (2 ^ 62).
    apply Z.div_lt_upper_bound; lia. }
  rewrite KG in C4. cbn [den] in C4.
  replace (A + i) with (0 + 8 * (A / 8) + 0 + i) by (pose proof (Z.div_mod A 8 ltac:(lia)); lia). exact C4.
Qed.

Lemma rw_cells_of_rb : forall (m : word -> option byte) A cs,
  cells_wf cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, (i < length (cells_bytes cs))%nat -> rb segs m (A + Z.of_nat i) = nth_error (cells_bytes cs) i) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> wb segs m (A + i) = true) ->
  AS.rw_cells segs m A cs.
Proof.
  intros m A cs WF HA HB HR HW. pose proof (cells_bytes_length cs WF) as L. split.
  - split; [exact WF|]. split; [exact HA|]. split; [rewrite L; exact HB|].
    intros i Hi. rewrite <- (GlueA.rb_mrdA segs). exact (HR i Hi).
  - split; [exact HA|]. split; [exact HB|]. intros i Hi. apply (GlueA.wb_wviewA segs). exact (HW i Hi).
Qed.

Lemma mapped_chunk : forall (m : word -> option byte) n A,
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> wb segs m (A + i) = true /\ rb segs m (A + i) <> None) ->
  exists j, AS.rw_cells segs m A [CB n j].
Proof.
  intros m n. induction n as [|n IH]; intros A HA HB H.
  - exists []. apply rw_cells_of_rb.
    + cbn. auto.
    + exact HA.
    + cbn. lia.
    + intros i Hi. cbn in Hi. lia.
    + intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [_ R0]. rewrite Z.add_0_r in R0. destruct (rb segs m A) as [b|] eqn:Eb; [|congruence].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as [j Hj].
    { intros i Hi. replace (A + 1 + i) with (A + (i + 1)) by lia. apply H. lia. }
    exists (b :: j). destruct Hj as [[WF (_ & _ & BY)] _]. cbn [cells_wf cell_wf cells_bytes cbytes app] in WF, BY. rewrite app_nil_r in BY.
    apply rw_cells_of_rb.
    + pose proof (proj1 WF) as WL. simpl in WL. simpl. split; [|exact I]. f_equal. exact WL.
    + exact HA.
    + cbn [cells_size csize Nat.add]. lia.
    + cbn [cells_bytes cbytes app]. rewrite app_nil_r. intros i Hi. destruct i as [|i]; cbn [nth_error].
      * rewrite Z.add_0_r. exact Eb.
      * rewrite (GlueA.rb_mrdA segs). replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply BY. cbn [length] in Hi. lia.
    + cbn [cells_size csize Nat.add]. intros i Hi. apply H. lia.
Qed.

Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb (bv_unsigned x) (bv_unsigned y) && bytes_eqb a' b'
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | exact (IH b H2)].
Qed.

Definition img_chunk_chk (A : Z) (cs : list ALib.Cells.cell) : bool :=
  let n := cells_size cs in
  match img_bytes segs A n with
  | Some bs => bytes_eqb bs (cells_bytes cs) && Mem.abs_writable segs A (Z.of_nat n)
               && forallb (fun c => match c with CB k bs' => Nat.eqb (length bs') k | _ => true end) cs
  | None => false
  end.

Lemma cells_wf_chk : forall cs : list ALib.Cells.cell,
  forallb (fun c => match c with CB k bs' => Nat.eqb (length bs') k | _ => true end) cs = true -> cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [exact I|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  split; [|exact (IH H2)]. destruct c; try exact I. apply Nat.eqb_eq in H1. exact H1.
Qed.

Lemma img_chunk_sound : forall (m : word -> option byte) A cs,
  img_chunk_chk A cs = true -> 0 <= A ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> rb segs m (A + i) = img_byte segs (A + i)) ->
  AS.rw_cells segs m A cs.
Proof.
  intros m A cs H HA HR. unfold img_chunk_chk in H. cbv zeta in H.
  destruct (img_bytes segs A (cells_size cs)) as [bs|] eqn:IB; [|discriminate H].
  apply andb_prop in H as [H WFc]. apply andb_prop in H as [EQ AW]. apply bytes_eqb_eq in EQ. subst bs.
  pose proof (cells_wf_chk cs WFc) as WF. pose proof (cells_bytes_length cs WF) as L.
  destruct (img_bytes_spec segs _ _ _ IB) as [_ BY].
  destruct (abs_writable_sound segs A (Z.of_nat (cells_size cs)) HA ltac:(lia) AW) as [_ WB].
  assert (TOP : A + Z.of_nat (cells_size cs) < 2 ^ 62).
  { unfold Mem.abs_writable in AW. apply andb_prop in AW as [B _]. apply Z.ltb_lt in B. rewrite two62Z_eq in B. exact B. }
  apply rw_cells_of_rb; [exact WF | exact HA | lia | |].
  - intros i Hi. rewrite L in Hi. rewrite (HR (Z.of_nat i) ltac:(lia)).
    destruct (BY i Hi) as [rest M]. unfold img_byte, rom_of. rewrite M.
    symmetry. apply nth_error_nth'. rewrite L. exact Hi.
  - intros i Hi. exact (proj1 (WB i Hi) m).
Qed.

Definition lit_chunk_chk (w : w64) (cs : list ALib.Cells.cell) : bool :=
  bytes_eqb (map (fun i => byte_of (wbv w) (Z.of_nat i)) (seq 0 (cells_size cs))) (cells_bytes cs)
  && Nat.leb (cells_size cs) 8
  && forallb (fun c => match c with CB k bs' => Nat.eqb (length bs') k | _ => true end) cs.

Lemma lit_chunk_sound : forall (m : word -> option byte) A w cs,
  lit_chunk_chk w cs = true -> 0 <= A -> A + 8 < 2 ^ 62 -> Mem.abs_writable segs A 8 = true ->
  (forall i, 0 <= i < 8 -> rb segs m (A + i) = Some (byte_of (wbv w) i)) ->
  AS.rw_cells segs m A cs.
Proof.
  intros m A w cs H HA HT AW HR. unfold lit_chunk_chk in H.
  apply andb_prop in H as [H WFc]. apply andb_prop in H as [EQ LE]. apply bytes_eqb_eq in EQ. apply Nat.leb_le in LE.
  pose proof (cells_wf_chk cs WFc) as WF. pose proof (cells_bytes_length cs WF) as L.
  destruct (abs_writable_sound segs A 8 HA ltac:(lia) AW) as [_ WB].
  apply rw_cells_of_rb; [exact WF | exact HA | lia | |].
  - intros i Hi. rewrite L in Hi. rewrite (HR (Z.of_nat i) ltac:(lia)). rewrite <- EQ.
    symmetry. rewrite nth_error_map, nth_error_seq. replace (i <? cells_size cs)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add]. reflexivity.
  - intros i Hi. exact (proj1 (WB i ltac:(lia)) m).
Qed.
End WithSegs.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step ValP MemP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Section WithSegs.
Variable segs : list Segment.

Definition range_untouched (r : region) (lo n : Z) : bool :=
  forallb (fun g => match IMap.find (of_Z g) (rg_cells r) with None => true | Some _ => false end)
          (map (fun i => lo / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1)))).
Definition range_in_image (lo n : Z) : bool :=
  forallb (fun i => match img_byte segs (lo + Z.of_nat i) with Some _ => true | None => false end) (seq 0 (Z.to_nat n)).

Lemma image_bytes_p : forall OPS E st ms m r lo n,
  st_ok segs OPS E st ms m -> IMap.find 0%uint63 (s_regs st) = Some r -> rg_bg r = BGImage ->
  0 <= lo -> lo + n < 2 ^ 62 ->
  in_priv_b (s_priv st) (of_Z lo) (of_Z n) = false ->
  range_untouched r lo n = true -> range_in_image lo n = true ->
  forall i, 0 <= i < n -> rb segs (ms_mem ms) (lo + i) = img_byte segs (lo + i).
Proof.
  intros OPS E st ms m r lo n HS Hr Hbg Hlo Hhi HP HU HI i Hi.
  pose proof (so_reg _ _ _ _ _ _ HS 0%uint63 r Hr) as RO. pose proof (so_zero _ _ _ _ _ _ HS) as Hz.
  assert (IMG : exists b, img_byte segs (lo + i) = Some b).
  { unfold range_in_image in HI. pose proof (proj1 (forallb_forall _ _) HI (Z.to_nat i) ltac:(apply in_seq; lia)) as Q. cbn beta in Q.
    rewrite Z2Nat.id in Q by lia. destruct (img_byte segs (lo + i)); [eexists; reflexivity | discriminate Q]. }
  destruct IMG as [b Hb].
  pose proof (St.ro_bg _ _ _ _ _ _ RO (lo + i)) as BG.
  assert (U : uncovered r (lo + i)).
  { intros g gr Hg Hf. exfalso. unfold range_untouched in HU.
    assert (Hgi : In ((lo + i) / 8) (map (fun j => lo / 8 + Z.of_nat j) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1))))).
    { apply in_map_iff. exists (Z.to_nat ((lo + i) / 8 - lo / 8)). split.
      - rewrite Z2Nat.id; [lia|]. apply Z.le_0_sub. apply Z.div_le_mono; lia.
      - apply in_seq. split; [lia|]. assert ((lo + i) / 8 <= (lo + n - 1) / 8) by (apply Z.div_le_mono; lia).
        assert (lo / 8 <= (lo + i) / 8) by (apply Z.div_le_mono; lia). lia. }
    pose proof (proj1 (forallb_forall _ _) HU _ Hgi) as Q. cbn beta in Q.
    assert (Hgk : of_Z ((lo + i) / 8) = g).
    { apply to_Z_inj. rewrite of_Z_spec, wB_two63, Z.mod_small.
      - unfold keyZ, Mem.keyZ in Hg. destruct (PrimInt63.ltb g bit62i) eqn:C; [lia|]. apply Bool.not_true_iff_false in C.
        exfalso. apply C. apply ltb_spec. change (to_Z bit62i) with (2 ^ 62). pose proof (int_range g).
        assert ((lo + i) / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia.
      - rewrite two63_eq. split; [apply Z.div_pos; lia|]. assert ((lo + i) / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia. }
    rewrite Hgk, Hf in Q. discriminate Q. }
  assert (P2 : 0 <= lo + i < two63 / 2 /\ (exists bs, memory_read segs (Z_to_bv 64 (lo + i)) 1 = Some bs) /\ ~ in_priv (s_priv st) (lo + i)).
  { split; [rewrite two63_eq; change (2 ^ 63 / 2) with (2 ^ 62); lia|]. split.
    - unfold img_byte, rom_of in Hb. destruct (memory_read segs (Z_to_bv 64 (lo + i)) 1) as [bs|]; [eexists; reflexivity | discriminate Hb].
    - assert (TL : to_Z (of_Z lo) = lo) by (rewrite of_Z_spec, wB_two63, Z.mod_small; [reflexivity| rewrite two63_eq; lia]).
      assert (TN : to_Z (of_Z n) = n) by (rewrite of_Z_spec, wB_two63, Z.mod_small; [reflexivity| rewrite two63_eq; lia]).
      apply (in_priv_b_false (s_priv st) (of_Z lo) (of_Z n) (lo + i) HP); rewrite ?TL, ?TN; [rewrite two63_eq; lia| lia]. }
  specialize (BG ltac:(intros K; discriminate K) (fun _ => P2) U).
  unfold bg_byte in BG. rewrite Hbg, Hb in BG. rewrite Hz in BG. change (bv_unsigned (Z_to_bv 64 0)) with 0 in BG.
  rewrite Z.add_0_l in BG. rewrite BG, Hb. reflexivity.
Qed.

Definition lit_cell0 (r : region) (A : Z) (w : w64) : bool :=
  match IMap.find (of_Z (A / 8)) (rg_cells r) with
  | Some gr => existsb (fun c => PrimInt63.eqb (c_idx c) 0%uint63 && PrimInt63.eqb (c_w c) 8%uint63 && sv_eqb (c_v c) (VL w)) (g_cells gr)
  | None => false
  end.

Lemma lit_cell0_bytes : forall OPS E st ms m r A w,
  st_ok segs OPS E st ms m -> IMap.find 0%uint63 (s_regs st) = Some r ->
  0 <= A < 2 ^ 62 -> A mod 8 = 0 ->
  lit_cell0 r A w = true ->
  forall i, 0 <= i < 8 -> rb segs (ms_mem ms) (A + i) = Some (byte_of (wbv w) i).
Proof.
  intros OPS E st ms m r A w HS Hr HA Hal H i Hi. unfold lit_cell0 in H.
  destruct (IMap.find (of_Z (A / 8)) (rg_cells r)) as [gr|] eqn:Hg; [|discriminate H].
  apply existsb_exists in H as (c & Hc & Q). apply andb_prop in Q as [Q Qv]. apply andb_prop in Q as [Qi Qw].
  apply Uint63.eqb_correct in Qi. apply Uint63.eqb_correct in Qw. apply sv_eqb_eq in Qv.
  pose proof (so_reg _ _ _ _ _ _ HS 0%uint63 r Hr) as RO. pose proof (so_zero _ _ _ _ _ _ HS) as Hz.
  destruct (St.ro_cells _ _ _ _ _ _ RO _ _ Hg) as [_ FC].
  pose proof (proj1 (Forall_forall _ _) FC c Hc) as (_ & _ & _ & C4).
  rewrite Qi, Qw, Qv in C4. change (to_Z 0%uint63) with 0 in C4. change (to_Z 8%uint63) with 8 in C4.
  specialize (C4 i Hi). rewrite Hz in C4. change (bv_unsigned (Z_to_bv 64 0)) with 0 in C4.
  assert (KG : keyZ (of_Z (A / 8)) = A / 8).
  { unfold keyZ, Mem.keyZ.
    assert (T : to_Z (of_Z (A / 8)) = A / 8).
    { rewrite of_Z_spec, wB_two63, Z.mod_small; [reflexivity|]. rewrite two63_eq. split; [apply Z.div_pos; lia|].
      assert (A / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia. }
    destruct (PrimInt63.ltb (of_Z (A / 8)) bit62i) eqn:C; [exact T|].
    exfalso. apply Bool.not_true_iff_false in C. apply C. apply ltb_spec. rewrite T. change (to_Z bit62i) with (2 ^ 62).
    apply Z.div_lt_upper_bound; lia. }
  rewrite KG in C4. cbn [den] in C4.
  replace (A + i) with (0 + 8 * (A / 8) + 0 + i) by (pose proof (Z.div_mod A 8 ltac:(lia)); lia). exact C4.
Qed.

Lemma rw_cells_of_rb : forall (m : word -> option byte) A cs,
  cells_wf cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, (i < length (cells_bytes cs))%nat -> rb segs m (A + Z.of_nat i) = nth_error (cells_bytes cs) i) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> wb segs m (A + i) = true) ->
  AS.rw_cells segs m A cs.
Proof.
  intros m A cs WF HA HB HR HW. pose proof (cells_bytes_length cs WF) as L. split.
  - split; [exact WF|]. split; [exact HA|]. split; [rewrite L; exact HB|].
    intros i Hi. rewrite <- (GlueA.TwinB.rb_mrdA segs). exact (HR i Hi).
  - split; [exact HA|]. split; [exact HB|]. intros i Hi. apply (GlueA.TwinB.wb_wviewA segs). exact (HW i Hi).
Qed.

Lemma mapped_chunk : forall (m : word -> option byte) n A,
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> wb segs m (A + i) = true /\ rb segs m (A + i) <> None) ->
  exists j, AS.rw_cells segs m A [CB n j].
Proof.
  intros m n. induction n as [|n IH]; intros A HA HB H.
  - exists []. apply rw_cells_of_rb.
    + cbn. auto.
    + exact HA.
    + cbn. lia.
    + intros i Hi. cbn in Hi. lia.
    + intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [_ R0]. rewrite Z.add_0_r in R0. destruct (rb segs m A) as [b|] eqn:Eb; [|congruence].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as [j Hj].
    { intros i Hi. replace (A + 1 + i) with (A + (i + 1)) by lia. apply H. lia. }
    exists (b :: j). destruct Hj as [[WF (_ & _ & BY)] _]. cbn [cells_wf cell_wf cells_bytes cbytes app] in WF, BY. rewrite app_nil_r in BY.
    apply rw_cells_of_rb.
    + pose proof (proj1 WF) as WL. simpl in WL. simpl. split; [|exact I]. f_equal. exact WL.
    + exact HA.
    + cbn [cells_size csize Nat.add]. lia.
    + cbn [cells_bytes cbytes app]. rewrite app_nil_r. intros i Hi. destruct i as [|i]; cbn [nth_error].
      * rewrite Z.add_0_r. exact Eb.
      * rewrite (GlueA.TwinB.rb_mrdA segs). replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply BY. cbn [length] in Hi. lia.
    + cbn [cells_size csize Nat.add]. intros i Hi. apply H. lia.
Qed.

Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb (bv_unsigned x) (bv_unsigned y) && bytes_eqb a' b'
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | exact (IH b H2)].
Qed.

Definition img_chunk_chk (A : Z) (cs : list ALib.Cells.cell) : bool :=
  let n := cells_size cs in
  match img_bytes segs A n with
  | Some bs => bytes_eqb bs (cells_bytes cs) && Mem.abs_writable segs A (Z.of_nat n)
               && forallb (fun c => match c with CB k bs' => Nat.eqb (length bs') k | _ => true end) cs
  | None => false
  end.

Lemma cells_wf_chk : forall cs : list ALib.Cells.cell,
  forallb (fun c => match c with CB k bs' => Nat.eqb (length bs') k | _ => true end) cs = true -> cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [exact I|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  split; [|exact (IH H2)]. destruct c; try exact I. apply Nat.eqb_eq in H1. exact H1.
Qed.

Lemma img_chunk_sound : forall (m : word -> option byte) A cs,
  img_chunk_chk A cs = true -> 0 <= A ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> rb segs m (A + i) = img_byte segs (A + i)) ->
  AS.rw_cells segs m A cs.
Proof.
  intros m A cs H HA HR. unfold img_chunk_chk in H. cbv zeta in H.
  destruct (img_bytes segs A (cells_size cs)) as [bs|] eqn:IB; [|discriminate H].
  apply andb_prop in H as [H WFc]. apply andb_prop in H as [EQ AW]. apply bytes_eqb_eq in EQ. subst bs.
  pose proof (cells_wf_chk cs WFc) as WF. pose proof (cells_bytes_length cs WF) as L.
  destruct (img_bytes_spec segs _ _ _ IB) as [_ BY].
  destruct (abs_writable_sound segs A (Z.of_nat (cells_size cs)) HA ltac:(lia) AW) as [_ WB].
  assert (TOP : A + Z.of_nat (cells_size cs) < 2 ^ 62).
  { unfold Mem.abs_writable in AW. apply andb_prop in AW as [B _]. apply Z.ltb_lt in B. rewrite two62Z_eq in B. exact B. }
  apply rw_cells_of_rb; [exact WF | exact HA | lia | |].
  - intros i Hi. rewrite L in Hi. rewrite (HR (Z.of_nat i) ltac:(lia)).
    destruct (BY i Hi) as [rest M]. unfold img_byte, rom_of. rewrite M.
    symmetry. apply nth_error_nth'. rewrite L. exact Hi.
  - intros i Hi. exact (proj1 (WB i Hi) m).
Qed.

Definition lit_chunk_chk (w : w64) (cs : list ALib.Cells.cell) : bool :=
  bytes_eqb (map (fun i => byte_of (wbv w) (Z.of_nat i)) (seq 0 (cells_size cs))) (cells_bytes cs)
  && Nat.leb (cells_size cs) 8
  && forallb (fun c => match c with CB k bs' => Nat.eqb (length bs') k | _ => true end) cs.

Lemma lit_chunk_sound : forall (m : word -> option byte) A w cs,
  lit_chunk_chk w cs = true -> 0 <= A -> A + 8 < 2 ^ 62 -> Mem.abs_writable segs A 8 = true ->
  (forall i, 0 <= i < 8 -> rb segs m (A + i) = Some (byte_of (wbv w) i)) ->
  AS.rw_cells segs m A cs.
Proof.
  intros m A w cs H HA HT AW HR. unfold lit_chunk_chk in H.
  apply andb_prop in H as [H WFc]. apply andb_prop in H as [EQ LE]. apply bytes_eqb_eq in EQ. apply Nat.leb_le in LE.
  pose proof (cells_wf_chk cs WFc) as WF. pose proof (cells_bytes_length cs WF) as L.
  destruct (abs_writable_sound segs A 8 HA ltac:(lia) AW) as [_ WB].
  apply rw_cells_of_rb; [exact WF | exact HA | lia | |].
  - intros i Hi. rewrite L in Hi. rewrite (HR (Z.of_nat i) ltac:(lia)). rewrite <- EQ.
    symmetry. rewrite nth_error_map, nth_error_seq. replace (i <? cells_size cs)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add]. reflexivity.
  - intros i Hi. exact (proj1 (WB i ltac:(lia)) m).
Qed.
End WithSegs.
End TwinB.
