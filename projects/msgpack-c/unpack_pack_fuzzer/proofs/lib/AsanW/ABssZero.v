(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Uint63.
From Corelib Require Import PrimString PrimStringAxioms.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AsanHexScan AsanHexZero.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainExport AsanPlanImages.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module API := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.AsanPlanImages.

Definition BSS0_LO : Z := 0xd8000.
Definition BSS0_HI : Z := 0x62f000.

Lemma bss_zwin : zwin Asan_seg_bytes_003 40960%uint63 11198464%uint63 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bss_hex0 : forall i : N, 20480 <= Z.of_N i < 5619712 ->
  hex_byte_at Asan_seg_bytes_003 i = Some (Z_to_bv 8 0).
Proof.
  intros i Hi. apply (zwin_hex_byte_at _ 40960%uint63 11198464%uint63 i bss_zwin).
  - vm_compute. discriminate.
  - change (Uint63.to_Z 40960%uint63) with 40960. lia.
  - change (Uint63.to_Z 40960%uint63) with 40960. change (Uint63.to_Z 11198464%uint63) with 11198464. lia.
Qed.

Lemma bss_rom_zero : forall a, BSS0_LO <= a < BSS0_HI -> seg_rom asegs (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha. unfold BSS0_LO, BSS0_HI in Ha. unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
  rewrite (a_find_segment_1 a) by lia.
  replace ((0x10000 <=? a) && (a + 1 <=? 0x3b000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0x3b000 <=? a) && (a + 1 <=? 0xcd000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xcd000 <=? a) && (a + 1 <=? 0xd3000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xd3000 <=? a) && (a + 1 <=? 0x62f000)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  cbn -[segment_byte_at Z.sub Z.to_N Z.of_N].
  change (Z.of_N 864256) with 0xd3000. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes segment_byte_at]. rewrite API.asan_len3.
  replace (Z.to_N (a - 0xd3000) <? 5619712)%N with true by (symmetry; apply N.ltb_lt; lia).
  rewrite bss_hex0 by lia. reflexivity.
Qed.

Lemma bss_wview : forall m a, BSS0_LO <= a < BSS0_HI -> wview asegs m (wa a) <> None.
Proof.
  intros m a Ha. unfold BSS0_LO, BSS0_HI in Ha. change asegs with API.ASEGS. apply API.asan_rw_window. rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_bss0 : forall (m : word -> option byte) A n, BSS0_LO <= A -> A + n <= BSS0_HI -> 0 <= n ->
  (forall i, A <= i < A + n -> m (wa i) = None) ->
  rw_cells asegs m A [CB (Z.to_nat n) (ME.zeros n)].
Proof.
  intros m A n HA Hn N0 HM. unfold BSS0_LO, BSS0_HI in *. split.
  - split; [cbn; split; [unfold ME.zeros; rewrite repeat_length; reflexivity| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [unfold ME.zeros; rewrite repeat_length, Z2Nat.id by lia; lia|].
    intros i Hi. unfold ME.zeros in Hi |- *. rewrite repeat_length in Hi. rewrite (nth_error_repeat (Z_to_bv 8 0) Hi).
    unfold mrd. rewrite (HM (A + Z.of_nat i)) by lia. apply bss_rom_zero. unfold BSS0_LO, BSS0_HI. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|].
    intros i Hi. apply bss_wview. unfold BSS0_LO, BSS0_HI. lia.
Qed.

Lemma rw_cells_bss0_as : forall (m : word -> option byte) A cs, BSS0_LO <= A -> A + Z.of_nat (cells_size cs) <= BSS0_HI ->
  cells_wf cs -> cells_bytes cs = ME.zeros (Z.of_nat (cells_size cs)) ->
  (forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None) ->
  rw_cells asegs m A cs.
Proof.
  intros m A cs HA Hn WF EB HM.
  apply (rw_cells_recast asegs m A [CB (Z.to_nat (Z.of_nat (cells_size cs))) (ME.zeros (Z.of_nat (cells_size cs)))]);
    [| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact EB| cbn [cells_size csize]; lia].
  apply rw_cells_bss0; [exact HA| exact Hn| lia| exact HM].
Qed.

Lemma bss_azero : forall (m : word -> option byte) A n, BSS0_LO <= A -> A + n <= BSS0_HI ->
  (forall i, A <= i < A + n -> m (wa i) = None) ->
  (forall i, 0 <= i < n -> mrd asegs m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at asegs m A n.
Proof.
  intros m A n HA Hn HM. unfold BSS0_LO, BSS0_HI in *. split.
  - intros i Hi. unfold mrd. rewrite (HM (A + i)) by lia. apply bss_rom_zero. unfold BSS0_LO, BSS0_HI. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. apply bss_wview. unfold BSS0_LO, BSS0_HI. lia.
Qed.

Lemma rw2_rom_some : forall a, 0xd3000 <= a < 0x62f000 -> exists b, seg_rom asegs (wa a) = Some b.
Proof.
  intros a Ha. unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
  rewrite (a_find_segment_1 a) by lia.
  replace ((0x10000 <=? a) && (a + 1 <=? 0x3b000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0x3b000 <=? a) && (a + 1 <=? 0xcd000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xcd000 <=? a) && (a + 1 <=? 0xd3000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xd3000 <=? a) && (a + 1 <=? 0x62f000)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  cbn -[segment_byte_at Z.sub Z.to_N Z.of_N].
  change (Z.of_N 864256) with 0xd3000. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes segment_byte_at]. rewrite API.asan_len3.
  replace (Z.to_N (a - 0xd3000) <? 5619712)%N with true by (symmetry; apply N.ltb_lt; lia).
  destruct (hex_byte_at Asan_seg_bytes_003 (Z.to_N (a - 0xd3000))) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. revert E. replace (Z.to_N (a - 0xd3000)) with (0 + Z.to_N (a - 0xd3000))%N by lia.
  apply (scanN_sound _ 64 0 5619712 API.asan_hex3). lia.
Qed.

Lemma rw2_stk : forall (m : word -> option byte) lo hi, 0xd3000 <= lo -> hi <= 0x62f000 -> stk asegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi. split; [lia|]. split; [lia|]. intros a Ha. split.
  - change asegs with API.ASEGS. apply API.asan_rw_window. rewrite wa_unsigned by lia. lia.
  - unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity|]. apply rw2_rom_some. lia.
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require BothPlanImages.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.AsanHexScan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.AsanHexZero.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module API := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.BothPlanImages.

Definition BSS0_LO : Z := 0xda000.
Definition BSS0_HI : Z := 0x631000.

Lemma bss_zwin : zwin AsanUbsan_seg_bytes_003 40960%uint63 11198464%uint63 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bss_hex0 : forall i : N, 20480 <= Z.of_N i < 5619712 ->
  hex_byte_at AsanUbsan_seg_bytes_003 i = Some (Z_to_bv 8 0).
Proof.
  intros i Hi. apply (zwin_hex_byte_at _ 40960%uint63 11198464%uint63 i bss_zwin).
  - vm_compute. discriminate.
  - change (Uint63.to_Z 40960%uint63) with 40960. lia.
  - change (Uint63.to_Z 40960%uint63) with 40960. change (Uint63.to_Z 11198464%uint63) with 11198464. lia.
Qed.

Lemma bss_rom_zero : forall a, BSS0_LO <= a < BSS0_HI -> seg_rom bsegs (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha. unfold BSS0_LO, BSS0_HI in Ha. unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
  rewrite (a_find_segment_1 a) by lia.
  replace ((0x10000 <=? a) && (a + 1 <=? 0x3c000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0x3c000 <=? a) && (a + 1 <=? 0xcf000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xcf000 <=? a) && (a + 1 <=? 0xd5000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xd5000 <=? a) && (a + 1 <=? 0x631000)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  cbn -[segment_byte_at Z.sub Z.to_N Z.of_N].
  change (Z.of_N 872448) with 0xd5000. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes segment_byte_at]. rewrite API.both_len3.
  replace (Z.to_N (a - 0xd5000) <? 5619712)%N with true by (symmetry; apply N.ltb_lt; lia).
  rewrite bss_hex0 by lia. reflexivity.
Qed.

Lemma bss_wview : forall m a, BSS0_LO <= a < BSS0_HI -> wview bsegs m (wa a) <> None.
Proof.
  intros m a Ha. unfold BSS0_LO, BSS0_HI in Ha. change bsegs with API.BSEGS. apply API.both_rw_window. rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_bss0 : forall (m : word -> option byte) A n, BSS0_LO <= A -> A + n <= BSS0_HI -> 0 <= n ->
  (forall i, A <= i < A + n -> m (wa i) = None) ->
  rw_cells bsegs m A [CB (Z.to_nat n) (ME.zeros n)].
Proof.
  intros m A n HA Hn N0 HM. unfold BSS0_LO, BSS0_HI in *. split.
  - split; [cbn; split; [unfold ME.zeros; rewrite repeat_length; reflexivity| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [unfold ME.zeros; rewrite repeat_length, Z2Nat.id by lia; lia|].
    intros i Hi. unfold ME.zeros in Hi |- *. rewrite repeat_length in Hi. rewrite (nth_error_repeat (Z_to_bv 8 0) Hi).
    unfold mrd. rewrite (HM (A + Z.of_nat i)) by lia. apply bss_rom_zero. unfold BSS0_LO, BSS0_HI. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|].
    intros i Hi. apply bss_wview. unfold BSS0_LO, BSS0_HI. lia.
Qed.

Lemma rw_cells_bss0_as : forall (m : word -> option byte) A cs, BSS0_LO <= A -> A + Z.of_nat (cells_size cs) <= BSS0_HI ->
  cells_wf cs -> cells_bytes cs = ME.zeros (Z.of_nat (cells_size cs)) ->
  (forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None) ->
  rw_cells bsegs m A cs.
Proof.
  intros m A cs HA Hn WF EB HM.
  apply (rw_cells_recast bsegs m A [CB (Z.to_nat (Z.of_nat (cells_size cs))) (ME.zeros (Z.of_nat (cells_size cs)))]);
    [| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact EB| cbn [cells_size csize]; lia].
  apply rw_cells_bss0; [exact HA| exact Hn| lia| exact HM].
Qed.

Lemma bss_azero : forall (m : word -> option byte) A n, BSS0_LO <= A -> A + n <= BSS0_HI ->
  (forall i, A <= i < A + n -> m (wa i) = None) ->
  (forall i, 0 <= i < n -> mrd bsegs m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at bsegs m A n.
Proof.
  intros m A n HA Hn HM. unfold BSS0_LO, BSS0_HI in *. split.
  - intros i Hi. unfold mrd. rewrite (HM (A + i)) by lia. apply bss_rom_zero. unfold BSS0_LO, BSS0_HI. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. apply bss_wview. unfold BSS0_LO, BSS0_HI. lia.
Qed.

Lemma rw2_rom_some : forall a, 0xd5000 <= a < 0x631000 -> exists b, seg_rom bsegs (wa a) = Some b.
Proof.
  intros a Ha. unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
  rewrite (a_find_segment_1 a) by lia.
  replace ((0x10000 <=? a) && (a + 1 <=? 0x3c000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0x3c000 <=? a) && (a + 1 <=? 0xcf000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xcf000 <=? a) && (a + 1 <=? 0xd5000)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((0xd5000 <=? a) && (a + 1 <=? 0x631000)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  cbn -[segment_byte_at Z.sub Z.to_N Z.of_N].
  change (Z.of_N 872448) with 0xd5000. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes segment_byte_at]. rewrite API.both_len3.
  replace (Z.to_N (a - 0xd5000) <? 5619712)%N with true by (symmetry; apply N.ltb_lt; lia).
  destruct (hex_byte_at AsanUbsan_seg_bytes_003 (Z.to_N (a - 0xd5000))) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. revert E. replace (Z.to_N (a - 0xd5000)) with (0 + Z.to_N (a - 0xd5000))%N by lia.
  apply (scanN_sound _ 64 0 5619712 API.both_hex3). lia.
Qed.

Lemma rw2_stk : forall (m : word -> option byte) lo hi, 0xd5000 <= lo -> hi <= 0x631000 -> stk bsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi. split; [lia|]. split; [lia|]. intros a Ha. split.
  - change bsegs with API.BSEGS. apply API.both_rw_window. rewrite wa_unsigned by lia. lia.
  - unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity|]. apply rw2_rom_some. lia.
Qed.
End TwinB.
