(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1ch X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh X1rg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_speex_packet_to_header : Z := 0x99e60.
Definition P2H_MAGIC : Z := 0x237a0.
Definition P2H_FMT_NOTIFY : Z := 0x23860.
Definition P2H_MSG_TOO_SMALL : Z := 0x237c0.
Definition P2H_MSG_BAD_MODE : Z := 0x23800.
Definition P2H_LOOP : Z := 0x99ea4.
Definition P2H_ALLOC : Z := 0x99f1c.
Definition P2H_EXIT : Z := 0x9a0a4.
Definition P2H_RET : Z := 0x9a0a8.
Definition RA_p2h_calloc : Z := 0x99f28.
Definition RA_p2h_memcpy : Z := 0x99f48.
Definition RA_p2h_fprintf_small : Z := 0x9a068.
Definition RA_p2h_fprintf_mode : Z := 0x9a09c.
Definition RA_p2h_free : Z := 0x9a0a4.
Definition wz (z : Z) : word := Z_to_bv 64 z.

Lemma s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros x. unfold s32. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Definition w4 (b0 b1 b2 b3 : byte) : Z := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Lemma w4_range : forall b0 b1 b2 b3, 0 <= w4 b0 b1 b2 b3 < 2^32.
Proof.
intros. unfold w4.
pose proof (bv_unsigned_in_range 8 b0). pose proof (bv_unsigned_in_range 8 b1).
pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3).
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.
Lemma byte_of_Z : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
intros b z E. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. exact E.
Qed.
Lemma le4_w4 : forall b0 b1 b2 b3, le4 (Z_to_bv 64 (w4 b0 b1 b2 b3)) = [b0; b1; b2; b3].
Proof.
intros.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le4. rewrite unsigned_lit64 by (unfold w4; lia). cbn [Z_to_le_bytes].
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia.
unfold w4.
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal. apply byte_of_Z; Z.div_mod_to_equations; nia.
Qed.
Lemma s32_eqm : forall x, (s32 x) mod 2^32 = x mod 2^32.
Proof.
intros x. unfold s32.
pose proof (Z.div_mod (x + 2^31) (2^32) ltac:(lia)) as E.
set (q := (x + 2 ^ 31) / 2 ^ 32) in E.
replace ((x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) with (x + (- q) * 2 ^ 32) by lia.
apply Z.mod_add. lia.
Qed.
Lemma le4_s32_w4 : forall b0 b1 b2 b3, le4 (Z_to_bv 64 (s32 (w4 b0 b1 b2 b3))) = [b0; b1; b2; b3].
Proof. intros. rewrite <- le4_w4. apply le4_lit_eqm. apply s32_eqm. Qed.
Lemma s32_small_id : forall x, 0 <= x < 2^31 -> s32 x = x.
Proof. intros x H. unfold s32. rewrite Z.mod_small by lia. lia. Qed.
Lemma s32_big : forall x, 2^31 <= x < 2^32 -> s32 x = x - 2^32.
Proof. intros x H. unfold s32. replace (x + 2^31) with ((x - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. Qed.

Lemma sx32_w : forall u, 0 <= u < 2^32 -> sx32 (Z_to_bv 64 u) = Z_to_bv 64 (s32 u).
Proof.
intros u Hu. unfold sx32. f_equal. rewrite unsigned_lit64 by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, s32.
change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31). reflexivity.
Qed.

Lemma lit64_neg_wrap : forall v, -2^63 <= v < 0 -> Z_to_bv 64 v = Z_to_bv 64 (v + 2^64).
Proof.
intros v Hv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
replace (v + 2^64) with (v + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma lts_zero_lit : forall c, -2^63 <= c < 2^63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 c) = (0 <? c).
Proof. intros c Hc. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.

Definition hb (pb : list byte) (i : nat) : byte := nth i pb (Z_to_bv 8 0).
Definition fw (pb : list byte) (i : nat) : Z := w4 (hb pb i) (hb pb (i + 1)) (hb pb (i + 2)) (hb pb (i + 3)).
Lemma skipn_hb : forall (pb : list byte) i, (i < length pb)%nat -> skipn i pb = hb pb i :: skipn (S i) pb.
Proof.
intros pb i Hi. unfold hb. revert i Hi. induction pb as [|x pb IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|].
apply IH. lia.
Qed.
Lemma le32_at_fw : forall (pb : list byte) (i : nat), (i + 4 <= length pb)%nat ->
le32_at (map bv_unsigned pb) (Z.of_nat i) = fw pb i.
Proof.
intros pb i Hi. unfold le32_at, zslice, ztake, zdrop. rewrite Nat2Z.id.
rewrite skipn_map.
rewrite (skipn_hb pb i), (skipn_hb pb (S i)), (skipn_hb pb (S (S i))), (skipn_hb pb (S (S (S i)))) by lia.
change (Z.to_nat 4) with 4%nat.
cbn [map firstn le_val]. rewrite firstn_O. cbn [le_val]. unfold fw, w4.
replace (i + 1)%nat with (S i) by lia. replace (i + 2)%nat with (S (S i)) by lia. replace (i + 3)%nat with (S (S (S i))) by lia.
lia.
Qed.
Lemma firstn_S_hb : forall (pb : list byte) i, (i < length pb)%nat -> firstn (S i) pb = firstn i pb ++ [hb pb i].
Proof.
intros pb i Hi. rewrite <- (firstn_skipn i pb) at 1. rewrite firstn_app, length_firstn, firstn_firstn.
replace (Nat.min (S i) i) with i by lia. replace (S i - Nat.min i (length pb))%nat with 1%nat by lia.
rewrite (skipn_hb pb i Hi). cbn. reflexivity.
Qed.
Lemma firstn_plus4 : forall (pb : list byte) n i, (n = i + 4)%nat -> (n <= length pb)%nat ->
firstn n pb = firstn i pb ++ [hb pb i; hb pb (i + 1); hb pb (i + 2); hb pb (i + 3)].
Proof.
intros pb n i -> Hi.
replace (i + 4)%nat with (S (S (S (S i)))) by lia.
rewrite (firstn_S_hb pb (S (S (S i)))) by lia. rewrite (firstn_S_hb pb (S (S i))) by lia.
rewrite (firstn_S_hb pb (S i)) by lia. rewrite (firstn_S_hb pb i) by lia.
rewrite <- !app_assoc. cbn. replace (i + 1)%nat with (S i) by lia. replace (i + 2)%nat with (S (S i)) by lia.
replace (i + 3)%nat with (S (S (S i))) by lia. reflexivity.
Qed.
Definition hdr_cells (pb : list byte) (c48 : word) : list cell :=
[CB 28 (firstn 28 pb); C4 (Z_to_bv 64 (fw pb 28)); C4 (Z_to_bv 64 (fw pb 32)); C4 (Z_to_bv 64 (fw pb 36));
C4 (Z_to_bv 64 (fw pb 40)); C4 (Z_to_bv 64 (fw pb 44)); C4 c48;
C4 (Z_to_bv 64 (fw pb 52)); C4 (Z_to_bv 64 (fw pb 56)); C4 (Z_to_bv 64 (fw pb 60)); C4 (Z_to_bv 64 (fw pb 64));
C4 (Z_to_bv 64 (fw pb 68)); C4 (Z_to_bv 64 (fw pb 72)); C4 (Z_to_bv 64 (fw pb 76))].
Lemma le4_fw : forall pb i, le4 (Z_to_bv 64 (fw pb i)) = [hb pb i; hb pb (i + 1); hb pb (i + 2); hb pb (i + 3)].
Proof. intros. unfold fw. apply le4_w4. Qed.

Lemma hdr_cells_bytes : forall pb, (80 <= length pb)%nat ->
cells_bytes (hdr_cells pb (Z_to_bv 64 (fw pb 48))) = firstn 80 pb.
Proof.
intros pb L. unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_fw, app_nil_r.
rewrite (firstn_plus4 pb 80 76), (firstn_plus4 pb 76 72), (firstn_plus4 pb 72 68), (firstn_plus4 pb 68 64) by lia.
rewrite (firstn_plus4 pb 64 60), (firstn_plus4 pb 60 56), (firstn_plus4 pb 56 52), (firstn_plus4 pb 52 48) by lia.
rewrite (firstn_plus4 pb 48 44), (firstn_plus4 pb 44 40), (firstn_plus4 pb 40 36), (firstn_plus4 pb 36 32) by lia.
rewrite (firstn_plus4 pb 32 28) by lia.
cbn [Nat.add]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma hdr_cells_wf : forall pb c48, (80 <= length pb)%nat -> cells_wf (hdr_cells pb c48).
Proof. intros pb c48 L. unfold hdr_cells. cbn. rewrite length_firstn. repeat split; try lia; exact I. Qed.
Lemma header_fields : forall pb, (80 <= length pb)%nat ->
let h := header_of_bytes (map bv_unsigned pb) in
hd_speex_version_id h = s32 (fw pb 28) /\ hd_header_size h = s32 (fw pb 32) /\ hd_rate h = s32 (fw pb 36)
/\ hd_mode h = s32 (fw pb 40) /\ hd_mode_bitstream_version h = s32 (fw pb 44) /\ hd_nb_channels h = s32 (fw pb 48)
/\ hd_frames_per_packet h = s32 (fw pb 64) /\ hd_extra_headers h = s32 (fw pb 68).
Proof.
intros pb L. cbn [header_of_bytes hd_speex_version_id hd_header_size hd_rate hd_mode hd_mode_bitstream_version hd_nb_channels
hd_frames_per_packet hd_extra_headers].
unfold s32_at.
change 28 with (Z.of_nat 28). change 32 with (Z.of_nat 32). change 36 with (Z.of_nat 36). change 40 with (Z.of_nat 40).
change 44 with (Z.of_nat 44). change 48 with (Z.of_nat 48). change 64 with (Z.of_nat 64). change 68 with (Z.of_nat 68).
rewrite !le32_at_fw by lia. repeat split; reflexivity.
Qed.

Lemma fw_range : forall pb i, 0 <= fw pb i < 2^32.
Proof. intros. unfold fw. apply w4_range. Qed.

Definition MAGIC_BYTES : list byte := map (fun z => Z_to_bv 8 z) SPEEX_MAGIC.
Lemma MAGIC_BYTES_eq : MAGIC_BYTES = [Z_to_bv 8 83; Z_to_bv 8 112; Z_to_bv 8 101; Z_to_bv 8 101; Z_to_bv 8 120; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32].
Proof. reflexivity. Qed.
Lemma MAGIC_unsigned : map bv_unsigned MAGIC_BYTES = SPEEX_MAGIC.
Proof. vm_compute. reflexivity. Qed.

Definition SIZEOF_SPEEX_HEADER_Z : Z := 80.
Definition spx_header_cells (junk28 : list byte) (hd : spx_header) (bitrate_w fsz_w vbr_w r1 r2 : word) : list cell :=
[CB 28 junk28;
C4 (wz (hd_speex_version_id hd)); C4 (wz (hd_header_size hd)); C4 (wz (hd_rate hd)); C4 (wz (hd_mode hd));
C4 (wz (hd_mode_bitstream_version hd)); C4 (wz (hd_nb_channels hd));
C4 bitrate_w; C4 fsz_w; C4 vbr_w;
C4 (wz (hd_frames_per_packet hd)); C4 (wz (hd_extra_headers hd)); C4 r1; C4 r2].

Lemma le4_s32_fw : forall pb i, le4 (Z_to_bv 64 (s32 (fw pb i))) = le4 (Z_to_bv 64 (fw pb i)).
Proof. intros. apply le4_lit_eqm. apply s32_eqm. Qed.

Lemma hdr_cells_post : forall (m3 : mem) A pb cv, (80 <= length pb)%nat ->
rw_cells bsegs m3 A (hdr_cells pb (Z_to_bv 64 cv)) ->
rw_cells bsegs m3 A (spx_header_cells (firstn 28 pb) (set_nb_channels (header_of_bytes (map bv_unsigned pb)) cv)
(Z_to_bv 64 (fw pb 52)) (Z_to_bv 64 (fw pb 56)) (Z_to_bv 64 (fw pb 60)) (Z_to_bv 64 (fw pb 72)) (Z_to_bv 64 (fw pb 76))).
Proof.
intros m3 A pb cv L HDR.
pose proof (header_fields pb L) as HFS. cbv zeta in HFS. destruct HFS as (E28 & E32 & E36 & E40 & E44 & E48 & E64 & E68).
unfold spx_header_cells, wz.
cbn [set_nb_channels hd_speex_version_id hd_header_size hd_rate hd_mode hd_mode_bitstream_version hd_nb_channels hd_frames_per_packet hd_extra_headers].
rewrite E28, E32, E36, E40, E44, E64, E68.
eapply rw_cells_samebytes; [exact HDR| | |].
- cbn. rewrite length_firstn. repeat split; try lia; exact I.
- unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_s32_fw. reflexivity.
- cbn. reflexivity.
Qed.

Lemma hdr_cells_of_bytes : forall (m : mem) A pb, (80 <= length pb)%nat ->
rw_cells bsegs m A [CB 80 (firstn 80 pb)] -> rw_cells bsegs m A (hdr_cells pb (Z_to_bv 64 (fw pb 48))).
Proof.
intros m A pb L X. apply (rw_cells_recast bsegs m A _ _ X); [apply hdr_cells_wf; exact L|].
rewrite (hdr_cells_bytes pb L). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
Qed.

Lemma p2h_magic_ro : forall m, mem_inv bsegs m -> u8ro bsegs m P2H_MAGIC MAGIC_BYTES.
Proof.
intros m MI. unfold u8ro.
pose proof (ro_cells_image bsegs m P2H_MAGIC MAGIC_BYTES MI ltac:(vm_compute; reflexivity) ltac:(unfold P2H_MAGIC; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Definition msg_too_small : list byte := map (fun z => Z_to_bv 8 z) MSG_HEADER_TOO_SMALL.
Definition msg_bad_mode : list byte := map (fun z => Z_to_bv 8 z) MSG_INVALID_MODE_HEADER.
Lemma msg_too_small_at : forall m, mem_inv bsegs m -> bytes_at bsegs m P2H_MSG_TOO_SMALL (msg_too_small ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image bsegs m P2H_MSG_TOO_SMALL (msg_too_small ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold P2H_MSG_TOO_SMALL; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma msg_bad_mode_at : forall m, mem_inv bsegs m -> bytes_at bsegs m P2H_MSG_BAD_MODE (msg_bad_mode ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image bsegs m P2H_MSG_BAD_MODE (msg_bad_mode ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold P2H_MSG_BAD_MODE; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma msg_too_small_unsigned : map bv_unsigned msg_too_small = MSG_HEADER_TOO_SMALL. Proof. vm_compute. reflexivity. Qed.
Lemma msg_bad_mode_unsigned : map bv_unsigned msg_bad_mode = MSG_INVALID_MODE_HEADER. Proof. vm_compute. reflexivity. Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_speex_packet_to_header : Z := 0x9941c.
Definition P2H_MAGIC : Z := 0x23760.
Definition P2H_FMT_NOTIFY : Z := 0x23820.
Definition P2H_MSG_TOO_SMALL : Z := 0x23780.
Definition P2H_MSG_BAD_MODE : Z := 0x237c0.
Definition P2H_LOOP : Z := 0x99458.
Definition P2H_ALLOC : Z := 0x994b8.
Definition P2H_EXIT : Z := 0x995b4.
Definition P2H_RET : Z := 0x995b8.
Definition RA_p2h_calloc : Z := 0x994c4.
Definition RA_p2h_memcpy : Z := 0x994d4.
Definition RA_p2h_fprintf_small : Z := 0x99578.
Definition RA_p2h_fprintf_mode : Z := 0x995ac.
Definition RA_p2h_free : Z := 0x995b4.
Definition wz (z : Z) : word := Z_to_bv 64 z.

Lemma s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros x. unfold s32. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Definition w4 (b0 b1 b2 b3 : byte) : Z := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Lemma w4_range : forall b0 b1 b2 b3, 0 <= w4 b0 b1 b2 b3 < 2^32.
Proof.
intros. unfold w4.
pose proof (bv_unsigned_in_range 8 b0). pose proof (bv_unsigned_in_range 8 b1).
pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3).
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.
Lemma byte_of_Z : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
intros b z E. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. exact E.
Qed.
Lemma le4_w4 : forall b0 b1 b2 b3, le4 (Z_to_bv 64 (w4 b0 b1 b2 b3)) = [b0; b1; b2; b3].
Proof.
intros.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le4. rewrite unsigned_lit64 by (unfold w4; lia). cbn [Z_to_le_bytes].
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia.
unfold w4.
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal. apply byte_of_Z; Z.div_mod_to_equations; nia.
Qed.
Lemma s32_eqm : forall x, (s32 x) mod 2^32 = x mod 2^32.
Proof.
intros x. unfold s32.
pose proof (Z.div_mod (x + 2^31) (2^32) ltac:(lia)) as E.
set (q := (x + 2 ^ 31) / 2 ^ 32) in E.
replace ((x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) with (x + (- q) * 2 ^ 32) by lia.
apply Z.mod_add. lia.
Qed.
Lemma le4_s32_w4 : forall b0 b1 b2 b3, le4 (Z_to_bv 64 (s32 (w4 b0 b1 b2 b3))) = [b0; b1; b2; b3].
Proof. intros. rewrite <- le4_w4. apply le4_lit_eqm. apply s32_eqm. Qed.
Lemma s32_small_id : forall x, 0 <= x < 2^31 -> s32 x = x.
Proof. intros x H. unfold s32. rewrite Z.mod_small by lia. lia. Qed.
Lemma s32_big : forall x, 2^31 <= x < 2^32 -> s32 x = x - 2^32.
Proof. intros x H. unfold s32. replace (x + 2^31) with ((x - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. Qed.

Lemma sx32_w : forall u, 0 <= u < 2^32 -> sx32 (Z_to_bv 64 u) = Z_to_bv 64 (s32 u).
Proof.
intros u Hu. unfold sx32. f_equal. rewrite unsigned_lit64 by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, s32.
change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31). reflexivity.
Qed.

Lemma lit64_neg_wrap : forall v, -2^63 <= v < 0 -> Z_to_bv 64 v = Z_to_bv 64 (v + 2^64).
Proof.
intros v Hv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
replace (v + 2^64) with (v + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma lts_zero_lit : forall c, -2^63 <= c < 2^63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 c) = (0 <? c).
Proof. intros c Hc. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.

Definition hb (pb : list byte) (i : nat) : byte := nth i pb (Z_to_bv 8 0).
Definition fw (pb : list byte) (i : nat) : Z := w4 (hb pb i) (hb pb (i + 1)) (hb pb (i + 2)) (hb pb (i + 3)).
Lemma skipn_hb : forall (pb : list byte) i, (i < length pb)%nat -> skipn i pb = hb pb i :: skipn (S i) pb.
Proof.
intros pb i Hi. unfold hb. revert i Hi. induction pb as [|x pb IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|].
apply IH. lia.
Qed.
Lemma le32_at_fw : forall (pb : list byte) (i : nat), (i + 4 <= length pb)%nat ->
le32_at (map bv_unsigned pb) (Z.of_nat i) = fw pb i.
Proof.
intros pb i Hi. unfold le32_at, zslice, ztake, zdrop. rewrite Nat2Z.id.
rewrite skipn_map.
rewrite (skipn_hb pb i), (skipn_hb pb (S i)), (skipn_hb pb (S (S i))), (skipn_hb pb (S (S (S i)))) by lia.
change (Z.to_nat 4) with 4%nat.
cbn [map firstn le_val]. rewrite firstn_O. cbn [le_val]. unfold fw, w4.
replace (i + 1)%nat with (S i) by lia. replace (i + 2)%nat with (S (S i)) by lia. replace (i + 3)%nat with (S (S (S i))) by lia.
lia.
Qed.
Lemma firstn_S_hb : forall (pb : list byte) i, (i < length pb)%nat -> firstn (S i) pb = firstn i pb ++ [hb pb i].
Proof.
intros pb i Hi. rewrite <- (firstn_skipn i pb) at 1. rewrite firstn_app, length_firstn, firstn_firstn.
replace (Nat.min (S i) i) with i by lia. replace (S i - Nat.min i (length pb))%nat with 1%nat by lia.
rewrite (skipn_hb pb i Hi). cbn. reflexivity.
Qed.
Lemma firstn_plus4 : forall (pb : list byte) n i, (n = i + 4)%nat -> (n <= length pb)%nat ->
firstn n pb = firstn i pb ++ [hb pb i; hb pb (i + 1); hb pb (i + 2); hb pb (i + 3)].
Proof.
intros pb n i -> Hi.
replace (i + 4)%nat with (S (S (S (S i)))) by lia.
rewrite (firstn_S_hb pb (S (S (S i)))) by lia. rewrite (firstn_S_hb pb (S (S i))) by lia.
rewrite (firstn_S_hb pb (S i)) by lia. rewrite (firstn_S_hb pb i) by lia.
rewrite <- !app_assoc. cbn. replace (i + 1)%nat with (S i) by lia. replace (i + 2)%nat with (S (S i)) by lia.
replace (i + 3)%nat with (S (S (S i))) by lia. reflexivity.
Qed.
Definition hdr_cells (pb : list byte) (c48 : word) : list cell :=
[CB 28 (firstn 28 pb); C4 (Z_to_bv 64 (fw pb 28)); C4 (Z_to_bv 64 (fw pb 32)); C4 (Z_to_bv 64 (fw pb 36));
C4 (Z_to_bv 64 (fw pb 40)); C4 (Z_to_bv 64 (fw pb 44)); C4 c48;
C4 (Z_to_bv 64 (fw pb 52)); C4 (Z_to_bv 64 (fw pb 56)); C4 (Z_to_bv 64 (fw pb 60)); C4 (Z_to_bv 64 (fw pb 64));
C4 (Z_to_bv 64 (fw pb 68)); C4 (Z_to_bv 64 (fw pb 72)); C4 (Z_to_bv 64 (fw pb 76))].
Lemma le4_fw : forall pb i, le4 (Z_to_bv 64 (fw pb i)) = [hb pb i; hb pb (i + 1); hb pb (i + 2); hb pb (i + 3)].
Proof. intros. unfold fw. apply le4_w4. Qed.

Lemma hdr_cells_bytes : forall pb, (80 <= length pb)%nat ->
cells_bytes (hdr_cells pb (Z_to_bv 64 (fw pb 48))) = firstn 80 pb.
Proof.
intros pb L. unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_fw, app_nil_r.
rewrite (firstn_plus4 pb 80 76), (firstn_plus4 pb 76 72), (firstn_plus4 pb 72 68), (firstn_plus4 pb 68 64) by lia.
rewrite (firstn_plus4 pb 64 60), (firstn_plus4 pb 60 56), (firstn_plus4 pb 56 52), (firstn_plus4 pb 52 48) by lia.
rewrite (firstn_plus4 pb 48 44), (firstn_plus4 pb 44 40), (firstn_plus4 pb 40 36), (firstn_plus4 pb 36 32) by lia.
rewrite (firstn_plus4 pb 32 28) by lia.
cbn [Nat.add]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma hdr_cells_wf : forall pb c48, (80 <= length pb)%nat -> cells_wf (hdr_cells pb c48).
Proof. intros pb c48 L. unfold hdr_cells. cbn. rewrite length_firstn. repeat split; try lia; exact I. Qed.
Lemma header_fields : forall pb, (80 <= length pb)%nat ->
let h := header_of_bytes (map bv_unsigned pb) in
hd_speex_version_id h = s32 (fw pb 28) /\ hd_header_size h = s32 (fw pb 32) /\ hd_rate h = s32 (fw pb 36)
/\ hd_mode h = s32 (fw pb 40) /\ hd_mode_bitstream_version h = s32 (fw pb 44) /\ hd_nb_channels h = s32 (fw pb 48)
/\ hd_frames_per_packet h = s32 (fw pb 64) /\ hd_extra_headers h = s32 (fw pb 68).
Proof.
intros pb L. cbn [header_of_bytes hd_speex_version_id hd_header_size hd_rate hd_mode hd_mode_bitstream_version hd_nb_channels
hd_frames_per_packet hd_extra_headers].
unfold s32_at.
change 28 with (Z.of_nat 28). change 32 with (Z.of_nat 32). change 36 with (Z.of_nat 36). change 40 with (Z.of_nat 40).
change 44 with (Z.of_nat 44). change 48 with (Z.of_nat 48). change 64 with (Z.of_nat 64). change 68 with (Z.of_nat 68).
rewrite !le32_at_fw by lia. repeat split; reflexivity.
Qed.

Lemma fw_range : forall pb i, 0 <= fw pb i < 2^32.
Proof. intros. unfold fw. apply w4_range. Qed.

Definition MAGIC_BYTES : list byte := map (fun z => Z_to_bv 8 z) SPEEX_MAGIC.
Lemma MAGIC_BYTES_eq : MAGIC_BYTES = [Z_to_bv 8 83; Z_to_bv 8 112; Z_to_bv 8 101; Z_to_bv 8 101; Z_to_bv 8 120; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32].
Proof. reflexivity. Qed.
Lemma MAGIC_unsigned : map bv_unsigned MAGIC_BYTES = SPEEX_MAGIC.
Proof. vm_compute. reflexivity. Qed.

Definition SIZEOF_SPEEX_HEADER_Z : Z := 80.
Definition spx_header_cells (junk28 : list byte) (hd : spx_header) (bitrate_w fsz_w vbr_w r1 r2 : word) : list cell :=
[CB 28 junk28;
C4 (wz (hd_speex_version_id hd)); C4 (wz (hd_header_size hd)); C4 (wz (hd_rate hd)); C4 (wz (hd_mode hd));
C4 (wz (hd_mode_bitstream_version hd)); C4 (wz (hd_nb_channels hd));
C4 bitrate_w; C4 fsz_w; C4 vbr_w;
C4 (wz (hd_frames_per_packet hd)); C4 (wz (hd_extra_headers hd)); C4 r1; C4 r2].

Lemma le4_s32_fw : forall pb i, le4 (Z_to_bv 64 (s32 (fw pb i))) = le4 (Z_to_bv 64 (fw pb i)).
Proof. intros. apply le4_lit_eqm. apply s32_eqm. Qed.

Lemma hdr_cells_post : forall (m3 : mem) A pb cv, (80 <= length pb)%nat ->
rw_cells asegs m3 A (hdr_cells pb (Z_to_bv 64 cv)) ->
rw_cells asegs m3 A (spx_header_cells (firstn 28 pb) (set_nb_channels (header_of_bytes (map bv_unsigned pb)) cv)
(Z_to_bv 64 (fw pb 52)) (Z_to_bv 64 (fw pb 56)) (Z_to_bv 64 (fw pb 60)) (Z_to_bv 64 (fw pb 72)) (Z_to_bv 64 (fw pb 76))).
Proof.
intros m3 A pb cv L HDR.
pose proof (header_fields pb L) as HFS. cbv zeta in HFS. destruct HFS as (E28 & E32 & E36 & E40 & E44 & E48 & E64 & E68).
unfold spx_header_cells, wz.
cbn [set_nb_channels hd_speex_version_id hd_header_size hd_rate hd_mode hd_mode_bitstream_version hd_nb_channels hd_frames_per_packet hd_extra_headers].
rewrite E28, E32, E36, E40, E44, E64, E68.
eapply rw_cells_samebytes; [exact HDR| | |].
- cbn. rewrite length_firstn. repeat split; try lia; exact I.
- unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_s32_fw. reflexivity.
- cbn. reflexivity.
Qed.

Lemma hdr_cells_of_bytes : forall (m : mem) A pb, (80 <= length pb)%nat ->
rw_cells asegs m A [CB 80 (firstn 80 pb)] -> rw_cells asegs m A (hdr_cells pb (Z_to_bv 64 (fw pb 48))).
Proof.
intros m A pb L X. apply (rw_cells_recast asegs m A _ _ X); [apply hdr_cells_wf; exact L|].
rewrite (hdr_cells_bytes pb L). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
Qed.

Lemma p2h_magic_ro : forall m, mem_inv asegs m -> u8ro asegs m P2H_MAGIC MAGIC_BYTES.
Proof.
intros m MI. unfold u8ro.
pose proof (ro_cells_image asegs m P2H_MAGIC MAGIC_BYTES MI ltac:(vm_compute; reflexivity) ltac:(unfold P2H_MAGIC; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Definition msg_too_small : list byte := map (fun z => Z_to_bv 8 z) MSG_HEADER_TOO_SMALL.
Definition msg_bad_mode : list byte := map (fun z => Z_to_bv 8 z) MSG_INVALID_MODE_HEADER.
Lemma msg_too_small_at : forall m, mem_inv asegs m -> bytes_at asegs m P2H_MSG_TOO_SMALL (msg_too_small ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image asegs m P2H_MSG_TOO_SMALL (msg_too_small ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold P2H_MSG_TOO_SMALL; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma msg_bad_mode_at : forall m, mem_inv asegs m -> bytes_at asegs m P2H_MSG_BAD_MODE (msg_bad_mode ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image asegs m P2H_MSG_BAD_MODE (msg_bad_mode ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold P2H_MSG_BAD_MODE; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma msg_too_small_unsigned : map bv_unsigned msg_too_small = MSG_HEADER_TOO_SMALL. Proof. vm_compute. reflexivity. Qed.
Lemma msg_bad_mode_unsigned : map bv_unsigned msg_bad_mode = MSG_INVALID_MODE_HEADER. Proof. vm_compute. reflexivity. Qed.
