(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X0ae.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac ogg_sigma_free EF ES :=
repeat match goal with H : rt_sp0 _ _ - _ <= _ |- _ => rewrite <- ES in H end;
repeat match goal with H : In _ (rt_frames _ _) |- _ => rewrite <- EF in H end.

Lemma ogg_ms_piece : forall (m m' : mem) d n c, wr_at bsegs m d (Z.of_nat n) -> wmono bsegs m m' -> bytes_at bsegs m' d (repeat c n) ->
rw_cells bsegs m' d [CB n (repeat c n)].
Proof.
intros m m' d n c WR WM BY. split; [split; [split; [apply repeat_length| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport bsegs m m' d _ WR WM).
Qed.

Lemma ogg_bytes_piece : forall (m m' : mem) d (bs : list byte), wr_at bsegs m d (Z.of_nat (length bs)) -> wmono bsegs m m' -> bytes_at bsegs m' d bs ->
rw_cells bsegs m' d [CB (length bs) bs].
Proof.
intros m m' d bs WR WM BY. split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport bsegs m m' d _ WR WM).
Qed.

Lemma u8arr_app : forall (m : mem) A (b1 b2 : list byte),
u8arr bsegs m A (b1 ++ b2) <-> u8arr bsegs m A b1 /\ u8arr bsegs m (A + Z.of_nat (length b1)) b2.
Proof.
intros m A b1 b2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, (wr_at_app bsegs m A) by lia. tauto.
Qed.

Lemma ogg_acc_agree : forall (m m' : mem) o n, acc bsegs m o n ->
agree_on (fun x => exists i, 0 <= i < n /\ x = shad (o + i)) m m' -> acc bsegs m' o n.
Proof.
intros m m' o n H HA i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
apply (bytes_at_agree bsegs m m' _ _ Hb). eapply agree_sub; [exact HA|]. intros x Hx. cbn [length] in Hx. exists i. split; [exact Hi| lia].
Qed.
Lemma ogg_frame_shadow_in : forall f fsz o n i, f mod 8 = 0 -> fsz mod 8 = 0 -> 0 <= f -> f <= o -> o + n <= f + fsz -> 0 <= i < n ->
shad f <= shad (o + i) < shad (f + fsz).
Proof.
intros f fsz o n i F8 S8 F0 Ho Hn Hi. unfold shad. split.
- apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : f + fsz = 8 * ((f + fsz) / 8)) by (pose proof (Z.div_mod (f + fsz) 8 ltac:(lia)) as X; rewrite Zplus_mod, F8, S8 in X; cbn in X; lia).
lia.
Qed.
Lemma acc_frame_pres_fp : forall live frames sp W (m m' : mem) f k o n, rt_pres_fp live frames sp W m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + n <= f + fs_size k ->
(forall x, shad f <= x < shad (f + fs_size k) -> outside W x) ->
acc bsegs m o n -> acc bsegs m' o n.
Proof.
intros live frames sp W m m' f k o n PRES Hin F8 S8 F0 Ho Hn HW H. apply (ogg_acc_agree m m' o n H).
apply (agree_of_pres_fp live frames sp W m m' _ PRES). intros x (i & Hi & ->).
pose proof (ogg_frame_shadow_in f (fs_size k) o n i F8 S8 F0 Ho Hn Hi) as R. split; [| exact (HW _ R)].
right; right; right; right. exists f, k. split; [exact Hin| exact R].
Qed.
Lemma fs_size_mod8 : forall k, fs_size k mod 8 = 0.
Proof. intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. Qed.

Section OggDefs.
Variable RT : rt_sig.

Definition sync_live (Σ : rts RT) (sy : sync_st bptr) (D : Z) : Prop :=
sy_data sy <> None -> In (D, sy_storage sy) (rt_live RT Σ).

Definition stream_live (Σ : rts RT) (os : stream_st bptr) (Bd L G : Z) : Prop :=
In (Bd, os_body_storage os) (rt_live RT Σ) /\ In (L, 4 * os_lacing_storage os) (rt_live RT Σ) /\ In (G, 8 * os_lacing_storage os) (rt_live RT Σ)
/\ Bd <> L /\ Bd <> G /\ L <> G.

Lemma frame_checked_dst : forall (Σ : rts RT) (m : mem) sp f k o n,
In (f, k) (rt_frames RT Σ) -> f <= o -> o + n <= f + fs_size k - 8 -> acc bsegs m o n -> wr_at bsegs m o n ->
checked_dst RT Σ m sp o n.
Proof.
intros Σ m sp f k o n INF F1 F2 AC WR. split; [intros _; split; [exact AC|]|split; [| exact WR]].
- right; left. exists f, k. split; [exact INF| lia].
- intros i Hi. right; right; right; left. exists f, k. split; [exact INF| lia].
Qed.

Lemma live_checked_src : forall (AF : art_facts RT) (Σ : rts RT) (m : mem) sp lo p k s n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= s -> s + n <= p + k -> p + k <= lo -> checked_src RT Σ m sp lo s n.
Proof.
intros AF Σ m sp lo p k s n ART0 INL H1 H2 H3. split; [intros _; split| left; lia].
- apply (acc_sub bsegs m p k s n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
Qed.
Lemma live_checked_dst : forall (AF : art_facts RT) (Σ : rts RT) (m : mem) sp p k d n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> wr_at bsegs m d n -> checked_dst RT Σ m sp d n.
Proof.
intros AF Σ m sp p k d n ART0 INL H1 H2 WR. split; [intros _; split| split; [| exact WR]].
- apply (acc_sub bsegs m p k d n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
- intros i Hi. right; right; left. exists p, k. split; [exact INL| lia].
Qed.
End OggDefs.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac ogg_sigma_free EF ES :=
repeat match goal with H : rt_sp0 _ _ - _ <= _ |- _ => rewrite <- ES in H end;
repeat match goal with H : In _ (rt_frames _ _) |- _ => rewrite <- EF in H end.

Lemma ogg_ms_piece : forall (m m' : mem) d n c, wr_at asegs m d (Z.of_nat n) -> wmono asegs m m' -> bytes_at asegs m' d (repeat c n) ->
rw_cells asegs m' d [CB n (repeat c n)].
Proof.
intros m m' d n c WR WM BY. split; [split; [split; [apply repeat_length| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport asegs m m' d _ WR WM).
Qed.

Lemma ogg_bytes_piece : forall (m m' : mem) d (bs : list byte), wr_at asegs m d (Z.of_nat (length bs)) -> wmono asegs m m' -> bytes_at asegs m' d bs ->
rw_cells asegs m' d [CB (length bs) bs].
Proof.
intros m m' d bs WR WM BY. split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport asegs m m' d _ WR WM).
Qed.

Lemma u8arr_app : forall (m : mem) A (b1 b2 : list byte),
u8arr asegs m A (b1 ++ b2) <-> u8arr asegs m A b1 /\ u8arr asegs m (A + Z.of_nat (length b1)) b2.
Proof.
intros m A b1 b2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, (wr_at_app asegs m A) by lia. tauto.
Qed.

Lemma ogg_acc_agree : forall (m m' : mem) o n, acc asegs m o n ->
agree_on (fun x => exists i, 0 <= i < n /\ x = shad (o + i)) m m' -> acc asegs m' o n.
Proof.
intros m m' o n H HA i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact HA|]. intros x Hx. cbn [length] in Hx. exists i. split; [exact Hi| lia].
Qed.
Lemma ogg_frame_shadow_in : forall f fsz o n i, f mod 8 = 0 -> fsz mod 8 = 0 -> 0 <= f -> f <= o -> o + n <= f + fsz -> 0 <= i < n ->
shad f <= shad (o + i) < shad (f + fsz).
Proof.
intros f fsz o n i F8 S8 F0 Ho Hn Hi. unfold shad. split.
- apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : f + fsz = 8 * ((f + fsz) / 8)) by (pose proof (Z.div_mod (f + fsz) 8 ltac:(lia)) as X; rewrite Zplus_mod, F8, S8 in X; cbn in X; lia).
lia.
Qed.
Lemma acc_frame_pres_fp : forall live frames sp W (m m' : mem) f k o n, rt_pres_fp live frames sp W m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + n <= f + fs_size k ->
(forall x, shad f <= x < shad (f + fs_size k) -> outside W x) ->
acc asegs m o n -> acc asegs m' o n.
Proof.
intros live frames sp W m m' f k o n PRES Hin F8 S8 F0 Ho Hn HW H. apply (ogg_acc_agree m m' o n H).
apply (agree_of_pres_fp live frames sp W m m' _ PRES). intros x (i & Hi & ->).
pose proof (ogg_frame_shadow_in f (fs_size k) o n i F8 S8 F0 Ho Hn Hi) as R. split; [| exact (HW _ R)].
right; right; right; right. exists f, k. split; [exact Hin| exact R].
Qed.
Lemma fs_size_mod8 : forall k, fs_size k mod 8 = 0.
Proof. intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. Qed.

Section OggDefs.
Variable RT : rt_sig.

Definition sync_live (Σ : rts RT) (sy : sync_st bptr) (D : Z) : Prop :=
sy_data sy <> None -> In (D, sy_storage sy) (rt_live RT Σ).

Definition stream_live (Σ : rts RT) (os : stream_st bptr) (Bd L G : Z) : Prop :=
In (Bd, os_body_storage os) (rt_live RT Σ) /\ In (L, 4 * os_lacing_storage os) (rt_live RT Σ) /\ In (G, 8 * os_lacing_storage os) (rt_live RT Σ)
/\ Bd <> L /\ Bd <> G /\ L <> G.

Lemma frame_checked_dst : forall (Σ : rts RT) (m : mem) sp f k o n,
In (f, k) (rt_frames RT Σ) -> f <= o -> o + n <= f + fs_size k - 8 -> acc asegs m o n -> wr_at asegs m o n ->
checked_dst RT Σ m sp o n.
Proof.
intros Σ m sp f k o n INF F1 F2 AC WR. split; [intros _; split; [exact AC|]|split; [| exact WR]].
- right; left. exists f, k. split; [exact INF| lia].
- intros i Hi. right; right; right; left. exists f, k. split; [exact INF| lia].
Qed.

Lemma live_checked_src : forall (AF : art_facts RT) (Σ : rts RT) (m : mem) sp lo p k s n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= s -> s + n <= p + k -> p + k <= lo -> checked_src RT Σ m sp lo s n.
Proof.
intros AF Σ m sp lo p k s n ART0 INL H1 H2 H3. split; [intros _; split| left; lia].
- apply (acc_sub asegs m p k s n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
Qed.
Lemma live_checked_dst : forall (AF : art_facts RT) (Σ : rts RT) (m : mem) sp p k d n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> wr_at asegs m d n -> checked_dst RT Σ m sp d n.
Proof.
intros AF Σ m sp p k d n ART0 INL H1 H2 WR. split; [intros _; split| split; [| exact WR]].
- apply (acc_sub asegs m p k d n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
- intros i Hi. right; right; left. exists p, k. split; [exact INL| lia].
Qed.
End OggDefs.
