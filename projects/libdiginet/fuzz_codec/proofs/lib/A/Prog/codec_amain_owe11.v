(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its addresses and numbers changed; 434 of its 520 lines of code are new or changed and 180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe5.v, with its numbers changed; 510 of its 552 lines of code are new or changed and 478 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe10.v; 830 of its 869 lines of code are new or changed and 513 lines of the source are left out. *)
(* OWE11 (SYSEX) of the image-A walk of LLVMFuzzerTestOneInput: seg_owe 11 of lib/A/Prog/codec_amain_inv.v, from the
   cut OWE11 (0x827c8) to CHK (0x8273c); owe()'s default case (fuzz_codec.c:234-250) with owe_sysex inlined.
     0x827c8 a = k.a; a >= 128 -> 0x827d4 (want_rc = -1)
     0x82838 s8 = k.b; b = 0x70 -> 0x82844 (-10); 0x8292c b > 127 -> 0x82730 (-11)
     0x82934 s7 = k.n; n >= 20 -> 0x82944 (-5)
     0x82a40 the seven-bit test of k.bytes[0 .. n) (lib/A/Prog/codec_amain_owe11_lib.v o11_loop0): a byte with bit 7
             set -> 0x82730 (-11)
     0x82a88 want[0 .. 2) = 0x13f0 (from 80(sp1)), want[2] = a, want[3] = b; __asan_memcpy(want + 4, k.bytes, n)
             (0x82aa4, CPgWalkIntr.cw_intrin_call); want[4 + n] = 0xf7 (address 40(sp1) + n + 4, named by the atom
             that holds F + 324 + n); s11 = 10; want_len = n + 5; want_display = ((b - 48) & ~16) == 0; to CHK.
   The loop. A case split on n (0 .. 19) would run the success tail (two runs, the memcpy call and the end) once per
   value and close one error leaf per byte (210 leaves); the loop lemma runs one small executor state per pass shape
   once, and this file re-seats its own state after the loop with st_ok_after_stretch (O11_CLOB), so the tail and
   the loop's error leaf are proved once each.
   The state: am_entry's base, k's fields read (region 6: a, b, the 24 bytes, n as atoms 37, 38, 40 .. 63, 39) and
   want_rc (region 5, window [316, 320), chunk 0); atom 64 holds F + 324 + n. On the success path the header
   [320, 324), the byte F + 324 + n (on atom 64) and want_len .. want_display [344, 360) (key's chunk 0) are added
   at 0x82a88, after the loop's error leaf, so no error path loses a byte of want. The error paths end in
   lib/A/Prog/codec_amain_owel.v owe_chk_end, the success path in lib/A/Prog/codec_amain_owex.v owex_chk. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkImg CPgWalkIntr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_owel codec_amain_owex codec_amain_owe11_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the state ================================ *)
Definition O11_PC : Z := 0x827c8.
Definition o11_bchunks : list YP09.chunk :=
  map (fun i : nat => YP09.mkChunk (216 + Z.of_nat i) (CVal 1 (SOff (40 + i) 0))) (seq 0 24).
Definition o11_rk : YP09.region :=
  am_frame_region 200 248 200 200
    ([YP09.mkChunk 200 (CVal 4 (SOff 37 0)); YP09.mkChunk 204 (CVal 4 (SOff 38 0))] ++ o11_bchunks ++
     [YP09.mkChunk 240 (CVal 8 (SOff 39 0))]).
Definition o11_rc : YP09.region := am_frame_region 316 320 316 320 [YP09.mkChunk 316 (CVal 4 (SLit 0))].
Definition o11_AF : list (nat * afact) :=
  [(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 24 0)] ++
  map (fun i : nat => ((40 + i)%nat, mkAF 0 255 0)) (seq 0 24) ++ [(64%nat, mkAF 4096 AM_HI 0)].
(* the values of atoms 37 .. 64 *)
Definition o11_ys (g : ectx) (pos : Z) (k : kcallZ) : list Z :=
  [kz_a k; kz_b k; kz_n k] ++ kz_bytes k ++ [FA g pos + 324 + kz_n k].
(* the success path's windows *)
Definition o11_hdr : YP09.region := am_frame_region 320 324 320 324 [].
Definition o11_tl : YP09.region := am_frame_region 344 360 344 360 [YP09.mkChunk 352 (CVal 4 (SLit 0))].
Definition o11_f7 : YP09.region := YP09.mkRegion (Some 64%nat) 0 1 0 1 [].
Definition o11_SH2 : list shent := [owe_SHk; mkSHE 64 0 1].
(* the spills with an empty window inside them (the runtime call keeps only such regions) *)
Definition o11_spill : YP09.region := YP09.mkRegion (Some 2%nat) 16 128 16 16 am_spill_chunks.
(* the bytes a path may write: the error paths (want_rc, the cursor's window), the success path *)
Definition o11_zerr (F sp1 a : Z) : Prop := (sp1 + 152 <= a < sp1 + 168) \/ (F + 316 <= a < F + 320).
(* the windows after the runtime call *)
Definition o11_zw (F sp1 n a : Z) : Prop :=
  (sp1 + 152 <= a < sp1 + 168) \/ (F + 316 <= a < F + 324) \/ (F + 324 + n <= a < F + 325 + n) \/ (F + 344 <= a < F + 360).
Definition o11_zok (F sp1 n a : Z) : Prop :=
  o11_zerr F sp1 a \/ (F + 320 <= a < F + 325 + n) \/ (F + 344 <= a < F + 360) \/ (sp1 - 4096 <= a < sp1).

(* ================================ small facts ================================ *)
Lemma o11_vm : forall m a (n : nat) u v, val_mem tfibsegs m a n u ->
  u mod 2 ^ (8 * Z.of_nat n) = v mod 2 ^ (8 * Z.of_nat n) -> val_mem tfibsegs m a n v.
Proof. intros m a n u v H E j Hj. rewrite (H j Hj). unfold YO0f.le_byte. rewrite E. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a kept-memory fact, under a name the run tactics do not take for their own *)
Definition o11_kept (H : word -> bool) (m m' : word -> option byte) (Zn : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m a = aview tfibsegs H m' a.

Lemma o11_aview1 : forall H (m : word -> option byte) a v, val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv.
cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

Lemma o11_ew_y : forall g pos c regs k j, ew (am_env g pos c regs (o11_ys g pos k)) (37 + j) =
  Z_to_bv 64 (nth j (o11_ys g pos k) 0).
Proof. intros. exact (am_ew_y g pos c regs (o11_ys g pos k) j). Qed.

Lemma o11_ys_byte : forall g pos k i, length (kz_bytes k) = 24%nat -> (i < 24)%nat ->
  nth (3 + i) (o11_ys g pos k) 0 = nth i (kz_bytes k) 0.
Proof.
intros g pos k i L Hi. unfold o11_ys. replace (3 + i)%nat with (S (S (S i))) by lia. cbn [app nth].
rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma o11_ys_f7 : forall g pos k, length (kz_bytes k) = 24%nat -> nth 27 (o11_ys g pos k) 0 = FA g pos + 324 + kz_n k.
Proof.
intros g pos k L. unfold o11_ys. cbn [app nth]. rewrite app_nth2 by lia. rewrite L. reflexivity.
Qed.

Lemma o11_atoms_map : forall E f (l : list nat), (forall i, In i l -> afact_ok E (40 + i) f) ->
  atoms_ok E (map (fun i => ((40 + i)%nat, f)) l).
Proof.
intros E f l H. induction l as [|i l IH]; cbn [map atoms_ok]; [exact I|].
split; [apply H; left; reflexivity | apply IH; intros j Hj; apply H; right; exact Hj].
Qed.

Lemma o11_kept_eq : forall E (m m' : word -> option byte) r, (forall x, m' x = m x) ->
  region_kept tfibsegs E m m' r.
Proof.
intros E m m' r M. split; intros a _.
- unfold mbyte. rewrite M. reflexivity.
- unfold writable_at, wview. rewrite M. tauto.
Qed.

(* the frame's 56 shadow bytes are on no byte a path writes *)
Lemma o11_shadow_out : forall F sp1 n i, F mod 64 = 0 -> in_app F 512 -> alloc_ceiling < sp1 - 4096 ->
  0 <= n <= 24 -> 0 <= i < 56 -> ~ o11_zok F sp1 n (shadow_addr F + i).
Proof.
intros F sp1 n i H64 Happ Hsp Hn Hi Hz.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (D8 : 0 <= F / 8 /\ 8 * (F / 8) <= F) by (split; [apply Z.div_pos | apply Z.mul_div_le]; unfold in_app in Happ; lia).
unfold o11_zok, o11_zerr, shadow_addr, SHADOW_OFF in Hz. appn. lia.
Qed.

(* k's 184 bytes are marked usable in a memory with the frame's shadow map shm 0 *)
Lemma o11_bsk : forall (W : world tfibsegs) m F, F mod 64 = 0 ->
  (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) m (shadow_addr F + i) = Some (nth (Z.to_nat i) (shm 0) 0)) ->
  block_shadow (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 176) 184.
Proof.
intros W m F H64 HSH.
apply am_block_shadow; [exact H64 | lia | reflexivity | lia |].
intros i Hi. change ((184 + 7) / 8) with 23 in Hi. change (184 / 8) with 23. change (176 / 8) with 22.
rewrite (proj2 (Z.ltb_lt i 23) ltac:(lia)).
rewrite (HSH (22 + i) ltac:(lia)). f_equal.
pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
apply (Hk23 0 (Z.to_nat (22 + i))). lia.
Qed.

(* the engine's shadow entries of k and of the byte F + 324 + n, from the frame's shadow map shm 0 *)
Lemma o11_shk : forall (W : world tfibsegs) m E F, F mod 64 = 0 -> in_app F 512 ->
  (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) m (shadow_addr F + i) = Some (nth (Z.to_nat i) (shm 0) 0)) ->
  ew E 33 = Z_to_bv 64 F -> ew E 32 = Z_to_bv 64 SB ->
  shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) m) owe_SHk.
Proof.
intros W m E F H64 Happ HSH E33 E32.
pose proof (o11_bsk W m F H64 HSH) as HBS.
pose proof (block_shadow_range (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 176) 184 (F + 176) 184 HBS
  ltac:(lia) ltac:(lia)) as Hra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ham : amem_range (F + 176) 184) by (appn; lia).
unfold owe_SHk. change 360 with (176 + 184).
apply (cw_shent_ra_off W m E 33 F 176 184 Hra Ham); [appn; lia | lia | lia | appn; lia | exact E33 | exact E32].
Qed.
Lemma o11_sh7 : forall (W : world tfibsegs) m E F n, F mod 64 = 0 -> in_app F 512 -> 0 <= n <= 24 ->
  (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) m (shadow_addr F + i) = Some (nth (Z.to_nat i) (shm 0) 0)) ->
  ew E 64 = Z_to_bv 64 (F + 324 + n) -> ew E 32 = Z_to_bv 64 SB ->
  shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) m) (mkSHE 64 0 1).
Proof.
intros W m E F n H64 Happ Hn HSH E64 E32.
pose proof (o11_bsk W m F H64 HSH) as HBS.
pose proof (block_shadow_range (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 176) 184 (F + 324 + n) 1 HBS
  ltac:(lia) ltac:(lia)) as Hra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ham : amem_range (F + 324 + n) 1) by (appn; lia).
apply (cw_shent_ra W m E 64 (F + 324 + n) 1 Hra Ham); [appn; lia | lia | appn; lia | exact E64 | exact E32].
Qed.

(* the header's two bytes 0xf0 0x13, stored as one half-word *)
Lemma o11_split2 : forall m a, val_mem tfibsegs m a 2 5104 -> val_mem tfibsegs m a 1 240 /\ val_mem tfibsegs m (a + 1) 1 19.
Proof.
intros m a V. split; intros j Hj; (destruct j as [|j]; [|lia]).
- rewrite (V 0%nat ltac:(lia)). reflexivity.
- replace (a + 1 + Z.of_nat 0) with (a + Z.of_nat 1) by lia. rewrite (V 1%nat ltac:(lia)). reflexivity.
Qed.

(* want[0 .. n + 5) from its pieces *)
Lemma o11_garr_bs : forall m F a b n bytes, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= n <= 24 ->
  length bytes = 24%nat -> Forall (fun x => 0 <= x < 256) bytes ->
  val_mem tfibsegs m (F + 320) 1 240 -> val_mem tfibsegs m (F + 321) 1 19 ->
  val_mem tfibsegs m (F + 322) 1 a -> val_mem tfibsegs m (F + 323) 1 b ->
  (forall i, 0 <= i < n -> val_mem tfibsegs m (F + 324 + i) 1 (nth (Z.to_nat i) bytes 0)) ->
  val_mem tfibsegs m (F + 324 + n) 1 247 ->
  garr8 tfibsegs m (F + 320) (o11_bs a b bytes n).
Proof.
intros m F a b n bytes Ha Hb Hn L Hr V0 V1 V2 V3 VB V7 j Hj.
unfold o11_bs in *. rewrite !length_app, length_firstn in Hj. cbn [length] in Hj.
rewrite Forall_forall in Hr.
destruct (Nat.lt_ge_cases j 4) as [Hj4 | Hj4].
- rewrite app_nth1 by (cbn; lia).
  destruct j as [|[|[|[|j]]]]; cbn [nth].
  + rewrite Z.add_0_r. split; [exact V0 | lia].
  + change (Z.of_nat 1) with 1. replace (F + 320 + 1) with (F + 321) by lia. split; [exact V1 | lia].
  + change (Z.of_nat 2) with 2. replace (F + 320 + 2) with (F + 322) by lia. split; [exact V2 | lia].
  + change (Z.of_nat 3) with 3. replace (F + 320 + 3) with (F + 323) by lia. split; [exact V3 | lia].
  + lia.
- rewrite app_nth2 by (cbn; lia). cbn [length].
  destruct (Nat.lt_ge_cases (j - 4) (Z.to_nat n)) as [Hjn | Hjn].
  + rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
    destruct (Nat.ltb_spec (j - 4) (Z.to_nat n)) as [_|]; [|lia].
    split.
    * replace (F + 320 + Z.of_nat j) with (F + 324 + Z.of_nat (j - 4)) by lia.
      specialize (VB (Z.of_nat (j - 4)) ltac:(lia)). rewrite Nat2Z.id in VB. exact VB.
    * apply Hr. apply nth_In. lia.
  + rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (j - 4 - Nat.min (Z.to_nat n) (length bytes))%nat with 0%nat by lia.
    cbn [nth]. split; [|lia].
    replace (F + 320 + Z.of_nat j) with (F + 324 + n) by lia. exact V7.
Qed.

Lemma o11_bs_len : forall a b bytes n, length bytes = 24%nat -> 0 <= n <= 24 ->
  Z.of_nat (length (o11_bs a b bytes n)) = n + 5.
Proof. intros a b bytes n L Hn. unfold o11_bs. rewrite !length_app, length_firstn. cbn [length]. lia. Qed.

Lemma o11_bs_u8 : forall a b bytes n, 0 <= a < 256 -> 0 <= b < 256 -> Forall (fun x => 0 <= x < 256) bytes ->
  map u8 (o11_bs a b bytes n) = o11_bs a b bytes n.
Proof.
intros a b bytes n Ha Hb Hr. rewrite <- (map_id (o11_bs a b bytes n)) at 2. apply map_ext_in.
intros x Hx. unfold u8. apply Z.mod_small. unfold o11_bs in Hx.
apply in_app_or in Hx as [Hx | Hx]; [cbn in Hx; lia|].
apply in_app_or in Hx as [Hx | Hx]; [|cbn in Hx; lia].
rewrite Forall_forall in Hr. apply Hr. rewrite <- (firstn_skipn (Z.to_nat n) bytes). apply in_or_app. left. exact Hx.
Qed.

(* want_display: ((b - 48) & ~16) == 0, as the executor leaves it *)
Definition o11_dpe : sv := SAlu ALU_SLTU (SAlu ALU_AND (SOff 38 (-48)) (SLit (-17))) (SLit 1).
Lemma o11_dp_den : forall E b, ew E 38 = Z_to_bv 64 b -> 0 <= b < 256 -> U E o11_dpe = o11_dp b.
Proof.
intros E b Hb Hr.
assert (C : forallb (fun y => U (ewset E 38 (Z_to_bv 64 y)) o11_dpe =? o11_dp y) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in C.
specialize (C b ltac:(apply in_map_iff; exists (Z.to_nat b); split; [lia | apply in_seq; lia])).
apply Z.eqb_eq in C. rewrite <- C. unfold U. f_equal.
symmetry. apply (YP06.sv_denot_agree 39 E (ewset E 38 (Z_to_bv 64 b)) o11_dpe); [|reflexivity].
split; [|reflexivity]. intros n Hn. destruct (Nat.eq_dec n 38) as [->|Hne].
- rewrite ew_ewset_same. symmetry. exact Hb.
- apply ew_ewset_other. exact Hne.
Qed.

(* the bytes the end reads back from the start lie on no window *)
Lemma o11_zw_zok : forall F sp1 n a, 0 <= n -> o11_zw F sp1 n a -> o11_zok F sp1 n a.
Proof. unfold o11_zw, o11_zok, o11_zerr. intros. lia. Qed.
Lemma o11_out : forall F sp0 sp1 n a, 4096 <= F -> F + 512 <= sp1 - 4096 -> sp1 + 168 <= sp0 - 104 -> sp0 <= 2 ^ 47 ->
  0 <= n <= 24 ->
  (sp1 + 16 <= a < sp1 + 128) \/ (sp0 - 104 <= a < sp0) \/ (F + 504 <= a < F + 512) \/
  (F + 176 <= a < F + 316) \/ (F + 325 + n <= a < F + 344) ->
  0 <= a < 2 ^ 64 /\ ~ o11_zok F sp1 n a /\ ~ o11_zw F sp1 n a.
Proof. unfold o11_zw, o11_zok, o11_zerr. intros F sp0 sp1 n a H1 H2 H3 H4 H5 Ha. lia. Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51998.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ================================ the start ================================ *)
Lemma o11_start : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
  frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
  cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> kz_want_rc k = 0 ->
  0 <= kz_a k < 256 -> 0 <= kz_b k < 256 -> 0 <= kz_n k <= 24 -> Forall (fun x => 0 <= x < 256) (kz_bytes k) ->
  st_ok tfibsegs (am_env g pos c regs2 (o11_ys g pos k)) (am_ss O11_PC [o11_rc; o11_rk] o11_AF)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 O11_PC) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k HJ Hfr HC Hcur Hkat Hwrc Ha Hb Hn Hbs.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in Hchi.
pose proof Hkat as (HK & Hwf).
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbefore & Gout & Vwrc & _).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lbytes & _).
set (E := am_env g pos c regs2 (o11_ys g pos k)).
assert (UF : bv_unsigned (ew E 33) = FA g pos) by (unfold E; rewrite am_ew_F; apply unsigned_lit_small; lia).
assert (DY : forall j v, nth j (o11_ys g pos k) 0 = v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff (37 + j) 0) = Z_to_bv 64 v).
{ intros j v Hj Hv. cbn [sv_denot]. unfold E. rewrite o11_ew_y, Hj, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
apply (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c O11_PC (o11_ys g pos k)
  [o11_rc; o11_rk] o11_AF HJ Hfr HC Hcur eq_refl).
- constructor; [|constructor; [|constructor]].
  + apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c _ 316 320 316 320 _
      HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ (FA g pos) 316 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. rewrite Hwrc in Vwrc. replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia.
    exact Vwrc.
  + apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c _ 200 248 200 200 _
      HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    apply Forall_app. split; [|apply Forall_app; split].
    * constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val tfibsegs _ _ (FA g pos) 200 4 (SOff 37 0) (kz_a k)); [ | cbn; lia | cbn; lia |].
         ++ apply (DY 0%nat); [reflexivity | lia].
         ++ change (N.to_nat 4) with 4%nat. replace (FA g pos + 200) with (FA g pos + 176 + 24) by lia. exact Va.
      -- apply (chunk_ok_val tfibsegs _ _ (FA g pos) 204 4 (SOff 38 0) (kz_b k)); [ | cbn; lia | cbn; lia |].
         ++ apply (DY 1%nat); [reflexivity | lia].
         ++ change (N.to_nat 4) with 4%nat. replace (FA g pos + 204) with (FA g pos + 176 + 28) by lia. exact Vb.
    * apply Forall_forall. intros ch Hch. unfold o11_bchunks in Hch. apply in_map_iff in Hch as (i & <- & Hi).
      apply in_seq in Hi.
      rewrite Forall_forall in Hbs.
      assert (Hr : 0 <= nth i (kz_bytes k) 0 < 256) by (apply Hbs; apply nth_In; lia).
      apply (chunk_ok_val tfibsegs _ _ (FA g pos) (216 + Z.of_nat i) 1 (SOff (40 + i) 0) (nth i (kz_bytes k) 0));
        [ | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
      -- change (40 + i)%nat with (37 + (3 + i))%nat. apply (DY (3 + i)%nat); [apply o11_ys_byte; lia | lia].
      -- change (N.to_nat 1) with 1%nat.
         replace (FA g pos + (216 + Z.of_nat i)) with (FA g pos + 176 + 40 + Z.of_nat i) by lia.
         exact (proj1 (Gbytes i ltac:(lia))).
    * constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ (FA g pos) 240 8 (SOff 39 0) (kz_n k)); [ | cbn; lia | cbn; lia |].
      -- apply (DY 2%nat); [reflexivity | lia].
      -- change (N.to_nat 8) with 8%nat. replace (FA g pos + 240) with (FA g pos + 176 + 64) by lia. exact Vn.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, o11_rc, o11_rk, am_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite UF. repeat split; lia.
- constructor; [|constructor; [|constructor]].
  + apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c _ 316 320);
      [exact HJ | exact Hfr | exact HC | lia | lia].
  + apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c _ 200 248);
      [exact HJ | exact Hfr | exact HC | lia | lia].
- assert (X37 : ew E 37 = Z_to_bv 64 (kz_a k)) by exact (o11_ew_y g pos c regs2 k 0).
  assert (X38 : ew E 38 = Z_to_bv 64 (kz_b k)) by exact (o11_ew_y g pos c regs2 k 1).
  assert (X39 : ew E 39 = Z_to_bv 64 (kz_n k)) by exact (o11_ew_y g pos c regs2 k 2).
  assert (X64 : ew E 64 = Z_to_bv 64 (FA g pos + 324 + kz_n k)).
  { rewrite <- (o11_ys_f7 g pos k Lbytes). exact (o11_ew_y g pos c regs2 k 27). }
  unfold o11_AF. apply am_atoms_ok_app; [|apply am_atoms_ok_app].
  + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite X37, X38, X39, !unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + apply o11_atoms_map. intros i Hi. apply in_seq in Hi.
    rewrite Forall_forall in Hbs.
    assert (Hr : 0 <= nth i (kz_bytes k) 0 < 256) by (apply Hbs; apply nth_In; lia).
    assert (Xi : ew E (40 + i) = Z_to_bv 64 (nth i (kz_bytes k) 0)).
    { rewrite <- (o11_ys_byte g pos k i Lbytes ltac:(lia)). exact (o11_ew_y g pos c regs2 k (3 + i)). }
    unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite Xi, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
  + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite X64, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. unfold AM_HI. repeat split; lia.
Qed.

(* ================================ an error path at CHK ================================ *)
Lemma o11_err_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k od E ss ms md3 v,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
  frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
  mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
  ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k od ->
  kz_rc k = fst (enc_kZ k od) -> kz_want_len k = 0 -> kz_want_key k = 0 -> kz_want_display k = 0 ->
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms) md3 kj ->
  env_agree 37 (am_env g pos c regs2 ys) E ->
  st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = PC_CHK -> ss_resv ss = None ->
  am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
  nth_error (ss_mem ss) 4 = Some am_cur_region ->
  nth_error (ss_mem ss) 5 = Some (am_frame_region 316 320 316 320 [YP09.mkChunk 316 (CVal 4 (SLit v))]) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
     aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
  fst (owe_kZ k od) <> 0 -> - 2 ^ 31 <= fst (owe_kZ k od) < 2 ^ 31 -> 0 <= v < 2 ^ 64 ->
  v mod 2 ^ 32 = fst (owe_kZ k od) mod 2 ^ 32 ->
  SRr tfibsegs W2 (mkCfg ms md3) (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k od E ss ms md3 v HJ Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc
  Hwl Hwk Hwd HJ3 HAE HS Hpc Hrv Hkeep H26 H4 H5 KE Hr0 Hrr Hv Hvr.
pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS Hrv) as Ems. rewrite Hpc in Ems.
rewrite Ems in HS. rewrite Ems.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in Hchi.
pose proof Hkat as (HK & Hwf).
destruct HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vwl & Vwk & Vwd).
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ destruct HAE as [HA _]. rewrite (HA 33%nat ltac:(lia)), am_ew_F. apply unsigned_lit_small. lia. }
pose proof (st_ok_region_nth E ss _ 5 _ HS H5) as Hr5. rewrite restrict_mkst_fx in Hr5. cbn [ms_mem] in Hr5.
unfold am_frame_region in Hr5.
pose proof (field_of_region_any E _ 33 (FA g pos) _ 316 320 316 320 316 4 (SLit v) Hr5 UF ltac:(left; reflexivity)
  ltac:(lia)) as V316.
change (N.to_nat 4) with 4%nat in V316.
assert (VK : forall a w x, 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  (forall y, a <= y < a + Z.of_nat w -> ~ o11_zerr (FA g pos) sp1 y) ->
  val_mem tfibsegs (rd W2 mem2) a w x -> val_mem tfibsegs (rd W2 (ms_mem ms)) a w x).
{ intros a w x Ha Haw Hz Vx. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact Vx].
  intros y Hy. apply KE; [lia | apply Hz; lia]. }
assert (FFS : LLVMF_STK = 32768) by reflexivity.
apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k od 0 (ms_mem ms) (ms_regs ms) md3
  E ss (fst (owe_kZ k od)) [] 0 0 0 HJ Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HAE HS Hkeep H26 H4 eq_refl
  ltac:(cbn; lia)).
- intros a Ha Hz. apply KE; [exact Ha | intros Hm; apply Hz; unfold owe_zone, o11_zerr in *; lia].
- apply (o11_vm _ _ 4 _ _ V316). cbn [sv_denot]. rewrite unsigned_lit_small by lia.
  change (8 * Z.of_N 4) with 32. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. exact Hvr.
- apply garr8_nil.
- rewrite Hwl in Vwl. replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia.
  apply VK; [lia | cbn; lia | intros y Hy; unfold o11_zerr; cbn in Hy; lia | exact Vwl].
- rewrite Hwk in Vwk. replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia.
  apply VK; [lia | cbn; lia | intros y Hy; unfold o11_zerr; cbn in Hy; lia | exact Vwk].
- rewrite Hwd in Vwd. replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia.
  apply VK; [lia | cbn; lia | intros y Hy; unfold o11_zerr; cbn in Hy; lia | exact Vwd].
- exact Hrr.
- lia.
- lia.
- lia.
- cbn [app length skipn]. apply owe_want_ok_fail; [reflexivity | exact Hr0].
Qed.

(* ================================ the walk's tactics ================================ *)
(* an atom below 65 of the env after runs and re-seats, as in the start env *)
Ltac o11_lift Ev n H0 H := assert (H : ew Ev n = _) by (rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact H0).
Ltac o11_liftb Hb n H0 H := lazymatch type of Hb with branch_taken _ (sv_denot ?Ev _) _ = _ => o11_lift Ev n H0 H end.
Ltac o11_liftS n H0 H := lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => o11_lift Ev n H0 H end.
(* the write windows: the cursor (atom 2), ranges of the frame (atom 33), the byte F + 324 + n (atom 64) *)
Ltac o11_inframe EFA :=
  right; right; right; eexists 3, _; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite EFA;
  change (fs_frame_bytes 3) with 512; lia.
Ltac o11_awr sp1v sp0v Fv f7v U2 UF U64 EFA :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1v - sp0v));
    [reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite U2; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat Fv);
    [ reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact UF
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; o11_inframe EFA
    | ]
  | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 64%nat f7v);
    [ reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact U64
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; o11_inframe EFA
    | ] ].
(* the windows lie in the kept fact's zone *)
Ltac o11_kwr U2 UF U64 :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
     rewrite ?U2, ?UF, ?U64 in Hb; unfold o11_zok, o11_zerr, o11_zw; lia | ]);
  destruct Hr.

Ltac o11_rreg HS r Q :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.
Ltac o11_mkst :=
  lazymatch goal with HS : st_ok _ _ ?ssv (restrict _ ?msv) |- _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
    let p := eval vm_compute in (ss_pc ssv) in change (ss_pc ssv) with p end.
(* an error path at CHK: o11_err_end with the code's literal v and the code's equation Hf *)
Ltac o11_close v Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE :=
  lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
    eapply (o11_err_end _ _ _ _ _ _ _ _ _ _ _ _ (o11_ys _ _ _) _ _ Ev ssv msv _ v) end;
    [exact HJ0 | exact Hfr | exact Hkj | exact Hmo | exact HC | exact Hops | exact Hcur | exact Hkat | exact Hrec
    | exact Hrc | exact Hwl | exact Hwk | exact Hwd | exact HJ | env_agree_chain HAE | exact HS | reflexivity
    | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | exact KE | | | | ];
    rewrite ?Hf; unfold E_ARG, E_REFUSED, E_RANGE, E_SPACE; [lia | lia | lia | reflexivity].

(* add a region to the state: its region_ok is the next goal, its disjointness from the others by arithmetic *)
Ltac o11_addr r :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
    let Hr := fresh "Hr" in let Hd := fresh "Hd" in let HS2 := fresh "HS" in
    assert (Hr : region_ok tfibsegs Ev (ms_mem msv) r); [ cbn [ms_mem restrict mkst]; unfold r, am_frame_region | ];
    [ | assert (Hd : all_disjoint Ev r (ss_mem ssv));
        [ let l := eval vm_compute in (ss_mem ssv) in change (all_disjoint Ev r l);
          unfold r, am_frame_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?ew_havoc_old, ?ew_ewset_other by lia;
          lazymatch goal with U2 : bv_unsigned (ew _ 2) = _, UF : bv_unsigned (ew _ 33) = _,
            U64 : bv_unsigned (ew _ 64) = _ |- _ => rewrite ?U2, ?UF, ?U64 end;
          repeat split; lia
        | pose proof (ast_ok_add_region tfibsegs Ev ssv msv r HS eq_refl Hr Hd) as HS2;
          cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS Hr Hd; rename HS2 into HS ] ] end.

Ltac o11_region HS i Hr :=
  lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
    let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Hr : region_ok tfibsegs E (ms_mem ms) r) by (apply (st_ok_region_nth E ss ms i r HS); vm_compute; reflexivity)
  end.
Ltac o11_in := repeat (first [left; reflexivity | right]).

(* a field's value read back modulo its width *)
Ltac o11_mm :=
  repeat match goal with |- context [2 ^ (8 * Z.of_N ?w)] =>
    let v := eval vm_compute in (2 ^ (8 * Z.of_N w)) in change (2 ^ (8 * Z.of_N w)) with v end;
  repeat match goal with |- context [2 ^ (8 * Z.of_nat ?w)] =>
    let v := eval vm_compute in (2 ^ (8 * Z.of_nat w)) in change (2 ^ (8 * Z.of_nat w)) with v end;
  first [reflexivity | apply Z.mod_mod; lia].

Lemma o11_ntest : forall n, 0 <= n <= 24 -> (18446744073709551590 <? zcanon (n + -20)) = (n <? 20).
Proof.
intros n Hn.
assert (C : forallb (fun y => Bool.eqb (18446744073709551590 <? zcanon (y + -20)) (y <? 20)) (map Z.of_nat (seq 0 25))
  = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C n ltac:(apply in_map_iff; exists (Z.to_nat n); split; [lia | apply in_seq; lia])).
apply Bool.eqb_prop in C. exact C.
Qed.

(* a region of the entry's frame, based on an atom that holds an address in it *)
Lemma o11_region_frame : forall E (W : world tfibsegs) mem md ly Sx pos nb b lo hi wlo whi cs,
  AR tfibsegs B ly Sx W mem md -> In (3, pos) (frames Sx) -> bv_unsigned (ew E nb) = b ->
  frame_addr ly 3 pos <= b + lo -> b + hi <= frame_addr ly 3 pos + 512 -> lo <= wlo -> whi <= hi -> lo <= hi ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) b) cs ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some nb) lo hi wlo whi cs).
Proof.
intros E W mem md ly Sx pos nb b lo hi wlo whi cs HAR Hin Hb Hlo Hhi Hwl Hwh Hlh Hcs.
destruct (al_frames _ _ LAWS ly Sx W mem md 3 pos HAR Hin) as (_ & _ & Hpr & _).
destruct (frames_bounds tfibsegs B LAWS ly Sx W mem md 3 pos HAR Hin) as (Hf4096 & Hfc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change (fs_frame_bytes 3) with 512 in Hfc.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable tfibsegs).
exact (proj1 (Hpr (b + o) ltac:(change (fs_frame_bytes 3) with 512; lia))).
Qed.

(* ================================ the segment ================================ *)
Theorem seg_owe11_holds : seg_owe B MT K XM_LIB 11.
Proof.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hkj & Hmo & HC &
  (Hops & _ & c & k & od & Hcur & Hkat & Hrec & Hkk & Hod & Hrc & Hwrc & Hwl & Hwk & Hwd & R23)).
replace (owe_pc 11) with O11_PC by reflexivity.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in Hchi.
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
assert (AMk : amem_range (FA g pos + 176) 184) by (clear - Happ Hf4096 Hfceil Hchi C1 C2 C3 C4 C5; appn; lia).
pose proof Hkat as (HK & Hwf).
pose proof HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbefore & Gout & Vwrc & Gwant &
  Vwl & Vwk & Vwd).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lbytes & _ & _ & Lwant).
pose proof Hrec as (_ & _ & Hrdr & _ & _). unfold rdr_kZ, reader_ok in Hrdr. rewrite Hkk in Hrdr.
destruct Hrdr as (Ha32 & Hb32 & _ & _ & _ & Fbytes & Hn24 & _ & _ & H11).
destruct (H11 eq_refl) as (Ha8 & Hb8). clear H11.
pose proof HC as (_ & _ & R2 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof (o11_start g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k HJ Hfr HC Hcur Hkat Hwrc ltac:(lia) ltac:(lia)
  ltac:(lia) Fbytes) as HS.
pose proof (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c (o11_ys g pos k) HJ Hfr HC) as SHK0.
remember (am_env g pos c regs2 (o11_ys g pos k)) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 (o11_ys g pos k)) E) by (subst E; apply env_agree_refl).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; apply am_ew_F).
pose proof HC as (_ & _ & _ & _ & _ & R3 & R4 & _).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (subst E; rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2; reflexivity).
assert (E3 : ew E 3 = w64 (as_gp B)) by (subst E; rewrite (am_ew_reg g pos c regs2 _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (subst E; rewrite (am_ew_reg g pos c regs2 _ 4 4%bv eq_refl); exact R4).
assert (Hsp16 : sp1 mod 16 = 0).
{ rewrite (Z.div_mod sp1 32) by lia. rewrite Hsp32, Z.add_0_r.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (UF : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply am_ew_SB).
assert (E37 : ew E 37 = Z_to_bv 64 (kz_a k)) by (subst E; exact (o11_ew_y g pos c regs2 k 0)).
assert (E38 : ew E 38 = Z_to_bv 64 (kz_b k)) by (subst E; exact (o11_ew_y g pos c regs2 k 1)).
assert (E39 : ew E 39 = Z_to_bv 64 (kz_n k)) by (subst E; exact (o11_ew_y g pos c regs2 k 2)).
assert (E64 : ew E 64 = Z_to_bv 64 (FA g pos + 324 + kz_n k)).
{ subst E. rewrite <- (o11_ys_f7 g pos k Lbytes). exact (o11_ew_y g pos c regs2 k 27). }
assert (U64 : bv_unsigned (ew E 64) = FA g pos + 324 + kz_n k) by (rewrite E64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W2) mem2))
  by (subst E; apply Forall_cons; [exact SHK0 | apply Forall_nil]).
clear HEE SHK0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 O11_PC) with (Z_to_bv 64 O11_PC).
(* 0x827c8-0x827d0: a = k.a, bltu a,128 *)
cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
cw_branch Hb1.
all: o11_liftb Hb1 37%nat E37 F37; rewrite branch_ltu_U, (U_atom _ 37 (kz_a k) F37), U_lit in Hb1 by lia.
- (* a < 128: 0x82838 s8 = k.b, bne s8,0x70 *)
  apply Z.ltb_lt in Hb1.
  cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
  cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
  cw_branch Hb2.
  all: o11_liftb Hb2 38%nat E38 F38; rewrite branch_ne_U, (U_atom _ 38 (kz_b k) F38), U_lit in Hb2 by lia.
  + (* b <> 0x70: 0x8292c bltu 127,s8 *)
    apply negb_true_iff, Z.eqb_neq in Hb2.
    cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
    cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
    cw_branch Hb3.
    all: o11_liftb Hb3 38%nat E38 F38'; rewrite branch_ltu_U, U_lit, (U_atom _ 38 (kz_b k) F38') in Hb3 by lia.
    * (* b > 127: E_RANGE (0x82730) *)
      apply Z.ltb_lt in Hb3.
      cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
      cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
      assert (Hf : fst (owe_kZ k od) = E_RANGE) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_b; lia).
      o11_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
    * (* b <= 127: 0x82934 s7 = k.n, the n test *)
      apply Z.ltb_ge in Hb3.
      cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
      cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
      cw_branch Hb4.
      all: o11_liftb Hb4 39%nat E39 F39;
        rewrite branch_ltu_U, U_lit, U_SOff, F39, unsigned_lit_small, o11_ntest in Hb4 by lia.
      -- (* n < 20: the loop *)
         apply Z.ltb_lt in Hb4.
         cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) O11_CNT.
         cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
         (* the state at 0x82a4c (beqz s7): the loop, o11_loop0 *)
         rename HS into HS4. rename HJ into HJ4. rename KE into KE4. rename SHOK into SHOK4.
         lazymatch goal with HS4 : st_ok _ ?Ev _ (restrict _ ?msv) |- _ =>
           rename msv into ms4;
           o11_lift Ev 33%nat E33 G33; o11_lift Ev 39%nat E39 G39; o11_lift Ev 32%nat E32 G32 end.
         o11_rreg HS4 (10%bv : bv 5) Q10. o11_rreg HS4 (12%bv : bv 5) Q12. o11_rreg HS4 (13%bv : bv 5) Q13.
         o11_rreg HS4 (23%bv : bv 5) Q23. o11_rreg HS4 (20%bv : bv 5) Q20.
         rewrite (am_den_off _ 33 (FA g pos) 216 G33) in Q10, Q12 by lia.
         rewrite (am_den_off _ 39 (kz_n k) 0 G39), Z.add_0_r in Q13, Q23 by lia.
         rewrite (am_den_off _ 32 SB 0 G32), Z.add_0_r in Q20 by (unfold SB; lia).
         assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
           by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
         assert (SH4 : forall i, 0 <= i < 56 ->
           aview tfibsegs (w_H W2) (ms_mem ms4) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
         { intros i Hi. rewrite KE4; [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia |].
           intros Hz. apply (o11_shadow_out (FA g pos) sp1 (kz_n k) i Hf64 Happ ltac:(lia) ltac:(lia) Hi). left. exact Hz. }
         pose proof (block_shadow_range (aview tfibsegs (w_H W2) (ms_mem ms4)) SHADOW_OFF (FA g pos + 176) 184
           (FA g pos + 216) (kz_n k) (o11_bsk W2 (ms_mem ms4) (FA g pos) Hf64 SH4) ltac:(lia) ltac:(lia)) as RA4.
         assert (BY4 : forall j, 0 <= j < kz_n k ->
           aview tfibsegs (w_H W2) (ms_mem ms4) (FA g pos + 216 + j) = Some (nth (Z.to_nat j) (kz_bytes k) 0) /\
           0 <= nth (Z.to_nat j) (kz_bytes k) 0 < 256).
         { intros j Hj. destruct (Gbytes (Z.to_nat j) ltac:(lia)) as (Vj & Rj). rewrite Z2Nat.id in Vj by lia.
           split; [|exact Rj]. rewrite KE4 by (unfold o11_zerr; lia).
           apply o11_aview1; [|exact Rj]. replace (FA g pos + 216 + j) with (FA g pos + 176 + 40 + j) by lia. exact Vj. }
         assert (ERR : forall regs' mem' md' j,
           ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
             mem' md' kj ->
           (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr (ms_regs ms4) r) ->
           0 <= j < kz_n k -> (forall l, 0 <= l < j -> nth (Z.to_nat l) (kz_bytes k) 0 < 128) ->
           128 <= nth (Z.to_nat j) (kz_bytes k) 0 ->
           (forall x, mrestrict (w_H W2) mem' x = mrestrict (w_H W2) (ms_mem ms4) x) ->
           SRr tfibsegs W2 (mkCfg (mkst regs' (Z_to_bv 64 O11_ERR) mem' (seg_rom tfibsegs)) md')
             (inv_chk B MT K XM_LIB g pos sp1 ops)).
         { intros regs' mem' md' j HJ Hk' Hj Hpre Hbad M'.
           lazymatch type of HS4 with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
             pose proof (st_ok_after_stretch tfibsegs 100 Ev ssv (restrict (w_H W2) msv) regs' (mrestrict (w_H W2) mem')
               (ss_mem ssv) O11_ERR O11_CLOB HS4 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hk'
               ltac:(apply Forall_forall; intros r _; apply o11_kept_eq; exact M')) as HS end.
           rewrite <- restrict_mkst_fx in HS.
           assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
             aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a).
           { intros a Ha Hz. rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' a (M' _)). exact (KE4 a Ha Hz). }
           clear HS4 HJ4 KE4 SHOK4.
           o11_liftS 33%nat E33 L33r. o11_liftS 32%nat E32 L32r.
           lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
             assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] Ev (mrestrict (w_H W2) mem'));
             [ apply Forall_cons; [|apply Forall_nil];
               apply (o11_shk W2 mem' Ev (FA g pos) Hf64 Happ); [|exact L33r | exact L32r];
               intros i Hi; rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' _ (M' _)); exact (SH4 i Hi) | ] end.
           (* 0x82730-0x82738: want_rc = -11, s11 = 10 *)
           cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
           cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
           assert (Hf : fst (owe_kZ k od) = E_RANGE).
           { unfold owe_kZ. rewrite Hkk. apply o11_fail_s; [lia | lia | lia | lia |].
             rewrite Forall_forall in Fbytes.
             apply (o11_sb_false _ _ j); [lia | rewrite Lbytes; lia | exact Hbad |].
             apply Fbytes. apply nth_In. lia. }
           o11_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE. }
         assert (OK : forall regs' mem' md',
           ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
             mem' md' kj ->
           (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr (ms_regs ms4) r) ->
           (forall l, 0 <= l < kz_n k -> nth (Z.to_nat l) (kz_bytes k) 0 < 128) ->
           (forall x, mrestrict (w_H W2) mem' x = mrestrict (w_H W2) (ms_mem ms4) x) ->
           SRr tfibsegs W2 (mkCfg (mkst regs' (Z_to_bv 64 O11_OK) mem' (seg_rom tfibsegs)) md')
             (inv_chk B MT K XM_LIB g pos sp1 ops)).
         { intros regs' mem' md' HJ Hk' Hall M'.
           lazymatch type of HS4 with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
             pose proof (st_ok_after_stretch tfibsegs 100 Ev ssv (restrict (w_H W2) msv) regs' (mrestrict (w_H W2) mem')
               [stack_region 0; o11_spill; am_cur_region; o11_rc; o11_rk] O11_OK O11_CLOB HS4 eq_refl
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(let l := eval vm_compute in (ss_mem ssv) in change (submem
                 [stack_region 0; o11_spill; am_cur_region; o11_rc; o11_rk] l);
                 unfold stack_region, o11_spill, am_spill_region, am_spill_chunks, am_cur_region, o11_rc, o11_rk, am_frame_region, o11_bchunks;
                 cbn [map seq app Z.of_nat]; submem_to)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hk'
               ltac:(apply Forall_forall; intros r _; apply o11_kept_eq; exact M')) as HS end.
           rewrite <- restrict_mkst_fx in HS.
           assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
             aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a).
           { intros a Ha Hz. rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' a (M' _)). exact (KE4 a Ha Hz). }
           assert (SHm : forall i, 0 <= i < 56 ->
             aview tfibsegs (w_H W2) mem' (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
           { intros i Hi. rewrite (aview_eq_of tfibsegs _ (ms_mem ms4) mem' _ (M' _)). exact (SH4 i Hi). }
           clear HS4 HJ4 KE4 SHOK4.
           pose proof HJ as (HAR & _).
           assert (Fsp : FA g pos + 512 <= sp1 - 4096 /\ sp1 + 168 <= e_sp0 g - 104 /\ e_sp0 g <= 2 ^ 47)
             by (clear - Hfceil Hsp0c Hsp Hsp047 FFS; lia).
           assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
           o11_liftS 33%nat E33 L33r. o11_liftS 32%nat E32 L32r. o11_liftS 64%nat E64 L64r.
           assert (V352 : val_mem tfibsegs (rd W2 mem') (FA g pos + 352) 4 0).
           { rewrite Hwk in Vwk. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem'); [|replace (FA g pos + 352)
               with (FA g pos + 176 + 176) by lia; exact Vwk].
             intros y Hy. apply KE; [lia | unfold o11_zerr; cbn in Hy; lia]. }
           (* the success path's windows: want_len .. want_display, the header, the byte F + 324 + n *)
           o11_addr o11_tl.
           { apply (o11_region_frame _ W2 mem' md' ly2 S2 pos 33 (FA g pos) 344 360 344 360 _ HAR Hin);
               [rewrite L33r; apply unsigned_lit_small; lia | rewrite EFA; lia | rewrite EFA; lia | lia | lia | lia |].
             constructor; [|constructor].
             apply (chunk_ok_val tfibsegs _ _ (FA g pos) 352 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V352]. }
           o11_addr o11_hdr.
           { apply (o11_region_frame _ W2 mem' md' ly2 S2 pos 33 (FA g pos) 320 324 320 324 _ HAR Hin);
               [rewrite L33r; apply unsigned_lit_small; lia | rewrite EFA; lia | rewrite EFA; lia | lia | lia | lia |].
             constructor. }
           o11_addr o11_f7.
           { apply (o11_region_frame _ W2 mem' md' ly2 S2 pos 64 (FA g pos + 324 + kz_n k) 0 1 0 1 _ HAR Hin);
               [rewrite L64r; apply unsigned_lit_small; lia | rewrite EFA; lia | rewrite EFA; lia | lia | lia | lia |].
             constructor. }
           lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
             assert (SHOK : sh_ok tfibsegs CW_Bx o11_SH2 Ev (mrestrict (w_H W2) mem'))
               by (apply Forall_cons; [apply (o11_shk W2 mem' Ev (FA g pos) Hf64 Happ SHm L33r L32r)
                  | apply Forall_cons; [apply (o11_sh7 W2 mem' Ev (FA g pos) (kz_n k) Hf64 Happ ltac:(lia) SHm L64r L32r)
                  | apply Forall_nil]]) end.
           assert (KEo : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zok (FA g pos) sp1 (kz_n k) a ->
             aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a)
             by (intros a Ha Hz; apply KE; [exact Ha | intros Hz'; apply Hz; left; exact Hz']).
           clear KE. rename KEo into KE.
           (* 0x82a88-0x82aa4: the header, the memcpy's arguments, jal *)
           cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) 0x51998.
           cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
           (* 0x51998: __asan_memcpy(F + 324, F + 216, n), returning to 0x82aa8 *)
           lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ => rename msv into msc end.
           o11_rreg HS (10%bv : bv 5) A10. o11_rreg HS (11%bv : bv 5) A11. o11_rreg HS (12%bv : bv 5) A12.
           o11_rreg HS (2%bv : bv 5) A2. o11_rreg HS (3%bv : bv 5) A3. o11_rreg HS (4%bv : bv 5) A4.
           o11_liftS 33%nat E33 Y33. o11_liftS 39%nat E39 Y39. o11_liftS 2%nat E2 Y2.
           o11_liftS 3%nat E3 Y3. o11_liftS 4%nat E4 Y4.
           rewrite (am_den_off _ 33 (FA g pos) 324 Y33) in A10 by lia.
           rewrite (am_den_off _ 33 (FA g pos) 216 Y33) in A11 by lia.
           rewrite (am_den_off _ 39 (kz_n k) 0 Y39), Z.add_0_r in A12 by lia.
           rewrite (am_den_off _ 2 sp1 0 Y2), Z.add_0_r in A2 by lia.
           cbn [sv_denot] in A3, A4. rewrite Y3, Z.add_0_r, Z_to_bv_bv_unsigned in A3.
           rewrite Y4, Z.add_0_r, Z_to_bv_bv_unsigned in A4.
           assert (SPc : spZ (ms_regs msc) = sp1) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
           pose proof HJ as (HARc & _).
           assert (SHc : forall i, 0 <= i < 56 ->
             aview tfibsegs (w_H W2) (ms_mem msc) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
           { intros i Hi. rewrite KE; [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia |].
             exact (o11_shadow_out (FA g pos) sp1 (kz_n k) i Hf64 Happ ltac:(lia) ltac:(lia) Hi). }
           pose proof (o11_bsk W2 (ms_mem msc) (FA g pos) Hf64 SHc) as BSc.
           lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ msc) |- _ =>
             let rs := eval vm_compute in (ss_mem ssv) in
             eapply (cw_intrin_call B LAWS OCpy 0x51998 AMEMCPY W2 Ev ssv msc _ LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
               (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj (FA g pos + 324) (FA g pos + 216) (kz_n k) 0x82aa8 300%nat
               rs _ HS eq_refl eq_refl HJ A10 A11 A12) end.
           all: try rewrite SPc.
           - lia.
           - lia.
           - lia.
           - change ESTACK with 4096. lia.
           - lia.
           - exact Hsp16.
           - exact Hsp016.
           - exact A3.
           - exact A4.
           - vm_compute; reflexivity.
           - lia.
           - apply ret_ok_even; vm_compute; reflexivity.
           - intros a Ha; split; [o11_inframe EFA | change ESTACK with 4096; lia].
           - unfold amem_range in *. lia.
           - exact (block_shadow_range _ _ (FA g pos + 176) 184 (FA g pos + 324) (kz_n k) BSc ltac:(lia) ltac:(lia)).
           - intros Hn0; apply (shadow_hull_vis_of_frame tfibsegs B LAWS ly2 S2 W2 (ms_mem msc) _ 3 pos _ _ HARc Hin);
               try rewrite EFA; try change (fs_frame_bytes 3) with 512; lia.
           - split; [lia|]. split; [lia|]. split.
             { intros a Ha. split; [|rewrite SPc; change ESTACK with 4096; lia].
               rewrite KE; [|lia | unfold o11_zok, o11_zerr; lia].
               destruct (Gbytes (Z.to_nat (a - (FA g pos + 216))) ltac:(lia)) as (Vj & Rj).
               rewrite Z2Nat.id in Vj by (lia).
               replace (FA g pos + 176 + 40 + (a - (FA g pos + 216))) with a in Vj by (lia).
               rewrite (o11_aview1 _ _ _ _ Vj Rj). discriminate. }
             split; [right; lia|]. split; [unfold amem_range in *; lia|]. split.
             + exact (block_shadow_range _ _ (FA g pos + 176) 184 (FA g pos + 216) (kz_n k) BSc ltac:(lia) ltac:(lia)).
             + intros Hn0; apply (shadow_hull_vis_of_frame tfibsegs B LAWS ly2 S2 W2 (ms_mem msc) _ 3 pos _ _ HARc Hin);
                 try rewrite EFA; try change (fs_frame_bytes 3) with 512; lia.
           - vm_compute; reflexivity.
           - vm_compute; reflexivity.
           - vm_compute; reflexivity.
           - vm_compute; reflexivity.
           - apply submem_refl.
           - repeat apply Forall_cons; try apply Forall_nil;
               cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
               rewrite ?ew_havoc_old, ?ew_ewset_other by lia; rewrite ?U2, ?UF, ?U64;
               (split; [intros a Ha; rewrite ?SPc; change ESTACK with 4096; lia
                       | lia]).
           - intros regs3 mem3 md3 HJ3 HP3 Ha03 Hcpy Hfr3 Hpres3 Hsm3 HS3.
             repeat (rewrite wvb_collapse in * ).
             clear HS HJ. rename HS3 into HS. rename HJ3 into HJ.
             assert (KEm : o11_kept (w_H W2) mem3 mem2 (o11_zok (FA g pos) sp1 (kz_n k))).
             { intros a Ha Hz. rewrite (Hfr3 a Ha).
               - exact (KE a Ha Hz).
               - intros Hd. apply Hz. unfold o11_zok. lia.
               - try rewrite SPc. change ESTACK with 4096. intros Hs. apply Hz. unfold o11_zok. lia. }
             assert (BYc : forall i, 0 <= i < kz_n k ->
               aview tfibsegs (w_H W2) mem3 (FA g pos + 324 + i) = Some (nth (Z.to_nat i) (kz_bytes k) 0)).
             { intros i Hi. rewrite (Hcpy i Hi). rewrite KE; [|lia | unfold o11_zok, o11_zerr; lia].
               destruct (Gbytes (Z.to_nat i) ltac:(lia)) as (Vj & Rj). rewrite Z2Nat.id in Vj by lia.
               replace (FA g pos + 216 + i) with (FA g pos + 176 + 40 + i) by lia. exact (o11_aview1 _ _ _ _ Vj Rj). }
             assert (SH3 : forall i, 0 <= i < 56 ->
               aview tfibsegs (w_H W2) mem3 (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
             { intros i Hi. rewrite KEm; [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia |].
               exact (o11_shadow_out (FA g pos) sp1 (kz_n k) i Hf64 Happ ltac:(lia) ltac:(lia) Hi). }
             clear KE Hfr3 Hcpy SHOK.
             assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zw (FA g pos) sp1 (kz_n k) a ->
               aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem3 a) by (intros; reflexivity).
             o11_liftS 33%nat E33 X33. o11_liftS 32%nat E32 X32. o11_liftS 64%nat E64 X64.
             lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
               assert (SHOK : sh_ok tfibsegs CW_Bx o11_SH2 Ev (mrestrict (w_H W2) mem3))
                 by (apply Forall_cons; [apply (o11_shk W2 mem3 Ev (FA g pos) Hf64 Happ SH3 X33 X32)
                    | apply Forall_cons; [apply (o11_sh7 W2 mem3 Ev (FA g pos) (kz_n k) Hf64 Happ ltac:(lia) SH3 X64 X32)
                    | apply Forall_nil]]) end.
             (* 0x82aa8-0x82ab0: a0 = 40(sp1) + n + 4 *)
             cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) 0x82ab4.
             cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
             (* a0 = F + 324 + n: named by the atom 64 *)
             o11_liftS 64%nat E64 Z64. o11_liftS 33%nat E33 Z33. o11_liftS 39%nat E39 Z39.
             lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
               assert (P10 : sv_denot Ev (SOff 64 0) = getr (ms_regs msv) 10%bv);
               [ rewrite (st_ok_restrict_reg tfibsegs _ Ev ssv _ 10%bv HS);
                 change (sr_get (ss_regs ssv) 10%bv) with (SAlu ALU_ADD (SOff 33 324) (SOff 39 0));
                 apply bv_eq; change (bv_unsigned (sv_denot Ev ?x)) with (U Ev x);
                 rewrite U_SAlu; cbn [zalu_raw];
                 rewrite (U_atom Ev 64 _ Z64), (o11_U_soff Ev 33 (FA g pos) 324 Z33), (U_atom Ev 39 _ Z39) by lia;
                 unfold zcanon, M64; rewrite Z.mod_small by lia; lia
               | pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv msv 10%bv (SOff 64 0) HS eq_refl P10) as HS2;
                 clear HS P10; rename HS2 into HS ] end.
             (* 0x82ab4-0x82ae8: the check of a0's byte, s11 = 10, want[4 + n] = 0xf7, want_len, want_display *)
             cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
             cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
             (* CHK: the record owe() leaves, and owex_chk *)
             o11_liftS 33%nat E33 W33. o11_liftS 64%nat E64 W64. o11_liftS 37%nat E37 W37.
             o11_liftS 38%nat E38 W38. o11_liftS 39%nat E39 W39.
             lazymatch goal with HS : st_ok _ ?Ev _ (restrict _ ?msv) |- _ =>
               rename msv into msF;
               assert (UFf : bv_unsigned (ew Ev 33) = FA g pos) by (rewrite W33; apply unsigned_lit_small; lia);
               assert (U64f : bv_unsigned (ew Ev 64) = FA g pos + 324 + kz_n k)
                 by (rewrite W64; apply unsigned_lit_small; lia) end.
             o11_region HS 0%nat Hr0. o11_region HS 1%nat Hr1. o11_region HS 2%nat Hr2. o11_region HS 6%nat Hr6.
             change (ms_mem (restrict (w_H W2) msF)) with (mrestrict (w_H W2) (ms_mem msF)) in Hr0, Hr1, Hr2, Hr6.
             pose proof (field_of_region_any _ _ 33 (FA g pos) _ _ _ _ _ 316 4 _ Hr6 UFf ltac:(o11_in) ltac:(lia)) as V316.
             pose proof (field_of_region_any _ _ 33 (FA g pos) _ _ _ _ _ 320 2 _ Hr1 UFf ltac:(o11_in) ltac:(lia)) as V320.
             pose proof (field_of_region_any _ _ 33 (FA g pos) _ _ _ _ _ 322 1 _ Hr1 UFf ltac:(o11_in) ltac:(lia)) as V322.
             pose proof (field_of_region_any _ _ 33 (FA g pos) _ _ _ _ _ 323 1 _ Hr1 UFf ltac:(o11_in) ltac:(lia)) as V323.
             pose proof (field_of_region_any _ _ 64 _ _ _ _ _ _ 0 1 _ Hr0 U64f ltac:(o11_in) ltac:(lia)) as V7.
             pose proof (field_of_region_any _ _ 33 (FA g pos) _ _ _ _ _ 344 8 _ Hr2 UFf ltac:(o11_in) ltac:(lia)) as V344.
             pose proof (field_of_region_any _ _ 33 (FA g pos) _ _ _ _ _ 352 4 _ Hr2 UFf ltac:(o11_in) ltac:(lia)) as V352f.
             pose proof (field_of_region_any _ _ 33 (FA g pos) _ _ _ _ _ 356 4 _ Hr2 UFf ltac:(o11_in) ltac:(lia)) as V356.
             change (N.to_nat 1) with 1%nat in V322, V323, V7. change (N.to_nat 2) with 2%nat in V320.
             change (N.to_nat 4) with 4%nat in V316, V352f, V356. change (N.to_nat 8) with 8%nat in V344.
             rewrite Z.add_0_r in V7.
             set (bs := o11_bs (kz_a k) (kz_b k) (kz_bytes k) (kz_n k)).
             assert (Lbs : Z.of_nat (length bs) = kz_n k + 5) by (apply o11_bs_len; [exact Lbytes | lia]).
             assert (Gbs : garr8 tfibsegs (rd W2 (ms_mem msF)) (FA g pos + 320) bs).
             { destruct (o11_split2 _ _ (o11_vm _ _ 2 _ _ V320 ltac:(cbn [sv_denot]; rewrite unsigned_lit_small by lia;
                 reflexivity))) as (B0 & B1).
               apply o11_garr_bs; [lia | lia | lia | exact Lbytes | exact Fbytes | exact B0
               | replace (FA g pos + 321) with (FA g pos + 320 + 1) by lia; exact B1 | | | | ].
               - apply (o11_vm _ _ 1 _ _ V322). pose proof (U_atom _ 37 (kz_a k) W37 ltac:(lia)) as UA. unfold U in UA. rewrite UA. o11_mm.
               - apply (o11_vm _ _ 1 _ _ V323). pose proof (U_atom _ 38 (kz_b k) W38 ltac:(lia)) as UA. unfold U in UA. rewrite UA. o11_mm.
               - intros i Hi. apply val_mem1_of_aviewA. rewrite KE; [exact (BYc i Hi) | lia |].
                 unfold o11_zw. lia.
               - apply (o11_vm _ _ 1 _ _ V7). cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity. }
             assert (Hspec : owe_kZ k od = (0, (bs, 0, o11_dp (kz_b k)))).
             { unfold owe_kZ. rewrite Hkk. apply o11_ok; [lia | lia | exact Hb2 | lia |].
               apply o11_sb_true; [lia | rewrite Lbytes; lia | exact Fbytes | exact Hall]. }
             lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ msF) |- _ =>
               eapply owex_chk with (E := Ev) (ys := o11_ys g pos k) (od := od)
                 (k' := owe_setZ k 0 (bs ++ skipn (length bs) (kz_want k)) (Z.of_nat (length bs)) 0 (o11_dp (kz_b k)))
             end.
             + exact LAWS.
             + exact HJ.
             + exact Hfr.
             + exact Hkj.
             + exact Hmo.
             + exact HC.
             + exact Hops.
             + exact Hcur.
             + env_agree_chain HAE.
             + exact HS.
             + reflexivity.
             + reflexivity.
             + vm_compute; reflexivity.
             + vm_compute; reflexivity.
             + vm_compute; o11_in.
             + intros a Ha. unfold am_keepzone in Ha.
               destruct (o11_out (FA g pos) (e_sp0 g) sp1 (kz_n k) a ltac:(lia) (proj1 Fsp) (proj1 (proj2 Fsp))
                 (proj2 (proj2 Fsp)) ltac:(lia) ltac:(clear - Ha; lia)) as (Ha64 & Hz1 & Hz2).
               rewrite (KE a Ha64 Hz2). exact (KEm a Ha64 Hz1).
             + intros i Hi. rewrite KE; [exact (SH3 i Hi) | unfold shadow_addr, SHADOW_OFF; lia |].
               intros Hz. apply (o11_shadow_out (FA g pos) sp1 (kz_n k) i Hf64 Happ ltac:(lia) ltac:(lia) Hi).
               exact (o11_zw_zok (FA g pos) sp1 (kz_n k) _ ltac:(lia) Hz).
             + apply (owe_k_at_end g pos k W2 mem2 W2 (ms_mem msF) 0 bs (Z.of_nat (length bs)) 0 (o11_dp (kz_b k)) Hkat).
               * apply Nat2Z.inj_le. rewrite Lbs. cbn. lia.
               * intros a Ha.
                 destruct (o11_out (FA g pos) (e_sp0 g) sp1 (kz_n k) a ltac:(lia) (proj1 Fsp) (proj1 (proj2 Fsp))
                   (proj2 (proj2 Fsp)) ltac:(lia) ltac:(clear - Ha Lbs; lia)) as (Ha64 & Hz1 & Hz2).
                 rewrite (KE a Ha64 Hz2). exact (KEm a Ha64 Hz1).
               * replace (FA g pos + 176 + 140) with (FA g pos + 316) by lia.
                 apply (o11_vm _ _ 4 _ _ V316). reflexivity.
               * replace (FA g pos + 176 + 144) with (FA g pos + 320) by lia. exact Gbs.
               * replace (FA g pos + 176 + 168) with (FA g pos + 344) by lia.
                 apply (o11_vm _ _ 8 _ _ V344). pose proof (o11_U_soff _ 39 (kz_n k) 5 W39 ltac:(lia) ltac:(lia)) as UA. unfold U in UA. rewrite UA, Lbs. o11_mm.
               * replace (FA g pos + 176 + 176) with (FA g pos + 352) by lia.
                 apply (o11_vm _ _ 4 _ _ V352f). reflexivity.
               * replace (FA g pos + 176 + 180) with (FA g pos + 356) by lia.
                 apply (o11_vm _ _ 4 _ _ V356). pose proof (o11_dp_den _ (kz_b k) W38 ltac:(lia)) as UA. unfold U in UA. unfold o11_dpe in UA. rewrite UA. o11_mm.
               * lia.
               * lia.
               * lia.
               * unfold o11_dp, bit_or_0. destruct (_ || _); lia.
             + apply owe_setZ_rec. exact Hrec.
             + destruct (owe_setZ_kz k od 0 (bs ++ skipn (length bs) (kz_want k)) (Z.of_nat (length bs)) 0
                 (o11_dp (kz_b k))) as (_ & E2' & E3'). rewrite E2', E3'. exact Hrc.
             + apply (owe_want_ok_succ k od _ bs 0 (o11_dp (kz_b k)) Hspec).
               rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
               symmetry. apply o11_bs_u8; [lia | lia | exact Fbytes]. }
         o11_mkst.
         apply (o11_loop0 B LAWS (kz_n k) (FA g pos + 216) (kz_bytes k) W2 (ms_regs ms4) (ms_mem ms4) (ms_mem ms4) _
           LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj
           (inv_chk B MT K XM_LIB g pos sp1 ops)); [lia | lia | unfold AM_HI; lia | exact HJ4 | exact Q10 | exact Q12
           | exact Q13 | exact Q23 | exact Q20 | intros x; reflexivity | exact BY4 | exact RA4 | appn; lia
           | exact ERR | exact OK].
      -- (* n >= 20: E_SPACE (0x82944) *)
         apply Z.ltb_ge in Hb4.
         cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
         cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
         assert (Hf : fst (owe_kZ k od) = E_SPACE) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_n; lia).
         o11_close 18446744073709551611 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
  + (* b = 0x70: E_REFUSED (0x82844) *)
    apply negb_false_iff, Z.eqb_eq in Hb2.
    cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
    cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
    assert (Hf : fst (owe_kZ k od) = E_REFUSED) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_70; lia).
    o11_close 18446744073709551606 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
- (* a >= 128: E_ARG (0x827d4) *)
  apply Z.ltb_ge in Hb1.
  cw_run_to ltac:(idtac; o11_awr sp1 (e_sp0 g) (FA g pos) (FA g pos + 324 + kz_n k) U2 UF U64 EFA) PC_CHK.
  cw_keep ltac:(idtac; o11_kwr U2 UF U64). repeat (rewrite wvb_collapse in * ).
  assert (Hf : fst (owe_kZ k od) = E_ARG) by (unfold owe_kZ; rewrite Hkk; apply o11_fail_a; lia).
  o11_close 18446744073709551615 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE.
Qed.

End b.
End a.
