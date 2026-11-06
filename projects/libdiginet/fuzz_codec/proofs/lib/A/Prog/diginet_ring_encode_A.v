(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 312 of its 358 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_bytes_A.v, with its module names changed; 1071 of its 1123 lines of code are new or changed and 306 lines of the source are left out. *)
(* diginet_ring_encode (diginet_codec.c:179-198) at image A 0x85314, 166 instructions, real frame 48, against
   lib/A/Prog/CPgEncC.v's cdc_ring_specX. a0 = the personality p, a1 = strip (lw), a2 = the mask (lhu),
   a3 = out. diginet_sysex_encode is inlined; the three payload bytes are built in the function's own real-stack
   frame at sp + 13 .. sp + 15 and copied to out + 4 by __asan_memcpy at 0x8547c.
   0x85330 beqz a0 and 0x85338 beqz a3: p = 0 returns -1; out is never 0 (0 < out from cdst_ok).
   0x8533c-0x85344 load the shadow offset through the .got slot and its cell; the walk then drops those two
   regions (the personality bytes and out may lie on them) and adds the personality's two bytes at p + 16 / p + 17
   and the four windows of out it writes.
   Branches: 0x85364 bgeu strip,strips -> -11; 0x8536c bltz (mask << 48) -> -11; 0x853ec bltz device -> -1;
   0x853fc bltz payload-byte -> -11; the loop 0x85388-0x853b8 is seven iterations with a concrete counter.
   The instrumented checks are paid by the shadow entries mkSHE 10 16 20 (pers_argA's cimg_range) and
   mkSHE 13 0 32 (cdst_ok). The three payload bytes the copy reads lie in the walk's own stack window, whose
   shadow is zero in every state (AR_zshadow_law). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI00 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk CPgWalkFrame CPgWalkIntr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_RING : Z := 0x85314.
Definition A_MEMCPY : Z := 0x51998.

(* ================================ the arithmetic of the body ================================ *)
Lemma rg_u8 : forall x, 0 <= x < 256 -> u8 x = x.
Proof. intros x Hx. unfold u8. apply Z.mod_small. exact Hx. Qed.
Lemma rg_lor_lt : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
assert (E : Z.lor a b = Z.land (Z.lor a b) (Z.ones n)).
{ rewrite Z.land_lor_distr_l, !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
rewrite E, Z.land_ones by lia.
pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as P.
pose proof (Z.mod_pos_bound (Z.lor a b) (2 ^ n) P). lia.
Qed.
(* `srai x, x, 63` of a 64-bit value, read back unsigned: all ones when its bit 63 is set *)
Lemma rg_sar63 : forall v, 0 <= v < 2 ^ 64 ->
Z.shiftr (bv_swrap 64 v) 63 mod 2 ^ 64 = if Z.testbit v 63 then 2 ^ 64 - 1 else 0.
Proof.
intros v Hv.
assert (T : Z.testbit v 63 = (2 ^ 63 <=? v)).
{ pose proof (Z.testbit_spec' v 63 ltac:(lia)) as Bt.
  destruct (Z.testbit v 63); cbn [Z.b2z] in Bt; symmetry;
  [apply Z.leb_le | apply Z.leb_gt]; Z.div_mod_to_equations; lia. }
rewrite T. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 64) with (2 ^ 63) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
destruct (Z.leb_spec (2 ^ 63) v) as [Hl|Hl].
- replace (v + 2 ^ 63) with ((v - 2 ^ 63) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 2 ^ 63)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (D : (v - 2 ^ 63 - 2 ^ 63) / 2 ^ 63 = -1) by (Z.div_mod_to_equations; lia).
  rewrite D. reflexivity.
- rewrite (Z.mod_small (v + 2 ^ 63)) by lia. replace (v + 2 ^ 63 - 2 ^ 63) with v by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small v) by lia. reflexivity.
Qed.
(* one picked bit of the loop body: bit 63 - s + k of the mask, placed by the literal c *)
Lemma rg_pick : forall E mask k s c, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
0 <= k <= 6 -> 1 <= s <= 63 -> 0 <= c < 2 ^ 64 ->
U E (SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SAluw ALU_SRL (SOff 12 0) (SLit k)) (SLit s)) (SLit 63)) (SLit c))
= if Z.testbit mask (63 - s + k) then c else 0.
Proof.
intros E mask k s c Hm Hmr Hk Hs Hc.
assert (Ux : U E (SAluw ALU_SRL (SOff 12 0) (SLit k)) = Z.shiftr mask k).
{ rewrite U_of_S, S_SAluw. cbn [zalu_raw].
  rewrite (U_atom E 12 mask Hm) by lia. rewrite U_lit by lia.
  rewrite (Z.mod_small mask (2 ^ 32)) by lia. rewrite (Z.mod_small k (2 ^ 32)) by lia.
  replace (Z.land k 31) with k by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  assert (Hsr : 0 <= Z.shiftr mask k < 65536).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; nia]. }
  rewrite (bv_swrap_small 32 (Z.shiftr mask k)) by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Hsr : 0 <= Z.shiftr mask k < 65536).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; nia]. }
assert (Uy : U E (SAlu ALU_SLL (SAluw ALU_SRL (SOff 12 0) (SLit k)) (SLit s))
  = Z.shiftl (Z.shiftr mask k) s mod 2 ^ 64).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Ux, U_lit by lia.
  replace (Z.land s 63) with s by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  unfold zcanon, M64. reflexivity. }
assert (Bz : Z.testbit (Z.shiftl (Z.shiftr mask k) s mod 2 ^ 64) 63 = Z.testbit mask (63 - s + k)).
{ rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia.
  try (f_equal; lia). }
assert (Uz : U E (SAlu ALU_SRA (SAlu ALU_SLL (SAluw ALU_SRL (SOff 12 0) (SLit k)) (SLit s)) (SLit 63))
  = if Z.testbit mask (63 - s + k) then 2 ^ 64 - 1 else 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Uy, U_lit by lia.
  replace (Z.land 63 63) with 63 by reflexivity.
  unfold zcanon, M64. rewrite <- Bz. apply rg_sar63.
  pose proof (Z.mod_pos_bound (Z.shiftl (Z.shiftr mask k) s) (2 ^ 64) ltac:(lia)). lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Uz, U_lit by lia.
destruct (Z.testbit mask (63 - s + k)).
- replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
  rewrite Z.land_comm, Z.land_ones by lia. unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
- rewrite Z.land_0_l. reflexivity.
Qed.
(* the seven iterations, as the engine leaves them, against ring_bits *)
Definition rg_t (k s c : Z) : sv :=
SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SAluw ALU_SRL (SOff 12 0) (SLit k)) (SLit s)) (SLit 63)) (SLit c).
Definition rg_acc (s : Z) : sv :=
SAlu ALU_OR (rg_t 6 s 1) (SAlu ALU_OR (rg_t 5 s 2) (SAlu ALU_OR (rg_t 4 s 4) (SAlu ALU_OR (rg_t 3 s 8)
(SAlu ALU_OR (rg_t 2 s 16) (SAlu ALU_OR (rg_t 1 s 32) (SAlu ALU_OR (rg_t 0 s 64) (SLit 0))))))).
Lemma rg_lor7 : forall a0 a1 a2 a3 a4 a5 a6,
Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor 0 a0) a1) a2) a3) a4) a5) a6
= Z.lor a6 (Z.lor a5 (Z.lor a4 (Z.lor a3 (Z.lor a2 (Z.lor a1 (Z.lor a0 0)))))).
Proof.
intros a0 a1 a2 a3 a4 a5 a6. apply Z.bits_inj'. intros n Hn.
rewrite !Z.lor_spec, !Z.bits_0.
destruct (Z.testbit a0 n), (Z.testbit a1 n), (Z.testbit a2 n), (Z.testbit a3 n),
(Z.testbit a4 n), (Z.testbit a5 n), (Z.testbit a6 n); reflexivity.
Qed.
Lemma rg_U_or : forall E a b va vb, U E a = va -> U E b = vb -> 0 <= va < 128 -> 0 <= vb < 128 ->
U E (SAlu ALU_OR a b) = Z.lor va vb /\ 0 <= Z.lor va vb < 128.
Proof.
intros E a b va vb Ha Hb Hva Hvb.
assert (Hr : 0 <= Z.lor va vb < 128) by (change 128 with (2 ^ 7); apply rg_lor_lt; cbn; lia).
split; [|exact Hr].
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rg_t_rng : forall E mask k s c, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
0 <= k <= 6 -> 1 <= s <= 63 -> 0 <= c <= 64 ->
U E (rg_t k s c) = (if Z.testbit mask (63 - s + k) then c else 0)
/\ 0 <= (if Z.testbit mask (63 - s + k) then c else 0) < 128.
Proof.
intros E mask k s c Hm Hmr Hk Hs Hc. unfold rg_t.
rewrite (rg_pick E mask k s c Hm Hmr Hk Hs ltac:(lia)).
split; [reflexivity | destruct (Z.testbit mask (63 - s + k)); lia].
Qed.
Lemma rg_acc_ok : forall E mask s off, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
1 <= s <= 63 -> off = 63 - s ->
U E (rg_acc s) =
fold_left (fun b k => Z.lor b (bit_or_0 (Z.testbit mask (off + k)) (2 ^ (6 - k)))) (map Z.of_nat (seq 0 7)) 0
/\ 0 <= U E (rg_acc s) < 128.
Proof.
intros E mask s off Hm Hmr Hs ->.
destruct (rg_t_rng E mask 0 s 64 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V0 R0].
destruct (rg_t_rng E mask 1 s 32 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V1 R1].
destruct (rg_t_rng E mask 2 s 16 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V2 R2].
destruct (rg_t_rng E mask 3 s 8 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V3 R3].
destruct (rg_t_rng E mask 4 s 4 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V4 R4].
destruct (rg_t_rng E mask 5 s 2 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V5 R5].
destruct (rg_t_rng E mask 6 s 1 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V6 R6].
assert (Z0 : U E (SLit 0) = 0) by (apply U_lit; lia).
destruct (rg_U_or E _ _ _ _ V0 Z0 R0 ltac:(lia)) as [P0 Q0].
destruct (rg_U_or E _ _ _ _ V1 P0 R1 Q0) as [P1 Q1].
destruct (rg_U_or E _ _ _ _ V2 P1 R2 Q1) as [P2 Q2].
destruct (rg_U_or E _ _ _ _ V3 P2 R3 Q2) as [P3 Q3].
destruct (rg_U_or E _ _ _ _ V4 P3 R4 Q3) as [P4 Q4].
destruct (rg_U_or E _ _ _ _ V5 P4 R5 Q4) as [P5 Q5].
destruct (rg_U_or E _ _ _ _ V6 P5 R6 Q5) as [P6 Q6].
unfold rg_acc. rewrite P6. split; [|exact Q6].
cbn [map seq fold_left]. unfold bit_or_0.
change (2 ^ (6 - 0)) with 64. change (2 ^ (6 - 1)) with 32. change (2 ^ (6 - 2)) with 16.
change (2 ^ (6 - 3)) with 8. change (2 ^ (6 - 4)) with 4. change (2 ^ (6 - 5)) with 2.
change (2 ^ (6 - 6)) with 1.
symmetry. apply rg_lor7.
Qed.
Lemma rg_acc_range : forall E mask s, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 -> 1 <= s <= 63 ->
0 <= U E (rg_acc s) < 128.
Proof.
intros E mask s Hm Hmr Hs. exact (proj2 (rg_acc_ok E mask s (63 - s) Hm Hmr Hs eq_refl)).
Qed.
Lemma rg_ring_bits_fst : forall E mask, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
U E (rg_acc 62) = fst (ring_bits mask).
Proof.
intros E mask Hm Hmr. rewrite (proj1 (rg_acc_ok E mask 62 1 Hm Hmr ltac:(lia) ltac:(lia))).
unfold ring_bits. cbn [map seq fold_left]. reflexivity.
Qed.
Lemma rg_ring_bits_snd : forall E mask, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
U E (rg_acc 55) = snd (ring_bits mask).
Proof.
intros E mask Hm Hmr. rewrite (proj1 (rg_acc_ok E mask 55 8 Hm Hmr ltac:(lia) ltac:(lia))).
unfold ring_bits. cbn [map seq fold_left]. reflexivity.
Qed.
(* `slli a2,a2,63; srli a2,a2,57; or a2,a2,a1`: the first payload byte *)
Lemma rg_pl0_val : forall E mask strip, ew E 12 = Z_to_bv 64 mask -> ew E 11 = Z_to_bv 64 strip ->
0 <= mask < 65536 -> 0 <= strip < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SOff 12 0) (SLit 63)) (SLit 57)) (SOff 11 0))
= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64).
Proof.
intros E mask strip Hm Hs Hmr Hsr.
assert (Ha : U E (SAlu ALU_SLL (SOff 12 0) (SLit 63)) = Z.shiftl mask 63 mod 2 ^ 64).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 12 mask Hm) by lia. rewrite U_lit by lia.
  replace (Z.land 63 63) with 63 by reflexivity. unfold zcanon, M64. reflexivity. }
assert (Hb : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 12 0) (SLit 63)) (SLit 57))
  = bit_or_0 (Z.testbit mask 0) 64).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_lit by lia.
  replace (Z.land 57 63) with 57 by reflexivity.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 63) with 9223372036854775808. change (2 ^ 57) with 144115188075855872.
  change (2 ^ 64) with 18446744073709551616.
  pose proof (Z.testbit_spec' mask 0 ltac:(lia)) as Bt. change (2 ^ 0) with 1 in Bt. rewrite Z.div_1_r in Bt.
  unfold bit_or_0, zcanon, M64.
  destruct (Z.testbit mask 0); cbn [Z.b2z] in Bt; Z.div_mod_to_equations; lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hb, (U_atom E 11 strip Hs) by lia.
assert (Hr : 0 <= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64) < 256).
{ change 256 with (2 ^ 8). apply rg_lor_lt; [lia | change (2 ^ 8) with 256; lia |].
  unfold bit_or_0. destruct (Z.testbit mask 0); change (2 ^ 8) with 256; lia. }
rewrite Z.lor_comm. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rg_pl0_range : forall mask strip, 0 <= strip < 256 ->
0 <= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64) < 256.
Proof.
intros mask strip Hs. change 256 with (2 ^ 8). apply rg_lor_lt; [lia | change (2 ^ 8) with 256; lia|].
unfold bit_or_0. destruct (Z.testbit mask 0); change (2 ^ 8) with 256; lia.
Qed.
(* `slli s0,s0,48; srli s0,s0,48; lui a2,0x30; or a2,s0,a2`: the key *)
Lemma rg_key_val : forall E strip, ew E 11 = Z_to_bv 64 strip -> 0 <= strip < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 48)) (SLit 48)) (SLit 196608))
= KEY 3 strip.
Proof.
intros E strip Hs Hsr.
assert (Ha : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 48)) (SLit 48)) = strip).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 11 strip Hs) by lia. rewrite !U_lit by lia.
  replace (Z.land 48 63) with 48 by reflexivity.
  rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
  rewrite (Z.mod_small (strip * 2 ^ 48)) by (change (2 ^ 48) with 281474976710656; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (change (2 ^ 48) with 281474976710656; lia).
  apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_lit by lia.
unfold KEY. change (3 * 65536) with 196608. change 0xffff with (2 ^ 16 - 1).
replace (Z.land strip (2 ^ 16 - 1)) with strip
by (change (2 ^ 16 - 1) with (Z.ones 16); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
rewrite (Z.lor_comm 196608 strip).
apply zcanon_id. unfold M64.
assert (0 <= Z.lor strip 196608 < 2 ^ 18) by (apply rg_lor_lt; cbn; lia). lia.
Qed.
(* the failing returns and the success of ring_spec *)
Lemma rg_spec_strips : forall d strip mask, d_strips d <= strip -> ring_spec (Some d) strip mask = (E_RANGE, None).
Proof.
intros d strip mask H. unfold ring_spec.
replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma rg_spec_mask : forall d strip mask, 0 <= mask -> 32768 <= mask -> ring_spec (Some d) strip mask = (E_RANGE, None).
Proof.
intros d strip mask H0 H. unfold ring_spec.
replace (Z.shiftr mask 15 =? 0) with false.
- cbn [negb]. rewrite orb_true_r. reflexivity.
- symmetry. apply Z.eqb_neq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 15) with 32768.
  intro E. Z.div_mod_to_equations. lia.
Qed.
Lemma rg_spec_go : forall d strip mask, strip < d_strips d -> 0 <= mask < 32768 ->
ring_spec (Some d) strip mask =
with_key (sysex_spec (d_dev d) 0 [u8 (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64));
                                  fst (ring_bits mask); snd (ring_bits mask)]) (KEY 3 strip).
Proof.
intros d strip mask Hs Hm. unfold ring_spec.
replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia).
replace (Z.shiftr mask 15 =? 0) with true
by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
cbn [orb negb]. destruct (ring_bits mask). reflexivity.
Qed.
Lemma rg_tb7_lo : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof.
intros x Hx. pose proof (Z.testbit_spec' x 7 ltac:(lia)) as Bt.
rewrite Z.div_small in Bt by (cbn; lia). destruct (Z.testbit x 7); [discriminate Bt | reflexivity].
Qed.
Lemma rg_tb7_hi : forall x, 128 <= x < 256 -> Z.testbit x 7 = true.
Proof.
intros x Hx. pose proof (Z.testbit_spec' x 7 ltac:(lia)) as Bt.
replace (x / 2 ^ 7) with 1 in Bt by (change (2 ^ 7) with 128; Z.div_mod_to_equations; lia).
destruct (Z.testbit x 7); [reflexivity | discriminate Bt].
Qed.
Lemma rg_sysex_dev_hi : forall dev pl, 128 <= dev -> sysex_spec dev 0 pl = (E_ARG, None).
Proof.
intros dev pl H. unfold sysex_spec. replace (0x7f <? dev) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.
Lemma rg_sysex_pl0_hi : forall dev p0 b1 b2, 0 <= dev < 128 -> 128 <= p0 < 256 ->
sysex_spec dev 0 [p0; b1; b2] = (E_RANGE, None).
Proof.
intros dev p0 b1 b2 Hd Hp. unfold sysex_spec.
replace (0x7f <? dev) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.eqb Z.ltb Z.compare existsb length Z.of_nat Pos.of_succ_nat Z.add].
rewrite (rg_tb7_hi p0 Hp). reflexivity.
Qed.
Lemma rg_sysex_ok : forall dev p0 b1 b2, 0 <= dev < 128 -> 0 <= p0 < 128 -> 0 <= b1 < 128 -> 0 <= b2 < 128 ->
sysex_spec dev 0 [p0; b1; b2] = (0, Some ([0xf0; 0x13; dev; 0; p0; b1; b2; 0xf7], 0, 0)).
Proof.
intros dev p0 b1 b2 Hd Hp H1 H2. unfold sysex_spec.
replace (0x7f <? dev) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.eqb Z.ltb Z.compare existsb length Z.of_nat Pos.of_succ_nat Z.add].
rewrite (rg_tb7_lo p0 Hp), (rg_tb7_lo b1 H1), (rg_tb7_lo b2 H2). reflexivity.
Qed.

(* ================================ reading bytes off the walk's regions ================================ *)
Lemma rg_denot_lit : forall E z v, z mod 2 ^ 64 = v mod 2 ^ 64 -> sv_denot E (SLit z) = w64 v.
Proof.
intros E z v H. rewrite denot_lit_U, U_SLit. unfold w64, zcanon, M64.
apply Z_to_bv64_eq_mod. rewrite Z.mod_mod by lia. exact H.
Qed.
Lemma rg_garr8_chunk : forall E m base off (w : N) (e : sv) (l : list Z),
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w e)) ->
Z.of_nat (length l) = Z.of_N w ->
(forall j, (j < length l)%nat -> nth j l 0 = (U E e / 2 ^ (8 * Z.of_nat j)) mod 256) ->
garr8 tfibsegs m (base + off) l.
Proof.
intros E m base off w e l Hc Hlen Hnth j Hj.
pose proof (Z.mod_pos_bound (U E e / 2 ^ (8 * Z.of_nat j)) 256 ltac:(lia)) as Hb.
rewrite (Hnth j Hj). split; [|lia].
destruct (Hc (Z.of_nat j) ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. injection Hb1 as Hb1. subst b.
intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
replace (base + off + Z.of_nat j + Z.of_nat 0) with (base + off + Z.of_nat j) by lia.
rewrite Hb2. f_equal.
unfold YP09.byte_of_word, YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256.
rewrite (Z.mod_mod _ 256) by lia.
rewrite denot_lit_U, unsigned_lit_small by (unfold U; apply u64_range).
rewrite Z.shiftr_div_pow2 by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma rg_garr8_sub : forall m base l i n, garr8 tfibsegs m base l -> (i + n <= length l)%nat ->
garr8 tfibsegs m (base + Z.of_nat i) (firstn n (skipn i l)).
Proof.
intros m base l i n H Hi j Hj.
rewrite length_firstn, length_skipn in Hj.
rewrite nth_firstn by lia. rewrite nth_skipn.
replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
replace (base + Z.of_nat i + Z.of_nat j) with (base + Z.of_nat (i + j)) by lia.
apply H. lia.
Qed.
Lemma rg_val_mem_move : forall (W : world tfibsegs) m m' a a' v,
aview tfibsegs (w_H W) m' a' = aview tfibsegs (w_H W) m a ->
val_mem tfibsegs (mrestrict (w_H W) m) a 1 v -> val_mem tfibsegs (mrestrict (w_H W) m') a' 1 v.
Proof.
intros W m m' a a' v He Hv kk Hk. assert (kk = 0%nat) by lia. subst kk.
rewrite Z.add_0_r. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview in He. rewrite Hv in He. cbn [option_map] in He.
destruct (mbyte tfibsegs (mrestrict (w_H W) m') a') as [b'|] eqn:Eb'; cbn [option_map] in He; [|discriminate He].
injection He as He. f_equal. apply bv_eq. exact He.
Qed.
Lemma rg_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r. unfold zcanon, M64.
rewrite Z.mod_small by apply u64_range. apply Z_to_bv_bv_unsigned.
Qed.
(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma rg_hull_sub : forall rd q n q' n', 0 <= q -> q <= q' -> 0 < n' -> q' + n' <= q + n ->
shadow_hull_vis rd q n -> shadow_hull_vis rd q' n'.
Proof.
intros rd q n q' n' Hq Hq' Hn' Hle H s Hs. apply H.
unfold shadow_addr, SHADOW_OFF in *.
assert (D1 : (2147450880 + q / 8) / 8 * 8 <= (2147450880 + q' / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (D2 : (2147450880 + (q' + n' - 1) / 8) / 8 * 8 <= (2147450880 + (q + n - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.
(* a sign-extended byte of a seven-bit value is that value *)
Lemma rg_U_sx8 : forall E e v, U E e = v -> 0 <= v < 128 -> U E (SExt true 8 e) = v.
Proof.
intros E e v Hv Hr. rewrite U_SExt. cbv iota beta. rewrite Hv.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small v 256) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
rewrite (Z.mod_small (v + 128) 256) by lia. replace (v + 128 - 128) with v by lia.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* the one byte a 1-byte chunk of a region holds *)
Lemma rg_byte_of_region : forall E m n b lo hi wlo whi cs od e v,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs -> U E e mod 256 = v ->
garr8 tfibsegs m (b + od) [v].
Proof.
intros E m n b lo hi wlo whi cs od e v HR Hb Hin Hv.
pose proof (field_of_region_any E m n b cs lo hi wlo whi od 1 e HR Hb Hin ltac:(cbn; lia)) as HV.
change (N.to_nat 1) with 1%nat in HV. change (8 * Z.of_N 1) with 8 in HV.
change (2 ^ 8) with 256 in HV. unfold U in Hv. rewrite Hv in HV.
intros j Hj. cbn [length] in Hj. assert (j = 0)%nat by lia. subst j. cbn [nth].
rewrite Z.add_0_r. split; [exact HV|]. rewrite <- Hv. apply Z.mod_pos_bound. lia.
Qed.
(* the bytes a wider chunk of a region holds *)
Lemma rg_region_garr8 : forall E m n b lo hi wlo whi cs od (w : N) e l,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs ->
Z.of_nat (length l) = Z.of_N w ->
(forall j, (j < length l)%nat -> nth j l 0 = (U E e / 2 ^ (8 * Z.of_nat j)) mod 256) ->
garr8 tfibsegs m (b + od) l.
Proof.
intros E m n b lo hi wlo whi cs od w e l HR Hb Hin Hlen Hnth.
apply (rg_garr8_chunk E m b od w e l); [| exact Hlen | exact Hnth].
destruct HR as (_ & _ & _ & HC). rewrite Forall_forall in HC. specialize (HC _ Hin).
cbn [YP09.r_base base_val] in HC. rewrite Hb in HC. exact HC.
Qed.
(* the shadow bytes of a range below 2 ^ 47 lie in the band, so a kept band keeps the range's marks *)
Lemma rg_shadow_keep : forall (W : world tfibsegs) m1 m2 q n,
0 <= q -> q + n <= 2 ^ 47 -> 0 < n ->
(forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
 aview tfibsegs (w_H W) m2 s = aview tfibsegs (w_H W) m1 s) ->
range_addressable (aview tfibsegs (w_H W) m1) SHADOW_OFF q n ->
shadow_hull_vis (aview tfibsegs (w_H W) m1) q n ->
range_addressable (aview tfibsegs (w_H W) m2) SHADOW_OFF q n /\
shadow_hull_vis (aview tfibsegs (w_H W) m2) q n.
Proof.
intros W m1 m2 q n Hq Hqn Hn HK HRA HH. split.
- intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite HK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF.
  split; [pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia|].
  assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  change (2 ^ 44) with 17592186044416 in *. lia.
- intros s Hs. rewrite HK; [exact (HH s Hs)|].
  unfold shadow_addr, SHADOW_OFF in *.
  pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)) as Hd1.
  assert (Hd2 : (q + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia)) as H1.
  pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia)) as H2.
  pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)) as H3.
  pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)) as H4.
  change (2 ^ 44) with 17592186044416 in *.
  clear - Hs H1 H2 H3 H4 Hd1 Hd2. lia.
Qed.
(* ================================ the branch conditions ================================ *)
Lemma rg_denot_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n c v H Hv. rewrite denot_lit_U, U_SOff, H, unsigned_lit_small by lia.
unfold w64, zcanon, M64. apply Z_to_bv64_eq_mod. apply Z.mod_mod. lia.
Qed.
Lemma rg_br_lt : forall E a b,
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (bv_swrap 64 (U E a) <? bv_swrap 64 (U E b)).
Proof. intros E a b. reflexivity. Qed.
Lemma rg_swrap_pos : forall v, 0 <= v < 2 ^ 63 -> bv_swrap 64 v = v.
Proof.
intros v Hv. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma rg_swrap_neg : forall v, 2 ^ 63 <= v < 2 ^ 64 -> bv_swrap 64 v = v - 2 ^ 64.
Proof.
intros v Hv. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
replace (v + 2 ^ 63) with ((v - 2 ^ 63) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
rewrite Z.mod_small by lia. lia.
Qed.
(* `lb` of a byte, then `bltz`: taken exactly when the byte has bit 7 set *)
Lemma rg_sx8_lt0 : forall E e v, U E e = v -> 0 <= v < 256 ->
branch_taken BC_LT (sv_denot E (SExt true 8 e)) (sv_denot E (SLit 0)) = (127 <? v).
Proof.
intros E e v Hv Hr. rewrite rg_br_lt.
assert (HL : U E (SLit 0) = 0) by (apply U_lit; lia). rewrite HL.
rewrite (rg_swrap_pos 0) by lia.
rewrite U_SExt. cbv iota beta. rewrite Hv.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small v 256) by lia.
assert (Hs8 : bv_swrap 8 v = if v <? 128 then v else v - 256).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  destruct (Z.ltb_spec v 128).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (v + 128) (-1) 256) by lia. rewrite Z.mod_small by lia. lia. }
rewrite Hs8. unfold zcanon, M64.
destruct (Z.ltb_spec v 128) as [Hl|Hl].
- rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite rg_swrap_pos by lia.
  destruct (Z.ltb_spec v 0); destruct (Z.ltb_spec 127 v); first [reflexivity | lia].
- replace ((v - 256) mod 2 ^ 64) with (v - 256 + 2 ^ 64)
  by (rewrite <- (Z.mod_add (v - 256) 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite rg_swrap_neg by lia.
  destruct (Z.ltb_spec (v - 256 + 2 ^ 64 - 2 ^ 64) 0); destruct (Z.ltb_spec 127 v); first [reflexivity | lia].
Qed.
(* `slli a2,a2,48; bltz`: taken exactly when bit 15 of the mask is set *)
Lemma rg_shl48_lt0 : forall E mask, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
branch_taken BC_LT (sv_denot E (SAlu ALU_SLL (SOff 12 0) (SLit 48))) (sv_denot E (SLit 0)) = (32767 <? mask).
Proof.
intros E mask Hm Hr. rewrite rg_br_lt.
assert (HL : U E (SLit 0) = 0) by (apply U_lit; lia). rewrite HL.
rewrite (rg_swrap_pos 0) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 12 mask Hm) by lia. rewrite U_lit by lia.
replace (Z.land 48 63) with 48 by reflexivity.
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
change (2 ^ 48) with 281474976710656 in *. change (2 ^ 64) with 18446744073709551616 in *.
rewrite (Z.mod_small (mask * 281474976710656)) by lia.
destruct (Z.ltb_spec 32767 mask) as [Hl|Hl].
- rewrite rg_swrap_neg by (change (2 ^ 63) with 9223372036854775808; change (2 ^ 64) with 18446744073709551616; lia).
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.ltb_spec (mask * 281474976710656 - 18446744073709551616) 0); [reflexivity | lia].
- rewrite rg_swrap_pos by (change (2 ^ 63) with 9223372036854775808; lia).
  destruct (Z.ltb_spec (mask * 281474976710656) 0); [lia | reflexivity].
Qed.
(* a1 = the strip as the caller passes it (sign-extended from bit 31), against a byte-sized bound *)
Lemma rg_s32_rng : forall strip, 0 <= strip < 2 ^ 32 -> 0 <= s32 strip mod 2 ^ 64 < 2 ^ 64.
Proof. intros strip Hs. apply Z.mod_pos_bound. lia. Qed.
Lemma rg_u11_lt : forall strip strips, 0 <= strip < 2 ^ 32 -> 0 <= strips < 256 ->
(s32 strip mod 2 ^ 64 <? strips) = (strip <? strips).
Proof.
intros strip strips Hs Hst. unfold s32.
destruct (Z.ltb_spec strip (2 ^ 31)) as [Hl|Hl].
- rewrite Z.mod_small by lia. reflexivity.
- replace ((strip - 2 ^ 32) mod 2 ^ 64) with (strip - 2 ^ 32 + 2 ^ 64)
  by (rewrite <- (Z.mod_add (strip - 2 ^ 32) 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
  destruct (Z.ltb_spec (strip - 2 ^ 32 + 2 ^ 64) strips); destruct (Z.ltb_spec strip strips);
  first [reflexivity | lia].
Qed.
(* an atom equation of the walk's base env, moved to the env a run or a call left *)
Ltac rg_ew H := rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact H.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_MEMCPY.

(* the bytes of a range the call may write are present *)
Lemma rg_dst_pres : forall lyc Sc (W : world tfibsegs) mem md q n a,
AR tfibsegs B lyc Sc W mem md -> tdst_ok B lyc Sc q n -> q <= a < q + n -> apresent (w_H W) mem a.
Proof.
intros lyc Sc W mem md q n a HAR Hd Ha.
destruct (Hd a Ha) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W mem md b m HAR Hin) as (_ & _ & _ & _ & Hp & _).
  exact (proj1 (Hp a Hr)).
- destruct (al_frames _ _ LAWS lyc Sc W mem md cid pos HAR Hin) as (_ & _ & Hp & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  exact (proj1 (Hp a ltac:(lia))).
Qed.
(* ================================ the walk's states ================================ *)
Definition rg_rPers : YP09.region :=
YP09.mkRegion (Some 10%nat) 16 18 0 0
[YP09.mkChunk 16 (CVal 1 (SOff 33 0)); YP09.mkChunk 17 (CVal 1 (SOff 34 0))].
Definition rg_rA : YP09.region := YP09.mkRegion (Some 13%nat) 0 4 0 4 [].
Definition rg_rB : YP09.region := YP09.mkRegion (Some 13%nat) 7 8 7 8 [].
Definition rg_rC : YP09.region := YP09.mkRegion (Some 13%nat) 24 26 24 26 [].
Definition rg_rD : YP09.region := YP09.mkRegion (Some 13%nat) 28 32 28 32 [].
Definition rg_AF : list (nat * afact) :=
[(10%nat, mkAF 1 (2 ^ 47 - 21) 0); (12%nat, mkAF 0 65535 0); (13%nat, mkAF 1 (2 ^ 47 - 33) 0);
 (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)].
Definition rg_SH : list shent := [mkSHE 10 16 20; mkSHE 13 0 32].
(* the atom values of the walk's base env, in the env a run left *)
Ltac rg_norm_base :=
rewrite ?ew_ewset_other, ?ew_havoc_old by lia;
repeat match goal with
| H : bv_unsigned (ew ?Ev 2) = _ |- context [bv_unsigned (ew ?Ev 2)] => rewrite H
| H : ew ?Ev ?n = Z_to_bv 64 _ |- context [bv_unsigned (ew ?Ev ?n)] => rewrite H
end;
rewrite ?unsigned_lit_small by lia.
(* the extents of the walk's regions are pairwise apart (cimg_range / cdst_ok's coff_win, cpers_disj) *)
Ltac rg_disj :=
cbn [ss_mem all_disjoint add_cond setreg setpc]; unfold extent_disjoint, rg_rPers, rg_rA, rg_rB, rg_rC, rg_rD;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rg_norm_base;
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
(* a window of out the call may write, with no chunk yet *)
Ltac rg_rok HW :=
unfold region_ok, rg_rA, rg_rB, rg_rC, rg_rD;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
rg_norm_base;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply HW; lia | apply Forall_nil].
Ltac rg_add r Hrok :=
lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS1 := fresh "HS" in
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv r HS eq_refl Hrok ltac:(rg_disj)) as HS1;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS; rename HS1 into HS
end.
(* the write right of a run that stores into out: the save area is the caller's, the windows of out are
   the bytes cdst_ok's twr_ok lets the call write *)
Ltac rg_awr HT :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| lazymatch goal with
  | HB : bv_unsigned (ew _ 2) = ?spv |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
    [reflexivity | rg_norm_base; try lia | cbn [YP09.r_wlo YP09.r_whi]; lia
     | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  end
| (eapply (cw_awr_ok_cons_twr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 13%nat);
   [reflexivity | | | | exact HT | ]);
  [rg_norm_base; try reflexivity | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | ] ].
(* every write window of such a run lies in the zone the kept fact leaves out *)
Ltac rg_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
    rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
    first
    [ lazymatch goal with HB : bv_unsigned (ew _ 2) = _ |- _ => rewrite HB in Hb end; left; lia
    | lazymatch goal with HB : ew _ 13 = Z_to_bv 64 _ |- _ =>
        rewrite HB, unsigned_lit_small in Hb by lia end;
      first [right; left; lia | right; right; left; lia | right; right; right; lia | right; right; lia]
    | lia ]
  | ]); destruct Hr.

Theorem diginet_ring_encode_A_holds : cdc_ring_specX tfibsegs B MT A_RING.
Proof using MTL TL LAWS ML AMEMCPY.
unfold cdc_ring_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip mask out before
HE H10 HPERS H11 H12 H13 HOUT HDISJ.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_ring HE ltac:(unfold T_ring, ESTACK; lia))
  as (Hceil & H47 & H46 & _ & Hpres).
pose proof HOUT as (HDST & HGARR & HLEN).
pose proof HDST as (Hout0 & Hout63 & HTD & HTW & HRAo & HHo & HAMo & HWINo).
assert (Hout47 : out + 32 <= 2 ^ 47 - 1).
{ unfold amem_range in HAMo. rewrite C4, C5 in HAMo. destruct HAMo as [Hl | [_ Hh]]; lia. }
assert (HAR : AR tfibsegs B lyc Sc W memc mdc) by exact (proj1 HJ0).
assert (EIMG : forall a, cenc_wr out a -> in_img tfibsegs a -> False).
{ intros a Ha Him. exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a HAR HTD Ha Him). }
unfold T_ring in *.
change (w64 p) with (Z_to_bv 64 p) in H10. change (w64 out) with (Z_to_bv 64 out) in H13.
destruct H11 as (Hstrip32 & H11). destruct H12 as (Hmask16 & H12).
unfold cfg_at, A_RING. change (w64 0x85314) with (Z_to_bv 64 0x85314).
destruct pd as [dsk|].
- (* ======================= the personality is registered ======================= *)
  pose proof HPERS as (Hp0 & Hp63 & Hdev & Hstrips & Hchars & Hcount & HGP & HIMGR).
  pose proof HIMGR as (Hq0 & _ & Hq63 & HAMp & HWINp & HPIMG & HUSE).
  assert (Hp47 : p + 20 <= 2 ^ 47 - 1).
  { unfold amem_range in HAMp. rewrite C4, C5 in HAMp. destruct HAMp as [Hl | [_ Hh]]; lia. }
  set (xs := [d_dev dsk; d_strips dsk]).
  assert (X33 : ew (Ereg regs (cw_extra xs)) 33 = Z_to_bv 64 (d_dev dsk)) by exact (cw_ew_x regs xs 0).
  assert (X34 : ew (Ereg regs (cw_extra xs)) 34 = Z_to_bv 64 (d_strips dsk)) by exact (cw_ew_x regs xs 1).
  assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) rg_AF).
  { unfold rg_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
    rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12.
    rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), H13.
    rewrite X33, X34.
    rewrite !unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
  pose proof (cw_entry_base_af B TL LAWS 0x85314 48 xs rg_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (48 + ESTACK) HE ltac:(unfold ESTACK; lia) ltac:(vm_compute; reflexivity) HAF) as HS.
  remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E2z : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- B2; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E3 : ew E 3 = w64 (as_gp B)) by (subst E; rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp).
  assert (E4 : ew E 4 = w64 (as_tp B)) by (subst E; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).
  assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 (s32 strip)) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 mask) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (B13 : bv_unsigned (ew E 13) = out) by (rewrite E13; apply unsigned_lit_small; lia).
  assert (B10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (E33 : ew E 33 = Z_to_bv 64 (d_dev dsk)) by (subst E; exact (cw_ew_x regs xs 0)).
  assert (E34 : ew E 34 = Z_to_bv 64 (d_strips dsk)) by (subst E; exact (cw_ew_x regs xs 1)).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx rg_SH E (mrestrict (w_H W) memc)).
  { unfold rg_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - exact (cw_shent_ra_off W memc E 10 p 16 4 (proj1 (HUSE lyc Sc W memc mdc HAR)) HAMp
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10 E32).
    - exact (cw_shent_cdst_off B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (48 + ESTACK) E 13 out 0 32
        ltac:(rewrite Z.add_0_r; exact HDST) E13 ltac:(lia) ltac:(lia) E32 ltac:(lia)). }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - (48 + ESTACK) <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold coff_win in HWINo, HWINp. unfold cpers_disj in HDISJ.
  (* 0x85314-0x85344: the frame, the two NULL tests, the shadow offset through the .got slot and its cell *)
  cw_run_to cw_awr_stk 0x85348. cw_keep cw_kwr_stk.
  (* the personality bytes may lie on the .got slot or the cell: drop both, add the two bytes it reads *)
  cw_drop_gb.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?ms0) |- _ =>
    assert (VK : forall q n v, 0 <= q -> q + Z.of_nat n <= 2 ^ 63 ->
      (spZ regs <= q \/ q + Z.of_nat n <= spZ regs - (48 + ESTACK)) ->
      val_mem tfibsegs (mrestrict (w_H W) memc) q n v ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms0)) q n v);
    [ intros q n v Hz0 Hz1 Hoff Hv; apply (cw_val_mem_kept (w_H W) (w_H W) memc (ms_mem ms0)); [|exact Hv];
      intros x Hx; apply KE; [lia | cbv beta; lia]
    | ];
    assert (HRP : region_ok tfibsegs Ev (ms_mem (restrict (w_H W) ms0)) rg_rPers);
    [ unfold region_ok, rg_rPers;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
      rewrite E10, unsigned_lit_small by lia;
      split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val tfibsegs Ev _ p 16 1 (SOff 33 0) (d_dev dsk));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
        apply (VK (p + 16) 1%nat); [lia | lia | lia |];
        pose proof (proj1 (HGP 0%nat ltac:(cbn; lia))) as Hv0; cbn [nth] in Hv0;
        rewrite Z.add_0_r in Hv0; exact Hv0
      | apply (chunk_ok_val tfibsegs Ev _ p 17 1 (SOff 34 0) (d_strips dsk));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
        apply (VK (p + 17) 1%nat); [lia | lia | lia |];
        pose proof (proj1 (HGP 1%nat ltac:(cbn; lia))) as Hv1; cbn [nth] in Hv1;
        replace (p + 17) with (p + 16 + Z.of_nat 1) by lia; exact Hv1 ]
    | ];
    assert (HDJ : all_disjoint Ev rg_rPers (ss_mem ssv));
    [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, rg_rPers;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite B2, E10, unsigned_lit_small by lia;
      split; [lia | exact I]
    | ];
    pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W) ms0) rg_rPers HS eq_refl HRP HDJ) as HS1;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS HRP HDJ; rename HS1 into HS
  end.
  assert (U11 : forall Ev, ew Ev 11 = Z_to_bv 64 (s32 strip mod 2 ^ 64) -> U Ev (SOff 11 0) = s32 strip mod 2 ^ 64)
  by (intros Ev HEv; apply (U_atom Ev 11); [exact HEv | apply rg_s32_rng; lia]).
  assert (E11m : ew E 11 = Z_to_bv 64 (s32 strip mod 2 ^ 64))
  by (rewrite E11; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by lia; reflexivity).
  (* 0x85348-0x85360: the check and the lbu of p->strips, to 0x85364 bgeu strip,strips *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_branch Hb1.
  all: rewrite branch_geu_U in Hb1;
       lazymatch type of Hb1 with context [U ?Ev _] =>
         rewrite (U11 Ev ltac:(rg_ew E11m)) in Hb1;
         rewrite (U_atom Ev 34 (d_strips dsk) ltac:(rg_ew E34) ltac:(lia)) in Hb1 end;
       rewrite (rg_u11_lt strip (d_strips dsk) ltac:(lia) ltac:(lia)) in Hb1.
  + (* taken: p->strips <= strip, the return -11 *)
    apply negb_true_iff, Z.ltb_ge in Hb1.
    assert (HSPEC : ring_spec (Some dsk) strip mask = (E_RANGE, None)) by (apply rg_spec_strips; lia).
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact EIMG) ltac:(intros ? Hz; left; cbv beta in Hz; lia))
      ltac:(idtac; unfold cenc_res; rewrite HSPEC; cbn [fst snd cmd_outZ]; split;
        [ cw_r10 Ra; rewrite Ra; apply rg_denot_lit; reflexivity
        | eapply garr8_frame; [exact HGARR|]; rewrite HLEN; intros a Ha;
          apply (mbyte_of_aview tfibsegs); apply KE; [lia | cbv beta; lia] ]).
  + (* strip < p->strips, so the strip is a byte; 0x85368-0x8536c test bit 15 of the mask *)
    apply negb_false_iff, Z.ltb_lt in Hb1.
    assert (E11s : ew E 11 = Z_to_bv 64 strip).
    { rewrite E11. f_equal. unfold s32. destruct (Z.ltb_spec strip (2 ^ 31)); lia. }
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_branch Hb2.
    all: lazymatch type of Hb2 with context [sv_denot ?Ev _] =>
           rewrite (rg_shl48_lt0 Ev mask ltac:(rg_ew E12) ltac:(lia)) in Hb2 end.
    * (* taken: bit 15 set, the return -11 *)
      apply Z.ltb_lt in Hb2.
      assert (HSPEC : ring_spec (Some dsk) strip mask = (E_RANGE, None)) by (apply rg_spec_mask; lia).
      cw_run cw_awr_stk. cw_keep cw_kwr_stk.
      cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact EIMG) ltac:(intros ? Hz; left; cbv beta in Hz; lia))
        ltac:(idtac; unfold cenc_res; rewrite HSPEC; cbn [fst snd cmd_outZ]; split;
          [ cw_r10 Ra; rewrite Ra; apply rg_denot_lit; reflexivity
          | eapply garr8_frame; [exact HGARR|]; rewrite HLEN; intros a Ha;
            apply (mbyte_of_aview tfibsegs); apply KE; [lia | cbv beta; lia] ]).
    * (* the mask is 15 bits: the seven loop iterations, the three payload bytes, then p->device *)
      apply Z.ltb_ge in Hb2.
      assert (HGO : ring_spec (Some dsk) strip mask =
        with_key (sysex_spec (d_dev dsk) 0 [u8 (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64));
                                            fst (ring_bits mask); snd (ring_bits mask)]) (KEY 3 strip))
      by (apply rg_spec_go; lia).
      rewrite (rg_u8 _ (rg_pl0_range mask strip ltac:(lia))) in HGO.
      cw_run cw_awr_stk. cw_keep cw_kwr_stk.
      cw_branch Hb3.
      all: lazymatch type of Hb3 with context [sv_denot ?Ev _] =>
             rewrite (rg_sx8_lt0 Ev (SOff 33 0) (d_dev dsk)
               ltac:(apply (U_atom Ev 33); [rg_ew E33 | lia]) ltac:(lia)) in Hb3 end.
      -- (* taken: p->device has bit 7 set, the return -1 *)
         apply Z.ltb_lt in Hb3.
         assert (HSPEC : ring_spec (Some dsk) strip mask = (E_ARG, None))
         by (rewrite HGO, (rg_sysex_dev_hi (d_dev dsk) _ ltac:(lia)); reflexivity).
         cw_run cw_awr_stk. cw_keep cw_kwr_stk.
         cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact EIMG) ltac:(intros ? Hz; left; cbv beta in Hz; lia))
           ltac:(idtac; unfold cenc_res; rewrite HSPEC; cbn [fst snd cmd_outZ]; split;
             [ cw_r10 Ra; rewrite Ra; apply rg_denot_lit; reflexivity
             | eapply garr8_frame; [exact HGARR|]; rewrite HLEN; intros a Ha;
               apply (mbyte_of_aview tfibsegs); apply KE; [lia | cbv beta; lia] ]).
      -- (* the device is a seven-bit byte: the three payload bytes are read back from the frame *)
         apply Z.ltb_ge in Hb3.
         cw_run cw_awr_stk. cw_keep cw_kwr_stk.
         cw_branch Hb4.
         all: lazymatch type of Hb4 with context [sv_denot ?Ev _] =>
                rewrite (rg_sx8_lt0 Ev _ (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64))
                  ltac:(apply rg_pl0_val; [rg_ew E12 | rg_ew E11s | lia | lia])
                  ltac:(apply rg_pl0_range; lia)) in Hb4 end.
         ++ (* taken: the first payload byte has bit 7 set, the return -11 *)
            apply Z.ltb_lt in Hb4.
            assert (HSPEC : ring_spec (Some dsk) strip mask = (E_RANGE, None))
            by (rewrite HGO, (rg_sysex_pl0_hi (d_dev dsk) (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64))
                  (fst (ring_bits mask)) (snd (ring_bits mask)) ltac:(lia)
                  ltac:(pose proof (rg_pl0_range mask strip ltac:(lia)); lia)); reflexivity).
            cw_run cw_awr_stk. cw_keep cw_kwr_stk.
            cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact EIMG) ltac:(intros ? Hz; left; cbv beta in Hz; lia))
              ltac:(idtac; unfold cenc_res; rewrite HSPEC; cbn [fst snd cmd_outZ]; split;
                [ cw_r10 Ra; rewrite Ra; apply rg_denot_lit; reflexivity
                | eapply garr8_frame; [exact HGARR|]; rewrite HLEN; intros a Ha;
                  apply (mbyte_of_aview tfibsegs); apply KE; [lia | cbv beta; lia] ]).
         ++ apply Z.ltb_ge in Hb4.
            (* the three payload bytes are seven-bit, so the command is the full one *)
            assert (HPL0 : 0 <= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64) < 128)
            by (pose proof (rg_pl0_range mask strip ltac:(lia)); lia).
            assert (HB1R : 0 <= fst (ring_bits mask) < 128)
            by (rewrite <- (rg_ring_bits_fst E mask E12 ltac:(lia));
                apply (rg_acc_range E mask 62 E12 ltac:(lia) ltac:(lia))).
            assert (HB2R : 0 <= snd (ring_bits mask) < 128)
            by (rewrite <- (rg_ring_bits_snd E mask E12 ltac:(lia));
                apply (rg_acc_range E mask 55 E12 ltac:(lia) ltac:(lia))).
            assert (HSPEC : ring_spec (Some dsk) strip mask =
              (0, Some ([240; 19; d_dev dsk; 0; Z.lor strip (bit_or_0 (Z.testbit mask 0) 64);
                         fst (ring_bits mask); snd (ring_bits mask); 247], KEY 3 strip, 0)))
            by (rewrite HGO, (rg_sysex_ok (d_dev dsk) (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64))
                  (fst (ring_bits mask)) (snd (ring_bits mask)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
                reflexivity).
            (* from here the walk writes out: widen the kept zone to the bytes it stores *)
            lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?mn a = _ =>
              assert (KE1 : forall a, 0 <= a < 2 ^ 64 ->
                ~ ((spZ regs - (48 + ESTACK) <= a < spZ regs) \/ (out <= a < out + 8) \/
                   (out + 24 <= a < out + 26) \/ (out + 28 <= a < out + 32)) ->
                aview tfibsegs (w_H W) mn a = aview tfibsegs (w_H W) memc a)
              by (intros a Ha Hz; apply KE; [exact Ha | intros Hw; apply Hz; left; exact Hw]);
              clear KE; rename KE1 into KE
            end.
            (* the four windows of out the walk stores into *)
            lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?ms0) |- _ =>
              assert (HW : forall o, 0 <= o < 32 ->
                writable_at tfibsegs (ms_mem (restrict (w_H W) ms0)) (out + o));
              [ intros o Ho; cbn [ms_mem restrict]; apply (apresent_writable tfibsegs);
                apply (rg_dst_pres lyc Sc W (ms_mem ms0) _ out 32 (out + o) (proj1 HJ) HTD ltac:(lia))
              | ] end.
            assert (HRA : True) by exact I.
            lazymatch goal with HS : YP0l.st_ok _ ?Ev _ ?msv |- _ =>
              assert (HRD : region_ok tfibsegs Ev (ms_mem msv) rg_rD) by rg_rok HW end.
            rg_add rg_rD HRD.
            lazymatch goal with HS : YP0l.st_ok _ ?Ev _ ?msv |- _ =>
              assert (HRC : region_ok tfibsegs Ev (ms_mem msv) rg_rC) by rg_rok HW end.
            rg_add rg_rC HRC.
            lazymatch goal with HS : YP0l.st_ok _ ?Ev _ ?msv |- _ =>
              assert (HRB : region_ok tfibsegs Ev (ms_mem msv) rg_rB) by rg_rok HW end.
            rg_add rg_rB HRB.
            lazymatch goal with HS : YP0l.st_ok _ ?Ev _ ?msv |- _ =>
              assert (HRA2 : region_ok tfibsegs Ev (ms_mem msv) rg_rA) by rg_rok HW end.
            rg_add rg_rA HRA2.
            (* 0x85400-0x8547c: the four checked stores of out[0..4) and the call of __asan_memcpy *)
            assert (HAband : out + 32 <= 2147450879 \/ 17594333495296 <= out)
            by (unfold amem_range in HAMo; rewrite C3, C5 in HAMo;
                destruct HAMo as [Hb | [Hb _]]; [left | right]; lia).
            cw_run ltac:(idtac; rg_awr HTW). cw_keep rg_kwr.
            (* 0x8547c jal __asan_memcpy(out + 4, sp + 13, 3): the source is the walk's own frame *)
            rename HJ into HJ1.
            rreg HS (2%bv : bv 5) Gsp. rreg HS (3%bv : bv 5) Ggp. rreg HS (4%bv : bv 5) Gtp.
            rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
            rewrite E3 in Ggp. rewrite E4 in Gtp.
            rewrite B13 in Ga0. rewrite B2 in Ga1, Gsp.
            replace (spZ regs + -35) with (spZ regs - 35) in Ga1 by lia.
            replace (spZ regs + -48) with (spZ regs - 48) in Gsp by lia.
            lazymatch type of HS with YP0l.st_ok _ _ _ (restrict _ ?msv) =>
              assert (GSP : spZ (ms_regs msv) = spZ regs - 48)
              by (unfold spZ at 1; rewrite Gsp; apply unsigned_lit_small; lia);
              assert (HSH : range_addressable (aview tfibsegs (w_H W) (ms_mem msv)) SHADOW_OFF (out + 4) 3 /\
                            shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem msv)) (out + 4) 3);
              [ apply (rg_shadow_keep W memc (ms_mem msv) (out + 4) 3); [lia | lia | lia | | | ];
                [ intros s Hs; apply KE;
                  [ unfold SHADOW_OFF in Hs; change (2 ^ 44) with 17592186044416 in Hs; lia
                  | cbv beta; unfold SHADOW_OFF in Hs;
                    change (2 ^ 44) with 17592186044416 in Hs; lia ]
                | intros y Hy; apply HRAo; lia
                | apply (rg_hull_sub _ out 32); [lia | lia | lia | lia | exact (HHo ltac:(lia))] ]
              | ];
              pose proof (cw_stack_src B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msv) _ k
                (spZ regs - 35) 3 LAWS HJ1 ltac:(lia) ltac:(lia) ltac:(lia)) as (Hxam & Hxra & Hxhull & Hxv)
            end.
            pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
            destruct HSH as (HSHa & HSHh).
            (* the three payload bytes the copy reads, in the walk's own frame *)
            lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
              pose proof (st_ok_region_nth Ev ssv (restrict (w_H W) msv) 5 _ HS
                ltac:(vm_compute; reflexivity)) as RSK end.
            cbn [ms_mem restrict] in RSK.
            assert (GP0 : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + -35)
              [Z.lor strip (bit_or_0 (Z.testbit mask 0) 64)]).
            { eapply (rg_byte_of_region _ _ 2%nat (spZ regs));
              [ exact RSK | exact B2 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
              | lazymatch goal with |- U ?Ev _ mod 256 = _ =>
                  rewrite (rg_pl0_val Ev mask strip ltac:(rg_ew E12) ltac:(rg_ew E11s) ltac:(lia) ltac:(lia)) end;
                apply Z.mod_small; apply rg_pl0_range; lia ]. }
            assert (GP1 : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + -34)
              [fst (ring_bits mask)]).
            { eapply (rg_byte_of_region _ _ 2%nat (spZ regs));
              [ exact RSK | exact B2 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
              | lazymatch goal with |- U ?Ev _ mod 256 = _ =>
                  change (U Ev (rg_acc 62) mod 256 = fst (ring_bits mask));
                  pose proof (rg_acc_range Ev mask 62 ltac:(rg_ew E12) ltac:(lia) ltac:(lia)) as HR62;
                  rewrite (rg_ring_bits_fst Ev mask ltac:(rg_ew E12) ltac:(lia)) in HR62 |- * end;
                apply Z.mod_small; lia ]. }
            assert (GP2 : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + -33)
              [snd (ring_bits mask)]).
            { eapply (rg_byte_of_region _ _ 2%nat (spZ regs));
              [ exact RSK | exact B2 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
              | lazymatch goal with |- U ?Ev _ mod 256 = _ =>
                  change (U Ev (rg_acc 55) mod 256 = snd (ring_bits mask));
                  pose proof (rg_acc_range Ev mask 55 ltac:(rg_ew E12) ltac:(lia) ltac:(lia)) as HR55;
                  rewrite (rg_ring_bits_snd Ev mask ltac:(rg_ew E12) ltac:(lia)) in HR55 |- * end;
                apply Z.mod_small; lia ]. }
            lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
              let l := eval vm_compute in (ss_mem ssv) in
              let rsv := eval vm_compute in (firstn 4 l ++ skipn 5 l) in
              eapply (cw_intrin_call B LAWS OCpy CA_MEMCPY AMEMCPY W Ev ssv msv _ STK sp0 FP ly S
                W0 mem0 md0 own lyc Sc k (out + 4) (spZ regs - 35) 3 0x85480 200%nat rsv) end.
            ** exact HS.
            ** vm_compute. reflexivity.
            ** reflexivity.
            ** exact HJ1.
            ** exact Ga0.
            ** exact Ga1.
            ** exact Ga2.
            ** lia.
            ** lia.
            ** lia.
            ** rewrite GSP. lia.
            ** rewrite GSP. lia.
            ** rewrite GSP. rewrite Zminus_mod, Hal16. reflexivity.
            ** exact Hsp0al.
            ** exact Ggp.
            ** exact Gtp.
            ** vm_compute. reflexivity.
            ** lia.
            ** apply ret_ok_even. vm_compute. reflexivity.
            ** intros a Ha. split; [exact (proj1 (HTW a ltac:(lia)))|]. rewrite GSP. lia.
            ** unfold amem_range in HAMo |- *. rewrite C3, C4, C5 in HAMo |- *. lia.
            ** exact HSHa.
            ** intros _. exact HSHh.
            ** split; [lia|]. split; [lia|].
               split; [intros aa Haa; split; [apply Hxv; lia | rewrite GSP; lia]|].
               split; [lia|]. split; [exact Hxam|]. split; [exact Hxra|].
               intros _. exact Hxhull.
            ** vm_compute. reflexivity.
            ** vm_compute. reflexivity.
            ** vm_compute. reflexivity.
            ** vm_compute. reflexivity.
            ** submem_to.
            ** repeat apply Forall_cons; try apply Forall_nil;
               (split; [ intros aa Haa;
                         cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Haa;
                         rewrite ?ew_ewset_other, ?ew_havoc_old in Haa by lia;
                         rewrite ?B2, ?B13 in Haa;
                         rewrite GSP; split; [lia | cbv beta; lia]
                       | cbn [YP09.r_lo YP09.r_wlo YP09.r_whi YP09.r_hi]; split; lia ]).
            ** intros regs2 mem2 md2 HJ2 HP2 Hd2 Heff Hfr Hpres2 Hsm HS2.
               clear HS. rename HS2 into HS. rename HJ2 into HJ.
               assert (KE2 : forall a, 0 <= a < 2 ^ 64 ->
                 ~ ((spZ regs - (48 + ESTACK) <= a < spZ regs) \/ (out <= a < out + 8) \/
                    (out + 24 <= a < out + 26) \/ (out + 28 <= a < out + 32)) ->
                 aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a).
               { intros aa Ha Hz. rewrite Hfr;
                   [ apply KE; [exact Ha | exact Hz]
                   | exact Ha
                   | intros HC; apply Hz; right; left; lia
                   | intros HC; apply Hz; left; rewrite GSP in HC; lia ]. }
               clear KE Hfr. rename KE2 into KE.
               lazymatch type of HS with YP0l.st_ok _ ?En _ _ => remember En as E' eqn:HE' in HS end.
               assert (E1' : ew E' 1 = getr regs 1) by (rewrite HE', ew_havoc_old by lia; exact E1).
               assert (B2' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite HE', ew_havoc_old by lia; exact B2).
               assert (E2z' : ew E' 2 = Z_to_bv 64 (spZ regs)) by (rewrite HE', ew_havoc_old by lia; exact E2z).
               assert (E10' : ew E' 10 = Z_to_bv 64 p) by (rewrite HE', ew_havoc_old by lia; exact E10).
               assert (E11s' : ew E' 11 = Z_to_bv 64 strip) by (rewrite HE', ew_havoc_old by lia; exact E11s).
               assert (E12' : ew E' 12 = Z_to_bv 64 mask) by (rewrite HE', ew_havoc_old by lia; exact E12).
               assert (E13' : ew E' 13 = Z_to_bv 64 out) by (rewrite HE', ew_havoc_old by lia; exact E13).
               assert (B13' : bv_unsigned (ew E' 13) = out) by (rewrite E13'; apply unsigned_lit_small; lia).
               assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite HE', ew_havoc_old by lia; exact E32).
               assert (E33' : ew E' 33 = Z_to_bv 64 (d_dev dsk)) by (rewrite HE', ew_havoc_old by lia; exact E33).
               assert (HAE' : env_agree 32 (Ereg regs (cw_extra xs)) E') by (rewrite HE'; env_agree_chain HAE).
               assert (HSH2 : range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF out 32 /\
                              shadow_hull_vis (aview tfibsegs (w_H W) mem2) out 32).
               { apply (rg_shadow_keep W memc mem2 out 32);
                   [lia | lia | lia | | exact HRAo | exact (HHo ltac:(lia))].
                 intros s Hs. apply KE;
                   [ unfold SHADOW_OFF in Hs; change (2 ^ 44) with 17592186044416 in Hs; lia
                   | cbv beta; unfold SHADOW_OFF in Hs;
                     change (2 ^ 44) with 17592186044416 in Hs; lia ]. }
               clear SHOK.
               assert (SHOK : sh_ok tfibsegs CW_Bx rg_SH E' (mrestrict (w_H W) mem2)).
               { unfold rg_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
                 - exact (cw_shent_ra_off W mem2 E' 10 p 16 4
                     (proj1 (HUSE lyc Sc W mem2 md2 (proj1 HJ))) HAMp
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10' E32').
                 - exact (cw_shent_ra_off W mem2 E' 13 out 0 32
                     ltac:(rewrite Z.add_0_r; exact (proj1 HSH2)) ltac:(rewrite Z.add_0_r; exact HAMo)
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E13' E32'). }
               clear E1 B2 E2z E10 E11 E11s E12 E13 B13 E32 E33 HAE.
               rename E1' into E1. rename B2' into B2. rename E2z' into E2z. rename E10' into E10.
               rename E11s' into E11s. rename E12' into E12. rename E13' into E13.
               rename B13' into B13. rename E32' into E32. rename E33' into E33. rename HAE' into HAE.
               (* the copied bytes out[4..7) stay put over the rest of the walk *)
               assert (KM : forall a, 0 <= a < 2 ^ 64 ->
                 ~ ((spZ regs - (48 + ESTACK) <= a < spZ regs) \/ (out <= a < out + 4) \/
                    (out + 7 <= a < out + 32)) ->
                 aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem2 a) by (intros; reflexivity).
               (* 0x85480-0x85508: out[7], out[24], out[25], the key, a0 = 0, the epilogue, 0x85524 ret *)
               cw_run ltac:(idtac; rg_awr HTW).
               lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
                 pose proof (cw_kept_run _ _ _ _ _ _ _ KM HFr ltac:(rg_kwr)) as KM2;
                 pose proof (cw_kept_run _ _ _ _ _ _ _ KE HFr ltac:(rg_kwr)) as KE3;
                 clear KM KE HFr; rename KM2 into KM; rename KE3 into KE end.
               (* the 32 bytes of the command *)
               lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msF) |- _ =>
                 pose proof (st_ok_region_nth Ev ssv (restrict (w_H W) msF) 0 _ HS
                   ltac:(vm_compute; reflexivity)) as RA;
                 pose proof (st_ok_region_nth Ev ssv (restrict (w_H W) msF) 1 _ HS
                   ltac:(vm_compute; reflexivity)) as RB;
                 pose proof (st_ok_region_nth Ev ssv (restrict (w_H W) msF) 2 _ HS
                   ltac:(vm_compute; reflexivity)) as RC;
                 pose proof (st_ok_region_nth Ev ssv (restrict (w_H W) msF) 3 _ HS
                   ltac:(vm_compute; reflexivity)) as RD;
                 assert (GM : forall i, 0 <= i < 3 ->
                   aview tfibsegs (w_H W) (ms_mem msF) (out + 4 + i) =
                   aview tfibsegs (w_H W) (ms_mem ms1) (spZ regs - 35 + i));
                 [ intros i Hi; rewrite (KM (out + 4 + i) ltac:(lia) ltac:(cbv beta; lia));
                   apply Heff; lia
                 | ]
               end.
               cbn [ms_mem restrict] in RA, RB, RC, RD.
               lazymatch type of RA with YP09.region_ok _ _ ?mF _ =>
                 assert (GA0 : garr8 tfibsegs mF (out + 0) [240])
                 by (eapply (rg_byte_of_region _ _ 13%nat out);
                     [ exact RA | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                     | rewrite U_SLit; vm_compute; reflexivity ]);
                 assert (GA1 : garr8 tfibsegs mF (out + 1) [19])
                 by (eapply (rg_byte_of_region _ _ 13%nat out);
                     [ exact RA | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                     | rewrite U_SLit; vm_compute; reflexivity ]);
                 assert (GA2 : garr8 tfibsegs mF (out + 2) [d_dev dsk])
                 by (eapply (rg_byte_of_region _ _ 13%nat out);
                     [ exact RA | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                     | lazymatch goal with |- U ?Ev _ mod 256 = _ =>
                         rewrite (rg_U_sx8 Ev (SOff 33 0) (d_dev dsk)
                           ltac:(apply (U_atom Ev 33); [exact E33 | lia]) ltac:(lia)) end;
                       apply Z.mod_small; lia ]);
                 assert (GA3 : garr8 tfibsegs mF (out + 3) [0])
                 by (eapply (rg_byte_of_region _ _ 13%nat out);
                     [ exact RA | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                     | rewrite U_SLit; vm_compute; reflexivity ]);
                 assert (GB7 : garr8 tfibsegs mF (out + 7) [247])
                 by (eapply (rg_byte_of_region _ _ 13%nat out);
                     [ exact RB | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                     | rewrite U_SLit; vm_compute; reflexivity ]);
                 assert (GC4 : garr8 tfibsegs mF (out + 24) [8])
                 by (eapply (rg_byte_of_region _ _ 13%nat out);
                     [ exact RC | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                     | rewrite U_SLit; vm_compute; reflexivity ]);
                 assert (GC5 : garr8 tfibsegs mF (out + 25) [0])
                 by (eapply (rg_byte_of_region _ _ 13%nat out);
                     [ exact RC | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                     | rewrite U_SLit; vm_compute; reflexivity ])
               end.
               lazymatch type of RA with YP09.region_ok _ _ ?mF _ =>
                 assert (GD : garr8 tfibsegs mF (out + 28) (le4Z (KEY 3 strip)));
                 [ eapply (rg_region_garr8 _ _ 13%nat out);
                   [ exact RD | exact B13 | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
                   | reflexivity
                   | lazymatch goal with |- forall j, _ -> nth j _ _ = (U ?Ev _ / _) mod _ =>
                       intros j Hj; rewrite (rg_key_val Ev strip ltac:(rg_ew E11s) ltac:(lia)) end;
                     cbn [length] in Hj; destruct j as [|[|[|[|j]]]];
                     [ cbn [nth Z.of_nat le4Z]; rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r; reflexivity
                     | cbn [nth Z.of_nat Pos.of_succ_nat le4Z]; reflexivity
                     | cbn [nth Z.of_nat Pos.of_succ_nat le4Z]; reflexivity
                     | cbn [nth Z.of_nat Pos.of_succ_nat le4Z]; reflexivity
                     | cbn in Hj; lia ] ]
                 | ];
                 assert (GP : garr8 tfibsegs mF (out + 4)
                   [Z.lor strip (bit_or_0 (Z.testbit mask 0) 64); fst (ring_bits mask); snd (ring_bits mask)]);
                 [ intros j Hj; cbn [length] in Hj; destruct j as [|[|[|j]]];
                   [ cbn [nth Z.of_nat]; rewrite Z.add_0_r; split;
                     [ apply (rg_val_mem_move W (ms_mem ms1) _ (spZ regs - 35) (out + 4));
                       [ replace (out + 4) with (out + 4 + 0) by lia;
                         replace (spZ regs - 35) with (spZ regs - 35 + 0) by lia;
                         exact (GM 0 ltac:(lia))
                       | pose proof (proj1 (GP0 0%nat ltac:(cbn; lia))) as V0;
                         replace (spZ regs + -35 + Z.of_nat 0) with (spZ regs - 35) in V0 by (cbn; lia);
                         exact V0 ]
                     | apply rg_pl0_range; lia ]
                   | cbn [nth Z.of_nat Pos.of_succ_nat]; split;
                     [ apply (rg_val_mem_move W (ms_mem ms1) _ (spZ regs - 35 + 1) (out + 4 + 1));
                       [ exact (GM 1 ltac:(lia))
                       | pose proof (proj1 (GP1 0%nat ltac:(cbn; lia))) as V1;
                         replace (spZ regs + -34 + Z.of_nat 0) with (spZ regs - 35 + 1) in V1 by (cbn; lia);
                         exact V1 ]
                     | lia ]
                   | cbn [nth Z.of_nat Pos.of_succ_nat]; split;
                     [ apply (rg_val_mem_move W (ms_mem ms1) _ (spZ regs - 35 + 2) (out + 4 + 2));
                       [ exact (GM 2 ltac:(lia))
                       | pose proof (proj1 (GP2 0%nat ltac:(cbn; lia))) as V2;
                         replace (spZ regs + -33 + Z.of_nat 0) with (spZ regs - 35 + 2) in V2 by (cbn; lia);
                         exact V2 ]
                     | lia ]
                   | cbn in Hj; lia ]
                 | ];
                 assert (G4 : garr8 tfibsegs mF (out + 8) (firstn 16 (skipn 8 before)));
                 [ eapply garr8_frame;
                   [ pose proof (rg_garr8_sub (mrestrict (w_H W) memc) out before 8 16 HGARR
                       ltac:(rewrite HLEN; lia)) as Hsub; cbn [Z.of_nat Pos.of_succ_nat] in Hsub; exact Hsub
                   | intros a Ha; rewrite length_firstn, length_skipn, HLEN in Ha; cbn in Ha;
                     apply (mbyte_of_aview tfibsegs); apply KE; [lia | cbv beta; lia] ]
                 | ];
                 assert (G6 : garr8 tfibsegs mF (out + 26) (firstn 2 (skipn 26 before)));
                 [ eapply garr8_frame;
                   [ pose proof (rg_garr8_sub (mrestrict (w_H W) memc) out before 26 2 HGARR
                       ltac:(rewrite HLEN; lia)) as Hsub; cbn [Z.of_nat Pos.of_succ_nat] in Hsub; exact Hsub
                   | intros a Ha; rewrite length_firstn, length_skipn, HLEN in Ha; cbn in Ha;
                     apply (mbyte_of_aview tfibsegs); apply KE; [lia | cbv beta; lia] ]
                 | ]
               end.
               assert (HL : cmd_outZ before (Some ([240; 19; d_dev dsk; 0;
                   Z.lor strip (bit_or_0 (Z.testbit mask 0) 64); fst (ring_bits mask);
                   snd (ring_bits mask); 247], KEY 3 strip, 0)) =
                 [240] ++ [19] ++ [d_dev dsk] ++ [0] ++
                 [Z.lor strip (bit_or_0 (Z.testbit mask 0) 64); fst (ring_bits mask); snd (ring_bits mask)] ++
                 [247] ++ firstn 16 (skipn 8 before) ++ [8] ++ [0] ++
                 firstn 2 (skipn 26 before) ++ le4Z (KEY 3 strip)).
               { unfold cmd_outZ. cbn [map length Z.of_nat Pos.of_succ_nat].
                 rewrite (firstn_skipn_comm 16 8 before). cbn [Nat.add].
                 rewrite (rg_u8 240 ltac:(lia)), (rg_u8 19 ltac:(lia)), (rg_u8 (d_dev dsk) ltac:(lia)),
                   (rg_u8 0 ltac:(lia)), (rg_u8 (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64)) ltac:(lia)),
                   (rg_u8 (fst (ring_bits mask)) ltac:(lia)), (rg_u8 (snd (ring_bits mask)) ltac:(lia)),
                   (rg_u8 247 ltac:(lia)).
                 rewrite rg_u8 by (cbn; lia).
                 reflexivity. }
               lazymatch type of RA with YP09.region_ok _ _ ?mF _ =>
                 assert (HFIN : garr8 tfibsegs mF out
                   (cmd_outZ before (Some ([240; 19; d_dev dsk; 0;
                     Z.lor strip (bit_or_0 (Z.testbit mask 0) 64); fst (ring_bits mask);
                     snd (ring_bits mask); 247], KEY 3 strip, 0))));
                 [ rewrite HL; repeat (apply (proj2 (garr8_app _ _ _ _ _)); split);
                   rewrite ?length_firstn, ?length_skipn, ?HLEN;
                   cbn [length Nat.min Nat.sub Z.of_nat Pos.of_succ_nat];
                   match goal with |- garr8 _ _ ?b _ =>
                     first [ (try replace b with (out + 0) by lia); exact GA0
                           | (try replace b with (out + 1) by lia); exact GA1
                           | (try replace b with (out + 2) by lia); exact GA2
                           | (try replace b with (out + 3) by lia); exact GA3
                           | (try replace b with (out + 4) by lia); exact GP
                           | (try replace b with (out + 7) by lia); exact GB7
                           | (try replace b with (out + 8) by lia); exact G4
                           | (try replace b with (out + 24) by lia); exact GC4
                           | (try replace b with (out + 25) by lia); exact GC5
                           | (try replace b with (out + 26) by lia); exact G6
                           | (try replace b with (out + 28) by lia); exact GD ] end
                 | ]
               end.
               cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact EIMG)
                   ltac:(intros ? Hz; cbv beta in Hz; destruct Hz as [Hz|[Hz|[Hz|Hz]]];
                         [left | right | right | right]; unfold cenc_wr; lia))
                 ltac:(idtac; unfold cenc_res; rewrite HSPEC; cbn [fst snd]; split;
                       [ cw_r10 Ra0; rewrite Ra0; apply rg_denot_lit; reflexivity
                       | exact HFIN ]).
- (* ======================= the personality is NULL (a0 = 0, the return -1) ======================= *)
  assert (HP0 : p = 0) by exact HPERS.
  pose proof (cw_entry_base B TL LAWS 0x85314 48 (@nil Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (48 + ESTACK) HE ltac:(unfold ESTACK; lia) ltac:(vm_compute; reflexivity)) as HS.
  remember (Ereg regs (cw_extra [])) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx (@nil shent) E (mrestrict (w_H W) memc)) by apply Forall_nil.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - (48 + ESTACK) <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold coff_win in HWINo.
  assert (HSPEC : ring_spec None strip mask = (E_ARG, None)) by reflexivity.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  (* 0x85330 beqz a0: taken, p = 0 *)
  cw_branch Hb0.
  + cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact EIMG) ltac:(intros ? Hz; left; cbv beta in Hz; lia))
      ltac:(idtac; unfold cenc_res; rewrite HSPEC; cbn [fst snd cmd_outZ]; split;
        [ cw_r10 Ra; rewrite Ra;
          apply rg_denot_lit; reflexivity
        | eapply garr8_frame; [exact HGARR|]; rewrite HLEN; intros a Ha;
          apply (mbyte_of_aview tfibsegs); apply KE; [lia | cbv beta; lia] ]).
  + exfalso. rewrite branch_eq_U, (U_atom E 10 p E10 ltac:(lia)), U_lit in Hb0 by lia.
    rewrite HP0, Z.eqb_refl in Hb0. discriminate Hb0.
Qed.
End d.
End b.
