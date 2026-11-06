(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths changed; 453 of its 506 lines of code are new or changed and 528 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_scribble_encode_A_lib.v; 307 of its 380 lines of code are new or changed and 433 lines of the source are left out. *)
(* The arithmetic of diginet_ring_encode's walk at image B (0x85c1c), against lib/AU/Prog/CPgEncU.v's
   cdcU_ring_specX: the seven loop iterations and the two loop bytes against ring_bits, the first payload byte,
   the key, the branch conditions (p->strips, bit 15 of the mask), the two alignment tests of the UBSan checks
   (p and out), and the shapes of ring_spec. Image-independent: nothing here names an address or a core file;
   the forms are the symbolic values the engine leaves (lib/A/Prog/diginet_ring_encode_A.v has the same
   instruction sequences at image A). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the arithmetic of the body ================================ *)
Lemma rgb_u8 : forall x, 0 <= x < 256 -> u8 x = x.
Proof. intros x Hx. unfold u8. apply Z.mod_small. exact Hx. Qed.
Lemma rgb_lor_lt : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
assert (E : Z.lor a b = Z.land (Z.lor a b) (Z.ones n)).
{ rewrite Z.land_lor_distr_l, !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
rewrite E, Z.land_ones by lia.
pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as P.
pose proof (Z.mod_pos_bound (Z.lor a b) (2 ^ n) P). lia.
Qed.
(* `srai x, x, 63` of a 64-bit value, read back unsigned: all ones when its bit 63 is set *)
Lemma rgb_sar63 : forall v, 0 <= v < 2 ^ 64 ->
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
Lemma rgb_pick : forall E mask k s c, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
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
  unfold zcanon, M64. rewrite <- Bz. apply rgb_sar63.
  pose proof (Z.mod_pos_bound (Z.shiftl (Z.shiftr mask k) s) (2 ^ 64) ltac:(lia)). lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Uz, U_lit by lia.
destruct (Z.testbit mask (63 - s + k)).
- replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
  rewrite Z.land_comm, Z.land_ones by lia. unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
- rewrite Z.land_0_l. reflexivity.
Qed.
(* the seven iterations, as the engine leaves them, against ring_bits *)
Definition rgb_t (k s c : Z) : sv :=
SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SAluw ALU_SRL (SOff 12 0) (SLit k)) (SLit s)) (SLit 63)) (SLit c).
Definition rgb_acc (s : Z) : sv :=
SAlu ALU_OR (rgb_t 6 s 1) (SAlu ALU_OR (rgb_t 5 s 2) (SAlu ALU_OR (rgb_t 4 s 4) (SAlu ALU_OR (rgb_t 3 s 8)
(SAlu ALU_OR (rgb_t 2 s 16) (SAlu ALU_OR (rgb_t 1 s 32) (SAlu ALU_OR (rgb_t 0 s 64) (SLit 0))))))).
Lemma rgb_lor7 : forall a0 a1 a2 a3 a4 a5 a6,
Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor 0 a0) a1) a2) a3) a4) a5) a6
= Z.lor a6 (Z.lor a5 (Z.lor a4 (Z.lor a3 (Z.lor a2 (Z.lor a1 (Z.lor a0 0)))))).
Proof.
intros a0 a1 a2 a3 a4 a5 a6. apply Z.bits_inj'. intros n Hn.
rewrite !Z.lor_spec, !Z.bits_0.
destruct (Z.testbit a0 n), (Z.testbit a1 n), (Z.testbit a2 n), (Z.testbit a3 n),
(Z.testbit a4 n), (Z.testbit a5 n), (Z.testbit a6 n); reflexivity.
Qed.
Lemma rgb_U_or : forall E a b va vb, U E a = va -> U E b = vb -> 0 <= va < 128 -> 0 <= vb < 128 ->
U E (SAlu ALU_OR a b) = Z.lor va vb /\ 0 <= Z.lor va vb < 128.
Proof.
intros E a b va vb Ha Hb Hva Hvb.
assert (Hr : 0 <= Z.lor va vb < 128) by (change 128 with (2 ^ 7); apply rgb_lor_lt; cbn; lia).
split; [|exact Hr].
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rgb_t_rng : forall E mask k s c, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
0 <= k <= 6 -> 1 <= s <= 63 -> 0 <= c <= 64 ->
U E (rgb_t k s c) = (if Z.testbit mask (63 - s + k) then c else 0)
/\ 0 <= (if Z.testbit mask (63 - s + k) then c else 0) < 128.
Proof.
intros E mask k s c Hm Hmr Hk Hs Hc. unfold rgb_t.
rewrite (rgb_pick E mask k s c Hm Hmr Hk Hs ltac:(lia)).
split; [reflexivity | destruct (Z.testbit mask (63 - s + k)); lia].
Qed.
Lemma rgb_acc_ok : forall E mask s off, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
1 <= s <= 63 -> off = 63 - s ->
U E (rgb_acc s) =
fold_left (fun b k => Z.lor b (bit_or_0 (Z.testbit mask (off + k)) (2 ^ (6 - k)))) (map Z.of_nat (seq 0 7)) 0
/\ 0 <= U E (rgb_acc s) < 128.
Proof.
intros E mask s off Hm Hmr Hs ->.
destruct (rgb_t_rng E mask 0 s 64 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V0 R0].
destruct (rgb_t_rng E mask 1 s 32 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V1 R1].
destruct (rgb_t_rng E mask 2 s 16 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V2 R2].
destruct (rgb_t_rng E mask 3 s 8 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V3 R3].
destruct (rgb_t_rng E mask 4 s 4 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V4 R4].
destruct (rgb_t_rng E mask 5 s 2 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V5 R5].
destruct (rgb_t_rng E mask 6 s 1 Hm Hmr ltac:(lia) Hs ltac:(lia)) as [V6 R6].
assert (Z0 : U E (SLit 0) = 0) by (apply U_lit; lia).
destruct (rgb_U_or E _ _ _ _ V0 Z0 R0 ltac:(lia)) as [P0 Q0].
destruct (rgb_U_or E _ _ _ _ V1 P0 R1 Q0) as [P1 Q1].
destruct (rgb_U_or E _ _ _ _ V2 P1 R2 Q1) as [P2 Q2].
destruct (rgb_U_or E _ _ _ _ V3 P2 R3 Q2) as [P3 Q3].
destruct (rgb_U_or E _ _ _ _ V4 P3 R4 Q3) as [P4 Q4].
destruct (rgb_U_or E _ _ _ _ V5 P4 R5 Q4) as [P5 Q5].
destruct (rgb_U_or E _ _ _ _ V6 P5 R6 Q5) as [P6 Q6].
unfold rgb_acc. rewrite P6. split; [|exact Q6].
cbn [map seq fold_left]. unfold bit_or_0.
change (2 ^ (6 - 0)) with 64. change (2 ^ (6 - 1)) with 32. change (2 ^ (6 - 2)) with 16.
change (2 ^ (6 - 3)) with 8. change (2 ^ (6 - 4)) with 4. change (2 ^ (6 - 5)) with 2.
change (2 ^ (6 - 6)) with 1.
symmetry. apply rgb_lor7.
Qed.
Lemma rgb_acc_range : forall E mask s, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 -> 1 <= s <= 63 ->
0 <= U E (rgb_acc s) < 128.
Proof.
intros E mask s Hm Hmr Hs. exact (proj2 (rgb_acc_ok E mask s (63 - s) Hm Hmr Hs eq_refl)).
Qed.
Lemma rgb_ring_bits_fst : forall E mask, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
U E (rgb_acc 62) = fst (ring_bits mask).
Proof.
intros E mask Hm Hmr. rewrite (proj1 (rgb_acc_ok E mask 62 1 Hm Hmr ltac:(lia) ltac:(lia))).
unfold ring_bits. cbn [map seq fold_left]. reflexivity.
Qed.
Lemma rgb_ring_bits_snd : forall E mask, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
U E (rgb_acc 55) = snd (ring_bits mask).
Proof.
intros E mask Hm Hmr. rewrite (proj1 (rgb_acc_ok E mask 55 8 Hm Hmr ltac:(lia) ltac:(lia))).
unfold ring_bits. cbn [map seq fold_left]. reflexivity.
Qed.
(* `slli a2,a2,63; srli a2,a2,57; or a2,a2,a1`: the first payload byte *)
Lemma rgb_pl0_val : forall E mask strip, ew E 12 = Z_to_bv 64 mask -> ew E 11 = Z_to_bv 64 strip ->
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
{ change 256 with (2 ^ 8). apply rgb_lor_lt; [lia | change (2 ^ 8) with 256; lia |].
  unfold bit_or_0. destruct (Z.testbit mask 0); change (2 ^ 8) with 256; lia. }
rewrite Z.lor_comm. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rgb_pl0_range : forall mask strip, 0 <= strip < 256 ->
0 <= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64) < 256.
Proof.
intros mask strip Hs. change 256 with (2 ^ 8). apply rgb_lor_lt; [lia | change (2 ^ 8) with 256; lia|].
unfold bit_or_0. destruct (Z.testbit mask 0); change (2 ^ 8) with 256; lia.
Qed.
(* `slli s0,s0,48; srli s0,s0,48; lui a2,0x30; or a2,s0,a2`: the key *)
Lemma rgb_key_val : forall E strip, ew E 11 = Z_to_bv 64 strip -> 0 <= strip < 256 ->
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
assert (0 <= Z.lor strip 196608 < 2 ^ 18) by (apply rgb_lor_lt; cbn; lia). lia.
Qed.
(* the failing returns and the success of ring_spec *)
Lemma rgb_spec_strips : forall d strip mask, d_strips d <= strip -> ring_spec (Some d) strip mask = (E_RANGE, None).
Proof.
intros d strip mask H. unfold ring_spec.
replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma rgb_spec_mask : forall d strip mask, 0 <= mask -> 32768 <= mask -> ring_spec (Some d) strip mask = (E_RANGE, None).
Proof.
intros d strip mask H0 H. unfold ring_spec.
replace (Z.shiftr mask 15 =? 0) with false.
- cbn [negb]. rewrite orb_true_r. reflexivity.
- symmetry. apply Z.eqb_neq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 15) with 32768.
  intro E. Z.div_mod_to_equations. lia.
Qed.
Lemma rgb_spec_go : forall d strip mask, strip < d_strips d -> 0 <= mask < 32768 ->
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
Lemma rgb_tb7_lo : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof.
intros x Hx. pose proof (Z.testbit_spec' x 7 ltac:(lia)) as Bt.
rewrite Z.div_small in Bt by (cbn; lia). destruct (Z.testbit x 7); [discriminate Bt | reflexivity].
Qed.


(* ================================ reading bytes off the walk's regions ================================ *)
Lemma rgb_denot_lit : forall E z v, z mod 2 ^ 64 = v mod 2 ^ 64 -> sv_denot E (SLit z) = w64 v.
Proof.
intros E z v H. rewrite denot_lit_U, U_SLit. unfold w64, zcanon, M64.
apply Z_to_bv64_eq_mod. rewrite Z.mod_mod by lia. exact H.
Qed.
Lemma rgb_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r. unfold zcanon, M64.
rewrite Z.mod_small by apply u64_range. apply Z_to_bv_bv_unsigned.
Qed.
(* ================================ the branch conditions ================================ *)
Lemma rgb_denot_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n c v H Hv. rewrite denot_lit_U, U_SOff, H, unsigned_lit_small by lia.
unfold w64, zcanon, M64. apply Z_to_bv64_eq_mod. apply Z.mod_mod. lia.
Qed.
Lemma rgb_br_lt : forall E a b,
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (bv_swrap 64 (U E a) <? bv_swrap 64 (U E b)).
Proof. intros E a b. reflexivity. Qed.
Lemma rgb_swrap_pos : forall v, 0 <= v < 2 ^ 63 -> bv_swrap 64 v = v.
Proof.
intros v Hv. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma rgb_swrap_neg : forall v, 2 ^ 63 <= v < 2 ^ 64 -> bv_swrap 64 v = v - 2 ^ 64.
Proof.
intros v Hv. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
replace (v + 2 ^ 63) with ((v - 2 ^ 63) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
rewrite Z.mod_small by lia. lia.
Qed.
(* `lb` of a byte, then `bltz`: taken exactly when the byte has bit 7 set *)
Lemma rgb_sx8_lt0 : forall E e v, U E e = v -> 0 <= v < 256 ->
branch_taken BC_LT (sv_denot E (SExt true 8 e)) (sv_denot E (SLit 0)) = (127 <? v).
Proof.
intros E e v Hv Hr. rewrite rgb_br_lt.
assert (HL : U E (SLit 0) = 0) by (apply U_lit; lia). rewrite HL.
rewrite (rgb_swrap_pos 0) by lia.
rewrite U_SExt. cbv iota beta. rewrite Hv.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small v 256) by lia.
assert (Hs8 : bv_swrap 8 v = if v <? 128 then v else v - 256).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  destruct (Z.ltb_spec v 128).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (v + 128) (-1) 256) by lia. rewrite Z.mod_small by lia. lia. }
rewrite Hs8. unfold zcanon, M64.
destruct (Z.ltb_spec v 128) as [Hl|Hl].
- rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite rgb_swrap_pos by lia.
  destruct (Z.ltb_spec v 0); destruct (Z.ltb_spec 127 v); first [reflexivity | lia].
- replace ((v - 256) mod 2 ^ 64) with (v - 256 + 2 ^ 64)
  by (rewrite <- (Z.mod_add (v - 256) 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite rgb_swrap_neg by lia.
  destruct (Z.ltb_spec (v - 256 + 2 ^ 64 - 2 ^ 64) 0); destruct (Z.ltb_spec 127 v); first [reflexivity | lia].
Qed.
(* `slli a2,a2,48; bltz`: taken exactly when bit 15 of the mask is set *)
Lemma rgb_shl48_lt0 : forall E mask, ew E 12 = Z_to_bv 64 mask -> 0 <= mask < 65536 ->
branch_taken BC_LT (sv_denot E (SAlu ALU_SLL (SOff 12 0) (SLit 48))) (sv_denot E (SLit 0)) = (32767 <? mask).
Proof.
intros E mask Hm Hr. rewrite rgb_br_lt.
assert (HL : U E (SLit 0) = 0) by (apply U_lit; lia). rewrite HL.
rewrite (rgb_swrap_pos 0) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 12 mask Hm) by lia. rewrite U_lit by lia.
replace (Z.land 48 63) with 48 by reflexivity.
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
change (2 ^ 48) with 281474976710656 in *. change (2 ^ 64) with 18446744073709551616 in *.
rewrite (Z.mod_small (mask * 281474976710656)) by lia.
destruct (Z.ltb_spec 32767 mask) as [Hl|Hl].
- rewrite rgb_swrap_neg by (change (2 ^ 63) with 9223372036854775808; change (2 ^ 64) with 18446744073709551616; lia).
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.ltb_spec (mask * 281474976710656 - 18446744073709551616) 0); [reflexivity | lia].
- rewrite rgb_swrap_pos by (change (2 ^ 63) with 9223372036854775808; lia).
  destruct (Z.ltb_spec (mask * 281474976710656) 0); [lia | reflexivity].
Qed.
(* a1 = the strip as the caller passes it (sign-extended from bit 31), against a byte-sized bound *)
Lemma rgb_s32_rng : forall strip, 0 <= strip < 2 ^ 32 -> 0 <= s32 strip mod 2 ^ 64 < 2 ^ 64.
Proof. intros strip Hs. apply Z.mod_pos_bound. lia. Qed.
Lemma rgb_u11_lt : forall strip strips, 0 <= strip < 2 ^ 32 -> 0 <= strips < 256 ->
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

(* ================================ the two alignment tests of the UBSan checks ================================ *)
(* `andi x, a, 7` of an 8-aligned value and `andi x, a, 3` of a 4-aligned one are 0 *)
Lemma rgb_and_al : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k <= 6 -> v mod 2 ^ k = 0 ->
U E (SAlu ALU_AND (SOff n 0) (SLit (2 ^ k - 1))) = 0.
Proof.
intros E n v k Hn Hv Hk Hm.
assert (Hk2 : 0 < 2 ^ k <= 64) by (split; [apply Z.pow_pos_nonneg; lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
rewrite U_and_lit by lia. rewrite (U_atom E n v Hn Hv).
replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
rewrite Z.land_ones by lia. exact Hm.
Qed.
Lemma rgb_and7 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v mod 8 = 0 ->
U E (SAlu ALU_AND (SOff n 0) (SLit 7)) = 0.
Proof. intros E n v Hn Hv Hm. exact (rgb_and_al E n v 3 Hn Hv ltac:(lia) Hm). Qed.
Lemma rgb_and3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v mod 4 = 0 ->
U E (SAlu ALU_AND (SOff n 0) (SLit 3)) = 0.
Proof. intros E n v Hn Hv Hm. exact (rgb_and_al E n v 2 Hn Hv ltac:(lia) Hm). Qed.

(* ================================ diginet_sysex_encode's result ================================ *)
(* a failure without a command, or rc 0 with key 0 and at most 24 bytes *)
Lemma rgb_sysex_shape : forall dev fn pl,
(exists rc, sysex_spec dev fn pl = (rc, None) /\ -11 <= rc <= -1) \/
(exists bs dp, sysex_spec dev fn pl = (0, Some (bs, 0, dp)) /\ (length bs <= 24)%nat).
Proof.
intros dev fn pl. unfold sysex_spec.
destruct (0x7f <? dev); [left; eexists; split; [reflexivity | unfold E_ARG; lia]|].
destruct (fn =? 0x70); [left; eexists; split; [reflexivity | unfold E_REFUSED; lia]|].
destruct (0x7f <? fn); [left; eexists; split; [reflexivity | unfold E_RANGE; lia]|].
destruct (24 <? Z.of_nat (length pl) + 5) eqn:Hl; [left; eexists; split; [reflexivity | unfold E_SPACE; lia]|].
destruct (existsb (fun x => Z.testbit x 7) pl); [left; eexists; split; [reflexivity | unfold E_RANGE; lia]|].
right. do 2 eexists. split; [reflexivity|]. apply Z.ltb_ge in Hl.
rewrite app_length, app_length. cbn [length]. lia.
Qed.
Lemma rgb_with_key_none : forall rc k, with_key (rc, None) k = (rc, None).
Proof. intros [|q|q] k; reflexivity. Qed.
(* the command bytes of a success with the key replaced: the first 28 bytes, then the key's four *)
Lemma rgb_cmd_key : forall before bs dp k0 k, length before = 32%nat -> (length bs <= 24)%nat ->
cmd_outZ before (Some (bs, k, dp)) = firstn 28 (cmd_outZ before (Some (bs, k0, dp))) ++ le4Z k.
Proof.
intros before bs dp k0 k Hb Hs. unfold cmd_outZ.
set (P := map u8 bs ++ skipn (length bs) (firstn 24 before) ++ [u8 (Z.of_nat (length bs)); u8 dp] ++ firstn 2 (skipn 26 before)).
assert (LP : length P = 28%nat)
  by (unfold P; rewrite !app_length, map_length, skipn_length, !firstn_length, skipn_length; cbn [length]; lia).
assert (E : forall K, map u8 bs ++ skipn (length bs) (firstn 24 before) ++ [u8 (Z.of_nat (length bs)); u8 dp] ++
  firstn 2 (skipn 26 before) ++ le4Z K = P ++ le4Z K)
  by (intros K; unfold P; rewrite <- !app_assoc; reflexivity).
rewrite !E. rewrite firstn_app, LP, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.
Lemma rgb_cmd_len : forall before bs k dp, length before = 32%nat -> (length bs <= 24)%nat ->
length (cmd_outZ before (Some (bs, k, dp))) = 32%nat.
Proof.
intros before bs k dp Hb Hs. unfold cmd_outZ.
rewrite !app_length, map_length, skipn_length, !firstn_length, skipn_length. unfold le4Z. cbn [length]. lia.
Qed.
