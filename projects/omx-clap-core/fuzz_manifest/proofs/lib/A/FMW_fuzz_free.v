(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v, with its module paths and module names changed; 684 of its 733 lines of code are new or changed and 450 lines of the source are left out. *)
(* fuzz_free 0x81a78..0x81b94 (alloc.c:107-116, disown :51-59 inlined), 71 instructions, frame 32. p = 0 returns;
   else __asan_unpoison_memory_region (p - 16, 16) at 0x81aac, the two inline checks of the head's 8-byte load
   (0x81ab0, 0x81ac4: one shadow byte, 0 after the unpoisoning), g_live -= n (0x81b24 / 0x81b38), the epilogue, and the
   tail jump `j __wrap_free` at 0x81b54 with a0 = p - 16. Control-flow template: fm's plain lib/Prog/fuzz_free.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05 YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AF0x AE2y ACeg ACej.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMpoisonS FMW_fuzz_alloc_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* fuzz_free's code: 0x81a78 .. 0x81b94 (fm-fn-measure.md section 1) *)
Definition tbl_ff : ctable := Eval vm_compute in build_table tfibsegs A_fuzz_free 71 TEmpty.
Lemma tbl_ff_eq : tbl_ff = build_table tfibsegs A_fuzz_free 71 TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_ff). Qed.
Lemma tbl_ff_ok : table_ok tfibsegs tbl_ff.
Proof. rewrite tbl_ff_eq. apply build_table_ok0. unfold A_fuzz_free. lia. Qed.

Lemma STK_fuzz_free_eq : STK_fuzz_free = 32 + ASTACK.
Proof. reflexivity. Qed.

(* the frame: ra@sp-8, s0@sp-16, s1@sp-24, s2@sp-32 *)
Definition R_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition ss_ff0 : sstate := mkSS A_fuzz_free sr_atoms [R_stk] None (mkFacts [] [] []).

(* p <> 0. Atoms: 10 = p, 32 = SHADOW_OFF, 33 = n (the head), 34 = live, 35 = SHADOW_OFF + p / 8. The shadow-base GOT
   slot 0x999b0 -> 0xa1d78 (TfibLib tl_got_shadow / tl_shadow_cell); the head's 8 bytes at p - 16; g_live. The alias
   ((p >> 3) + SHADOW_OFF = atom 35) lets the shadow loads of the two checks resolve (YP0i shadow_norm). *)
Definition R_got : YP09.region := YP09.mkRegion None 0x999b0 0x999b8 0 0 [YP09.mkChunk 0x999b0 (CVal 8 (SLit 0xa1d78))].
Definition R_head : YP09.region := YP09.mkRegion (Some 10%nat) (-16) (-8) 0 0 [YP09.mkChunk (-16) (CVal 8 (SOff 33 0))].
Definition ff_alias : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0), SOff 35 0).
Definition F_ff1 : facts := mkFacts [(10%nat, mkAF 4112 0x7fffff800000 4)] [] [ff_alias].
Definition ss_ff1 : sstate :=
  mkSS A_fuzz_free sr_atoms [R_stk; R_got; fm_rcell 0xa1d78 32; R_head; fm_wcell G_LIVE 34] None F_ff1.
(* after the call: the frame read-only (the rest of the walk only reads it back), the head's shadow byte (0 after the
   unpoisoning) at atom 35 - 2 = shadow_addr (p - 16) *)
Definition R_stkA : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 0 0
  [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition R_sh : YP09.region := YP09.mkRegion (Some 35%nat) (-2) (-1) 0 0 [YP09.mkChunk (-2) (CVal 1 (SLit 0))].
Definition rs_ffA : smem := [R_stkA; R_got; fm_rcell 0xa1d78 32; R_head; fm_wcell G_LIVE 34].

(* the head's 8 bytes, read back by 8 `lbu` and or-ed together (0x81ad4 .. 0x81b30), as the walk computes them *)
Definition ffb0 : sv := SExt false 8 (SOff 33 0).
Definition ffb (k : Z) : sv := SExt false 8 (SAlu ALU_SRL (SOff 33 0) (SLit k)).
Definition ffq (a b c d : sv) : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL d (SLit 24)) (SAlu ALU_SLL c (SLit 16))) (SAlu ALU_OR (SAlu ALU_SLL b (SLit 8)) a).
Definition ff_nexpr : sv :=
  SAlu ALU_OR (SAlu ALU_SLL (ffq (ffb 32) (ffb 40) (ffb 48) (ffb 56)) (SLit 32)) (ffq ffb0 (ffb 8) (ffb 16) (ffb 24)).

Lemma ff_lor_shl : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof.
intros a b k Hk Ha Hb.
assert (Hd : Z.land (a * 2 ^ k) b = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec. destruct (Z_lt_le_dec i k) as [Hi|Hi].
  - destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
    rewrite <- Z.shiftl_mul_pow2 by exact Hk. rewrite Z.shiftl_spec_low by exact Hi. reflexivity.
  - rewrite <- (Z.mod_small b (2 ^ k)) by exact Hb. rewrite Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r. }
rewrite <- (Z.lxor_lor _ _ Hd). rewrite <- (Z.add_nocarry_lxor _ _ Hd). reflexivity.
Qed.

Lemma ff_U_b : forall E n k, ew E 33 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> 0 < k < 64 -> U E (ffb k) = n / 2 ^ k mod 256.
Proof.
intros E n k Hn Hr Hk. unfold ffb. rewrite U_zext, U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 33 n Hn Hr).
rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity | change (2 ^ 6) with 64; lia]).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as P.
assert (D : 0 <= n / 2 ^ k <= n).
{ split; [apply Z.div_pos; lia|]. rewrite <- (Z.div_1_r n) at 2. apply Z.div_le_compat_l; lia. }
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

Lemma ff_U_b0 : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> U E ffb0 = n mod 256.
Proof. intros E n Hn Hr. unfold ffb0. rewrite U_zext, (U_atom E 33 n Hn Hr). reflexivity. Qed.

Lemma ff_U_sll : forall E x v k, U E x = v -> 0 <= v -> 0 <= k < 64 -> v * 2 ^ k < 2 ^ 64 ->
  U E (SAlu ALU_SLL x (SLit k)) = v * 2 ^ k.
Proof.
intros E x v k Hx Hv Hk Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, U_SLit, (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity | change (2 ^ 6) with 64; lia]).
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). split; [apply Z.mul_nonneg_nonneg; lia | exact Hb].
Qed.

Lemma ff_U_or : forall E x y w vy k, U E x = w * 2 ^ k -> U E y = vy -> 0 <= k -> 0 <= w -> 0 <= vy < 2 ^ k ->
  w * 2 ^ k + vy < 2 ^ 64 -> U E (SAlu ALU_OR x y) = w * 2 ^ k + vy.
Proof.
intros E x y w vy k Hx Hy Hk Hw Hvy Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy, ff_lor_shl by lia.
apply zcanon_id. unfold M64.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). pose proof (Z.mul_nonneg_nonneg w (2 ^ k) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma ff_U_q : forall E a b c d va vb vc vd, U E a = va -> U E b = vb -> U E c = vc -> U E d = vd ->
  0 <= va < 256 -> 0 <= vb < 256 -> 0 <= vc < 256 -> 0 <= vd < 256 ->
  U E (ffq a b c d) = va + 256 * vb + 65536 * vc + 16777216 * vd.
Proof.
intros E a b c d va vb vc vd Ha Hb Hc Hd Ra Rb Rc Rd. unfold ffq.
assert (HD : U E (SAlu ALU_SLL d (SLit 24)) = vd * 2 ^ 24) by (apply ff_U_sll; lia).
assert (HC : U E (SAlu ALU_SLL c (SLit 16)) = vc * 2 ^ 16) by (apply ff_U_sll; lia).
assert (HB' : U E (SAlu ALU_SLL b (SLit 8)) = vb * 2 ^ 8) by (apply ff_U_sll; lia).
assert (HL : U E (SAlu ALU_OR (SAlu ALU_SLL d (SLit 24)) (SAlu ALU_SLL c (SLit 16))) = vd * 2 ^ 24 + vc * 2 ^ 16)
  by (apply (ff_U_or E _ _ vd (vc * 2 ^ 16) 24); [exact HD | exact HC | lia | lia | lia | lia]).
assert (HR : U E (SAlu ALU_OR (SAlu ALU_SLL b (SLit 8)) a) = vb * 2 ^ 8 + va)
  by (apply (ff_U_or E _ _ vb va 8); [exact HB' | exact Ha | lia | lia | lia | lia]).
rewrite (ff_U_or E _ _ (vd * 2 ^ 8 + vc) (vb * 2 ^ 8 + va) 16); [lia | rewrite HL; lia | exact HR | lia | lia | lia | lia].
Qed.

Lemma ff_divstep : forall n a b, 0 < a -> b = a * 256 -> n / a = 256 * (n / b) + n / a mod 256.
Proof. intros n a b Ha ->. rewrite (Z.div_mod (n / a) 256) at 1 by lia. rewrite Z.div_div by lia. reflexivity. Qed.

Lemma ff_bytes8 : forall n, 0 <= n < 2 ^ 64 ->
  (n / 2 ^ 32 mod 256 + 256 * (n / 2 ^ 40 mod 256) + 65536 * (n / 2 ^ 48 mod 256) + 16777216 * (n / 2 ^ 56 mod 256)) * 2 ^ 32 +
  (n mod 256 + 256 * (n / 2 ^ 8 mod 256) + 65536 * (n / 2 ^ 16 mod 256) + 16777216 * (n / 2 ^ 24 mod 256)) = n.
Proof.
intros n Hn.
pose proof (Z.div_mod n 256 ltac:(lia)) as D0. change 256 with (2 ^ 8) in D0 at 2.
pose proof (ff_divstep n (2 ^ 8) (2 ^ 16) ltac:(lia) eq_refl) as D1.
pose proof (ff_divstep n (2 ^ 16) (2 ^ 24) ltac:(lia) eq_refl) as D2.
pose proof (ff_divstep n (2 ^ 24) (2 ^ 32) ltac:(lia) eq_refl) as D3.
pose proof (ff_divstep n (2 ^ 32) (2 ^ 40) ltac:(lia) eq_refl) as D4.
pose proof (ff_divstep n (2 ^ 40) (2 ^ 48) ltac:(lia) eq_refl) as D5.
pose proof (ff_divstep n (2 ^ 48) (2 ^ 56) ltac:(lia) eq_refl) as D6.
pose proof (ff_divstep n (2 ^ 56) (2 ^ 64) ltac:(lia) eq_refl) as D7.
assert (D8 : n / 2 ^ 64 = 0) by (apply Z.div_small; lia).
set (b0 := n mod 256) in *. set (b1 := n / 2 ^ 8 mod 256) in *. set (b2 := n / 2 ^ 16 mod 256) in *.
set (b3 := n / 2 ^ 24 mod 256) in *. set (b4 := n / 2 ^ 32 mod 256) in *. set (b5 := n / 2 ^ 40 mod 256) in *.
set (b6 := n / 2 ^ 48 mod 256) in *. set (b7 := n / 2 ^ 56 mod 256) in *.
set (d1 := n / 2 ^ 8) in *. set (d2 := n / 2 ^ 16) in *. set (d3 := n / 2 ^ 24) in *. set (d4 := n / 2 ^ 32) in *.
set (d5 := n / 2 ^ 40) in *. set (d6 := n / 2 ^ 48) in *. set (d7 := n / 2 ^ 56) in *. set (d8 := n / 2 ^ 64) in *.
clearbody b0 b1 b2 b3 b4 b5 b6 b7 d1 d2 d3 d4 d5 d6 d7 d8.
change (2 ^ 32) with 4294967296. lia.
Qed.

Lemma ff_U_nexpr : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> U E ff_nexpr = n.
Proof.
intros E n Hn Hr.
assert (M : forall z, 0 <= z mod 256 < 256) by (intros z; apply Z.mod_pos_bound; lia).
assert (QL : U E (ffq ffb0 (ffb 8) (ffb 16) (ffb 24)) =
  n mod 256 + 256 * (n / 2 ^ 8 mod 256) + 65536 * (n / 2 ^ 16 mod 256) + 16777216 * (n / 2 ^ 24 mod 256)).
{ apply ff_U_q; [apply ff_U_b0 | apply ff_U_b | apply ff_U_b | apply ff_U_b | | | |]; try exact Hn; try exact Hr; try lia; apply M. }
assert (QH : U E (ffq (ffb 32) (ffb 40) (ffb 48) (ffb 56)) =
  n / 2 ^ 32 mod 256 + 256 * (n / 2 ^ 40 mod 256) + 65536 * (n / 2 ^ 48 mod 256) + 16777216 * (n / 2 ^ 56 mod 256)).
{ apply ff_U_q; [apply ff_U_b | apply ff_U_b | apply ff_U_b | apply ff_U_b | | | |]; try exact Hn; try exact Hr; try lia; apply M. }
pose proof (ff_bytes8 n Hr) as BY.
pose proof (M n) as M0. pose proof (M (n / 2 ^ 8)) as M1. pose proof (M (n / 2 ^ 16)) as M2. pose proof (M (n / 2 ^ 24)) as M3.
pose proof (M (n / 2 ^ 32)) as M4. pose proof (M (n / 2 ^ 40)) as M5. pose proof (M (n / 2 ^ 48)) as M6. pose proof (M (n / 2 ^ 56)) as M7.
set (b0 := n mod 256) in *. set (b1 := n / 2 ^ 8 mod 256) in *. set (b2 := n / 2 ^ 16 mod 256) in *.
set (b3 := n / 2 ^ 24 mod 256) in *. set (b4 := n / 2 ^ 32 mod 256) in *. set (b5 := n / 2 ^ 40 mod 256) in *.
set (b6 := n / 2 ^ 48 mod 256) in *. set (b7 := n / 2 ^ 56 mod 256) in *.
clearbody b0 b1 b2 b3 b4 b5 b6 b7. clear M.
unfold ff_nexpr.
change (2 ^ 32) with 4294967296 in BY |- *.
rewrite (ff_U_or E _ _ (b4 + 256 * b5 + 65536 * b6 + 16777216 * b7) (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) 32).
- exact BY.
- change (2 ^ 32) with 4294967296. apply ff_U_sll; [exact QH | lia | lia | change (2 ^ 32) with 4294967296; lia].
- exact QL.
- lia.
- lia.
- change (2 ^ 32) with 4294967296. lia.
- change (2 ^ 32) with 4294967296. lia.
Qed.

(* g_live - n, the value the walk stores at 0x81b38 *)
Lemma ff_U_live : forall E n live, ew E 33 = Z_to_bv 64 n -> ew E 34 = Z_to_bv 64 live -> 0 <= n <= live -> live < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SUB (SOff 34 0) ff_nexpr) = Z_to_bv 64 (live - n).
Proof.
intros E n live Hn Hl Hr Hl64. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (ff_U_nexpr E n Hn ltac:(lia)), (U_atom E 34 live Hl ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* fuzz/alloc.c's statics keep their values when no byte below lo changes *)
Lemma ff_glob_kept : forall (W : world tfibsegs) mem mem' live peak cnt fail lo,
  fm_glob tfibsegs W mem live peak cnt fail -> 0x5f7000 <= lo ->
  (forall x : word, bv_unsigned x < lo -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  fm_glob tfibsegs W mem' live peak cnt fail.
Proof.
intros W mem mem' live peak cnt fail lo (GL & GP & GC & GF & R) Hlo Hk.
assert (K : forall g, g + 8 <= 0x5f7000 -> 0 <= g -> forall i, 0 <= i < Z.of_nat 8 ->
  aview tfibsegs (w_H W) mem' (g + i) = aview tfibsegs (w_H W) mem (g + i)).
{ intros g Hg Hg0 i Hi. cbn in Hi. apply aview_eq_of. apply Hk. rewrite unsigned_lit_small by lia. lia. }
split; [|split; [|split; [|split]]].
- eapply val_mem_kept; [exact GL|]. apply K; unfold G_LIVE; lia.
- eapply val_mem_kept; [exact GP|]. apply K; unfold G_PEAK; lia.
- eapply val_mem_kept; [exact GC|]. apply K; unfold G_COUNT; lia.
- eapply val_mem_kept; [exact GF|]. apply K; unfold G_FAIL; lia.
- exact R.
Qed.

(* a run whose only writable window is the frame [sp - 32, sp) keeps every other byte *)
Lemma ff_frame_stk : forall E (rs : smem) (m m' : word -> option byte) sp,
  frame_of E rs m m' -> bv_unsigned (ew E 2) = sp ->
  (forall t, In t (windows rs) -> t = (Some 2%nat, -32, 0) \/ snd t <= snd (fst t)) ->
  forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> m' x = m x.
Proof.
intros E rs m m' sp HF Hsp Hw x Hx. apply HF. intros Hin.
pose proof (in_wrange_single E rs (bv_unsigned x) 2 (-32) 0 sp Hw Hsp Hin). lia.
Qed.

(* only the head's two shadow bytes differ between mem and unpoison [(h, 16)] mem *)
Lemma ff_unp_out : forall h (mem : word -> option byte) (w : word),
  ~ (shadow_addr h <= bv_unsigned w < shadow_addr h + 2) -> unpoison [(h, 16)] mem w = mem w.
Proof.
intros h mem w Hw. unfold unpoison. rewrite in_ush_cons16.
replace (in_ush [] (bv_unsigned w)) with false by reflexivity.
destruct (Z.leb_spec (shadow_addr h) (bv_unsigned w)); destruct (Z.ltb_spec (bv_unsigned w) (shadow_addr h + 2));
  cbn; try reflexivity; lia.
Qed.

(* a byte above the image that reads the same and was present stays present *)
Lemma ff_apresent_kept : forall (H : word -> bool) (m m' : word -> option byte) a,
  AF0x.TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H m' a = aview tfibsegs H m a -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Ha Hv (Hh & b & Hb). split; [exact Hh|].
unfold aview, mbyte, mrestrict in Hv. rewrite Hh, Hb in Hv.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
rewrite (AF0x.seg_rom_none_high a Ha) in Hv. discriminate Hv.
Qed.

(* AR survives a change that reads the same outside present stack bytes and keeps the hidden band bytes *)
Lemma ff_AR_stack : forall ly S W (m m' : word -> option byte) md md' lo hi,
  AR tfibsegs B ly S W m md -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  (forall a, lo <= a < hi -> apresent (w_H W) m' a) ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> m' (w64 a) = m (w64 a)) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  AR tfibsegs B ly S W m' md'.
Proof.
intros ly S W m m' md md' lo hi HAR Hlo Hhi AV Hpr Hband E1 E2 E3.
apply (al_frame _ _ LAWS ly S W m md m' md' HAR); [| | exact E1 | exact E2 | exact E3 | exact Hband].
- intros a Ha Ho. apply AV; [exact Ha|]. intros Hc. exact (al_stack _ _ LAWS ly S W m md a HAR ltac:(lia) Ho).
- intros a Hv. rewrite (AE2y.aview_mod _ m' a). rewrite (AE2y.aview_mod _ m a) in Hv.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  set (a' := a mod 2 ^ 64) in *.
  destruct (Z_le_gt_dec lo a') as [L1|L1]; [destruct (Z_lt_ge_dec a' hi) as [L2|L2]|].
  + apply aview_some_of_apresent. apply Hpr. lia.
  + rewrite AV by lia. exact Hv.
  + rewrite AV by lia. exact Hv.
Qed.

(* a writable byte above the image is present *)
Lemma ff_apresent_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
  kLowMemEnd <= a < 2 ^ 64 -> writable_at tfibsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hw.
assert (Hn : ~ in_img tfibsegs a) by (intros Hi; pose proof (fma_segs_low a Hi); lia).
unfold apresent. unfold writable_at, wview, mrestrict in Hw.
rewrite unsigned_lit_small in Hw by (unfold kLowMemEnd in Ha; lia). rewrite (find_segment_none a Hn) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
try rewrite Eb in Hw. exfalso. apply Hw. reflexivity.
Qed.

(* two memories that hold the same value at a0 read the same there *)
Lemma ff_aview_of_val_mem : forall (H : word -> bool) (m m' : word -> option byte) a0 (n : nat) v i,
  val_mem tfibsegs (mrestrict H m) a0 n v -> val_mem tfibsegs (mrestrict H m') a0 n v -> 0 <= i < Z.of_nat n ->
  aview tfibsegs H m' (a0 + i) = aview tfibsegs H m (a0 + i).
Proof.
intros H m m' a0 n v i Hv Hv' Hi. unfold aview.
rewrite <- (Z2Nat.id i ltac:(lia)). rewrite (Hv (Z.to_nat i) ltac:(lia)), (Hv' (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.

(* the head's shadow bytes are the only ones U = [(h, 16)] covers *)
Lemma ff_in_ush1 : forall h s, in_ush [(h, 16)] s = true -> shadow_addr h <= s < shadow_addr h + 2.
Proof.
intros h s Hs. rewrite in_ush_cons16 in Hs. replace (in_ush [] s) with false in Hs by reflexivity.
rewrite Bool.orb_false_r in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* a read-only region keeps its bytes when they read the same *)
Lemma ff_region_kept_ro : forall E (H : word -> bool) (m m' : word -> option byte) r,
  YP09.r_whi r <= YP09.r_wlo r ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     aview tfibsegs H m' a = aview tfibsegs H m a) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H m') r.
Proof.
intros E H m m' r Hro Hk. split.
- intros a Ha. apply mbyte_of_aview. apply Hk. exact Ha.
- intros a Ha. lia.
Qed.

(* the journal of a walk that used its stack window and wrote one alloc.c static g whose bytes are in FP (G1's
   ajournal_pstat1, FMW_fuzz_alloc_base.v, for any FP and a model that changed by an aos_step) *)
Lemma ff_journal : forall STK FP ly S (W : world tfibsegs) regs mem md ch mem' md' g,
  afn_pre tfibsegs B STK ly S W regs mem md ch ->
  In (g, g + 8) FM_PSTAT_FP -> (forall a, g <= a < g + 8 -> inFP FP a) ->
  AR tfibsegs B ly S W mem' md' -> aos_step FP md md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> ~ (g <= a < g + 8) ->
     aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem' a) ->
  ajournal tfibsegs B STK (spZ regs) FP ly S W mem md [] ly S W mem' md' 0.
Proof.
intros STK FP ly S W regs mem md ch mem' md' g HPRE Hg HgFP HAR' Haos Heq Hpres'.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HAR as (M & L & _).
pose proof (am_layout B ly S _ M) as HLY.
pose proof (lo_stk_ceil ly HLY) as LSC.
pose proof (AF0x.img_cover_of_ledger _ _ _ L) as [IC1 IC2]. unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in IC1, IC2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fm_pstat_range g Hg) as [Hg1 Hg2].
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
assert (HNOG : forall a, 4096 <= a < ASAN_CEIL -> ~ (spZ regs - STK <= a < spZ regs)).
{ intros a Ha Hs. unfold ASAN_CEIL in Ha. lia. }
assert (HGEX : forall a, ~ inFP FP a -> ~ (g <= a < g + 8)).
{ intros a Hp Hgc. exact (Hp (HgFP a Hgc)). }
assert (HIMG : forall a, ~ in_img tfibsegs a -> ~ (g <= a < g + 8)).
{ intros a Hn Hgc. apply Hn. apply fma_in_img. lia. }
split; [exact HAR'|].
split; [apply layout_le_refl|].
split; [apply Nat.le_refl|].
split; [apply wle_refl|].
split; [exact Haos|].
split; [reflexivity|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha Hs. apply Heq; [lia | exact Hs | intros Hgc; lia]. }
split.
{ intros p n i H1 H2 Hi Hnf.
  destruct (al_blocks _ _ LAWS ly S W mem' md' p n HAR' H1) as (_ & H4096 & Hpc & Happ & _ & _).
  pose proof (app_addr_below_ceil (p + i) (in_app_addr p (req_size n) (p + i) Happ ltac:(lia))) as Hab.
  destruct (al_client_img _ _ LAWS ly S W mem' md' (p + i) HAR'
    ltac:(left; exists p, n; split; [exact H1 | lia])) as [_ Hni].
  apply Heq; [unfold ASAN_CEIL in Hab; lia | exact (HNOG _ Hab) | exact (HIMG _ Hni)]. }
split.
{ intros a Hi Hns He Hps Hsp.
  pose proof (fma_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  apply Heq; [lia | intros Hs; lia | exact (HGEX _ Hps)]. }
split.
{ intros cid pos a Hin Hr Hnf.
  destruct (al_frames _ _ LAWS ly S W mem' md' cid pos HAR' Hin) as (_ & Happ & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  assert (Hfa : 4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= ASAN_CEIL).
  { destruct Happ as [Hf0 [Hf1 | [Hf1 Hf2]]]; cbv [ASAN_CEIL kLowShadowBeg] in *; lia. }
  destruct Hr as [Hr | Hr].
  - unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    pose proof (app_addr_below_ceil a (in_app_addr (frame_addr ly cid pos) (fs_frame_bytes cid) a Happ ltac:(lia))) as Hab.
    destruct (al_client_img _ _ LAWS ly S W mem' md' a HAR'
      ltac:(right; left; exists cid, pos; split; [exact Hin | lia])) as [_ Hni].
    apply Heq; [unfold ASAN_CEIL in Hab; lia | exact (HNOG _ Hab) | exact (HIMG _ Hni)].
  - unfold in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(cbv [ASAN_CEIL] in Hfa; lia)) as [Hs1 Hs2].
    assert (Hfb8 : 0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid).
    { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
    cbv [kLowMemEnd kHighShadowEnd ASAN_CEIL] in *.
    apply Heq; [lia | intros Hs; lia | intros Hgc; lia]. }
split.
{ intros p n i H1 H2 Hi. exfalso. exact (H2 H1). }
split; [exact Hpres'|].
split; [exact Hstk|].
split; [|exact HQT].
intros a Hex He.
pose proof (lo_extra ly HLY) as (_ & HEF & HED).
apply Exists_exists in Hex as (e & Hin & Hr). unfold in_zr in Hr.
pose proof (proj1 (Forall_forall _ _) HEF e Hin) as (_ & Hpos & H4096 & Hce & _).
assert (Hdisj : zdisjoint e (ly_img ly)).
{ apply (pairwise_cross zdisjoint (ly_extra ly) (static_extents ly) e (ly_img ly) HED Hin).
  unfold static_extents. apply in_or_app. right. right. left. reflexivity. }
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
apply Heq; [unfold ASAN_CEIL in Hce; lia | intros Hs; unfold ASAN_CEIL in Hce; lia | intros Hgc; lia].
Qed.

(* an alloc.c static survives a callee that keeps the non-owned image bytes (acall_kept's image clause) *)
Lemma ff_static_kept : TfibSyms B -> forall (W W' : world tfibsegs) (m m' : word -> option byte) g v,
  In (g, g + 8) FM_PSTAT_FP ->
  (forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v.
Proof.
intros HB W W' m m' g v Hg Himg Hv. pose proof (fm_pstat_range g Hg) as [Hg1 Hg2].
eapply YCbq.val_mem_kept; [|exact Hv]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
apply Himg; [apply fma_in_img; lia | | rewrite (ts_errno B HB); unfold TFIB_ERRNO].
- cbv [FM_PSTAT_FP] in Hg. cbn in Hg.
  destruct Hg as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; subst g.
  + apply (fma_not_owned_static B 0x9df80 0x9df88 _ HB); [vm_compute; reflexivity | lia].
  + apply (fma_not_owned_static B 0x5d4400 0x5d4408 _ HB); [vm_compute; reflexivity | lia].
  + apply (fma_not_owned_static B 0x5d4420 0x5d4428 _ HB); [vm_compute; reflexivity | lia].
  + apply (fma_not_owned_static B 0x5d4440 0x5d4448 _ HB); [vm_compute; reflexivity | lia].
- cbv [FM_PSTAT_FP] in Hg. cbn in Hg.
  destruct Hg as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; subst g; lia.
Qed.

(* p = 0: the prologue, `beqz a0` taken, the epilogue, `ret` *)
Lemma ff_null : forall ly S W regs mem md ch live peak cnt fail,
  getr regs 10 = w64 0 -> fm_glob tfibsegs W mem live peak cnt fail ->
  afn_pre tfibsegs B STK_fuzz_free ly S W regs mem md ch ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_free regs mem md)
    (fpost tfibsegs B STK_fuzz_free [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       ablocks B ly' S' = ablocks B ly S /\ fm_glob tfibsegs W' mem' live peak cnt fail)).
Proof.
intros ly S W regs mem md ch live peak cnt fail H10 HGL HAN.
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_fuzz_free_eq as FFS. unfold ASTACK in FFS.
pose proof fma_wx as Hwx. pose proof fma_segs_low as Hsl. pose proof LAWS as HL.
pose proof HGL as (GL & GP & GC & GF & Hlp & Hp64 & Hc64 & Hf64).
remember (Ereg regs []) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs [] 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Ereg_nat regs [] 10 10%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HS : st_ok tfibsegs E ss_ff0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_fuzz_free) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply entry_st_ok.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (spZ regs) (-32)).
    + rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). reflexivity.
    + lia.
    + lia.
    + intros a Ha. apply apresent_writable. apply Hpres. lia.
  - cbn. split; exact I.
  - constructor. }
pose proof (ajournal_init tfibsegs B STK_fuzz_free [] ly S W regs mem md ch HAN) as HJ.
unfold cfg_at. change (w64 A_fuzz_free) with (Z_to_bv 64 A_fuzz_free).
aj_run tbl_ff_ok HS HJ.
{ awr_ok_tac. exact Usp. }
pose proof (ff_frame_stk _ _ _ _ _ HFr Usp) as OUT1.
specialize (OUT1 ltac:(intros t Ht; vm_compute in Ht; repeat (destruct Ht as [<-|Ht]; [left; reflexivity|]); destruct Ht)).
clear HF HFr HG.
srr_branch_with tbl_ff_ok HS.
- (* a0 = 0: `beqz` taken *)
  aj_run tbl_ff_ok HS HJ.
  { awr_ok_tac. exact Usp. }
  pose proof (ff_frame_stk _ _ _ _ _ HFr Usp) as OUT2.
  specialize (OUT2 ltac:(intros t Ht; vm_compute in Ht; repeat (destruct Ht as [<-|Ht]; [left; reflexivity|]); destruct Ht)).
  clear HF HFr HG.
  eapply (SRr_ret_at tfibsegs tbl_ff tbl_ff_ok Hwx W E); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat2. rewrite ?wvb_collapse.
  rreg HS (1%bv : bv 5) R1.
  pose proof (ajournal_materialize tfibsegs B LAWS fma_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ) as HJ2.
  rewrite ?wvb_collapse in HJ2.
  unfold fpost, apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst _ _ (ms_mem ?m) _) ?d = _ /\ _ =>
    exists ly, S, (ms_regs m), (ms_mem m), d end.
  split; [rewrite R1, E1, Hra; reflexivity|].
  split; [exact HJ2|].
  split; [eapply aregs_preserved_of_st_ok; [exact HS | rewrite HE; apply env_agree_refl | vm_compute; reflexivity]|].
  split; [reflexivity|].
  apply (ff_glob_kept W mem _ live peak cnt fail (spZ regs - 32) HGL); [lia|].
  intros x Hx. cbn [ms_mem mkst] in OUT1, OUT2.
  rewrite OUT2 by lia. apply OUT1. lia.
- (* a0 <> 0 contradicts p = 0 *)
  exfalso. rewrite branch_eq_U in Hc.
  rewrite (U_atom E 10 0) in Hc; [| rewrite E10, H10; reflexivity | lia].
  rewrite U_lit in Hc by lia. discriminate Hc.
Qed.

(* p <> 0 *)
Section m.
Hypothesis HB : TfibSyms B.
Hypothesis TL : TfibLib B.
Hypothesis UNIV : fm_univ B.
Hypothesis UNP : aunpoison16_realizes tfibsegs B PC_unpoison.
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.

Lemma ff_main : forall ly S W regs mem md ch p n live peak cnt fail,
  In (raZ regs :: spine ch) CTX_fuzz_free -> getr regs 10 = w64 p ->
  fm_glob tfibsegs W mem live peak cnt fail -> p <> 0 ->
  afn_preU tfibsegs B STK_fuzz_free ly S [(p - HEAD, HEAD)] W regs mem md ch ->
  fm_rblock tfibsegs B ly S W mem p n -> n <= live -> st_nev S + 1 <= EV_MAX ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_free regs mem md)
    (apost_baseU tfibsegs B STK_fuzz_free (ablocks_fp [(p - HEAD, n + HEAD)] ++ FM_PSTAT_FP) regs ly S W mem md 1
       [(p - HEAD, HEAD)] []
       (fun ly' S' W' regs' mem' md' =>
          (exists l1 l2, ablocks B ly S = l1 ++ (p - HEAD, n + HEAD) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
          fm_glob tfibsegs W' mem' (live - n) peak cnt fail)).
Proof.
intros ly S W regs mem md ch p n live peak cnt fail HCTX H10 HGL Hp0 (HAN & HUOK & HUP) (Hblk & Hp16 & Hn0 & Hhead) Hnl Hev.
unfold HEAD in *.
set (mem0 := unpoison [(p - 16, 16)] mem) in *.
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_fuzz_free_eq as FFS. unfold ASTACK in FFS.
pose proof fma_wx as Hwx. pose proof fma_segs_low as Hsl. pose proof LAWS as HL.
pose proof HGL as (GL & GP & GC & GF & Hlp & Hp64 & Hc64 & Hf64).
destruct (al_blocks _ _ LAWS ly S W mem0 md (p - 16) (n + 16) HAR Hblk) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbmax).
assert (Hreq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hreq in Hbceil, Hbapp, Hbpres.
assert (Hp8 : p = 8 * (p / 8)) by (apply Z.mod_divide in Hp16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((2 * k) * 8) by lia; rewrite Z.div_mul by lia; lia).
assert (Hsh : shadow_addr (p - 16) = SHADOW_OFF + p / 8 - 2).
{ unfold shadow_addr. rewrite Hp8 at 1. replace (8 * (p / 8) - 16) with ((p / 8 - 2) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (Hpapp : p - 16 + (n + 16) <= kLowShadowBeg \/ kHighMemBeg <= p - 16) by (unfold in_app in Hbapp; lia).
unfold kLowShadowBeg, SHADOW_OFF in *.
(* where mem and mem0 differ: the two shadow bytes of the head *)
assert (AV0 : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (p - 16) <= a < shadow_addr (p - 16) + 2) ->
  aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a).
{ intros a Ha Hc. apply aview_eq_of. unfold mrestrict, mem0. rewrite ff_unp_out; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hc. }
assert (PR0 : forall a, spZ regs - STK_fuzz_free <= a < spZ regs -> apresent (w_H W) mem a).
{ intros a Ha. destruct (Hpres a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mem0 in Hb.
  rewrite ff_unp_out in Hb; [exact Hb|]. rewrite unsigned_lit_small by lia. rewrite Hsh. lia. }
destruct (al_const _ _ LAWS ly S W mem0 md HAR) as (Kcell & _ & Kgot & _).
rewrite (tl_got_shadow B TL), (tl_shadow_cell B TL) in Kgot. rewrite (tl_shadow_cell B TL) in Kcell.
unfold A_GOT_shadow, A_shadow_glob, SHADOW_OFF in Kgot, Kcell.
assert (VGOT : val_mem tfibsegs (mrestrict (w_H W) mem) 0x999b0 8 0xa1d78).
{ eapply val_mem_kept; [exact (val_mem_of_rdword _ _ _ _ Kgot)|]. intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply AV0; [lia|]. rewrite Hsh. lia. }
assert (VCELL : val_mem tfibsegs (mrestrict (w_H W) mem) 0xa1d78 8 0x7fff8000).
{ eapply val_mem_kept; [exact (val_mem_of_rdword _ _ _ _ Kcell)|]. intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply AV0; [lia|]. rewrite Hsh. lia. }
(* the head is not in the image *)
assert (NI0 : ~ (0x99000 <= p - 16 < 0x5f7000)).
{ intros Hc. destruct (al_client_img _ _ LAWS ly S W mem0 md (p - 16) HAR ltac:(left; exists (p - 16), (n + 16); split; [exact Hblk | rewrite Hreq; lia])) as [_ Hni].
  exact (Hni (fma_in_img _ Hc)). }
assert (NI7 : ~ (0x99000 <= p - 9 < 0x5f7000)).
{ intros Hc. destruct (al_client_img _ _ LAWS ly S W mem0 md (p - 9) HAR ltac:(left; exists (p - 16), (n + 16); split; [exact Hblk | rewrite Hreq; lia])) as [_ Hni].
  exact (Hni (fma_in_img _ Hc)). }
remember (Ereg regs [w64 0x7fff8000; w64 n; w64 live; w64 (0x7fff8000 + p / 8)]) as E eqn:HE.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) by (intros i r Hi; subst E; exact (ew_Ereg_nat _ _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E1. pose proof (EE 2%nat (2%bv : bv 5) eq_refl) as E2.
pose proof (EE 3%nat (3%bv : bv 5) eq_refl) as E3. pose proof (EE 4%nat (4%bv : bv 5) eq_refl) as E4.
pose proof (EE 8%nat (8%bv : bv 5) eq_refl) as E8. pose proof (EE 10%nat (10%bv : bv 5) eq_refl) as E10.
assert (E32 : ew E 32 = w64 0x7fff8000) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 n) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 live) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (0x7fff8000 + p / 8)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
rewrite H10 in E10.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Up : bv_unsigned (ew E 10) = p) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok tfibsegs E ss_ff1 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_fuzz_free) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [| | | | | apply Forall_nil].
    + apply (region_ok_stack tfibsegs _ _ 2 (spZ regs) (-32)); [exact Usp | lia | lia |].
      intros a Ha. apply apresent_writable. apply PR0. lia.
    + unfold region_ok, R_got. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ 0 0x999b0 8 (SLit 0xa1d78) 0xa1d78); [reflexivity | cbn; lia | cbn; lia | exact VGOT].
    + apply (region_ok_fm_rcell _ _ 0xa1d78 32 0x7fff8000); [exact VCELL | exact E32 | lia | lia | lia].
    + unfold region_ok, R_head. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Up. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ p (-16) 8 (SOff 33 0) n); [| cbn; lia | cbn; lia | replace (p + -16) with (p - 16) by lia; exact Hhead].
      cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    + apply (region_ok_fm_wcell _ _ G_LIVE 34 live); [exact GL | exact E34 | lia | unfold G_LIVE; lia | unfold G_LIVE; lia].
  - cbn. repeat split; try exact I; unfold extent_disjoint, R_stk, R_got, R_head, fm_rcell, fm_wcell, G_LIVE;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?Usp, ?Up; lia.
  - split; [|split; [exact I|split; [|exact I]]].
    + cbn [f_atoms F_ff1 atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Up. change (2 ^ 4) with 16. lia.
    + apply (shadow_decl_ok _ 10 32 35 p 0x7fff8000); [exact E10 | lia | exact E32 | exact E35]. }
unfold cfg_at. change (w64 A_fuzz_free) with (Z_to_bv 64 A_fuzz_free).
srr_run_with tbl_ff_ok HS.
(* at the `jal` to __asan_unpoison_memory_region: the frame holds ra, s0, s1, s2; g_live is still live *)
assert (WIN1 : forall a, in_wrange E (ss_mem ss_ff1) a -> spZ regs - 32 <= a < spZ regs \/ G_LIVE <= a < G_LIVE + 8).
{ intros a (r & Hr & Ha). cbn [ss_mem ss_ff1 In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [R_stk R_got R_head fm_rcell fm_wcell YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?Usp in Ha; lia. }
assert (RAW1 : forall x : word, ~ (spZ regs - 32 <= bv_unsigned x < spZ regs) -> ~ (G_LIVE <= bv_unsigned x < G_LIVE + 8) ->
  ms_mem ms x = mem x).
{ intros x Hx1 Hx2. apply HF. intros Hin. destruct (WIN1 _ Hin); tauto. }
clear HF.
assert (VL1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) G_LIVE 8 live).
{ eapply (val_mem_of_chunk8 E _ (ss_mem _) 4%nat G_LIVE (SOff 34 0) live);
  [ exact (st_ok_mem_ok E _ (w_H W) ms HS) | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite E34; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
  | lia ]. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hc. destruct (Z_le_gt_dec G_LIVE a) as [L1|L1]; [destruct (Z_lt_ge_dec a (G_LIVE + 8)) as [L2|L2]|].
  - replace a with (G_LIVE + (a - G_LIVE)) by lia. apply (ff_aview_of_val_mem _ _ _ G_LIVE 8 live); [exact GL | exact VL1 | cbn; lia].
  - apply aview_eq_of. unfold mrestrict. rewrite RAW1; [reflexivity | rewrite unsigned_lit_small by lia; exact Hc | rewrite unsigned_lit_small by lia; lia].
  - apply aview_eq_of. unfold mrestrict. rewrite RAW1; [reflexivity | rewrite unsigned_lit_small by lia; exact Hc | rewrite unsigned_lit_small by lia; lia]. }
assert (PRS1 : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) (ms_mem ms) a).
{ intros a Ha. pose proof (st_ok_mem_ok E _ (w_H W) ms HS) as (_ & Hrs & _).
  apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp in Hw.
  specialize (Hw (a - spZ regs) ltac:(lia)). replace (spZ regs + (a - spZ regs)) with a in Hw by lia.
  apply ff_apresent_of_writable; [lia | exact Hw]. }
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
rreg HS (8%bv : bv 5) R8.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *. set (md1 := with_vm_backing (m_vm_lazy md) mat md).
assert (Hsp1 : spZ regs1 = spZ regs - 32).
{ unfold spZ at 1. rewrite R2, Usp, unsigned_lit_small by lia. reflexivity. }
assert (SHB : 0x7fff8000 + p / 8 - 2 + 2 <= alloc_ceiling) by lia.
pose proof (same_but_materialized_frame md md1 (with_vm_backing_same md mat)) as MF.
rewrite Hshape. change (Z_to_bv 64 345140) with (w64 PC_unpoison).
change (mkCfg (mkst regs1 (w64 PC_unpoison) mem1 (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs PC_unpoison regs1 mem1 md1).
eapply SRr_bind.
{ apply (UNP ly S [] W regs1 mem1 md1 (p - 16) (p - 16) (n + 16)).
  - split; [|split].
    + split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      * apply (ff_AR_stack ly S W mem0 (unpoison [(p - 16, 16)] mem1) md md1 (spZ regs - 32) (spZ regs) HAR); [lia | lia | | | | apply MF | apply MF | apply MF].
        -- intros a Ha Hc. destruct (in_ush [(p - 16, 16)] (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
           ++ apply aview_unpoison_in. exact Ei.
           ++ unfold mem0. rewrite !aview_unpoison_out by exact Ei.
              apply AV1; [exact Ha | exact Hc].
        -- intros a Ha. destruct (PRS1 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
           rewrite ff_unp_out; [exact Hb|]. rewrite unsigned_lit_small by lia. rewrite Hsh. lia.
        -- intros a Hb Hh. unfold mem0, unpoison. destruct (in_ush [(p - 16, 16)] (bv_unsigned (w64 a))); [reflexivity|].
           unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb.
           apply RAW1; unfold w64; rewrite unsigned_lit_small by lia; unfold G_LIVE; lia.
      * rewrite R1. vm_compute. reflexivity.
      * rewrite Hsp1. replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
      * rewrite Hsp1. unfold ESTACK. lia.
      * rewrite Hsp1. lia.
      * intros a Ha. rewrite Hsp1 in Ha. unfold ESTACK in Ha. destruct (PR0 a ltac:(lia)) as [Hh [b Hb]].
        split; [exact Hh|]. exists b. rewrite ff_unp_out; [|rewrite unsigned_lit_small by lia; rewrite Hsh; lia].
        unfold mem1. rewrite RAW1; [exact Hb | rewrite unsigned_lit_small by lia; lia | rewrite unsigned_lit_small by lia; unfold G_LIVE; lia].
      * rewrite R3, E3. exact Hgp.
      * rewrite R4, E4. exact Htp.
    + exact HUOK.
    + intros s Hs. pose proof (ff_in_ush1 _ _ Hs) as Hs2. rewrite Hsh in Hs2.
      rewrite AV1 by lia. exact (HUP s Hs).
  - rewrite R10, Up. unfold w64. f_equal; lia.
  - rewrite R11. reflexivity.
  - exact Hblk.
  - lia.
  - rewrite Hreq. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HARU2 & HP2 & Hsbm2 & Sh0 & Sh1 & Hfr2 & Hpres2 & _).
assert (Hra1 : raZ regs1 = 0x81ab0) by (unfold raZ; rewrite R1; reflexivity).
rewrite Hra1. unfold cfg_at.
(* back at 0x81ab0: s0 = p - 16, s1 = p, s2 = SHADOW_OFF, sp = entry sp - 32; the frame and the cells kept *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs - 32) ->
  ~ (0x7fff8000 + p / 8 - 2 <= a < 0x7fff8000 + p / 8) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem1 a).
{ intros a Ha H1 H2. apply Hfr2; [exact Ha | rewrite Hsp1; unfold PO_WIN; lia | rewrite Hsh; lia]. }
pose proof (st_ok_after_call tfibsegs 36 E _ _ regs2 (mrestrict (w_H W) mem2) rs_ffA 0x81ab0 HS eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(cbn [ss_mem]; unfold rs_ffA, R_stkA;
        apply submem_keep; [split; [reflexivity | cbn; split; [lia | split; [lia | split; [left; lia | intros c Hc; exact Hc]]]]|];
        repeat (apply submem_keep; [apply subregion_refl|]); apply submem_nil)
  ltac:(vm_compute; reflexivity) HP2) as HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ unfold rs_ffA. cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | apply Forall_nil].
  - apply ff_region_kept_ro; [cbn; lia|]. intros a Ha. cbn [R_stkA YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply KEEP2; lia.
  - apply ff_region_kept_ro; [cbn; lia|]. intros a Ha. cbn [R_got YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    apply KEEP2; lia.
  - apply ff_region_kept_ro; [cbn; lia|]. intros a Ha. cbn [fm_rcell YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    apply KEEP2; lia.
  - apply ff_region_kept_ro; [cbn; lia|]. intros a Ha. cbn [R_head YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Up in Ha.
    apply KEEP2; lia.
  - split.
    + intros a Ha. cbn [fm_wcell YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. apply mbyte_of_aview. apply KEEP2; unfold G_LIVE in Ha; lia.
    + intros a Ha _. cbn [fm_wcell YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. apply fma_rw. unfold G_LIVE in Ha; lia. }
rewrite <- restrict_mkst_fx in HS2.
remember (havoc E 36 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS2.
assert (OLD2 : forall i, (i < 36)%nat -> ew Eb i = ew E i) by (intros i Hi; rewrite HEb; apply ew_havoc_old; exact Hi).
assert (F35 : bv_unsigned (ew Eb 35) = 0x7fff8000 + p / 8) by (rewrite OLD2 by lia; rewrite E35; unfold w64; apply unsigned_lit_small; lia).
assert (Usp2 : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (Up2 : bv_unsigned (ew Eb 10) = p) by (rewrite OLD2 by lia; exact Up).
(* the head's shadow byte, 0 after the unpoisoning *)
assert (ROK : region_ok tfibsegs Eb (mrestrict (w_H W) mem2) R_sh).
{ unfold region_ok, R_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite F35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ _ (-2) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
  intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Hsh in Sh0.
  unfold aview in Sh0.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) (2147450880 + p / 8 - 2)) as [b|] eqn:Hb; [|discriminate Sh0].
  cbn in Sh0. injection Sh0 as Hb0.
  replace (0x7fff8000 + p / 8 + -2 + Z.of_nat 0) with (2147450880 + p / 8 - 2) by lia. rewrite Hb.
  f_equal. apply bv_eq. rewrite Hb0. reflexivity. }
assert (DISJ : all_disjoint Eb R_sh rs_ffA).
{ unfold rs_ffA. cbn [all_disjoint]. repeat split; unfold extent_disjoint, R_sh, R_stkA, R_got, R_head, fm_rcell, fm_wcell, G_LIVE;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?F35, ?Usp2, ?Up2; lia. }
pose proof (ast_ok_add_region tfibsegs Eb _ _ R_sh HS2 eq_refl ROK DISJ) as HS3. clear HS2.
change (w64 531120) with (Z_to_bv 64 531120).
srr_run_sh tbl_ff_ok HS3.
(* at `j __wrap_free` (0x81b54 -> 0x52db8): a0 = p - 16, ra / sp / s0 the entry values, g_live = live - n *)
assert (RAW2 : forall x : word, ~ (G_LIVE <= bv_unsigned x < G_LIVE + 8) -> ms_mem ms0 x = mem2 x).
{ intros x Hx. apply HF. intros (r & Hr & Ha). vm_compute in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; unfold G_LIVE in Hx; lia|]).
  destruct Hr. }
clear HF.
set (memF := ms_mem ms0) in *.
assert (VLF : val_mem tfibsegs (mrestrict (w_H W) memF) G_LIVE 8 (live - n)).
{ eapply (val_mem_of_chunk8 Eb _ (ss_mem _) 5%nat G_LIVE (SAlu ALU_SUB (SOff 34 0) ff_nexpr) (live - n));
  [ exact (st_ok_mem_ok Eb _ (w_H W) ms0 HS3) | vm_compute; reflexivity | | lia ].
  apply ff_U_live; [rewrite OLD2 by lia; rewrite E33; reflexivity | rewrite OLD2 by lia; rewrite E34; reflexivity | lia | lia]. }
assert (AVF2 : forall a, 0 <= a < 2 ^ 64 -> ~ (G_LIVE <= a < G_LIVE + 8) ->
  aview tfibsegs (w_H W) memF a = aview tfibsegs (w_H W) mem2 a).
{ intros a Ha Hc. apply aview_eq_of. unfold mrestrict, memF. rewrite RAW2; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hc. }
(* memF against the journal's entry memory mem0 = unpoison [(p - 16, 16)] mem *)
assert (AVF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_fuzz_free <= a < spZ regs) -> ~ (G_LIVE <= a < G_LIVE + 8) ->
  aview tfibsegs (w_H W) memF a = aview tfibsegs (w_H W) mem0 a).
{ intros a Ha Hs Hg. rewrite AVF2 by assumption.
  destruct (Z_le_gt_dec (shadow_addr (p - 16)) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (shadow_addr (p - 16) + 2)) as [L2|L2]|].
  - assert (Hv0 : aview tfibsegs (w_H W) mem2 a = Some 0).
    { destruct (Z.eq_dec a (shadow_addr (p - 16))) as [->|Hne]; [exact Sh0|]. replace a with (shadow_addr (p - 16) + 1) by lia. exact Sh1. }
    rewrite Hv0. symmetry. rewrite Hsh in L1, L2.
    unfold aview, mbyte, mrestrict in Hv0 |- *.
    destruct (w_H W (Z_to_bv 64 a)) eqn:Hh.
    + rewrite (AF0x.seg_rom_none_high a) in Hv0 by (unfold AF0x.TFIB_IMG_END; lia). discriminate Hv0.
    + unfold mem0. rewrite unpoison_in; [reflexivity|]. rewrite in_ush_cons16. rewrite unsigned_lit_small by lia.
      rewrite Hsh. apply Bool.orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - rewrite KEEP2 by (try rewrite Hsh in *; lia). rewrite AV1 by lia. apply AV0; [exact Ha | lia].
  - rewrite KEEP2 by (try rewrite Hsh in *; lia). rewrite AV1 by lia. apply AV0; [exact Ha | lia]. }
assert (PRF : forall a, spZ regs - STK_fuzz_free <= a < spZ regs -> apresent (w_H W) memF a).
{ intros a Ha.
  assert (P2 : apresent (w_H W) mem2 a).
  { destruct (Z_lt_ge_dec a (spZ regs - 32)) as [L1|L1]; [destruct (Z_le_gt_dec (spZ regs - 32 - ESTACK) a) as [L2|L2]|].
    - apply Hpres2. rewrite Hsp1. lia.
    - unfold ESTACK in L2. apply (ff_apresent_kept _ mem1); [unfold AF0x.TFIB_IMG_END; lia | apply KEEP2; lia |].
      apply (ff_apresent_kept _ mem); [unfold AF0x.TFIB_IMG_END; lia | apply AV1; lia | apply PR0; lia].
    - apply (ff_apresent_kept _ mem1); [unfold AF0x.TFIB_IMG_END; lia | apply KEEP2; lia | apply PRS1; lia]. }
  destruct P2 as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold memF. rewrite RAW2; [exact Hb|].
  rewrite unsigned_lit_small by lia. unfold G_LIVE. lia. }
(* AR at the jump: mem2 with g_live written *)
pose proof (proj1 HARU2) as HAR2. rewrite unpoison_nil in HAR2.
assert (HARF : AR tfibsegs B ly S W memF md2).
{ apply (AR_write_static B HB ly S W mem2 md2 memF G_LIVE HAR2); [cbv [FM_PSTAT_FP G_LIVE]; cbn; tauto | exact RAW2 |].
  intros i Hi. exact (aview_some_of_val_mem (w_H W) memF G_LIVE 8 (live - n) i VLF ltac:(cbn; lia)). }
set (FPf := ablocks_fp [(p - 16, n + 16)] ++ FM_PSTAT_FP).
assert (HJF0 : ajournal tfibsegs B STK_fuzz_free (spZ regs) FPf ly S W mem0 md [] ly S W memF md2 0).
{ apply (ff_journal STK_fuzz_free FPf ly S W regs mem0 md ch memF md2 G_LIVE HAN); [cbv [FM_PSTAT_FP G_LIVE]; cbn; tauto | | exact HARF | | exact AVF | exact PRF].
  - intros a Ha. unfold FPf. apply inFP_app. right. apply (inFP_FM_PSTAT_FP G_LIVE); [cbv [FM_PSTAT_FP G_LIVE]; cbn; tauto | exact Ha].
  - apply aos_step_of_same_io. apply same_io_materialized.
    exact (same_but_materialized_trans md md1 md2 (with_vm_backing_same md mat) Hsbm2). }
pose proof (ajournal_materialize tfibsegs B LAWS fma_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat0 HJF0) as HJF.
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (2%bv : bv 5) Q2. rreg HS3 (3%bv : bv 5) Q3. rreg HS3 (4%bv : bv 5) Q4.
rreg HS3 (8%bv : bv 5) Q8. rreg HS3 (10%bv : bv 5) Q10.
rewrite !OLD2 in Q1, Q2, Q3, Q4, Q8, Q10 by lia.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Eb _ ms0 HS3 eq_refl) as HshapeF. cbn [ss_pc] in HshapeF.
set (regsF := ms_regs ms0) in *.
assert (HspF : spZ regsF = spZ regs) by (unfold spZ at 1; rewrite Q2; exact Usp).
assert (HraF : getr regsF 1 = getr regs 1) by (rewrite Q1, E1; reflexivity).
rewrite HshapeF. fold memF.
replace (Z_to_bv 64 339384) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite (ts_code B HB); reflexivity).
destruct HCTX as [HC|[]]. injection HC as Hra0 Hsp0. destruct ch as [|c ch]; [|discriminate Hsp0].
eapply SRr_mono.
{ eapply (AFREE4 W regsF memF STK_fuzz_free (spZ regs) FPf ly S W mem0 md [] ly S _ 0 (p - 16) (n + 16) 0 (getr regs 1) []
    HJF Hblk).
  - rewrite Q10, Up. unfold w64. f_equal; lia.
  - rewrite HspF. lia.
  - reflexivity.
  - lia.
  - unfold STK_fuzz_free, ASTACK. lia.
  - rewrite Q3, E3. exact Hgp.
  - rewrite Q4, E4. exact Htp.
  - exact HraF.
  - exact Hra.
  - lia.
  - apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) [] regsF).
    + apply (achain_kept ly _ _ (spZ regs) (s0Z regs) [] (spZ regs) Hch); [lia | lia |].
      intros a Ha. apply AVF; [lia | lia | unfold G_LIVE; lia].
    + rewrite HspF. lia.
    + unfold s0Z. rewrite Q8, E8. reflexivity.
    + unfold raZ. rewrite HraF. exact Hra4.
  - rewrite call_trace_nil. unfold raZ in *. rewrite HraF, <- Hra0. replace (pc_free_ra0 (as_code B)) with 0x52ef8 by (rewrite (ts_code B HB); reflexivity). cbn.
    apply UNIV. apply TRACES_fuzz_free_U. left. reflexivity.
  - intros _ i Hi. unfold FPf. apply inFP_app. left. apply (inFP_ablocks_fp _ (p - 16) (n + 16) i); [left; reflexivity | exact Hi].
  - exact I. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & Ebl & Ebl2) & Hfrs3 & HK3 & _).
unfold apost_baseU. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|].
split; [exact HJ3|].
split; [split; [constructor | exact I]|].
split; [intros s0 Hs0; discriminate Hs0|].
split.
{ eapply aregs_preserved_trans; [|exact HP3].
  eapply aregs_preserved_of_st_ok; [exact HS3 | | vm_compute; reflexivity].
  rewrite HEb, HE. apply env_agree_havoc_ge; [lia | apply env_agree_refl]. }
split; [exists l1, l2; split; [exact Ebl | exact Ebl2]|].
destruct HK3 as (_ & _ & HK3img & _).
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (spZ regs - 96 <= a < spZ regs - 32) ->
  ~ (0x7fff8000 + p / 8 - 2 <= a < 0x7fff8000 + p / 8) -> ~ (G_LIVE <= a < G_LIVE + 8) ->
  aview tfibsegs (w_H W) memF a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1 H2 H3 H4. rewrite AVF2 by assumption. rewrite KEEP2 by assumption. apply AV1; assumption. }
split; [|split; [|split; [|split]]].
- exact (ff_static_kept HB W W3 memF mem3 G_LIVE (live - n) ltac:(cbv [FM_PSTAT_FP G_LIVE]; cbn; tauto) HK3img VLF).
- apply (ff_static_kept HB W W3 memF mem3 G_PEAK peak ltac:(cbv [FM_PSTAT_FP G_PEAK]; cbn; tauto) HK3img).
  eapply val_mem_kept; [exact GP|]. intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply KF; unfold G_PEAK, G_LIVE; lia.
- apply (ff_static_kept HB W W3 memF mem3 G_COUNT cnt ltac:(cbv [FM_PSTAT_FP G_COUNT]; cbn; tauto) HK3img).
  eapply val_mem_kept; [exact GC|]. intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply KF; unfold G_COUNT, G_LIVE; lia.
- apply (ff_static_kept HB W W3 memF mem3 G_FAIL fail ltac:(cbv [FM_PSTAT_FP G_FAIL]; cbn; tauto) HK3img).
  eapply val_mem_kept; [exact GF|]. intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply KF; unfold G_FAIL, G_LIVE; lia.
- lia.
Qed.

(* fuzz_free_spec (FMH_Fn.v), at fm's call context of fuzz_free (lib/A/ACej.v CTX_fuzz_free) *)
Theorem fuzz_free_holds : fuzz_free_spec tfibsegs B CTX_fuzz_free.
Proof.
intros ly S W regs mem md ch p n live peak cnt fail HCTX H10 HG [[Hp0 HPRE] | (Hp0 & HPREU & HRO & HBLK & Hnl)] Hev.
- subst p. eapply SRr_mono; [apply (ff_null ly S W regs mem md ch live peak cnt fail H10 HG (proj1 HPRE))|].
  intros W' c' _ Hpost. left. split; [reflexivity | exact Hpost].
- eapply SRr_mono; [apply (ff_main ly S W regs mem md ch p n live peak cnt fail HCTX H10 HG Hp0 HPREU HBLK Hnl Hev)|].
  intros W' c' _ Hpost. right. split; [exact Hp0 | exact Hpost].
Qed.
End m.
End c.
