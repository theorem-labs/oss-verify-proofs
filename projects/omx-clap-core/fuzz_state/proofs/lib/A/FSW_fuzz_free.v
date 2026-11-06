(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v, with its module paths and module names changed; 639 of its 687 lines of code are new or changed and 451 lines of the source are left out. *)
(* fs ASan, group ALLOC: the walk of fuzz_free (A 0x82d40, alloc.c:107-116 with disown() :51-59 inlined), proving
   fuzz_free_spec of lib/A/FSH_Fn_alloc.v over fs.asan (image tfibsegs).

   Measured control flow (capstone on the pinned fuzz_state.asan, 71 words 0x82d40..0x82e5c, FSW_malloc_free.tbl_ff):
   0x82d40..0x82d50 frame 32 + save ra / s0 / s1 / s2; `beqz a0` 0x82d54.
   - p = 0: taken to the epilogue 0x82e20, `ret`: FSW_malloc_free.fsw_fuzz_free_null (used as is).
   - p <> 0: s1 = p; s2 = the shadow base (GOT word 0x9f6f0 -> cell 0xa7f38); s0 = a0 = p - 16, a1 = 16;
     `jal __asan_unpoison_memory_region` 0x82d74 (ra 0x82d78); the two inline checks of disown's 8-byte head load
     (lb shadow(s0) / bnez 0x82d84, lb shadow(s1 - 9) / bnez 0x82d98: both read the head's first shadow byte, 0 after
     the unpoisoning, so the report arms 0x82e38 / 0x82e4c are never entered: the token run resolves both loads to 0);
     8 x lbu of the head 0x82d9c..0x82dcc and their reassembly; g_live -= n (ld 0x82dec, sub 0x82dfc, sd 0x82e00);
     a0 = s0; epilogue 0x82e08..0x82e18; tail `j __wrap_free` 0x82e1c (0x53070) with a0 = p - 16.

   Shape: entry FSW_statics.fsw_entryTS, runs by FSW_K.fsw_aj_runU (awr_ok: FSW_statics_awr.fsw_awr_TS), the branch by
   SRr_sym_branch, the unpoison call by FSW_poison_conv.fsw_unpoison16_atU over a call-relative journal (FP = [], so
   the image clause keeps the statics) composed back by YCbq.ajournal_sub, the resumed state by
   FSW_rres.fsw_resume_after_rtU_args (FSW_ret.fss_retT plus the head's 8-byte region, FSW_head.fs_head_region), the
   checks and the rest of the body by one token run FSW_K.fsw_aj_run_tokU (awr_ok: FSW_statics_awr.fsw_awr_retTS; the
   two shadow entries from FSW_head.fs_head_shadow0 / fs_head_shent), the tail call by FSW_malloc_free.fsw_aj_freeU over
   a call-relative journal (FP = the freed block) composed back by ajournal_sub, fs_glob by FSW_statics.fs_glob_of_TS.
   Kit rules R1 (per-goal `first [solve ..]`, computing alternatives guarded by goal shape) and R2 are followed.

   TEMPLATES (no import): the pre-ruling bespoke ASan proof of the same code, a working branch 7c4897eaa4b
   lib/A/Prog/fuzz_free.v (its segment cut at the unpoison call, the invariants carried across it: the frame, g_live,
   the head's shadow; the post's footprint {g_live, the head's shadow, the frame} and the tail call with a0 = p - 16);
   and a Theorem Labs lane's ASan walk of the byte-identical fm code, a working branch 8ff81300fd2 lib/A/FMW_fuzz_free.v
   (its head reassembly expression and the lemmas that evaluate it, ff_lor_shl .. ff_U_live below, ported with the
   head atom 41 and the g_live atom 35 of this walk's resumed state). Relocated files: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSpoisonS FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc
FSW_K FSW_K3 FSW_ret FSW_rres FSW_statics FSW_statics_awr FSW_malloc_free FSW_head FSW_poison_conv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The head's 8 bytes, read back by 8 `lbu` and or-ed together (0x82d9c .. 0x82df8), as the walk computes them, and  *)
(* their value. Ported from: a Theorem Labs lane's FMW_fuzz_free.v ffb0 .. ff_U_live (8ff81300fd2), head atom 33 -> 41, g_live atom   *)
(* 34 -> 35; proofs unchanged.                                                                                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Definition ffb0 : sv := SExt false 8 (SOff 41 0).
Definition ffb (k : Z) : sv := SExt false 8 (SAlu ALU_SRL (SOff 41 0) (SLit k)).
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

Lemma ff_U_b : forall E n k, ew E 41 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> 0 < k < 64 -> U E (ffb k) = n / 2 ^ k mod 256.
Proof.
intros E n k Hn Hr Hk. unfold ffb. rewrite U_zext, U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 41 n Hn Hr).
rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity | change (2 ^ 6) with 64; lia]).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as P.
assert (D : 0 <= n / 2 ^ k <= n).
{ split; [apply Z.div_pos; lia|]. rewrite <- (Z.div_1_r n) at 2. apply Z.div_le_compat_l; lia. }
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

Lemma ff_U_b0 : forall E n, ew E 41 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> U E ffb0 = n mod 256.
Proof. intros E n Hn Hr. unfold ffb0. rewrite U_zext, (U_atom E 41 n Hn Hr). reflexivity. Qed.

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

Lemma ff_U_nexpr : forall E n, ew E 41 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> U E ff_nexpr = n.
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

(* g_live - n, the value the walk stores at 0x82e00 *)
Lemma ff_U_live : forall E n live, ew E 41 = Z_to_bv 64 n -> ew E 35 = Z_to_bv 64 live -> 0 <= n <= live -> live < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SUB (SOff 35 0) ff_nexpr) = Z_to_bv 64 (live - n).
Proof.
intros E n live Hn Hl Hr Hl64. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (ff_U_nexpr E n Hn ltac:(lia)), (U_atom E 35 live Hl ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Small kit facts for this walk                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* awr_ok sees a region list only through its skeleton (base and write window). Ported from: a Theorem Labs lane's
   fm_awr_skel (a working branch 1e530cd69f6 lib/A/FSW_fuzz_malloc.v), same statement and proof. *)
Lemma ff_awr_skel : forall segs B E rs rs' STK sp0 FP bl0 blc ly own fr0,
  skeleton rs' = skeleton rs ->
  awr_ok segs B E rs STK sp0 FP bl0 blc ly own fr0 -> awr_ok segs B E rs' STK sp0 FP bl0 blc ly own fr0.
Proof. intros segs B E rs rs' STK sp0 FP bl0 blc ly own fr0 Hsk H a Ha. apply H. exact (in_wrange_skeleton E rs' rs a Hsk Ha). Qed.

(* a value chunk read under one env and base is the same chunk under another env and base when the absolute address
   and the value agree. Ported from: a Theorem Labs lane's fm_chunk_move (same file), same statement and proof. *)
Lemma ff_chunk_move : forall E E' m base base' off off' sz e e',
  base + off = base' + off' -> sv_denot E e = sv_denot E' e' ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal sz e)) ->
  YP09.chunk_ok tfibsegs E' m base' (YP09.mkChunk off' (CVal sz e')).
Proof.
intros E E' m base base' off off' sz e e' Hb He H i Hi. destruct (H i Hi) as (b & H1 & H2). exists b.
cbn [cbyte YP09.c_off YP09.c_val] in *. rewrite <- He, <- Hb. split; [exact H1 | exact H2].
Qed.

(* the GOT word 0x9f6f0 and the shadow cell 0xa7f38 are image bytes (FSW_statics.fs_pstat_img's method) *)
Definition FF_CELLS : list (Z * Z) := [(0x9f6f0, 0x9f6f8); (0xa7f38, 0xa7f40)].
Lemma ff_cells_img : forall a, inFP FF_CELLS a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
    (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FF_CELLS = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H.
apply existsb_exists in H as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

(* two ranges, one of non-image bytes and one of image bytes, are ordered *)
Lemma ff_img_apart : forall h g len, 0 < len ->
  (forall x, h <= x < h + 8 -> ~ in_img tfibsegs x) -> (forall x, g <= x < g + len -> in_img tfibsegs x) ->
  h + 8 <= g \/ g + len <= h.
Proof.
intros h g len Hl Hh Hg. destruct (Z_le_gt_dec (h + 8) g) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (g + len) h) as [L'|L']; [right; exact L'|].
exfalso. apply (Hh (Z.max h g)); [lia|]. apply Hg. lia.
Qed.

(* the statics' four ranges hold fs_glob's values; a memory that reads the same there holds them too *)
Lemma ff_glob_kept : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VK : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv. apply (val_mem_kept tfibsegs (w_H W) (w_H W') m m'); [|exact Hv].
  intros j Hj. apply Hk. apply (inFP_FS_PSTAT_FP g Hg). cbn in Hj. lia. }
unfold fs_glob, fs_glob_at in *.
split; [apply VK; [unfold G_LIVE; vm_compute; tauto | exact G1]|].
split; [apply VK; [unfold G_PEAK; vm_compute; tauto | exact G2]|].
split; [apply VK; [unfold G_COUNT; vm_compute; tauto | exact G3]|].
split; [apply VK; [unfold G_FAIL; vm_compute; tauto | exact G4] | exact R].
Qed.

(* FSW_statics.fs_pstat_regions_ok under an env with further atoms after the statics' (the resumed state's saved
   registers and the head value). Ported from: a Theorem Labs lane's fm_pstat_ok (same file), env written fs_extraT ++ xs. *)
Lemma ff_pstat_ok : forall (W : world tfibsegs) regs mem live peak cnt fail ys,
  fs_glob tfibsegs W mem live peak cnt fail ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraT ++ (fs_pstat_xs cnt fail live peak ++ ys))) (mrestrict (w_H W) mem))
    fs_pstat_regions.
Proof.
intros W regs mem live peak cnt fail ys GL.
pose proof GL as (G1 & G2 & G3 & G4 & GR).
set (E := Ereg regs (fs_extraT ++ (fs_pstat_xs cnt fail live peak ++ ys))).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite ew_Ereg_extra, app_assoc; apply app_nth1; cbn; lia).
assert (RS : forall g (j : nat) v, (1 <= j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> 0x9f000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (fs_pstat_region g (32 + j))).
{ intros g j v Hj Hv Hr Hg1 Hg2 Hm.
  unfold region_ok, fs_pstat_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold writable_at. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. lia.
  - constructor; [|constructor].
    exact (chunk_ok_val tfibsegs _ _ 0 g 8 (SOff (32 + j) 0) v
      ltac:(rewrite fsw_SOff0; etransitivity; [exact (EX j ltac:(lia)) | exact Hv]) ltac:(cbn [Z.of_N]; lia)
      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Hm)). }
unfold fs_pstat_regions, xatom.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- apply (RS G_COUNT 1%nat cnt); first [solve [lia] | solve [reflexivity] | solve [unfold G_COUNT; lia] | solve [exact G3]].
- apply (RS G_FAIL 2%nat fail); first [solve [lia] | solve [reflexivity] | solve [unfold G_FAIL; lia] | solve [exact G4]].
- apply (RS G_LIVE 3%nat live); first [solve [lia] | solve [reflexivity] | solve [unfold G_LIVE; lia] | solve [exact G1]].
- apply (RS G_PEAK 4%nat peak); first [solve [lia] | solve [reflexivity] | solve [unfold G_PEAK; lia] | solve [exact G2]].
Qed.

Lemma ff_w64_of_unsigned : forall (x : word) v, bv_unsigned x = v -> x = w64 v.
Proof. intros x v E. unfold w64. rewrite <- E. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the token run's shadow entry for the head held at offset lo of atom m (FSW_head.fs_head_shent at any offset: the
   second inline check addresses the head from s1 = p, i.e. offset -16) *)
Lemma ff_head_shent_at : forall (Bx : sv) E (W : world tfibsegs) mem (m : nat) lo h,
  U E (SOff m 0) + lo = h -> U E Bx = SHADOW_OFF -> h mod 8 = 0 -> in_app h 16 ->
  aview tfibsegs (w_H W) mem (shadow_addr h) = Some 0 -> aview tfibsegs (w_H W) mem (shadow_addr h + 1) = Some 0 ->
  YCbn.shent_ok tfibsegs Bx E (mrestrict (w_H W) mem) (YCbn.mkSHE m lo (lo + 16)).
Proof.
intros Bx E W mem m lo h Hm HB H8 Happ Z0 Z1.
pose proof asan_consts as (C1 & _ & C3 & _).
split.
- intros x Hx. cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi] in Hx. rewrite Hm in Hx.
  replace (lo + 16 - lo) with 16 in Hx by lia. rewrite HB.
  exists 0. split; [|left; reflexivity].
  change (YCbn.rd_of tfibsegs (mrestrict (w_H W) mem) (shadow_of_addr SHADOW_OFF x))
    with (aview tfibsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
  apply Z.mod_divide in H8 as [q Hq]; [|lia]. rewrite Hq in Z0, Z1, Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  assert (E0 : shadow_addr (q * 8) = SHADOW_OFF + q) by (unfold shadow_addr; rewrite Z.div_mul by lia; reflexivity).
  rewrite E0 in Z0, Z1. unfold shadow_of_addr.
  assert (x / 8 = q \/ x / 8 = q + 1) as [-> | ->] by lia; [exact Z0 | rewrite Z.add_assoc; exact Z1].
- intros a Ha. cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi] in Ha.
  rewrite (Z.min_l lo (lo + 16)), (Z.max_r lo (lo + 16)) in Ha by lia. rewrite HB.
  unfold in_app, kLowShadowBeg, SHADOW_OFF in *. rewrite C3 in Happ. lia.
Qed.

(* the resumed state carries the head's region after the statics; its write window is empty, so awr_ok over the
   resumed regions is FSW_statics_awr.fsw_awr_retTS's *)
Lemma ff_awr_ret_hd : forall segs B E rs hd STK sp0 FP bl0 blc ly own fr0,
  YP09.r_whi hd <= YP09.r_wlo hd ->
  awr_ok segs B E rs STK sp0 FP bl0 blc ly own fr0 -> awr_ok segs B E (rs ++ [hd]) STK sp0 FP bl0 blc ly own fr0.
Proof.
intros segs B E rs hd STK sp0 FP bl0 blc ly own fr0 Hw H a (rg & Hr & Ha). apply H.
apply in_app_or in Hr as [Hr | [<- | []]]; [exists rg; split; [exact Hr | exact Ha] | lia].
Qed.
End h.

(* the statics are low image bytes *)
Lemma ff_pstat_low : forall a, inFP FS_PSTAT_FP a -> 0x9f000 <= a < 0x5fd000.
Proof.
intros a (r & Hr & Ha). cbv [FS_PSTAT_FP In] in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.

(* the write windows of the entry state fss0TS (and of every state with its skeleton): the frame and the statics *)
Lemma ff_win0 : forall E rs a, skeleton rs = skeleton (ss_mem (fss0TS A_fuzz_free 32)) -> in_wrange E rs a ->
  (bv_unsigned (ew E 2) - 32 <= a < bv_unsigned (ew E 2)) \/ inFP FS_PSTAT_FP a.
Proof.
intros E rs a Hsk Hw. apply (in_wrange_skeleton E rs _ a Hsk) in Hw. destruct Hw as (rg & Hr & Ha).
unfold fss0TS, fss0T_args, fsT_regions_args, fsT_regions, fs_pstat_regions in Hr. cbn [ss_mem app] in Hr.
repeat (destruct Hr as [<- | Hr]).
all: first
  [ solve [exfalso; exact Hr]
  | solve [left; cbn [fstk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia]
  | solve [exfalso; cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia]
  | solve [exfalso; cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia]
  | solve [right; cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (inFP_FS_PSTAT_FP G_COUNT); [vm_compute; tauto | exact Ha]]
  | solve [right; cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (inFP_FS_PSTAT_FP G_FAIL); [vm_compute; tauto | exact Ha]]
  | solve [right; cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (inFP_FS_PSTAT_FP G_LIVE); [vm_compute; tauto | exact Ha]]
  | solve [right; cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (inFP_FS_PSTAT_FP G_PEAK); [vm_compute; tauto | exact Ha]] ].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The resumed state after the unpoison call (0x82d78): the frame [sp - 32, sp) holding the entry's s2 / s1 / s0 / ra *)
(* (atoms 40 / 39 / 38 / 37), the two shadow-base cells, the four statics (atoms 33..36), the head's first 8 bytes at *)
(* s0 = p - 16 (atom 8) holding n (atom 41); facts for s0, s1 = p and s2 = the shadow base (the token run's span).     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Definition ff_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 40 0)); YP09.mkChunk 8 (CVal 8 (SOff 39 0));
   YP09.mkChunk 16 (CVal 8 (SOff 38 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0))].
Definition ff_hd : YP09.region := fs_head_region 8 0 [YP09.mkChunk 0 (CVal 8 (SOff 41 0))].
Definition ff_rs : list YP09.region := fs_pstat_regions ++ [ff_hd].
Definition ff_gf : list (nat * afact) :=
  [(8%nat, mkAF 4096 (2 ^ 47 - 16) 4); (9%nat, mkAF 4112 (2 ^ 47) 4); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition ff_ssR : sstate := fss_retT 0x82d78 32 ff_cs ff_rs ff_gf.
Definition ff_SH : list shent := [mkSHE 8 0 16; mkSHE 9 (-16) 0].
(* the resumed env's extra atoms after the shadow base: the statics, the entry's ra / s0 / s1 / s2, n *)
Definition ff_xs (regs : bvmap 5 word) (cnt fail live peak n : Z) : list word :=
  fs_pstat_xs cnt fail live peak ++ [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 n].
(* what the callee-saved registers hold at the tail jump *)
Definition ff_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 32 | 8 => SOff 38 0 | 9 => SOff 39 0 | 18 => SOff 40 0
  | z => SOff (Z.to_nat z) 0
  end.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk                                                                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* fs's image facts (FSH_Rt.fs_img_facts); owner RELOC, proved once for fs's TfibB. Used for awr_byte's static arm and
   for the statics surviving the free (not owned, not errno). *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the two shadow-base cells of fs.asan (FSH_Base.FsShadowSyms: GOT word 0x9f6f0 -> cell 0xa7f38), fsw_entryTS's and
   the resume's premises; owner RELOC / S0 start-up layer (lib/A/ACeg.v TfibLib) *)
Hypothesis SHS : FsShadowSyms B.
(* the allocator call's environment and model laws, FSW_malloc_free.fsw_aj_freeU's Section hypotheses *)
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
(* __wrap_free in ARU form at its measured pc: FSH_Rt.FsRt's fr_free field (pc pin and POISON-U's afree_realizesU) *)
Hypothesis AFREE : pc_wrap_free (as_code B) = PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.
(* __asan_unpoison_memory_region (h, 16) at PC_unpoison 0x54a34 (POISON-U's FS_AUNPOISON16_A row; proved as
   FSpoisonW.tfib_unpoison16 on a working branch 646ee89c004, not in this tree) *)
Hypothesis FS_AUNPOISON : aunpoison16_realizes tfibsegs B PC_unpoison.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let FS_GOT_SHADOW : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let FS_SHADOW_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.

(* below the shadow the unpoisoned memory is the machine's *)
Lemma ff_unp_low : forall ly S U (W' : world tfibsegs) m md a, ARU tfibsegs B ly S U W' m md -> 0 <= a < SHADOW_OFF ->
  aview tfibsegs (w_H W') (unpoison U m) a = aview tfibsegs (w_H W') m a.
Proof.
intros ly S U W' m md a H Ha. apply FSupoison.aview_at. apply (ARU_mem_low tfibsegs B ly S U W' m md (Z_to_bv 64 a) H).
rewrite (wz a ltac:(unfold SHADOW_OFF in *; lia)). lia.
Qed.

Lemma ff_main : forall ly S U1 U2 (W : world tfibsegs) regs mem md ch p n live peak cnt fail,
  getr regs 10 = w64 p ->
  fs_glob tfibsegs W mem live peak cnt fail -> fs_heads B ly S (U1 ++ (p - 16, 16) :: U2) ->
  fpreU tfibsegs B STK_fuzz_free ly S (U1 ++ (p - 16, 16) :: U2) W regs mem md ch ->
  fs_rblock tfibsegs B ly S W mem p n -> n <= live -> st_nev S + 1 <= EV_MAX ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_free regs mem md)
    (apost_baseU tfibsegs B STK_fuzz_free (FS_PSTAT_FP ++ ablocks_fp [(p - 16, n + 16)]) regs ly S W mem md 1
       (U1 ++ (p - 16, 16) :: U2) (U1 ++ U2)
       (fun ly' S' W' regs' mem' md' =>
          (exists l1 l2, ablocks B ly S = l1 ++ (p - 16, n + 16) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
          fs_heads B ly' S' (U1 ++ U2) /\ fs_glob tfibsegs W' mem' (live - n) peak cnt fail)).
Proof.
intros ly S U1 U2 W regs mem md ch p n live peak cnt fail H10 HGL FH HPRE Hrb Hnl Hev.
pose proof Hrb as (Hin & Hp16 & Hn0 & Hhead). unfold HEAD in Hin, Hhead.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_free ly S _ W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & OK & PO).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_fuzz_free ly S _ W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof Hstk as (_ & _ & Hacl & Hslo & Hshi & Hshi47 & _ & Htop1 & Htop2).
pose proof HGL as (_ & _ & _ & _ & Hlp & Hp64 & Hc64 & Hf64).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FS : STK_fuzz_free = 16416) by reflexivity.
assert (HP2L : (2 : Z) ^ 47 <= 2 ^ 64) by (vm_compute; discriminate).
assert (Htop64 : ly_top ly <= 2 ^ 64) by lia.
destruct (al_blocks _ _ LAWS ly S W _ md (p - 16) (n + 16) HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbmx).
assert (Hreq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hreq in Hbceil, Hbapp, Hbpres.
assert (Hp64' : 0 <= p < 2 ^ 64) by lia.
set (Up := U1 ++ (p - 16, 16) :: U2) in *.
set (U12 := U1 ++ U2).
set (FP := FS_PSTAT_FP ++ ablocks_fp [(p - 16, n + 16)]).
assert (HFPs : forall a, inFP FS_PSTAT_FP a -> inFP FP a)
  by (intros a (r & Hr & Ha); exists r; split; [apply in_or_app; left; exact Hr | exact Ha]).
assert (HFPb : forall a, p - 16 <= a < p + n -> inFP FP a)
  by (intros a Ha; exists (p - 16, p - 16 + req_size (n + 16)); split;
      [apply in_or_app; right; left; reflexivity | cbn [fst snd]; rewrite Hreq; lia]).
(* the pairwise disjointness of U and the head's apartness from the rest *)
pose proof (proj2 OK) as PW.
pose proof (fs_head_apart_rest U1 U2 (p - 16) PW) as DJ.
pose proof (head_not_in_rest U1 U2 (p - 16) PW) as NIN.
(* the head is no image byte *)
assert (HNI : forall x, p - 16 <= x < p - 16 + 8 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (blk_img tfibsegs B LAWS ly S W _ md (p - 16) (n + 16) x HAR Hin ltac:(rewrite Hreq; lia))).
(* entry state and journal *)
pose proof (fsw_entryTS B STK_fuzz_free 32 ly S Up W regs mem md ch A_fuzz_free live peak cnt fail
  FS_GOT_SHADOW FS_SHADOW_CELL HAP ltac:(rewrite FS; lia) ltac:(vm_compute; reflexivity) HGL) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_free FP ly S W regs (unpoison Up mem) md ch HAN) as HJ.
set (E := Ereg regs (fs_extraTS cnt fail live peak)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Up10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
assert (EX : forall j v, (j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj Hv; subst E; rewrite ew_Ereg_extra; exact Hv).
unfold cfg_at. change (w64 A_fuzz_free) with (Z_to_bv 64 A_fuzz_free).
(* 0x82d40..0x82d50: frame, saves; stops at `beqz a0` 0x82d54 *)
fsw_aj_runU tbl_ff_ok HS HJ HARU.
{ exact (fsw_awr_TS B IMG E A_fuzz_free 32 STK_fuzz_free (spZ regs) FP _ _ _ _ _ Usp ltac:(rewrite FS; lia) HFPs). }
rename HF into HF1. rename ms into ms1. clear HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS).
{ (* taken: p = 0, refuted *)
  intros Hb _. exfalso. rewrite branch_eq_U, (U_atom E 10 p E10 Hp64'), U_lit in Hb by lia.
  apply Z.eqb_eq in Hb. lia. }
intros _ HS2. clear HS.
(* 0x82d58..0x82d74: s1 = p, s2 = shadow base, s0 = a0 = p - 16, a1 = 16; `jal __asan_unpoison_memory_region` stops at
   the fetch of 0x54a34 *)
fsw_aj_runU tbl_ff_ok HS2 HJ HARU.
{ eapply ff_awr_skel; [| exact (fsw_awr_TS B IMG E A_fuzz_free 32 STK_fuzz_free (spZ regs) FP _ _ _ _ _ Usp
    ltac:(rewrite FS; lia) HFPs)].
  lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
rename HF into HF2. clear HFr HG.
rewrite ?wvb_collapse in HJ, HARU.
(* the registers and the frame at the call (pc 0x54a34) *)
pose proof (fsw_reg_lit (w_H W) E _ ms 1%bv 535928 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_off (w_H W) E _ ms 2%bv 2 (-32) (spZ regs) HS2 ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom (w_H W) regs _ _ ms 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom (w_H W) regs _ _ ms 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_off (w_H W) E _ ms 8%bv 10 (-16) p HS2 ltac:(vm_compute; reflexivity) Up10 ltac:(lia)) as R8.
pose proof (fsw_reg_atom (w_H W) regs _ _ ms 9%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fsw_reg_off (w_H W) E _ ms 10%bv 10 (-16) p HS2 ltac:(vm_compute; reflexivity) Up10 ltac:(lia)) as R10.
pose proof (fsw_reg_lit (w_H W) E _ ms 11%bv 16 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_extra (w_H W) regs _ _ ms 18%bv 0 HS2 ltac:(vm_compute; reflexivity)) as R18.
assert (KT : forall q : bv 5, In q [3%bv; 4%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr (ms_regs ms) q = getr regs q).
{ intros q Hq. cbv [In] in Hq. repeat (destruct Hq as [<- | Hq]); [..|destruct Hq].
  all: lazymatch goal with |- getr _ ?q = _ =>
         let z := eval vm_compute in (Z.to_nat (bv_unsigned q)) in
         exact (fsw_reg_atom (w_H W) regs _ _ ms q q z HS2 ltac:(vm_compute; reflexivity) eq_refl) end. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS2 eq_refl) as Hshape. cbn [ss_pc] in Hshape.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; rewrite R2; lia).
assert (H101 : getr (ms_regs ms) 10 = w64 (p - 16)) by (apply ff_w64_of_unsigned; rewrite R10; lia).
assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity).
(* the statics at the call, from the symbolic memory *)
pose proof (st_ok_mem_ok tfibsegs E _ _ HS2) as HMEMc. cbn [ms_mem restrict] in HMEMc.
assert (HGT : fs_glob tfibsegs W (ms_mem ms) live peak cnt fail).
{ apply (fs_glob_of_TS E W (ms_mem ms) _ live peak cnt fail (SOff 35 0) (SOff 36 0) (SOff 33 0) (SOff 34 0) HMEMc).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX 3%nat live ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 4%nat peak ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 1%nat cnt ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 2%nat fail ltac:(lia) eq_refl)]
    | solve [lia] ]. }
(* the frame's four saved words at the call *)
pose proof (proj1 (proj2 HMEMc)) as HRS. cbn [ss_mem] in HRS.
apply Forall_inv in HRS. destruct HRS as (_ & _ & _ & HCS). cbn [YP09.r_chunks YP09.r_base base_val] in HCS.
rewrite Usp in HCS.
pose proof (proj1 (Forall_forall _ _) HCS _ (or_introl eq_refl)) as C18.
pose proof (proj1 (Forall_forall _ _) HCS _ (or_intror (or_introl eq_refl))) as C9.
pose proof (proj1 (Forall_forall _ _) HCS _ (or_intror (or_intror (or_introl eq_refl)))) as C8.
pose proof (proj1 (Forall_forall _ _) HCS _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Cra.
clear HCS.
(* the head bytes at the call are the entry's: no window of the two runs holds them *)
assert (HDT : forall i, 0 <= i < 8 ->
  aview tfibsegs (w_H W) (ms_mem ms) (p - 16 + i) = aview tfibsegs (w_H W) mem (p - 16 + i)).
{ intros i Hi.
  assert (Hw : forall rs, skeleton rs = skeleton (ss_mem (fss0TS A_fuzz_free 32)) ->
    ~ in_wrange E rs (bv_unsigned (Z_to_bv 64 (p - 16 + i)))).
  { intros rs Hsk Hw. rewrite (wz (p - 16 + i) ltac:(lia)) in Hw.
    destruct (ff_win0 E rs _ Hsk Hw) as [Hf | Hs]; [rewrite Usp in Hf; lia|].
    exact (HNI (p - 16 + i) ltac:(lia) (fs_pstat_img _ Hs)). }
  apply FSupoison.aview_at. rewrite (HF2 (Z_to_bv 64 (p - 16 + i))).
  - apply HF1. apply Hw. reflexivity.
  - apply Hw. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
clear HF1 HF2.
rewrite Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdT := m) in * end.
change (mkCfg (mkst regsT (Z_to_bv 64 346676) memT (seg_rom tfibsegs)) mdT) with (cfg_at tfibsegs PC_unpoison regsT memT mdT).
(* 0x82d74: __asan_unpoison_memory_region (p - 16, 16), over the call-relative journal at the entry sp (FP = []) *)
pose proof (ajournal_sub_init tfibsegs B STK_fuzz_free (spZ regs) FP ly S W (unpoison Up mem) md [] ly S W
  (unpoison Up memT) mdT 0 (ESTACK + 32) (spZ regs) [] 0 HJ ltac:(lia) eq_refl ltac:(lia) ltac:(unfold ESTACK; lia)
  ltac:(unfold ESTACK; lia)) as J0.
eapply SRr_bind.
{ exact (fsw_unpoison16_atU B PC_unpoison FS_AUNPOISON (ESTACK + 32) (spZ regs) [] ly S W (unpoison Up memT) mdT []
    ly S U1 U2 W memT mdT 0 regsT (-32) (p - 16) (p - 16) (n + 16) J0 HARU ltac:(lia) eq_refl ltac:(lia) ltac:(lia)
    Hra1 ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) H101 ltac:(rewrite R11; reflexivity) Hin
    ltac:(lia) ltac:(rewrite Hreq; lia)). }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & J1 & HARU2 & HP2 & Hkeep).
pose proof (ajournal_sub tfibsegs B LAWS fs_segs_low STK_fuzz_free (spZ regs) FP ly S W (unpoison Up mem) md [] ly S W
  (unpoison Up memT) mdT 0 (ESTACK + 32) (spZ regs) [] [] ly S W (unpoison U12 mem2) md2 0 HJ J1
  ltac:(unfold ESTACK; lia) ltac:(lia) ltac:(intros a (rg & [] & _))) as JM.
cbn [app] in JM. rewrite Z.add_0_r in JM.
(* what the unpoison call kept: the statics (J1's image clause at FP = []) and the head (its block clause) *)
pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J1blk & J1img & _).
assert (HGL2 : fs_glob tfibsegs W mem2 live peak cnt fail).
{ apply (ff_glob_kept W W memT mem2 live peak cnt fail); [|exact HGT].
  intros a Ha. pose proof (ff_pstat_low a Ha) as La.
  rewrite <- (ff_unp_low ly S U12 W mem2 md2 a HARU2 ltac:(unfold SHADOW_OFF; lia)),
    <- (ff_unp_low ly S Up W memT mdT a HARU ltac:(unfold SHADOW_OFF; lia)).
  destruct (proj1 IMG a Ha) as [Hno He].
  apply J1img; [exact (fs_pstat_img a Ha) | exact Hno | exact He | intros (rg & [] & _) | ].
  apply fp_spares_closed. exact sink_closed_nil. }
assert (Happ : forall a, p - 16 <= a < p - 16 + 8 -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. unfold in_app, kLowShadowBeg, SHADOW_OFF in *. rewrite C3 in *. lia. }
assert (HD2 : val_mem tfibsegs (mrestrict (w_H W) mem2) (p - 16) 8 n).
{ apply (val_mem_kept tfibsegs (w_H W) (w_H W) mem mem2); [|exact Hhead].
  intros k Hk. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. rewrite <- (HDT k ltac:(lia)).
  destruct (Happ (p - 16 + k) ltac:(lia)) as [Ha64 Ha].
  rewrite <- (FSupoison.aview_at tfibsegs _ (unpoison U12 mem2) mem2 _ (fs_head_app_view B ly S U12 W mem2 md2 _ HARU2 Ha64 Ha)),
    <- (FSupoison.aview_at tfibsegs _ (unpoison Up memT) memT _ (fs_head_app_view B ly S Up W memT mdT _ HARU Ha64 Ha)).
  apply (J1blk (p - 16) (n + 16) k Hin Hin ltac:(rewrite Hreq; lia)). intros (rg & [] & _). }
(* ---- the resumed state at 0x82d78 (fss_retT plus the head's region) ---- *)
set (xs := ff_xs regs cnt fail live peak n).
set (E2 := Ereg regs2 (fs_extraT ++ xs)).
assert (P2 : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs2 q = getr regsT q)
  by (intros q Hq; exact (fsw_pres regsT regs2 q HP2 Hq)).
assert (E2_2 : bv_unsigned (ew E2 2) = spZ regs - 32).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (P2 2%bv ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)).
  exact Hsp1. }
assert (E2_8 : bv_unsigned (ew E2 8) = p - 16).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), (P2 8%bv ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)).
  rewrite R8. lia. }
assert (E2_9 : ew E2 9 = Z_to_bv 64 p).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), (P2 9%bv ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)).
  rewrite R9. exact H10. }
assert (E2_18 : ew E2 18 = Z_to_bv 64 SHADOW_OFF).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), (P2 18%bv ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)).
  rewrite R18. reflexivity. }
assert (E2_35 : ew E2 35 = Z_to_bv 64 live) by exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 3).
assert (E2_41 : ew E2 41 = Z_to_bv 64 n) by exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 9).
(* the head lies off every image range of the resumed state *)
assert (AP : forall g len, 0 < len -> (forall x, g <= x < g + len -> in_img tfibsegs x) ->
  p - 16 + 8 <= g \/ g + len <= p - 16)
  by (intros g len Hl Hg; exact (ff_img_apart (p - 16) g len Hl HNI Hg)).
assert (AGot : p - 16 + 8 <= 0x9f6f0 \/ 0x9f6f0 + 8 <= p - 16).
{ apply AP; [lia|]. intros x Hx. apply ff_cells_img. exists (0x9f6f0, 0x9f6f8).
  split; [left; reflexivity | cbn; lia]. }
assert (ACell : p - 16 + 8 <= 0xa7f38 \/ 0xa7f38 + 8 <= p - 16).
{ apply AP; [lia|]. intros x Hx. apply ff_cells_img. exists (0xa7f38, 0xa7f40).
  split; [right; left; reflexivity | cbn; lia]. }
assert (AC : p - 16 + 8 <= G_COUNT \/ G_COUNT + 8 <= p - 16).
{ apply AP; [lia|]. intros x Hx. apply fs_pstat_img.
  apply (inFP_FS_PSTAT_FP G_COUNT); [unfold G_COUNT; cbn; tauto | exact Hx]. }
assert (AF : p - 16 + 8 <= G_FAIL \/ G_FAIL + 8 <= p - 16).
{ apply AP; [lia|]. intros x Hx. apply fs_pstat_img.
  apply (inFP_FS_PSTAT_FP G_FAIL); [unfold G_FAIL; cbn; tauto | exact Hx]. }
assert (AL : p - 16 + 8 <= G_LIVE \/ G_LIVE + 8 <= p - 16).
{ apply AP; [lia|]. intros x Hx. apply fs_pstat_img.
  apply (inFP_FS_PSTAT_FP G_LIVE); [unfold G_LIVE; cbn; tauto | exact Hx]. }
assert (AK : p - 16 + 8 <= G_PEAK \/ G_PEAK + 8 <= p - 16).
{ apply AP; [lia|]. intros x Hx. apply fs_pstat_img.
  apply (inFP_FS_PSTAT_FP G_PEAK); [unfold G_PEAK; cbn; tauto | exact Hx]. }
unfold G_COUNT, G_FAIL, G_LIVE, G_PEAK in AC, AF, AL, AK.
assert (HS3 : st_ok tfibsegs E2 ff_ssR (restrict (w_H W) (mkst regs2 (Z_to_bv 64 535928) mem2 (seg_rom tfibsegs)))).
{ unfold ff_ssR.
  apply (fsw_resume_after_rtU_args B STK_fuzz_free (spZ regs) FP ly S W (unpoison Up mem) md [] ly S U12 W mem2 md2 0
    regsT regs2 memT 32 xs ff_cs ff_rs ff_gf 535928 FS_GOT_SHADOW FS_SHADOW_CELL JM HARU2 HP2 Hsp1).
  all: first
    [ lazymatch goal with |- _ mod _ = _ => solve [reflexivity] end
    | lazymatch goal with |- regions_wf _ = true => solve [vm_compute; reflexivity] end
    | lazymatch goal with |- Forall (fun _ => _) ff_cs => solve [unfold ff_cs; repeat constructor; cbn; lia] end
    | lazymatch goal with |- forall a, _ -> mbyte _ _ _ = _ => solve [intros a Ha; apply Hkeep; lia] end
    | lazymatch goal with |- (_ <= _)%Z => solve [lia] | |- (_ < _)%Z => solve [lia] end
    | idtac ].
  - (* the frame's saved words, moved from the call-site state (base sp, offsets -32..-8) to the resumed one *)
    unfold ff_cs. repeat constructor.
    + apply (ff_chunk_move E _ _ (spZ regs) _ (-32) _ 8 (SOff 18 0) _); [lia | | exact C18].
      rewrite !fsw_SOff0. etransitivity; [exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)|].
      symmetry. exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 8).
    + apply (ff_chunk_move E _ _ (spZ regs) _ (-24) _ 8 (SOff 9 0) _); [lia | | exact C9].
      rewrite !fsw_SOff0. etransitivity; [exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)|].
      symmetry. exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 7).
    + apply (ff_chunk_move E _ _ (spZ regs) _ (-16) _ 8 (SOff 8 0) _); [lia | | exact C8].
      rewrite !fsw_SOff0. etransitivity; [exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)|].
      symmetry. exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 6).
    + apply (ff_chunk_move E _ _ (spZ regs) _ (-8) _ 8 (SOff 1 0) _); [lia | | exact Cra].
      rewrite !fsw_SOff0. etransitivity; [exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)|].
      symmetry. exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 5).
  - (* the statics and the head *)
    unfold ff_rs. apply Forall_app. split; [exact (ff_pstat_ok W regs2 mem2 live peak cnt fail _ HGL2)|].
    constructor; [|constructor].
    apply (fs_head_region_ok B ly S U12 W mem2 md2 _ 8 (p - 16) 0 _ (p - 16) (n + 16) HARU2 Hin ltac:(lia)
      ltac:(rewrite Hreq; lia) E2_8 ltac:(lia)).
    constructor; [|constructor].
    exact (fs_head_chunk_ok _ (w_H W) mem2 (p - 16) (SOff 41 0) n ltac:(rewrite fsw_SOff0; exact E2_41) ltac:(lia) HD2).
  - (* the regions are apart: the frame on the stack, the image cells, the head in its block *)
    unfold fsT_ret_regions, ff_rs, fs_pstat_regions, ff_hd, fs_head_region, fstk_ret, fs_got_region, fs_bcell_region,
      fs_pstat_region.
    cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E2. rewrite E2_2, E2_8.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
      G_COUNT, G_FAIL, G_LIVE, G_PEAK.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - (* the atom facts: s0 = p - 16, s1 = p, s2 = the shadow base *)
    unfold ff_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E2.
    assert (U9 : bv_unsigned (ew E2 9) = p) by (rewrite E2_9; apply unsigned_lit_small; lia).
    assert (U18 : bv_unsigned (ew E2 18) = SHADOW_OFF) by (rewrite E2_18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
    rewrite E2_8, U9, U18. change (2 ^ 4) with 16. rewrite Z.pow_0_r.
    repeat split; first [lia | apply Z.mod_1_r | exact Hp16 | exact Hb16]. }
(* ---- the token run from 0x82d78 to `j __wrap_free`: the two checks (both shadow loads covered: 0), the head load,
   g_live -= n, the epilogue ---- *)
destruct (fs_head_shadow0 B ly S U12 W mem2 md2 (p - 16) (n + 16) HARU2 Hin ltac:(rewrite Hreq; lia) DJ) as [Z0 Z1].
assert (U8 : U E2 (SOff 8 0) = p - 16) by (apply (U_atom E2 8 (p - 16)); [exact (ff_w64_of_unsigned _ _ E2_8) | lia]).
assert (U9 : U E2 (SOff 9 0) = p) by exact (U_atom E2 9 p E2_9 Hp64').
assert (U18 : U E2 (SOff 18 0) = SHADOW_OFF) by (apply (U_atom E2 18 SHADOW_OFF E2_18); unfold SHADOW_OFF; lia).
assert (H8 : (p - 16) mod 8 = 0) by lia.
assert (HappH : in_app (p - 16) 16) by (unfold in_app in Hbapp |- *; lia).
assert (SHOK : sh_ok tfibsegs (SOff 18 0) ff_SH E2 (mrestrict (w_H W) mem2)).
{ unfold ff_SH, sh_ok. constructor; [|constructor; [|constructor]].
  - exact (fs_head_shent (SOff 18 0) E2 W mem2 8 (p - 16) U8 U18 H8 HappH Z0 Z1).
  - exact (ff_head_shent_at (SOff 18 0) E2 W mem2 9 (-16) (p - 16) ltac:(rewrite U9; lia) U18 H8 HappH Z0 Z1). }
rewrite R1.
fsw_aj_run_tokU tbl_ff_ok HS3 JM HARU2 SHOK fs_Bspan.
{ change (ss_mem ff_ssR) with (ss_mem (fss_retT 535928 32 ff_cs fs_pstat_regions ff_gf) ++ [ff_hd]).
  apply ff_awr_ret_hd; [unfold ff_hd, fs_head_region; cbn; lia|].
  exact (fsw_awr_retTS B IMG E2 535928 32 STK_fuzz_free (spZ regs) ff_cs ff_gf FP _ _ _ _ _ E2_2 ltac:(lia) HFPs). }
clear HF HFr HG.
rewrite ?wvb_collapse in JM, HARU2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdF := m) in * end.
(* ---- at `j __wrap_free` 0x82e1c: a0 = p - 16, ra / sp / s0 the entry's, g_live = live - n ---- *)
assert (KQ : forall q : bv 5, In q [3%bv; 4%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr regs2 q = getr regs q).
{ intros q Hq. rewrite <- (KT q Hq). apply P2.
  cbv [In] in Hq. repeat (destruct Hq as [<-|Hq]); [..|destruct Hq];
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?w] =>
    let z := eval vm_compute in (bv_unsigned w) in change (bv_unsigned w) with z end; lia. }
assert (Q1 : getr (ms_regs ms0) 1 = getr regs 1)
  by exact (fsw_reg_extra (w_H W) regs2 _ _ ms0 1%bv 5 HS3 ltac:(vm_compute; reflexivity)).
assert (Q8 : getr (ms_regs ms0) 8 = getr regs 8)
  by exact (fsw_reg_extra (w_H W) regs2 _ _ ms0 8%bv 6 HS3 ltac:(vm_compute; reflexivity)).
assert (Q2 : bv_unsigned (getr (ms_regs ms0) 2) = spZ regs).
{ rewrite (fsw_reg_off (w_H W) E2 _ ms0 2%bv 2 32 (spZ regs - 32) HS3 ltac:(vm_compute; reflexivity) E2_2
    ltac:(lia)). lia. }
assert (Q2' : spZ (ms_regs ms0) = spZ regs) by exact Q2.
assert (Q3 : getr (ms_regs ms0) 3 = getr regs 3).
{ etransitivity; [exact (fsw_reg_atom (w_H W) regs2 _ _ ms0 3%bv 3%bv 3 HS3 ltac:(vm_compute; reflexivity) eq_refl)|].
  apply KQ. cbv [In]. tauto. }
assert (Q4 : getr (ms_regs ms0) 4 = getr regs 4).
{ etransitivity; [exact (fsw_reg_atom (w_H W) regs2 _ _ ms0 4%bv 4%bv 4 HS3 ltac:(vm_compute; reflexivity) eq_refl)|].
  apply KQ. cbv [In]. tauto. }
assert (Q10 : getr (ms_regs ms0) 10 = w64 (p - 16)).
{ apply ff_w64_of_unsigned.
  rewrite (fsw_reg_off (w_H W) E2 _ ms0 10%bv 8 0 (p - 16) HS3 ltac:(vm_compute; reflexivity) E2_8 ltac:(lia)). lia. }
assert (HPF : aregs_preserved regs (ms_regs ms0)).
{ apply (fsw_preserved (w_H W) E2 _ _ regs ff_expect HS3 ltac:(vm_compute; reflexivity)).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (ff_expect ?q) = _ =>
    let e := eval vm_compute in (ff_expect q) in change (ff_expect q) with e end;
  first
  [ solve [apply fsw_sp_back; exact E2_2]
  | solve [rewrite fsw_SOff0; reflexivity]
  | solve [rewrite fsw_SOff0;
           lazymatch goal with |- ew _ ?nn = getr _ ?q =>
             transitivity (getr regs2 q);
             [ exact (ew_Ereg_nat regs2 (fs_extraT ++ xs) nn q eq_refl)
             | apply KQ; cbv [In]; tauto ] end] ]. }
set (regsF := ms_regs ms0) in *. set (memF := ms_mem ms0) in *.
(* g_live, read back from the final symbolic memory *)
pose proof (st_ok_mem_ok tfibsegs E2 _ _ HS3) as HMEMF. cbn [ms_mem restrict] in HMEMF.
assert (HGLF : fs_glob tfibsegs W memF (live - n) peak cnt fail).
{ apply (fs_glob_of_TS E2 W memF _ (live - n) peak cnt fail (SAlu ALU_SUB (SOff 35 0) ff_nexpr) (SOff 36 0)
    (SOff 33 0) (SOff 34 0) HMEMF).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [lazymatch goal with |- sv_denot _ (SAlu _ _ _) = _ =>
               exact (ff_U_live E2 n live E2_41 E2_35 ltac:(lia) ltac:(lia)) end]
    | solve [rewrite fsw_SOff0; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 4)]
    | solve [rewrite fsw_SOff0; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 1)]
    | solve [rewrite fsw_SOff0; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 2)]
    | solve [lia] ]. }
(* ---- the tail call `j __wrap_free` (0x53070) ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ ms0 HS3 eq_refl) as HshapeF. cbn [ss_pc] in HshapeF.
assert (FH12 : fs_heads B ly S U12) by exact (fs_heads_remove B ly S U1 U2 (p - 16) FH).
pose proof JM as (_ & _ & _ & _ & _ & _ & _ & _ & JMf1 & _).
set (FP1 := ablocks_fp [(p - 16, n + 16)]).
assert (HinFP1 : forall a, inFP FP1 a -> p - 16 <= a < p + n).
{ intros a (rg & Hr & Ha). unfold FP1, ablocks_fp in Hr. cbn [map fst snd] in Hr.
  destruct Hr as [<- | []]. cbn [fst snd] in Ha. rewrite Hreq in Ha. lia. }
assert (HFP1 : forall i, 0 <= i < req_size (n + 16) -> inFP FP1 (p - 16 + i)).
{ intros i Hi. exists (p - 16, p - 16 + req_size (n + 16)).
  split; [unfold FP1, ablocks_fp; cbn [map fst snd]; left; reflexivity | cbn [fst snd]; lia]. }
pose proof (ajournal_sub_init tfibsegs B STK_fuzz_free (spZ regs) FP ly S W (unpoison Up mem) md [] ly S W
  (unpoison U12 memF) mdF 0 ASTACK (spZ regs) FP1 0 JM ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold ASTACK; lia) ltac:(unfold ASTACK; lia)) as Jf0.
rewrite HshapeF. fold regsF memF.
replace (Z_to_bv 64 340080) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite (proj1 AFREE); reflexivity).
eapply SRr_mono.
{ apply (fsw_aj_freeU B FS_ENV ML (proj2 AFREE) W regsF memF ASTACK (spZ regs) FP1 ly S W memF mdF []
    ly S U12 mdF 0 (p - 16) (n + 16) 0 (getr regs 1) ch Jf0 HARU2 Hin).
  all: first
    [ solve [exact (FSupoisonU.ARU_free_outside tfibsegs B LAWS ly S U12 W memF mdF (p - 16) (n + 16) HARU2 FH12 Hin NIN)]
    | solve [exact Q10]
    | solve [lia]
    | solve [reflexivity]
    | solve [unfold ASTACK; lia]
    | solve [rewrite Q3; exact Hgp]
    | solve [rewrite Q4; exact Htp]
    | solve [exact Q1]
    | solve [exact Hra]
    | solve [lazymatch goal with |- chain_pre _ _ _ _ =>
               apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch regsF);
               first
                 [ solve [apply (achain_kept ly (aview tfibsegs (w_H W) (unpoison Up mem)) _ (spZ regs) (s0Z regs) ch
                     (spZ regs) Hch ltac:(lia) ltac:(lia));
                   intros a Ha; apply JMf1; [lia | lia]]
                 | solve [lia]
                 | solve [unfold s0Z; rewrite Q8; reflexivity]
                 | solve [unfold raZ; rewrite Q1; exact Hra4] ] end]
    | solve [intros _ i Hi; exact (HFP1 i Hi)] ]. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HARU3 & Jf1 & HP3 & (l1 & l2 & Eb1 & Eb2) & Hfrs3 & HK).
pose proof (fsw_ajournal_sub5 B STK_fuzz_free (spZ regs) FP ly S W (unpoison Up mem) md [] ly S W
  (unpoison U12 memF) mdF 0 ASTACK (spZ regs) FP1 [] ly3 S3 W3 (unpoison U12 mem3) md3 1 JM Jf1
  ltac:(unfold ASTACK; lia) ltac:(lia)
  ltac:(intros a Ha; left; split; [apply HFPb; exact (HinFP1 a Ha)|];
        exists (p - 16), (n + 16); split; [exact Hin|]; rewrite Hreq; pose proof (HinFP1 a Ha); lia)) as JF.
cbn [app] in JF. rewrite Z.add_0_l in JF.
destruct HK as (_ & _ & K3 & _).
unfold apost_baseU, fpostU. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|].
split; [exact JF|].
split; [exact (proj1 (proj2 HARU3))|].
split; [exact (proj2 (proj2 HARU3))|].
split; [intros r Hr; rewrite (HP3 r Hr); exact (HPF r Hr)|].
split; [exists l1, l2; split; [exact Eb1 | exact Eb2]|].
split.
{ intros r Hr. destruct (FH12 r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m. split; [|exact M16].
  rewrite Eb2. rewrite Eb1 in Hm. apply in_app_or in Hm as [Hm | [Hm | Hm]];
    [apply in_or_app; left; exact Hm | | apply in_or_app; right; exact Hm].
  exfalso. apply NIN. destruct r as [q sz]. cbn [fst snd] in *. subst sz.
  injection Hm as Ha1 Ha2;
    first [rewrite Ha1; exact Hr | rewrite Ha2; exact Hr | rewrite <- Ha1; exact Hr | rewrite <- Ha2; exact Hr]. }
apply (ff_glob_kept W W3 memF mem3 (live - n) peak cnt fail); [|exact HGLF].
intros a Ha. pose proof (ff_pstat_low a Ha) as La. destruct (proj1 IMG a Ha) as [Hno He].
rewrite <- (ff_unp_low ly3 S3 U12 W3 mem3 md3 a HARU3 ltac:(unfold SHADOW_OFF; lia)),
  <- (ff_unp_low ly S U12 W memF mdF a HARU2 ltac:(unfold SHADOW_OFF; lia)).
exact (K3 a (fs_pstat_img a Ha) Hno He).
Qed.

(* the p = 0 arm is FSW_malloc_free.fsw_fuzz_free_null; the p <> 0 arm is ff_main *)
Theorem fuzz_free_holds : @FSH_Fn_alloc.fuzz_free_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch p n live peak cnt fail H10 HGL FH
  [[Hp0 HPRE] | (Hp0 & U1 & U2 & EU & HPRE & Hrb & Hnl)] Hev.
- eapply SRr_mono.
  { rewrite Hp0 in H10. exact (fsw_fuzz_free_null B ly S U W regs mem md ch live peak cnt fail HPRE FH H10 HGL). }
  intros W' c' _ HQ. left. split; [exact Hp0 | exact HQ].
- unfold HEAD in EU |- *. subst U.
  eapply SRr_mono.
  { exact (ff_main ly S U1 U2 W regs mem md ch p n live peak cnt fail H10 HGL FH HPRE Hrb Hnl (Hev Hp0)). }
  intros W' c' _ HQ. right. split; [exact Hp0|]. exists U1, U2. split; [reflexivity | exact HQ].
Qed.


End w.
