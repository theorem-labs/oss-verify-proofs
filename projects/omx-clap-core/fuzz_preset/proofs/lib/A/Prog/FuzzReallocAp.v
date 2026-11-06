(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths, module names and numbers changed; 5113 of its 5220 lines of code are new or changed and 407 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/BTxValue.v, with its module paths and module names changed; 2360 of its 2536 lines of code are new or changed and 5044 lines of the source are left out. *)
(* proves function fuzz_realloc (A' 0x858ac) (reuse search: the proof index v5 on main / ossv/recipes@25e3d17bdb50 / ossv/candidates / release/pau-projects-recipes (the unpinned ones at their tips at index build 2026-10-29T21:33:35Z, as the index output header states) + lemma index + live heads, and git grep of 0x858ac on those four refs: 0 released lemmas for 0x858ac; the released fuzz_realloc lemmas are the old-pin plain / ubsan contracts; this file restates this walk's own proof)
   fuzz_preset, row AL3 (the internal file FREE-PIECES-102.md Part 5): the ASan walk of fuzz_realloc on image A' (asan, #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519b; merged alloc.c :104-128,
   blob bd2740a) and its top theorem fuzz_realloc_holds_Ap : tfuzz_realloc_specX (lib/A/PRH_FnAlloc.v, the #102 kit of
   record, post-implication position form) at the generated PrhImg prh_img_A, the allocator lane's room invariant
   prh_room_live_a8 and the allocator relation ARcf /\ xs_placed_cf. The segments before the realloc call are restated
   from the held walk lib/A/Prog/FuzzRealloc.v.wip blob ec606ccf (commit dc23a75bafa, V1 pin).
   SOURCES: the A' listing Listing_prog.v (sha256 62db5cdc9519; internal record) / PAImg_prog.v (sha256 04074e99eb62; internal record) / lib/Reusable/YPsym.v (as in this tree) of
   the #102 pins listing (A_OBJ by symbol: 7 g_count, 8 g_fail_at, 9 g_live, 10 g_peak,
   11 g_ran_out, 12 __asan_shadow_memory_dynamic_address, 13 g_own_ran_out, 14 g_most), carried by the AL base
   tree. A' fuzz_realloc = A_prog_sigma AS_fuzz_realloc (0x858ac, slot 4275, 223 slots,
   frame 64). The segment plan: the AL3 plan (row AL3), section 3: 21 segments, 10 ported, 11 new.
   THE WALK, one lemma per cut (each takes its start cut and a continuation at its end cut; the cut states ss_* are
   the runner's own results, by vm_compute of the run the tactic makes): the entry seats (ra_cut_entry / _entry0);
   Z0 Z1 (p = 0 up to the tail call of fuzz_malloc); S1 (count + the CHOSEN-FAIL branch); S2 + ra_arm_fail
   (CHOSEN-FAIL to its `ret`); S3 (the TOOBIG test, the TOOBIG arm refuted by n + 16 < cf_malloc_max); S4 + CU (disown's
   __asan_unpoison_memory_region, YGcallMxmn.aj_unpoison_x_m); S5 (the head read, k pinned to atom 37); S6 (g_live -= k
   up to the realloc call); CR (__wrap_realloc by YGcallRkKeep.aj_realloc_x_cfR_keep and its `beqz`); ra_arm_refused
   (refused (n) after disown: g_peak := max (g_peak, live - k + n), g_ran_out := 1 when n <= g_most; then own (b, old)
   with YGcallMxmn.aj_poison_x_mR, g_live back to live, return NULL); ra_arm_success (own (nb, n), g_live += n,
   g_peak := max, return nb + 16). The memory stays normal along every run (YSRrMemnorm's paj_run_x_m_inv(R)) and call.
   THE RE-HIDING (the kit's primed tfuzz_realloc_specX, SRr' at YGcfRehidePost.RZ_cf): the realloc call's post is at
   RRZ = wle' SEGS RZ_cf, so CR and both arms are SRr' over journals at RRZ (the R runner, branch and poison rule); the
   segments before the call stay plain SRr (F12 route (b)) and the top lifts ONCE at its entry (YGcfRhLift.ra_rh_of_SRr);
   the other path ends (p = 0's tail call, CHOSEN-FAIL) return through SRr'_ret with their wle journals widened. The
   call's room carries the hull admission (from the text's hull budget, PresetHullPay) and its call memory QMm_cf (the
   RELRO fact carried from fpre's reader form, ra_aro_entry); each path end states the hull use.
   THE OUTCOME CLAUSE (the kit's batch, PRH_FnAlloc 4d8aeba047e5): the p = 0 arm passes fuzz_malloc's own clause on;
   CHOSEN-FAIL fails its cnt <> fail premise; SUCCESS granted (res = nb + 16) at the position after HRe; REFUSED is dead
   at a consumer allocation of the run (the kit's PRH_Refute.prh_refute_at on the realloc's NULL witness mt_refused).
   THE STAND-INS the final instance discharges (Section hypotheses): PAL (the image binding of B); the walk's static set
   PST (the five written statics) with PST_ok / PST_cells / PST_errno / PST_sub (it lies in the prh_pst) /
   PST_own_out / PST_most_out; MOST_ok / OWN_ok (g_most and g_own_ran_out are image bytes no allocator owns, not
   errno, never written by the walk, so every journal keeps them); the callee texts FMALLOC (the tfuzz_malloc_specX),
   AUNPOISON / APOISON (YGcfHp.v, cf form), AREAL_cf (the realloc keep row
   YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep at every ghost set and headroom; its discharge is the top-level
   assembler's); CF_unpoison / CF_poison (the CfImg's two runtime call targets are the listing's entries; {ci} stays
   abstract); the cf layer's RELRO image rows RELRO_SEG / ERRNO_RELRO / RELRO_TOP / RO_READS_NW / RELRO_EQ and PST_aro
   (lib/A/CfAroPresetA.v and computation).
   Numerals: slot offsets (DERIVED: 4 * slot), the frame 64 (LENGTH: `addi sp, sp, -64`), the head 16 and its offsets
   (LENGTH: alloc.c HEAD), atom indices (DERIVED: the engine's numbering), register numbers (WORD), 2 ^ k bounds
   (DERIVED / WORD), the stack budgets 16480 / 16416 (DERIVED: STK_fuzz_realloc / STK_fuzz_malloc, by vm_compute).
   No ADDRESS literal: every address is A_prog_sigma / A_prog_val of lib/A/PAImg_prog.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YG0sshcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallPx YGcallPcf YGcallRx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfHp YGcfRealloc YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfApath YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfRoomStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
(* the realloc re-hiding restate (round6g): the keep call rule over R := wle' RZ_cf (YGcallRkKeep, the cf row
   YGcfInstReallocKKeep), the primed relation (YA0nH, YGcfRehidePost), the R runners and branch (YSRrG), the lift at the
   top's entry (YGcfRhLift), the call memory's RELRO fact (YGcfAroBridge) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YGcallRkKeep YGcfAroBridge.
(* the hull PRE of the kit's primed text and its use: the budget gives the call's admission (PresetHullPay), the realloc
   step's secs post (YGcfSecsStep) gives the use (PresetHullBudget) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetRun PresetReqAt
  PresetLiveBounds.
(* the outcome clause's refused arm: the kit's refutation family (P8 at the run position, the realloc's NULL witness on
   granted paths) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the head read (A 0x854c8-0x85524): eight lbu of the head bytes recombined by slli / or are the head word.
   Same shape as image B's (S1ReallocB, lib/B/Prog/FuzzReallocB.v hdr_sv); restated here so this file does not
   depend on image B's walk. ---- *)
Definition ra_hb (x : nat) (s : Z) : sv := SExt false 8 (SAlu ALU_SRL (SOff x 0) (SLit s)).
Definition ra_hsll (v : sv) (t : Z) : sv := SAlu ALU_SLL v (SLit t).
Definition ra_hhalf (b3 b2 b1 b0 : sv) : sv :=
  SAlu ALU_OR (SAlu ALU_OR (ra_hsll b3 24) (ra_hsll b2 16)) (SAlu ALU_OR (ra_hsll b1 8) b0).
Definition ra_hdr_sv (x : nat) : sv :=
  SAlu ALU_OR (ra_hsll (ra_hhalf (ra_hb x 56) (ra_hb x 48) (ra_hb x 40) (ra_hb x 32)) 32)
    (ra_hhalf (ra_hb x 24) (ra_hb x 16) (ra_hb x 8) (SExt false 8 (SOff x 0))).
Lemma ra_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma ra_land63 : forall s, 0 <= s < 64 -> Z.land s 63 = s.
Proof. intros s Hs. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma ra_lor_add : forall a b s, 0 <= a -> 0 <= s -> 0 <= b < 2 ^ s -> Z.lor (a * 2 ^ s) b = a * 2 ^ s + b.
Proof.
intros a b s Ha Hs Hb. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
destruct (Z.lt_ge_cases n s) as [Hl|Hl].
- rewrite Z.mul_pow2_bits_low by lia.
  rewrite <- (Z.mod_pow2_bits_low (a * 2 ^ s + b) s n Hl).
  rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia. reflexivity.
- rewrite Z.mul_pow2_bits by lia.
  assert (Hbn : Z.testbit b n = false).
  { destruct (Z.eq_dec b 0) as [->|Hb0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
    apply (Z.lt_le_trans _ (2 ^ s)); [lia | apply Z.pow_le_mono_r; lia]. }
  rewrite Hbn, Bool.orb_false_r.
  assert (Ht : Z.testbit (a * 2 ^ s + b) n = Z.testbit ((a * 2 ^ s + b) / 2 ^ s) (n - s)).
  { rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia. f_equal; lia. }
  rewrite Ht. rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
  rewrite (Z.div_small b) by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma ra_U_hb : forall E x s, 0 <= s < 64 -> U E (ra_hb x s) = (bv_unsigned (ew E x) / 2 ^ s) mod 256.
Proof.
intros E x s Hs. unfold ra_hb. rewrite U_SExt, U_SAlu, U_SLit, U_SOff, Z.add_0_r. cbn [zalu_raw].
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
rewrite (ra_zc (bv_unsigned (ew E x))) by lia. rewrite (ra_zc s) by lia. rewrite ra_land63 by lia.
rewrite Z.shiftr_div_pow2 by lia.
assert (H0 : 0 <= bv_unsigned (ew E x) / 2 ^ s < 2 ^ 64).
{ split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (bv_unsigned (ew E x))); [apply Z.div_le_upper_bound; nia | lia]. }
rewrite (ra_zc (bv_unsigned (ew E x) / 2 ^ s)) by lia. change (2 ^ Z.of_N 8) with 256.
apply ra_zc. pose proof (Z.mod_pos_bound (bv_unsigned (ew E x) / 2 ^ s) 256 ltac:(lia)). lia.
Qed.
Lemma ra_U_hb0 : forall E x, U E (SExt false 8 (SOff x 0)) = (bv_unsigned (ew E x) / 2 ^ 0) mod 256.
Proof.
intros E x. rewrite U_SExt, U_SOff, Z.add_0_r. change (2 ^ 0) with 1. rewrite Z.div_1_r.
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
rewrite (ra_zc (bv_unsigned (ew E x))) by lia. change (2 ^ Z.of_N 8) with 256.
apply ra_zc. pose proof (Z.mod_pos_bound (bv_unsigned (ew E x)) 256 ltac:(lia)). lia.
Qed.
Lemma ra_U_hsll : forall E v t c, U E v = c -> 0 <= c -> 0 <= t < 64 -> c * 2 ^ t < 2 ^ 64 ->
  U E (ra_hsll v t) = c * 2 ^ t.
Proof.
intros E v t c Hv Hc Ht Hlt. unfold ra_hsll. rewrite U_SAlu, U_SLit, Hv. cbn [zalu_raw].
rewrite (ra_zc t) by lia. rewrite ra_land63 by lia. rewrite Z.shiftl_mul_pow2 by lia.
apply ra_zc. assert (0 <= c * 2 ^ t) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma ra_U_hor : forall E u v a s b, U E u = a * 2 ^ s -> U E v = b -> 0 <= a -> 0 <= s -> 0 <= b < 2 ^ s ->
  a * 2 ^ s + b < 2 ^ 64 -> U E (SAlu ALU_OR u v) = a * 2 ^ s + b.
Proof.
intros E u v a s b Hu Hv Ha Hs Hb Hlt. rewrite U_SAlu, Hu, Hv. cbn [zalu_raw]. rewrite ra_lor_add by lia.
apply ra_zc. assert (0 <= a * 2 ^ s) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma ra_dm : forall w k k', 0 <= w -> 0 <= k -> k' = k + 8 ->
  w / 2 ^ k = (w / 2 ^ k) mod 256 + 256 * (w / 2 ^ k').
Proof.
intros w k k' Hw Hk ->. rewrite (Z.div_mod (w / 2 ^ k) 256) at 1 by lia.
rewrite Z.div_div by (try apply Z.pow_nonzero; lia). rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.
Lemma ra_hdr_U : forall E x, U E (ra_hdr_sv x) = bv_unsigned (ew E x).
Proof.
intros E x.
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
set (w := bv_unsigned (ew E x)) in *.
assert (BB : forall s, 0 <= (w / 2 ^ s) mod 256 < 256) by (intros s; apply Z.mod_pos_bound; lia).
pose proof (BB 0) as R0. pose proof (BB 8) as R8. pose proof (BB 16) as R16. pose proof (BB 24) as R24.
pose proof (BB 32) as R32. pose proof (BB 40) as R40. pose proof (BB 48) as R48. pose proof (BB 56) as R56.
set (b0 := (w / 2 ^ 0) mod 256) in *. set (b8 := (w / 2 ^ 8) mod 256) in *. set (b16 := (w / 2 ^ 16) mod 256) in *.
set (b24 := (w / 2 ^ 24) mod 256) in *. set (b32 := (w / 2 ^ 32) mod 256) in *. set (b40 := (w / 2 ^ 40) mod 256) in *.
set (b48 := (w / 2 ^ 48) mod 256) in *. set (b56 := (w / 2 ^ 56) mod 256) in *.
assert (HL : U E (ra_hhalf (ra_hb x 24) (ra_hb x 16) (ra_hb x 8) (SExt false 8 (SOff x 0))) =
  (b24 * 2 ^ 8 + b16) * 2 ^ 16 + (b8 * 2 ^ 8 + b0)).
{ unfold ra_hhalf. apply ra_U_hor; try lia.
  - replace ((b24 * 2 ^ 8 + b16) * 2 ^ 16) with (b24 * 2 ^ 24 + b16 * 2 ^ 16) by ring.
    apply ra_U_hor; try lia.
    + apply ra_U_hsll; [apply ra_U_hb; lia | lia | lia | lia].
    + apply ra_U_hsll; [apply ra_U_hb; lia | lia | lia | lia].
  - apply ra_U_hor; try lia.
    + apply ra_U_hsll; [apply ra_U_hb; lia | lia | lia | lia].
    + apply ra_U_hb0. }
assert (HH : U E (ra_hhalf (ra_hb x 56) (ra_hb x 48) (ra_hb x 40) (ra_hb x 32)) =
  (b56 * 2 ^ 8 + b48) * 2 ^ 16 + (b40 * 2 ^ 8 + b32)).
{ unfold ra_hhalf. apply ra_U_hor; try lia.
  - replace ((b56 * 2 ^ 8 + b48) * 2 ^ 16) with (b56 * 2 ^ 24 + b48 * 2 ^ 16) by ring.
    apply ra_U_hor; try lia.
    + apply ra_U_hsll; [apply ra_U_hb; lia | lia | lia | lia].
    + apply ra_U_hsll; [apply ra_U_hb; lia | lia | lia | lia].
  - apply ra_U_hor; try lia.
    + apply ra_U_hsll; [apply ra_U_hb; lia | lia | lia | lia].
    + apply ra_U_hb; lia. }
unfold ra_hdr_sv. rewrite (ra_U_hor E _ _ ((b56 * 2 ^ 8 + b48) * 2 ^ 16 + (b40 * 2 ^ 8 + b32)) 32
  ((b24 * 2 ^ 8 + b16) * 2 ^ 16 + (b8 * 2 ^ 8 + b0))); [| apply ra_U_hsll; [exact HH | lia | lia | lia] | exact HL | lia | lia | lia | lia].
pose proof (ra_dm w 0 8 ltac:(lia) ltac:(lia) eq_refl) as D0. pose proof (ra_dm w 8 16 ltac:(lia) ltac:(lia) eq_refl) as D8.
pose proof (ra_dm w 16 24 ltac:(lia) ltac:(lia) eq_refl) as D16. pose proof (ra_dm w 24 32 ltac:(lia) ltac:(lia) eq_refl) as D24.
pose proof (ra_dm w 32 40 ltac:(lia) ltac:(lia) eq_refl) as D32. pose proof (ra_dm w 40 48 ltac:(lia) ltac:(lia) eq_refl) as D40.
pose proof (ra_dm w 48 56 ltac:(lia) ltac:(lia) eq_refl) as D48. pose proof (ra_dm w 56 64 ltac:(lia) ltac:(lia) eq_refl) as D56.
assert (Z0 : w / 2 ^ 0 = w) by (change (2 ^ 0) with 1; apply Z.div_1_r).
assert (Z64 : w / 2 ^ 64 = 0) by (apply Z.div_small; lia).
fold b0 b8 b16 b24 b32 b40 b48 b56 in D0, D8, D16, D24, D32, D40, D48, D56.
clearbody b0 b8 b16 b24 b32 b40 b48 b56 w. clear HL HH BB.
rewrite Z0 in D0. rewrite Z64 in D56. clear Z0 Z64.
remember (w / 2 ^ 8) as q8 eqn:Q8. remember (w / 2 ^ 16) as q16 eqn:Q16. remember (w / 2 ^ 24) as q24 eqn:Q24.
remember (w / 2 ^ 32) as q32 eqn:Q32. remember (w / 2 ^ 40) as q40 eqn:Q40. remember (w / 2 ^ 48) as q48 eqn:Q48.
remember (w / 2 ^ 56) as q56 eqn:Q56. clear Q8 Q16 Q24 Q32 Q40 Q48 Q56.
change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *. change (2 ^ 32) with 4294967296 in *.
lia.
Qed.
Lemma ra_hdr_denot : forall E x, sv_denot E (ra_hdr_sv x) = ew E x.
Proof. intros E x. apply bv_eq. exact (ra_hdr_U E x). Qed.

(* ---- the symbolic states at fuzz_realloc's entry (atoms per the listing lane's internal file INTERFACE.md: A_OBJ 0 the shadow-base GOT
   cell, A_OBJ 12 the cell it points to, A_OBJ 7 .. 11 g_count, g_fail_at, g_live, g_peak, g_ran_out, A_OBJ 14 g_most).
   p <> 0 (ss_ra): atoms 2 = entry sp, 10 = p, 11 = n, 32 = the shadow offset, 33 .. 36 = g_count, g_fail_at, g_live,
   g_peak, 37 = the old block's head word k, 38 = g_ran_out, 39 = g_most (NEW on A': refused() reads it); regions: the
   64-byte frame, the GOT slot and the cell (read only), the four 8-byte statics (read and written), g_ran_out's byte
   (written), the old head (read only here), g_most (read only); the static stores' alias rows are the generated
   A_alias_hints. p = 0 (ss_ra0): the frame only. ---- *)
Definition RA_PC : Z := 4 * Z.of_nat (A_prog_slot AS_fuzz_realloc).
Definition RA_Bx : sv := SOff 32 0.
Definition RA_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ra_st (j x : nat) : YP09.region := YP09.mkRegion (Some (A_OBJ j)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff x 0))].
Definition ra_ran : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 11)) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition ra_most : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 14)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
Definition ra_hdr (w : Z) : YP09.region :=
  YP09.mkRegion (Some 10%nat) (-16) (-8) (-16) (-16 + w) [YP09.mkChunk (-16) (CVal 8 (SOff 37 0))].
Definition ra_regions : smem :=
  [ stack_region 64; got_regionP; bcell_regionP 32; ra_st 7 33; ra_st 8 34; ra_st 9 35; ra_st 10 36; ra_ran; ra_hdr 0;
    ra_most ].
Definition ra_obj (j : nat) : nat * afact := (A_OBJ j, mkAF (A_prog_val (A_OBJ j)) (A_prog_val (A_OBJ j)) 0).
Definition ra_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4112 (2 ^ 47 - 2 ^ 23) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           ra_obj 7; ra_obj 8; ra_obj 9; ra_obj 10; ra_obj 11; ra_obj 14] [] A_alias_hints.
Definition ss_ra : sstate := mkSS RA_PC sr_atoms ra_regions None ra_facts.
Definition ss_ra0 : sstate := mkSS RA_PC sr_atoms [stack_region 64] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* the head's shadow entry after the unpoison: its 16 bytes read shadow 0 *)
Definition ra_SH1 : list shent := [mkSHE 10 (-16) 0].

(* ---- the cut states: the runner's own results (the run / branch / call-return the walk tactics make), by name ---- *)
Definition ra_tpi : ptree asym := A_prog_tpi.
Definition ra_tw : ctable := A_prog_tw.
Definition ra_K (SH : list shent) (ss : sstate) : nat := run_K A_LIM RA_Bx SH ss.
(* the state a run stops in (a branch, a call, a `ret`) *)
Definition ra_run (SH : list shent) (ss : sstate) : sstate :=
  sh_ss (fst (sym_runN_pi_tok ra_tpi ra_tw (ra_K SH ss) RA_Bx RA_Bspan SH YP03.FUEL ss)).
Definition ra_run_to (SH : list shent) (stop : Z) (ss : sstate) : sstate :=
  sh_ss (fst (sym_run_toN_pi_tok ra_tpi ra_tw (ra_K SH ss) RA_Bx RA_Bspan SH YP03.FUEL stop ss)).
Definition ra_stop (SH : list shent) (ss : sstate) : ptrun_status asym :=
  snd (sym_runN_pi_tok ra_tpi ra_tw (ra_K SH ss) RA_Bx RA_Bspan SH YP03.FUEL ss).
(* the branch a state is stuck at, and the two arms paj_branch makes of it *)
Definition ra_why (SH : list shent) (ss : sstate) : ptres asym :=
  sym_step_pi_tok ra_tpi ra_tw (ra_K SH ss) RA_Bx RA_Bspan SH (YCbn.start (ra_K SH ss) RA_Bx RA_Bspan SH ss).
Definition ra_arm (tk : bool) (SH : list shent) (ss : sstate) : sstate :=
  match ra_why SH ss with
  | PTStop (SR_branch c a b) => add_cond ss (mkAC (if tk then c else neg_bc c) a b)
  | _ => ss
  end.
(* the state after a call that keeps the regions idxs, with the clobber atoms from k (YC1fP's jafter_call_keep_pi) *)
Definition ra_after_call (ss : sstate) (idxs : list nat) (k : nat) : sstate :=
  ss_after_call ss (pick (ss_mem ss) idxs) k (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end).

(* The cut states of the segment plan (the internal file AL3-plan.md section 3.1), A' pcs as offsets from RA_PC (DERIVED: 4 * slot);
   each is the symbolic state the walk's tactic reaches there (checked: the stop reasons in the comments are the
   runner's, ra_stop / ra_why at these states).
   p <> 0:
   ss_cnt     +0x54 (0x85900)  `bne g_count, g_fail_at`            (S1 stops; SR_branch BC_NE (SOff 33 0) (SOff 34 0))
   ss_go      the bne taken: cnt <> fail                            (S1's go cut)
   ss_cf      the bne not taken: cnt = fail, CHOSEN-FAIL            (S1's fail cut)
   ss_cf_ret  +0x30c (0x85bb8) the epilogue's `ret`                 (S2's end: SR_jalr (SOff 1 0))
   ss_tb      +0x98 (0x85944)  `bltu n, -16`                         (S3 stops; SR_branch BC_LTU (SOff 11 0) (SLit (2^64-16)))
   ss_tb_go   the bltu taken: n < 2 ^ 64 - 16 (the TOOBIG arm is the other one)
   ss_unp     +0xf0 (0x8599c)  `jal __asan_unpoison_memory_region`   (S4's end: PTS_call; a0 = p - 16, a1 = 16)
   ss_unp_ret +0xf4 (0x859a0)  after the unpoison call, all ten regions kept, clobbers from atom 40 (CU's end)
   ss_head    +0x178 (0x85a24) before `sub a0, a1, s6` (RA_PC + 376; V1 RA_PC + 312)   (S5's run-to stop)
   ss_pin     ss_head with s6 (x22) := SOff 37 0, the head word k  (S5's end)
   ss_real    +0x188 (0x85a34) `jal __wrap_realloc`                  (S6's end: PTS_call; a0 = p - 16, a1 = n + 16)
   p = 0:
   ss_z0      +0x28 (0x858d4)  `beqz p`                              (Z0 stops; SR_branch BC_EQ (SOff 10 0) (SLit 0))
   ss_z0t     the beqz taken: p = 0                                 (Z0's end)
   ss_tail    +0x90 (0x8593c)  the tail `j fuzz_malloc`              (Z1's end: PTS_call AS_fuzz_malloc) *)
Definition ss_cnt : sstate := Eval vm_compute in ra_run [] ss_ra.
Definition ss_go : sstate := Eval vm_compute in ra_arm true [] ss_cnt.
Definition ss_cf : sstate := Eval vm_compute in ra_arm false [] ss_cnt.
Definition ss_cf_ret : sstate := Eval vm_compute in ra_run [] ss_cf.
Definition ss_tb : sstate := Eval vm_compute in ra_run [] ss_go.
Definition ss_tb_go : sstate := Eval vm_compute in ra_arm true [] ss_tb.
Definition ss_unp : sstate := Eval vm_compute in ra_run [] ss_tb_go.
Definition ss_unp_ret : sstate := Eval vm_compute in ra_after_call ss_unp [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat 40.
Definition RA_PIN : Z := RA_PC + 376.
Definition ss_head : sstate := Eval vm_compute in ra_run_to ra_SH1 RA_PIN ss_unp_ret.
Definition ss_pin : sstate := Eval vm_compute in
  mkSS (ss_pc ss_head) (sr_set (ss_regs ss_head) 22%bv (SOff 37 0)) (ss_mem ss_head) (ss_resv ss_head) (ss_facts ss_head).
Definition ss_real : sstate := Eval vm_compute in ra_run ra_SH1 ss_pin.
Definition ss_z0 : sstate := Eval vm_compute in ra_run [] ss_ra0.
Definition ss_z0t : sstate := Eval vm_compute in ra_arm true [] ss_z0.
Definition ss_tail : sstate := Eval vm_compute in ra_run [] ss_z0t.
(* the stop reasons (the comments above), checked *)
Lemma ra_stops :
  ra_stop [] ss_ra = PTS_stopped (SR_branch BC_NE (SOff 33 0) (SOff 34 0)) /\
  ra_stop [] ss_cf = PTS_stopped (SR_jalr (SOff 1 0)) /\
  ra_stop [] ss_go = PTS_stopped (SR_branch BC_LTU (SOff 11 0) (SLit (2 ^ 64 - 16))) /\
  ra_stop [] ss_tb_go = PTS_call AS___asan_unpoison_memory_region /\
  ra_stop ra_SH1 ss_pin = PTS_call AS___wrap_realloc /\
  ra_stop [] ss_ra0 = PTS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0)) /\
  ra_stop [] ss_z0t = PTS_call AS_fuzz_malloc.
Proof. vm_compute. repeat split. Qed.
Lemma ra_cut_pcs :
  ss_pc ss_cnt = RA_PC + 84 /\ ss_pc ss_cf_ret = RA_PC + 780 /\ ss_pc ss_tb = RA_PC + 152 /\
  ss_pc ss_unp = RA_PC + 244 /\ ss_pc ss_unp_ret = RA_PC + 244 /\ ss_pc ss_head = RA_PIN /\
  ss_pc ss_real = RA_PC + 396 /\ ss_pc ss_z0 = RA_PC + 40 /\ ss_pc ss_tail = RA_PC + 144.
Proof. vm_compute. repeat split. Qed.

#[local] Abbreviation PA := (PI_prog_A).
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
#[local] Existing Instance CfParams_preset.

(* the image numbers a walk compares, computed from the generated instance, never typed *)
Ltac ra_lits0 :=
  repeat match goal with
  | |- context [A_prog_val ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v
  end.
(* the value widths of the statics the walk writes (LENGTH, asan_globals: size_t 8, `static int g_ran_out` ONE byte) *)
Definition ra_w (j : nat) : Z := if (j =? 11)%nat then 1 else 8.
(* the written statics as byte ranges of the listing's atoms; writable in the image, by computation *)
Definition ra_cells : list (Z * Z) :=
  [(A_prog_val (A_OBJ 7), 8); (A_prog_val (A_OBJ 8), 8); (A_prog_val (A_OBJ 9), 8); (A_prog_val (A_OBJ 10), 8);
   (A_prog_val (A_OBJ 11), 1)].
Lemma ra_cells_wv : S1ImgCheck.pst_allb (S1ImgCheck.wv_b rsegs) ra_cells = true.
Proof. vm_compute. reflexivity. Qed.
Ltac ra_ex_zr := repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
Lemma ra_cell_in : forall j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j ->
  Exists (in_zr (A_prog_val (A_OBJ j) + o)) ra_cells.
Proof.
intros j o Hj Ho. unfold ra_cells, ra_w in *.
destruct j as [|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]; try lia; cbn [Nat.eqb] in Ho; ra_ex_zr.
Qed.
Lemma ra_writable : forall (m : word -> option byte) j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j ->
  writable_at rsegs m (A_prog_val (A_OBJ j) + o).
Proof.
intros m j o Hj Ho. apply S1ImgCheck.writable_of_wv_b. exact (S1ImgCheck.pst_allb_sound _ _ _ ra_cells_wv (ra_cell_in j o Hj Ho)).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
Lemma ra_val : forall j, VAL j = A_prog_val j.
Proof. reflexivity. Qed.
Ltac ra_lits := rewrite ?ra_val; ra_lits0.
(* atoms 32 .. 39: the shadow base, the four 8-byte statics' entry values, the old head word, g_ran_out, g_most
   (cgif's extra-atom convention) *)
Definition RA_E (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) xs)).
Lemma RA_E_img : forall regs xs j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew (RA_E regs xs) j) = VAL j.
Proof. intros regs xs j Hj. unfold RA_E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. Qed.
Lemma RA_E_reg : forall regs xs n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (RA_E regs xs) n = getr regs x.
Proof.
intros regs xs n x Hn. unfold RA_E. pose proof (u5_range x) as Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n x Hn).
Qed.
Definition RA_X (c f l p k r m : Z) : list Z := [SHADOW_OFF; c; f; l; p; k; r; m].
Lemma RA_E_extra : forall regs c f l p k r m,
  ew (RA_E regs (RA_X c f l p k r m)) 32 = Z_to_bv 64 SHADOW_OFF /\
  ew (RA_E regs (RA_X c f l p k r m)) 33 = Z_to_bv 64 c /\
  ew (RA_E regs (RA_X c f l p k r m)) 34 = Z_to_bv 64 f /\
  ew (RA_E regs (RA_X c f l p k r m)) 35 = Z_to_bv 64 l /\
  ew (RA_E regs (RA_X c f l p k r m)) 36 = Z_to_bv 64 p /\
  ew (RA_E regs (RA_X c f l p k r m)) 37 = Z_to_bv 64 k /\
  ew (RA_E regs (RA_X c f l p k r m)) 38 = Z_to_bv 64 r /\
  ew (RA_E regs (RA_X c f l p k r m)) 39 = Z_to_bv 64 m.
Proof. intros regs c f l p k r m. unfold RA_E, RA_X. rewrite !Eimg_low by (unfold A_TEXT; lia). repeat split. Qed.
Lemma ra_entry_pc : SIGMA AS_fuzz_realloc = BASE + RA_PC.
Proof. vm_compute. reflexivity. Qed.
(* the image hull, by its generated names *)
Lemma ra_img_range : forall a, in_img SEGS a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP.
Proof. intros a Ha. exact (pa_img_range a Ha). Qed.
Lemma ra_obj_img : forall i, (i < 39)%nat -> YImgTop.IMG_LO <= VAL (A_OBJ i) /\ VAL (A_OBJ i) + 8 <= YImgTop.IMG_TOP.
Proof. intros i Hi. exact (pa_obj_img i Hi). Qed.

Section f.
Variable B : asyms.
(* the allocator relation: the allocator lane's ARcf with the error-buffer extents placed (S1KitAlloc's YGcallcf.v) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the image binding of B (PALib: GOT cell, shadow cell, allocator entries), proved once by the final instance *)
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
(* the journal's program statics: the instance takes the prh_pst; the walk needs two facts of it, both proved at the
   instance by computation (the statics are image bytes no allocator owns; the five written cells are in it) *)
Variable PST : list (Z * Z).
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis PST_cells : forall j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j -> Exists (in_zr (A_prog_val (A_OBJ j) + o)) PST.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B).
(* the size fact at ARcf (S1Ledger's prh_ablocks_nonneg_cf, restated: this file imports no ledger) *)
Lemma ra_ablocks_nonneg : forall ly S Hp (W : world SEGS) mem md,
  ARcf SEGS B ly S Hp W mem md -> Forall (fun b => 0 <= snd b) (ablocks B ly S).
Proof.
intros ly S Hp W mem md (M & _).
pose proof (wfc_chunks _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as HC.
unfold ablocks, YG01.blocks. rewrite Forall_forall in HC |- *. intros x Hx.
apply in_map_iff in Hx as (y & <- & Hy). apply in_map_iff in Hy as (k & <- & Hk).
apply filter_In in Hk as [Hk _]. cbn [snd]. exact (proj1 (proj1 (HC k Hk))).
Qed.
(* a block lies off the image range (blk_off_imgPI's twin at ARcf: ALedger_cf's image cover and the client law) *)
Lemma ra_blk_off_img : forall ly S Hp (W : world SEGS) mem md b n, ARcfx ly S Hp W mem md -> In (b, n) (ablocks B ly S) ->
  b + req_size n <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= b.
Proof.
intros ly S Hp W mem md b n HAR Hin. pose proof HAR as ((_ & LG & _) & _).
pose proof (alc_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [C1 _].
pose proof (alc_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ C2].
cbn in C1, C2.
pose proof (proj1 (Forall_forall _ _) (ra_ablocks_nonneg ly S Hp W mem md (proj1 HAR)) _ Hin) as Hn0.
cbn [snd] in Hn0.
assert (Hr0 : 0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct (Z.le_gt_cases (b + req_size n) YImgTop.IMG_LO) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases YImgTop.IMG_TOP b) as [|H2]; [right; lia|]. exfalso.
destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max b YImgTop.IMG_LO) HAR) as [Hn _];
  [left; exists b, n; split; [exact Hin | unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia] |].
apply Hn. unfold in_zr. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
Qed.

(* the statics' values at entry, keyed by the listing's atoms (the prh_glob + prh_most give them by ra_pst_vals-style
   computation at the instance; stated here so no PrhImg is imported) *)
Definition ra_glob (W : world SEGS) (mem : word -> option byte) (cnt fail live peak ran most : Z) : Prop :=
  val_mem SEGS (mrestrict (w_H W) mem) (A_prog_val (A_OBJ 7)) 8 cnt /\
  val_mem SEGS (mrestrict (w_H W) mem) (A_prog_val (A_OBJ 8)) 8 fail /\
  val_mem SEGS (mrestrict (w_H W) mem) (A_prog_val (A_OBJ 9)) 8 live /\
  val_mem SEGS (mrestrict (w_H W) mem) (A_prog_val (A_OBJ 10)) 8 peak /\
  val_mem SEGS (mrestrict (w_H W) mem) (A_prog_val (A_OBJ 11)) 1 ran /\
  val_mem SEGS (mrestrict (w_H W) mem) (A_prog_val (A_OBJ 14)) 8 most /\
  0 <= cnt < 2 ^ 64 /\ 0 <= fail < 2 ^ 64 /\ 0 <= live < 2 ^ 64 /\ 0 <= peak < 2 ^ 64 /\ (ran = 0 \/ ran = 1) /\
  0 <= most < 2 ^ 64.

(* ---- the entry seats: fuzz_realloc's entry state as the symbolic state ss_ra (p <> 0) / ss_ra0 (p = 0) ---- *)
Lemma ra_entry : forall STK ly S Hp (W : world SEGS) regs mem md ch p k cnt fail live peak ran most,
  afn_pre_x SEGS B ARcfx STK ly S Hp W regs mem md ch -> 64 <= STK ->
  getr regs 10 = w64 p -> In (p - 16, k + 16) (ablocks B ly S) -> 0 <= k ->
  val_mem SEGS (mrestrict (w_H W) mem) (p - 16) 8 k ->
  ra_glob W mem cnt fail live peak ran most ->
  st_ok_pi SEGS VAL (RA_E regs (RA_X cnt fail live peak k ran most)) ss_ra
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RA_PC)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS RA_Bx [] (RA_E regs (RA_X cnt fail live peak k ran most)) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch p k cnt fail live peak ran most HPRE H64 H10 Hin Hk Hhd HG.
pose proof HPRE as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct HG as (Mcnt & Mfail & Mlive & Mpeak & Mran & Mmost & Rc & Rf & Rl & Rp & Rr & Rm).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (k + 16) (conj HAR HXS) Hin) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
assert (Hreq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
destruct (alc_const _ _ (AR_laws_ok_cf SEGS B) ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
pose proof (pal_got_cell B PAL) as HgcD.
pose proof (ra_blk_off_img ly S Hp W mem md (p - 16) (k + 16) (conj HAR HXS) Hin) as Hoff. rewrite Hreq in Hoff.
assert (Hobj : forall j, (j < 39)%nat -> YImgTop.IMG_LO <= VAL (A_OBJ j) /\ VAL (A_OBJ j) + 8 <= YImgTop.IMG_TOP)
  by (intros j Hj; exact (pa_obj_img j Hj)).
rewrite restrict_mkst_fx.
set (E := RA_E regs (RA_X cnt fail live peak k ran most)).
destruct (RA_E_extra regs cnt fail live peak k ran most) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39).
fold E in E32, E33, E34, E35, E36, E37, E38, E39.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (Up : bv_unsigned (ew E 10) = p)
  by (subst E; rewrite (RA_E_reg _ _ 10 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j) by (intros j Hj; subst E; apply RA_E_img; exact Hj).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold RA_E; apply Eimg_env).
assert (Dv : forall (x : nat) v, ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff x 0) = Z_to_bv 64 v).
{ intros x v Hx Hv. cbn [sv_denot]. rewrite Hx, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j) by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
assert (Ww : forall (m : word -> option byte) j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j ->
  writable_at SEGS m (VAL (A_OBJ j) + o)) by (intros m j o Hj Ho; exact (ra_writable m j o Hj Ho)).
split.
- unfold ss_ra. apply pa_entry_st_ok_full.
  + subst E. unfold RA_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ra_regions, stack_region, got_regionP, bcell_regionP, ra_st, ra_ran, ra_hdr, ra_most.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 12)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * pose proof (pa_val_range (A_OBJ 12)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [apply Dv; [exact E32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * pose proof (pa_val_range (A_OBJ 7)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; apply (Ww _ 7%nat); cbn; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 33 0) cnt); [apply Dv; [exact E33 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Mcnt.
    * pose proof (pa_val_range (A_OBJ 8)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; apply (Ww _ 8%nat); cbn; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 34 0) fail); [apply Dv; [exact E34 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Mfail.
    * pose proof (pa_val_range (A_OBJ 9)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; apply (Ww _ 9%nat); cbn; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 35 0) live); [apply Dv; [exact E35 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Mlive.
    * pose proof (pa_val_range (A_OBJ 10)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; apply (Ww _ 10%nat); cbn; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 36 0) peak); [apply Dv; [exact E36 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Mpeak.
    * pose proof (pa_val_range (A_OBJ 11)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; apply (Ww _ 11%nat); cbn [ra_w Nat.eqb]; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 38 0) ran); [apply Dv; [exact E38 | lia] | cbn; lia | lia | exact Mran].
    * cbn [base_val]. rewrite Up. split; [lia|]. split; [lia|].
      split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p (-16) 8 (SOff 37 0) k); [apply Dv; [exact E37 | lia] | lia | lia |].
      replace (p + -16) with (p - 16) by lia. exact Hhd.
    * pose proof (pa_val_range (A_OBJ 14)).
      split; [lia|]. split; [ra_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 39 0) most); [apply Dv; [exact E39 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Mmost.
  + unfold ra_regions, stack_region, got_regionP, bcell_regionP, ra_st, ra_ran, ra_hdr, ra_most.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    cbn [base_val]. rewrite Usp, Up. rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    pose proof (Hobj 0%nat ltac:(lia)) as I0. pose proof (Hobj 12%nat ltac:(lia)) as I12.
    pose proof (Hobj 7%nat ltac:(lia)) as I7. pose proof (Hobj 8%nat ltac:(lia)) as I8.
    pose proof (Hobj 9%nat ltac:(lia)) as I9. pose proof (Hobj 10%nat ltac:(lia)) as I10.
    pose proof (Hobj 11%nat ltac:(lia)) as I11. pose proof (Hobj 14%nat ltac:(lia)) as I14.
    rewrite !ra_val in I0, I12, I7, I8, I9, I10, I11, I14.
    revert I0 I12 I7 I8 I9 I10 I11 I14 HgcD Hoff. cbn [pa_val PI_prog_A]. ra_lits0. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP.
    intros I0 I12 I7 I8 I9 I10 I11 I14 HgcD Hoff.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + split; [|split; [exact I | exact (A_alias_hints_ok E HEI)]].
    unfold ra_facts, ra_obj. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Up, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia). cbn [pa_val PI_prog_A].
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hp16 : p mod 16 = 0) by (replace p with ((p - 16) + 1 * 16) by lia; rewrite Z.mod_add by lia; exact Hb16).
    pose proof ASAN_CEIL_range as HCE. unfold ASAN_CEIL in HCE.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
- unfold sh_ok. apply Forall_nil.
Qed.

Lemma ra_entry0 : forall STK ly S Hp (W : world SEGS) regs mem md ch,
  afn_pre_x SEGS B ARcfx STK ly S Hp W regs mem md ch -> 64 <= STK ->
  st_ok_pi SEGS VAL (RA_E regs []) ss_ra0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RA_PC)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS RA_Bx [] (RA_E regs []) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch HPRE H64.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := RA_E regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
split.
- unfold ss_ra0. apply pa_entry_st_ok_full.
  + subst E. unfold RA_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
  + exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. repeat match goal with |- _ /\ _ => split end; try lia; exact I.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- helpers the walk uses at every stop (the template's, unchanged) ---- *)
Lemma ra_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma ra_region_ok : forall E ss ms r, st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms r HS Hin. destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r Hin).
Qed.
Lemma ra_kept_gen : forall E (m m' : word -> option byte) k b lo hi wlo whi cs, bv_unsigned (ew E k) = b ->
  (forall a, b + lo <= a < b + hi -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall a, b + wlo <= a < b + whi -> writable_at SEGS m' a) ->
  region_kept SEGS E m m' (YP09.mkRegion (Some k) lo hi wlo whi cs).
Proof.
intros E m m' k b lo hi wlo whi cs Hb Hm Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hb; intros a Ha;
  [exact (Hm a Ha) | intros _; exact (Hw a Ha)].
Qed.
Lemma ra_set_reg : forall E ss ms (r : bv 5) v, st_ok_pi SEGS VAL E ss ms ->
  sv_denot E v = sv_denot E (sr_get (ss_regs ss) r) -> bv_eqb r 0 = false ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r v HS Hv Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r v) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. exact Hv.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma ra_U_off : forall E0 E (k : nat) v c, env_agree 40 E0 E -> (k < 40)%nat -> ew E0 k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff k c) = (v + c) mod 2 ^ 64.
Proof.
intros E0 E k v c [A _] Hk He Hv. rewrite U_SOff, (A k Hk), He, unsigned_lit_small by exact Hv.
unfold zcanon, M64. reflexivity.
Qed.
Lemma ra_U0 : forall E0 E (k : nat) v, env_agree 40 E0 E -> (k < 40)%nat -> ew E0 k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff k 0) = v.
Proof. intros E0 E k v c Hk He Hv. rewrite (ra_U_off E0 E k v 0 c Hk He Hv), Z.add_0_r. apply Z.mod_small. exact Hv. Qed.

(* ---- the walk's tactics (the template's, at a variable stack budget and the Section's PST) ---- *)
Lemma ra_pst_lit : forall a, (exists j, (7 <= j <= 11)%nat /\ A_prog_val (A_OBJ j) <= a < A_prog_val (A_OBJ j) + ra_w j) ->
  Exists (in_zr a) PST.
Proof.
intros a (j & Hj & Ha). replace a with (A_prog_val (A_OBJ j) + (a - A_prog_val (A_OBJ j))) by lia.
apply PST_cells; [exact Hj | lia].
Qed.
Ltac ra_lits_in H :=
  repeat match type of H with context [@pa_val ?r ?L ?P ?j] =>
    let v := eval vm_compute in (@pa_val r L P j) in change (@pa_val r L P j) with v in H end;
  repeat match type of H with context [A_prog_val ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v in H end.
(* an address hypothesis with its atoms read off: the base facts (bv_unsigned (ew E j) = _) first, then the image
   atoms (img_env), then an agreement with an EARLIER env of the walk (never the register env Ereg) *)
Ltac ra_at H :=
  repeat match type of H with
  | context [bv_unsigned (ew ?Ex ?j)] =>
    first
    [ match goal with Ux : bv_unsigned (ew Ex j) = _ |- _ => rewrite Ux in H end
    | lazymatch goal with HEIx : img_env _ _ Ex |- _ => rewrite (HEIx j ltac:(unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia)) in H end
    | match goal with AGx : env_agree ?kk ?E0 Ex |- _ =>
        lazymatch E0 with Ex => fail | Ereg _ _ => fail | _ => rewrite (proj1 AGx j ltac:(lia)) in H end end ]
  end.
Ltac ra_pst_j j := exists j; split; [lia | cbn [ra_w Nat.eqb]; ra_lits0; lia].
Ltac ra_pst_lit_tac H :=
  apply ra_pst_lit; ra_lits_in H;
  first [ ra_pst_j 7%nat | ra_pst_j 8%nat | ra_pst_j 9%nat | ra_pst_j 10%nat | ra_pst_j 11%nat ].
(* the mixed runner's write premise, region by region: the frame, the statics (PST), a block (blk) *)
Ltac ra_wr blk :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; ra_at Ha;
           first [ exfalso; lia
                 | left; unfold awr_byte; left; lia
                 | right; ra_pst_lit_tac Ha
                 | blk Ha ] |]);
  destruct Hin.
(* an address in none of a run's write windows *)
Ltac ra_nw :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; ra_at Hr; ra_lits_in Hr;
           unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia |]);
  destruct Hin.
(* the env of a new state agrees with an earlier one below kk *)
Ltac ra_ag AGp :=
  split; [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
           rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact (proj1 AGp i Hi)
         | exact (proj2 AGp) ].
Ltac ra_newenv kk E0 HS AGp AGn :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?En _ _ => assert (AGn : env_agree kk E0 En) by ra_ag AGp
  | st_ok _ ?En _ _ => assert (AGn : env_agree kk E0 En) by ra_ag AGp
  end.

(* ---- THE CUTS. A cut is the symbolic state ss (plain st_ok at a callee's entry pc for a call cut), an env E that
   agrees with the entry env E0 below atom 40, the shadow entries SH, the journal from the entry (no allocator step yet:
   layout, state and counter kept, the ghost set Hpc), the overlay normal form kept (fpostm's memnorm), and the
   off-image bytes below the ceiling kept except the set X. ---- *)
Definition ra_P (mem0 m : word -> option byte) : Prop := YAkMemnorm.memnorm SEGS mem0 -> YAkMemnorm.memnorm SEGS m.
Definition ra_PLAW (mem0 : word -> option byte) : srr_inv_laws SEGS (ra_P mem0) :=
  YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS).
Definition ra_off (W : world SEGS) (mem m : word -> option byte) (X : Z -> Prop) : Prop :=
  forall a, 4096 <= a < alloc_ceiling -> (a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a) -> ~ X a ->
    aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a.
Definition ra_cut (STK sp0 : Z) (FP : list (Z * Z)) (E0 : env) (ss : sstate) (SH : list shent)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (Hpc : list Z) (X : Z -> Prop) (ms : machine_state) (mdc : Model) : Prop :=
  exists E, img_env VAL A_LIM E /\ env_agree 40 E0 E /\ st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) /\
    sh_ok SEGS RA_Bx SH E (mrestrict (w_H W) (ms_mem ms)) /\
    ajournal_x (SK := SK) SEGS B PST ARcfx STK sp0 FP ly S Hp W mem md [] ly S Hpc W (ms_mem ms) mdc 0 /\
    ra_P mem (ms_mem ms) /\ ra_off W mem (ms_mem ms) X.
Definition ra_cutc (pc : Z) (STK sp0 : Z) (FP : list (Z * Z)) (E0 : env) (ss : sstate) (SH : list shent)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (Hpc : list Z) (X : Z -> Prop) (ms : machine_state) (mdc : Model) : Prop :=
  exists E, img_env VAL A_LIM E /\ env_agree 40 E0 E /\ st_ok SEGS E (YP0l.setpc ss pc) (restrict (w_H W) ms) /\
    sh_ok SEGS RA_Bx SH E (mrestrict (w_H W) (ms_mem ms)) /\
    ajournal_x (SK := SK) SEGS B PST ARcfx STK sp0 FP ly S Hp W mem md [] ly S Hpc W (ms_mem ms) mdc 0 /\
    ra_P mem (ms_mem ms) /\ ra_off W mem (ms_mem ms) X.
(* a run's frame keeps ra_off when none of its write windows holds an off-image byte below the ceiling *)
Lemma ra_off_step : forall (W : world SEGS) E rs (mem mA mB : word -> option byte) X,
  frame_of E rs (mrestrict (w_H W) mA) (mrestrict (w_H W) mB) ->
  (forall a, 4096 <= a < alloc_ceiling -> (a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a) -> ~ in_wrange E rs a) ->
  ra_off W mem mA X -> ra_off W mem mB X.
Proof.
intros W E rs mem mA mB X HF Hn HK a Ha Hi Hx. pose proof (@alloc_ceiling_lt rc) as Hc.
rewrite (ra_aview_of_frame W E rs mA mB a HF (Hn a Ha Hi)) by lia. exact (HK a Ha Hi Hx).
Qed.
(* the entry cut (the entry seat + YCbqG's journal at its start) *)
Lemma ra_cut_entry : forall STK ly S Hp (W : world SEGS) regs mem md ch p k cnt fail live peak ran most FP,
  afn_pre_x SEGS B ARcfx STK ly S Hp W regs mem md ch -> 64 <= STK ->
  getr regs 10 = w64 p -> In (p - 16, k + 16) (ablocks B ly S) -> 0 <= k ->
  val_mem SEGS (mrestrict (w_H W) mem) (p - 16) 8 k ->
  ra_glob W mem cnt fail live peak ran most ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_ra [] ly S Hp W mem md Hp
    (fun _ => False) (mkst regs (Z_to_bv 64 (BASE + RA_PC)) mem (seg_rom SEGS)) md.
Proof.
intros STK ly S Hp W regs mem md ch p k cnt fail live peak ran most FP HPRE H64 H10 Hin Hk Hhd HG.
destruct (ra_entry STK ly S Hp W regs mem md ch p k cnt fail live peak ran most HPRE H64 H10 Hin Hk Hhd HG) as [HS SH].
exists (RA_E regs (RA_X cnt fail live peak k ran most)).
refine (conj _ (conj _ (conj HS (conj SH (conj _ (conj _ _)))))).
- unfold RA_E. apply Eimg_env.
- split; [intros; reflexivity | reflexivity].
- exact (ajournal_x_init (SK := SK) SEGS B PST ARcfx STK FP ly S Hp W regs mem md ch HPRE).
- intros H. exact H.
- intros a _ _ _. reflexivity.
Qed.
Lemma ra_cut_entry0 : forall STK ly S Hp (W : world SEGS) regs mem md ch,
  afn_pre_x SEGS B ARcfx STK ly S Hp W regs mem md ch -> 64 <= STK ->
  ra_cut STK (spZ regs) [] (RA_E regs []) ss_ra0 [] ly S Hp W mem md Hp
    (fun _ => False) (mkst regs (Z_to_bv 64 (BASE + RA_PC)) mem (seg_rom SEGS)) md.
Proof.
intros STK ly S Hp W regs mem md ch HPRE H64.
destruct (ra_entry0 STK ly S Hp W regs mem md ch HPRE H64) as [HS SH].
exists (RA_E regs []).
refine (conj _ (conj _ (conj HS (conj SH (conj _ (conj _ _)))))).
- unfold RA_E. apply Eimg_env.
- split; [intros; reflexivity | reflexivity].
- exact (ajournal_x_init (SK := SK) SEGS B PST ARcfx STK [] ly S Hp W regs mem md ch HPRE).
- intros H. exact H.
- intros a _ _ _. reflexivity.
Qed.

(* ---- the segment proofs' common steps ---- *)
(* the cut at the end of a segment, from the state the last run / branch left *)
Ltac ra_close :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ _ |- ra_cut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exists En; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
    [ assumption | assumption | exact HS | assumption | assumption | assumption | assumption ]
  | HS : st_ok _ ?En _ _ |- ra_cutc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exists En; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
    [ assumption | assumption | exact HS | assumption | assumption | assumption | assumption ]
  end.
(* one run of the mixed runner with the memnorm invariant, its write premise, the new env's agreement and ra_off *)
Ltac ra_step RUN E0 HS HJ SHOK HPM AG AGn KP KPn :=
  paj_run_tok_x_inv RUN HS HJ SHOK HPM RA_Bspan; [ra_wr ltac:(fun H => fail)|];
  ra_newenv 40%nat E0 HS AG AGn;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
    pose proof (ra_off_step Wx Ex rs _ mA mB _ HFr ltac:(intros ?a ?Ha ?Hi; ra_nw) KP) as KPn end.
Ltac ra_step_to RUN E0 HS HJ SHOK HPM AG AGn KP KPn stop :=
  paj_run_to_tok_x_inv RUN HS HJ SHOK HPM RA_Bspan stop; [ra_wr ltac:(fun H => fail)|];
  ra_newenv 40%nat E0 HS AG AGn;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
    pose proof (ra_off_step Wx Ex rs _ mA mB _ HFr ltac:(intros ?a ?Ha ?Hi; ra_nw) KP) as KPn end.
Ltac ra_cont K :=
  lazymatch goal with |- SRr _ _ (mkCfg ?m ?d) _ => apply (K m d); ra_close end.

(* the p = 0 arm writes only its frame [sp0 - 64, sp0): every other byte keeps its entry view *)
Definition ra_frame0 (sp0 : Z) (W : world SEGS) (mem m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a.
Ltac ra_frame0_step sp0 K0 K0n :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
  lazymatch type of K0 with ra_frame0 _ _ ?m0 _ =>
    assert (K0n : ra_frame0 sp0 Wx m0 mB);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
      rewrite (ra_aview_of_frame Wx Ex rs mA mB a HFr); [exact (K0 a Ha Hn) | | exact Ha];
      ra_nw | ] end end.
(* ---- Z0: p = 0, entry to the `beqz p` (+0x28); the fall-through (p <> 0) refuted ---- *)
Lemma ra_seg_z0 : forall STK ly S Hp (W : world SEGS) regs mem md ms mdc Q,
  64 <= STK -> alloc_ceiling <= spZ regs - STK -> getr regs 10 = w64 0 ->
  ra_cut STK (spZ regs) [] (RA_E regs []) ss_ra0 [] ly S Hp W mem md Hp (fun _ => False) ms mdc ->
  ra_frame0 (spZ regs) W mem (ms_mem ms) ->
  (forall ms' mdc', ra_cut STK (spZ regs) [] (RA_E regs []) ss_z0t [] ly S Hp W mem md Hp (fun _ => False) ms' mdc' ->
     ra_frame0 (spZ regs) W mem (ms_mem ms') -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK ly S Hp W regs mem md ms mdc Q H64 Hlo H10 (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K0 K.
set (E0 := RA_E regs []) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E0 10 = getr regs 10) by (subst E0; exact (RA_E_reg regs [] 10 10%bv eq_refl)).
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
pose proof (paj_branch (L := A_prog_listing) (PI := PA)) as BR.
ra_step RUN E0 HS HJ SHOK HPM AG AG1 KP KP1.
ra_frame0_step (spZ regs) K0 K1.
psrr_branch_tok RUN BR HS SHOK RA_Bspan.
2:{ exfalso. rewrite branch_eq_U, U_SLit in Hc.
    rewrite (ra_U0 E0 _ 10 0 AG1 ltac:(lia) ltac:(rewrite E10, H10; reflexivity) ltac:(lia)) in Hc.
    vm_compute in Hc. discriminate Hc. }
lazymatch goal with |- SRr _ _ (mkCfg ?m ?d) _ => apply (K m d); [ra_close | exact K1] end.
Qed.

(* ---- Z1: p = 0, the restore and pop to the TAIL `j fuzz_malloc` (+0x90): the cut at fuzz_malloc's entry ---- *)
Lemma ra_seg_z1 : forall STK ly S Hp (W : world SEGS) regs mem md ms mdc Q,
  64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  ra_cut STK (spZ regs) [] (RA_E regs []) ss_z0t [] ly S Hp W mem md Hp (fun _ => False) ms mdc ->
  ra_frame0 (spZ regs) W mem (ms_mem ms) ->
  (forall ms' mdc', ra_cutc (SIGMA AS_fuzz_malloc) STK (spZ regs) [] (RA_E regs []) ss_tail [] ly S Hp W mem md Hp
     (fun _ => False) ms' mdc' -> ra_frame0 (spZ regs) W mem (ms_mem ms') -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK ly S Hp W regs mem md ms mdc Q H64 Hlo (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K0 K.
set (E0 := RA_E regs []) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
ra_step RUN E0 HS HJ SHOK HPM AG AG1 KP KP1.
ra_frame0_step (spZ regs) K0 K1.
lazymatch goal with |- SRr _ _ (mkCfg ?m ?d) _ => apply (K m d); [ra_close | exact K1] end.
Qed.

(* ---- S1: the count step (+0x0 .. +0x54): prologue, the shadow offset, g_count += 1; the `bne` decides CHOSEN-FAIL ---- *)
Lemma ra_seg_count : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q k cnt fail live peak ran most X,
  64 <= STK -> alloc_ceiling <= spZ regs - STK -> 0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_ra [] ly S Hp W mem md Hp X ms mdc ->
  (cnt = fail -> forall ms' mdc', ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_cf []
     ly S Hp W mem md Hp X ms' mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  (cnt <> fail -> forall ms' mdc', ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_go []
     ly S Hp W mem md Hp X ms' mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q k cnt fail live peak ran most X H64 Hlo Rc Rf
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) Kcf Kgo.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
destruct (RA_E_extra regs cnt fail live peak k ran most) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39).
fold E0 in E32, E33, E34, E35, E36, E37, E38, E39.
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
pose proof (paj_branch (L := A_prog_listing) (PI := PA)) as BR.
ra_step RUN E0 HS HJ SHOK HPM AG AG1 KP KP1.
psrr_branch_tok RUN BR HS SHOK RA_Bspan.
- rewrite branch_ne_U, (ra_U0 E0 _ 33 cnt AG1 ltac:(lia) E33 Rc), (ra_U0 E0 _ 34 fail AG1 ltac:(lia) E34 Rf) in Hc.
  assert (Hcf : cnt <> fail) by (intros Heq; rewrite Heq, Z.eqb_refl in Hc; discriminate Hc).
  ra_cont (Kgo Hcf).
- rewrite branch_ne_U, (ra_U0 E0 _ 33 cnt AG1 ltac:(lia) E33 Rc), (ra_U0 E0 _ 34 fail AG1 ltac:(lia) E34 Rf) in Hc.
  assert (Hcf : cnt = fail) by (destruct (Z.eqb_spec cnt fail); [assumption | discriminate Hc]).
  ra_cont (Kcf Hcf).
Qed.

(* ---- S2: CHOSEN-FAIL (+0x58 .. +0x64, `j` to the epilogue): a0 = 0, g_fail_at := SIZE_MAX, up to the `ret` (+0x30c) ---- *)
Lemma ra_seg_fail : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q k cnt fail live peak ran most X,
  64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_cf [] ly S Hp W mem md Hp X ms mdc ->
  (forall ms' mdc', ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_cf_ret []
     ly S Hp W mem md Hp X ms' mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q k cnt fail live peak ran most X H64 Hlo
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
ra_step RUN E0 HS HJ SHOK HPM AG AG1 KP KP1.
ra_cont K.
Qed.

(* ---- S3: the TOOBIG test (+0x94 .. +0x98, `bltu n, -16`): the TOOBIG arm (n >= 2 ^ 64 - 16) refuted ---- *)
Lemma ra_seg_toobig : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q k n cnt fail live peak ran most X,
  64 <= STK -> alloc_ceiling <= spZ regs - STK -> getr regs 11 = w64 n -> 0 <= n -> n + 16 < 2 ^ 64 ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_go [] ly S Hp W mem md Hp X ms mdc ->
  (forall ms' mdc', ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_tb_go []
     ly S Hp W mem md Hp X ms' mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q k n cnt fail live peak ran most X H64 Hlo H11 Hn0 Hn
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (E11 : ew E0 11 = Z_to_bv 64 n) by (subst E0; rewrite (RA_E_reg _ _ 11 11%bv eq_refl), H11; reflexivity).
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
pose proof (paj_branch (L := A_prog_listing) (PI := PA)) as BR.
ra_step RUN E0 HS HJ SHOK HPM AG AG1 KP KP1.
psrr_branch_tok RUN BR HS SHOK RA_Bspan.
2:{ exfalso. rewrite branch_ltu_U, U_SLit, (ra_U0 E0 _ 11 n AG1 ltac:(lia) E11 ltac:(lia)) in Hc.
    rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. lia. }
ra_cont K.
Qed.

(* ---- S4: disown's arguments (+0xe4 .. +0xec): b = p - 16, a1 = 16, up to `jal __asan_unpoison_memory_region` ---- *)
Lemma ra_seg_unp_args : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q k cnt fail live peak ran most X,
  64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_tb_go [] ly S Hp W mem md Hp X ms mdc ->
  (forall ms' mdc', ra_cutc (SIGMA AS___asan_unpoison_memory_region) STK (spZ regs) FP
     (RA_E regs (RA_X cnt fail live peak k ran most)) ss_unp [] ly S Hp W mem md Hp X ms' mdc' ->
     SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q k cnt fail live peak ran most X H64 Hlo
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
ra_step RUN E0 HS HJ SHOK HPM AG AG1 KP KP1.
ra_cont K.
Qed.

(* ---- S5: the head read after the unpoison (+0xf4 .. +0x174): the two shadow checks (shadow 0 by ra_SH1), the eight
   lbu recombined into s6; the run stops before `sub` (RA_PIN) and s6 is pinned to the head word's atom 37 ---- *)
Lemma ra_seg_head : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q k cnt fail live peak ran most Hpc X,
  64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_unp_ret ra_SH1 ly S Hp W mem md Hpc X ms mdc ->
  (forall ms' mdc', ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_pin ra_SH1
     ly S Hp W mem md Hpc X ms' mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q k cnt fail live peak ran most Hpc X H64 Hlo
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
pose proof (paj_run_to_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUNTO.
ra_step_to RUNTO E0 HS HJ SHOK HPM AG AG1 KP KP1 RA_PIN.
(* s6 holds the head word k: pin it to its atom (37) so the later stores and sums stay small *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hx ?msx) =>
  assert (HSp : st_ok_pi SEGS VAL Ex (mkSS (ss_pc ssx) (sr_set (ss_regs ssx) 22%bv (SOff 37 0)) (ss_mem ssx) (ss_resv ssx)
                  (ss_facts ssx)) (restrict Hx msx));
  [ apply ra_set_reg; [exact HS | | reflexivity];
    let v := eval vm_compute in (sr_get (ss_regs ssx) 22%bv) in
    (tryif (assert (v = ra_hdr_sv 37) as _ by reflexivity) then idtac else (idtac "S6VAL" v; fail 2));
    change (sr_get (ss_regs ssx) 22%bv) with (ra_hdr_sv 37);
    rewrite ra_hdr_denot; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | ] end.
clear HS. rename HSp into HS.
ra_cont K.
Qed.

(* ---- S6: g_live -= k (+0x178 .. +0x184) and the realloc call's arguments (p - 16, n + 16), up to `jal __wrap_realloc`
   (+0x188) ---- *)
Lemma ra_seg_live : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q k cnt fail live peak ran most Hpc X,
  64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_pin ra_SH1 ly S Hp W mem md Hpc X ms mdc ->
  (forall ms' mdc', ra_cutc (SIGMA AS___wrap_realloc) STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most))
     ss_real ra_SH1 ly S Hp W mem md Hpc X ms' mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q k cnt fail live peak ran most Hpc X H64 Hlo
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
ra_step RUN E0 HS HJ SHOK HPM AG AG1 KP KP1.
ra_cont K.
Qed.

(* a static's region keeps its bytes whenever the static's bytes are kept (writable by ra_writable) *)
Lemma ra_kept_st : forall E (m m' : word -> option byte) j w whi cs, (7 <= j <= 11)%nat -> img_env VAL A_LIM E ->
  0 <= whi <= w -> w <= ra_w j ->
  (forall o, 0 <= o < ra_w j -> mbyte SEGS m' (A_prog_val (A_OBJ j) + o) = mbyte SEGS m (A_prog_val (A_OBJ j) + o)) ->
  region_kept SEGS E m m' (YP09.mkRegion (Some (A_OBJ j)) 0 w 0 whi cs).
Proof.
intros E m m' j w whi cs Hj HEI Hw1 Hw2 Hk.
apply (ra_kept_gen E m m' (A_OBJ j) (A_prog_val (A_OBJ j))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | |].
- intros a Ha. replace a with (A_prog_val (A_OBJ j) + (a - A_prog_val (A_OBJ j))) by lia. apply Hk. lia.
- intros a Ha. replace a with (A_prog_val (A_OBJ j) + (a - A_prog_val (A_OBJ j))) by lia. apply ra_writable; [exact Hj | lia].
Qed.


(* ---- CU: the unpoison call at +0xf0 (0x8599c), ret +0xf4: Hp loses p - 16, the head's two shadow bytes read 0; all
   ten regions kept (only the shadow of [p - 16, p) and the callee's stack window change); clobbers from atom 40 ---- *)
Lemma ra_seg_unpoison : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q p k cnt fail live peak ran most X,
  aunpoison_realizes_x SEGS B ARcfx 16 (SIGMA AS___asan_unpoison_memory_region) ->
  ESTACK + 64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 10 = w64 p ->
  In (p - 16) Hp -> In (p - 16, k + 16) (ablocks B ly S) -> 0 <= k ->
  ra_cutc (SIGMA AS___asan_unpoison_memory_region) STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most))
    ss_unp [] ly S Hp W mem md Hp X ms mdc ->
  (forall ms' mdc', ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_unp_ret ra_SH1
     ly S Hp W mem md (remove Z.eq_dec (p - 16) Hp)
     (fun a => X a \/ shadow_addr (p - 16) <= a < shadow_addr (p - 16) + 2) ms' mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q p k cnt fail live peak ran most X AUNPOISONx H64 Hlo Hgp Htp H10 Hhp Hab Hk
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) K.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (E3 : ew E0 3 = getr regs 3) by (subst E0; exact (RA_E_reg _ _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4) by (subst E0; exact (RA_E_reg _ _ 4 4%bv eq_refl)).
assert (E10 : ew E0 10 = getr regs 10) by (subst E0; exact (RA_E_reg _ _ 10 10%bv eq_refl)).
destruct (RA_E_extra regs cnt fail live peak k ran most) as (E32 & _).
fold E0 in E32.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (@alloc_ceiling_lt rc) as Hcl. pose proof (@alloc_ceiling_value rc) as Hcv.
pose proof (ajx_ar HJ) as HARc.
pose proof (ajx_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hrq : forall x, 0 <= x -> req_size (x + 16) = x + 16)
  by (intros x Hx; unfold req_size; destruct (Z.eqb_spec (x + 16) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W (ms_mem ms) mdc (p - 16) (k + 16) HARc Hab)
  as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
rewrite Hrq in Hbceil, Happ, Hbpres by lia.
assert (Rp : 0 <= p < 2 ^ 64) by lia.
assert (Up : bv_unsigned (ew E 10) = p).
{ rewrite (proj1 AG 10%nat ltac:(lia)), E10, H10. unfold w64. apply unsigned_lit_small. lia. }
assert (Usp' : bv_unsigned (ew E 2) = spZ regs) by (rewrite (proj1 AG 2%nat ltac:(lia)); exact Usp).
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_unpoison_x_m SEGS B PST ARcfx 16 LAWS (@pa_segs_low _ _ PA)
    (SIGMA AS___asan_unpoison_memory_region) AUNPOISONx W E _ ms STK (spZ regs) FP ly S Hp W mem md
    [] ly S Hp mdc 0 (p - 16) (k + 16) (-64) (ew E 2) _ HS).
  - reflexivity.
  - reflexivity.
  - exact HJ.
  - rewrite Ra0, Up. first [reflexivity | unfold w64; f_equal; lia].
  - rewrite Ra1. reflexivity.
  - reflexivity.
  - exact Hhp.
  - exact Hab.
  - rewrite Hrq by lia. lia.
  - exact (st_ok_restrict_reg SEGS (w_H W) E _ _ 2%bv HS).
  - reflexivity.
  - exact Usp'.
  - reflexivity.
  - lia.
  - lia.
  - rewrite Rgp, (proj1 AG 3%nat ltac:(lia)), E3. exact Hgp.
  - rewrite Rtp, (proj1 AG 4%nat ltac:(lia)), E4. exact Htp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (L := A_prog_listing) (PI := PA)); [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hshd & Hkeep & Hpres2 & HMN).
change (16 / 8) with 2 in Hkeep.
pose proof (ajx_pres HJ2) as HJpres2.
assert (Hshb : SHADOW_OFF <= shadow_addr (p - 16) /\ shadow_addr (p - 16) + 2 <= SHADOW_OFF + alloc_ceiling / 8 + 2).
{ unfold shadow_addr. pose proof (Z.div_pos (p - 16) 8 ltac:(lia) ltac:(lia)).
  assert ((p - 16) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia). lia. }
assert (Hacd : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 16) by (apply Z.div_le_upper_bound; lia).
unfold SHADOW_OFF in Hshb.
(* back at the return slot: all ten regions are kept by the unpoison *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRKX : tq); [|specialize (HS2 HRKX); clear HRKX] end.
{ cbn [ms_mem restrict].
  pose proof Happ as Happ'. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ'.
  pose proof (ra_obj_img 0%nat ltac:(lia)) as I0. pose proof (ra_obj_img 12%nat ltac:(lia)) as I12.
  pose proof (ra_obj_img 14%nat ltac:(lia)) as I14.
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in I0, I12, I14.
  assert (KS : forall j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j ->
    mbyte SEGS (mrestrict (w_H W) mem2) (A_prog_val (A_OBJ j) + o) =
    mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (A_prog_val (A_OBJ j) + o)).
  { intros j o Hj Ho. pose proof (ra_obj_img j ltac:(lia)) as Ij. rewrite ra_val in Ij. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Ij.
    assert (Hw : ra_w j <= 8) by (unfold ra_w; destruct (j =? 11)%nat; lia).
    apply (YCbq.mbyte_of_aview SEGS). apply Hkeep; [lia | rewrite Hes; lia | lia]. }
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (ra_kept_gen E _ _ 2 (spZ regs)); [exact Usp' | |].
    + intros a Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hkeep; [lia | rewrite Hes; lia | lia].
    + intros a Ha. apply (apresent_writable SEGS). apply HJpres2. lia.
  - apply (ra_kept_gen E _ _ (A_OBJ 0) (VAL (A_OBJ 0))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia].
    intros a Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hkeep; [lia | rewrite Hes; lia | lia].
  - apply (ra_kept_gen E _ _ (A_OBJ 12) (VAL (A_OBJ 12))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia].
    intros a Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hkeep; [lia | rewrite Hes; lia | lia].
  - exact (ra_kept_st E _ _ 7 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KS 7%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 8 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KS 8%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 9 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KS 9%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 10 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KS 10%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 11 1 1 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KS 11%nat o ltac:(lia) Ho)).
  - apply (ra_kept_gen E _ _ 10 p); [exact Up | | intros a Ha; lia].
    intros a Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hkeep; [lia | rewrite Hes; lia | lia].
  - apply (ra_kept_gen E _ _ (A_OBJ 14) (VAL (A_OBJ 14))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia].
    intros a Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hkeep; [lia | rewrite Hes; lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as EU eqn:HEU in HS.
assert (HEI4 : img_env VAL A_LIM EU)
  by (rewrite HEU; apply (img_env_havoc (L := A_prog_listing) (PI := PA)); [exact HEI | cbv; lia]).
assert (AG4 : env_agree 40 E0 EU) by (rewrite HEU; apply env_agree_havoc_ge; [lia | exact AG]).
clear HEU.
(* the head's shadow entry: its 16 bytes read shadow 0 after the unpoison *)
assert (SHOK4 : sh_ok SEGS RA_Bx ra_SH1 EU (mrestrict (w_H W) mem2)).
{ unfold sh_ok, ra_SH1. apply Forall_cons; [|apply Forall_nil].
  assert (UB : U EU RA_Bx = SHADOW_OFF) by (unfold RA_Bx; exact (ra_U0 E0 EU 32 SHADOW_OFF AG4 ltac:(lia) E32 ltac:(unfold SHADOW_OFF; lia))).
  assert (UP : U EU (SOff 10 0) = p) by (rewrite (ra_U0 E0 EU 10 p AG4 ltac:(lia) ltac:(rewrite E10, H10; reflexivity) ltac:(lia)); reflexivity).
  unfold shent_ok, app_apart, range_addressable. cbn [she_m she_lo she_hi]. rewrite UB, UP. split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    rewrite <- (aview_rd_of SEGS). change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply Hshd. lia.
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
assert (KP4 : ra_off W mem mem2 (fun a => X a \/ shadow_addr (p - 16) <= a < shadow_addr (p - 16) + 2)).
{ intros a Ha Hi Hx. rewrite Hkeep; [exact (KP a Ha Hi ltac:(intros H; apply Hx; left; exact H)) | lia | rewrite Hes; lia |].
  intros H; apply Hx; right; exact H. }
assert (HPM4 : ra_P mem mem2) by (intros H; exact (HMN (HPM H))).
apply (K _ _). exists EU.
refine (conj HEI4 (conj AG4 (conj HS (conj SHOK4 (conj HJ2 (conj HPM4 KP4)))))).
Qed.

(* ---- THE REALLOC CALL (+0x188 `jal __wrap_realloc`, return +0x18c = pi_ret_realloc) and its `beqz a0` ---- *)
(* one more fact of the walk's PST (the instance's gives it by computation): no static byte is errno; and g_most's eight
   bytes are image bytes no allocator owns and not errno (the image binding; g_most is read, never written, so it is
   not in the walk's PST and a call keeps it by its image clause) *)
Hypothesis PST_errno : forall a, Exists (in_zr a) PST -> ~ (as_errno B <= a < as_errno B + 4).
Hypothesis MOST_ok : forall o, 0 <= o < 8 ->
  (in_img SEGS (A_prog_val (A_OBJ 14) + o)) /\ (~ Exists (in_zr (A_prog_val (A_OBJ 14) + o)) (as_owned_static B)) /\
  (~ (as_errno B <= A_prog_val (A_OBJ 14) + o < as_errno B + 4)).
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.
Let XSL := ARx_xs_law_xs SEGS B.
(* the re-hiding relation of the realloc call's post: YA0nH.wle' at the cf zone (the keep call rule's R) *)
#[local] Abbreviation RRZ := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* the call memory's RELRO fact (QMm_cf's last conjunct, carried by YGcallcf.arodata_ok_cf_of_journal): the cf layer's
   image rows, as Caw102A_Base's cwi_relro_seg / cwi_errno_relro / cwi_relro_top / cwi_relro_eq /
   cwi_ro_reads_nw (at the instance: lib/A/CfAroPresetA.v's relro_seg_preset_A / errno_relro_preset_A /
   relro_top_preset_A / ro_reads_nw_preset_A, the range equation by computation), and the walk's statics apart from the
   covered addresses (PST lies in the kit's prh_pst, all writable cells) *)
Hypothesis RELRO_SEG : relro_seg_t SEGS.
Hypothesis ERRNO_RELRO : errno_relro_t B.
Hypothesis RELRO_TOP : cf_relro_hi <= 2 ^ 64.
Hypothesis RO_READS_NW : YGcfAroBridge.ro_reads_nw_t SEGS.
Hypothesis RELRO_EQ : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA.
Hypothesis PST_aro : forall a, aro_addr_cf a -> ~ Exists (in_zr a) PST.
(* the entry memory's RELRO fact from fpre's reader form (YGcfAroBridge.arodata_ok_cf_of_P at the range equation) *)
Lemma ra_aro_entry : forall (W : world SEGS) mem,
  PresetRodata.arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) ->
  arodata_ok_cf SEGS B mem.
Proof.
intros W mem H. destruct RELRO_EQ as [E1 E2].
apply (YGcfAroBridge.arodata_ok_cf_of_P SEGS B W mem RELRO_SEG ERRNO_RELRO RELRO_TOP RO_READS_NW).
rewrite E1, E2. exact H.
Qed.
(* a cut after the realloc call keeps the bytes of the ranges L at their values in mr (the call's post memory) *)
Definition ra_keepl (W2 : world SEGS) (mr m : word -> option byte) (L : list (Z * Z)) : Prop :=
  forall a, Exists (in_zr a) L -> aview SEGS (w_H W2) m a = aview SEGS (w_H W2) mr a.
(* a cut after the realloc call: the journal ends at the call's post allocator state (ly2, S2, Hp2, W2, kj) *)
Definition ra_cutj (Pe : env -> Prop) (STK sp0 : Z) (FP : list (Z * Z)) (E0 : env) (ss : sstate) (SH : list shent)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (kj : Z) (mr : word -> option byte) (L : list (Z * Z))
  (ms : machine_state) (mdc : Model) : Prop :=
  exists E, img_env VAL A_LIM E /\ env_agree 40 E0 E /\ Pe E /\ st_ok_pi SEGS VAL E ss (restrict (w_H W2) ms) /\
    sh_ok SEGS RA_Bx SH E (mrestrict (w_H W2) (ms_mem ms)) /\
    ajournal_xR (SK := SK) SEGS B PST ARcfx RRZ STK sp0 FP ly S Hp W mem md [] ly2 S2 Hp2 W2 (ms_mem ms) mdc kj /\
    ra_P mem (ms_mem ms) /\ ra_keepl W2 mr (ms_mem ms) L.
(* the realloc call's model and leaf facts, as YGcallRkKeep.aj_realloc_x_cfR_keep gives them at this call (empty
   chain): the call memory's QMm_cf and the keep leaf over the cf post APOST_cf *)
Definition ra_rcall (ly : alayout) (S : astate) (Hpc : list Z) (W : world SEGS) (ms : machine_state) (mdc : Model)
  (pa n_old n : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) (res : Z) (raw : word) : Prop :=
  acall_pre_x SEGS B ARcfx (QMm_cf SEGS B) ly S Hpc W (ms_regs ms) (ms_mem ms) mdc [] /\
  In (call_trace ly cf_pc_realloc_ra0 (ms_regs ms) []) (as_universe B) /\
  exists pq q, sptr_addr B ly pq = pa /\ In (pq, n_old) (blocks S) /\ sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
    (exists trc, apath (ReallocP.realloc_tree_with malloc_cf free_cf pq n (call_trace ly cf_pc_realloc_ra0 (ms_regs ms) []) S)
      trc (q, S2) /\ YG0d.gflag trc = true) /\
    YGcallRkKeep.realloc_leaf_xR_keep SEGS B xs_cf (APOST_cf SEGS B) Hpc ly S W (ms_regs ms) (ms_mem ms) mdc pq n_old n
      (q, S2) W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2).
(* the state back at +0x18c: the frame, the five written statics and g_most kept (the GOT slot and its cell are not
   read again: s4 holds the shadow offset; the old head is re-seated by the REFUSED arm); clobbers from atom 60, the
   result a0 is atom 64. Then the `beqz a0`: taken = NULL = REFUSED (+0x224), not taken = SUCCESS. *)
Definition ss_r0 : sstate := Eval vm_compute in ra_after_call ss_real [0; 3; 4; 5; 6; 7; 9]%nat 60.
Definition ss_rN : sstate := Eval vm_compute in ra_arm true [] ss_r0.
Definition ss_rS : sstate := Eval vm_compute in ra_arm false [] ss_r0.
Lemma ra_r0_why : ra_why [] ss_r0 = PTStop (SR_branch BC_EQ (SOff 64 0) (SLit 0)).
Proof. vm_compute. reflexivity. Qed.

(* THE CALL over the keep rule (YGcallRkKeep.aj_realloc_x_cfR_keep at k = 0): its room is qtight /\ ROOM_cf_k
   (RK_realloc + 0) /\ cf_hull_adm at the request n + 16, its call memory carries QMm_cf (the room QM_cf and the RELRO
   fact, from the entry memory's arodata_ok_cf through the journal), and its post is at the re-hiding relation RRZ, so
   this segment and its continuations are SRr' at the cf zone (the segments before it stay plain SRr: F12 route (b)) *)
Lemma ra_seg_realloc : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q p k n cnt fail live peak ran most X,
  (forall Hp' kk, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep SEGS B Hp' (SIGMA AS___wrap_realloc) kk) ->
  ASTACK + 64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 10 = w64 p -> getr regs 11 = w64 n ->
  In (p - 16, k + 16) (ablocks B ly S) -> 0 <= k -> 0 <= n -> n + 16 < cf_malloc_max ->
  blocks_bytes S + (n + 16) <= LIVE_MAX -> QM_cf S -> ROOM_cf_k S (RK_realloc + 0) ->
  cf_hull_adm S (n + 16) -> arodata_ok_cf SEGS B mem -> ~ YI16.sink_open_fp FP ->
  In [cf_pc_realloc_ra0] (as_universe B) ->
  In (unwind_of_chain cf_pc_realloc_ra0 [(0, SIGMA AS_fuzz_realloc + 396, 0)]) (as_universe B) ->
  (forall i, 0 <= i < k + 16 -> inFP FP (p - 16 + i)) ->
  (forall i, 0 <= i < k + 16 -> ~ X (p - 16 + i)) ->
  ra_cutc (SIGMA AS___wrap_realloc) STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_real ra_SH1
    ly S Hp W mem md (remove Z.eq_dec (p - 16) Hp) X ms mdc ->
  (forall W2 ly2 S2 regs2 mem2 md2 raw, RRZ W W2 ->
     ra_rcall ly S (remove Z.eq_dec (p - 16) Hp) W ms mdc (p - 16) (k + 16) (n + 16) ly2 S2 W2 regs2 mem2 md2 0 raw ->
     ablocks B ly2 S2 = ablocks B ly S -> blocks S2 = blocks S -> frames S2 = frames S ->
     rd32 (aview SEGS (w_H W2) mem2) (as_errno B) 12 ->
     mt_refused malloc_cf free_cf (n + 16) (call_trace ly cf_pc_realloc_ra0 (ms_regs ms) []) S S2 ->
     (forall i, 0 <= i < k -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)) ->
     forall ms' mdc', ra_cutj (fun E => ew E 64 = w64 0) STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most))
       ss_rN [] ly S Hp W mem md ly2 S2 (remove Z.eq_dec (p - 16) Hp) W2 (0 + (st_nev S2 - st_nev S)) mem2
       [(p, k); (as_errno B, 4)] ms' mdc' ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg ms' mdc') Q) ->
  (forall W2 ly2 S2 regs2 mem2 md2 raw res, RRZ W W2 ->
     ra_rcall ly S (remove Z.eq_dec (p - 16) Hp) W ms mdc (p - 16) (k + 16) (n + 16) ly2 S2 W2 regs2 mem2 md2 res raw ->
     4096 <= res -> res mod 16 = 0 -> frames S2 = frames S ->
     (exists l1 l2, ablocks B ly S = l1 ++ (p - 16, k + 16) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n + 16)]) ->
     (forall i, 0 <= i < Z.min k n -> aview SEGS (w_H W2) mem2 (res + 16 + i) = aview SEGS (w_H W) mem (p + i)) ->
     forall ms' mdc', ra_cutj (fun E => ew E 64 = w64 res) STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most))
       ss_rS [] ly S Hp W mem md ly2 S2 (remove Z.eq_dec (p - 16) (remove Z.eq_dec (p - 16) Hp)) W2
       (0 + (st_nev S2 - st_nev S)) mem2 [(res + 16, n)] ms' mdc' ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg ms' mdc') Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q p k n cnt fail live peak ran most X AREALx H64 Hlo Hgp Htp H10 H11 Hab Hk Hn0
  Hnmax Hlive HQM HROOM HADM HARO HSK HU0 HU1 HFP HXo (E & HEI & AG & HS & SHOK & HJ & HPM & KP) KN KS.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (E3 : ew E0 3 = getr regs 3) by (subst E0; exact (RA_E_reg _ _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4) by (subst E0; exact (RA_E_reg _ _ 4 4%bv eq_refl)).
assert (E10 : ew E0 10 = getr regs 10) by (subst E0; exact (RA_E_reg _ _ 10 10%bv eq_refl)).
assert (E11 : ew E0 11 = getr regs 11) by (subst E0; exact (RA_E_reg _ _ 11 11%bv eq_refl)).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hcm : cf_malloc_max <= 2 ^ 30) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (@alloc_ceiling_lt rc) as Hcl. pose proof (@alloc_ceiling_value rc) as Hcv.
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_pres HJ) as HJpres.
pose proof (ajx_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _). pose proof (ajx_qt HJ) as HQT.
assert (Hrq : forall x, 0 <= x -> req_size (x + 16) = x + 16)
  by (intros x Hx; unfold req_size; destruct (Z.eqb_spec (x + 16) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S (remove Z.eq_dec (p - 16) Hp) W (ms_mem ms) mdc (p - 16) (k + 16) HARc Hab)
  as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
rewrite Hrq in Hbceil, Happ, Hbpres by lia.
pose proof (ra_blk_off_img ly S _ W (ms_mem ms) mdc (p - 16) (k + 16) HARc Hab) as Hoff. rewrite Hrq in Hoff by lia.
assert (Up : bv_unsigned (ew E 10) = p).
{ rewrite (proj1 AG 10%nat ltac:(lia)), E10, H10. unfold w64. apply unsigned_lit_small. lia. }
assert (Un : bv_unsigned (ew E 11) = n).
{ rewrite (proj1 AG 11%nat ltac:(lia)), E11, H11. unfold w64. apply unsigned_lit_small. lia. }
assert (Usp' : bv_unsigned (ew E 2) = spZ regs) by (rewrite (proj1 AG 2%nat ltac:(lia)); exact Usp).
pose proof (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HARc)) as HU.
(* the realloc argument's base is shown (disown's HEAD_SHOW at CU took it out of Hp): the premise the allocator lane's
   rxhide change adds to aj_realloc_x *)
assert (Hshown : ~ In (p - 16) (remove Z.eq_dec (p - 16) Hp)) by apply remove_In.
(* the call memory's QMm_cf: the room QM_cf, and the RELRO fact the journal carries from the entry memory *)
assert (HQMm : QMm_cf SEGS B S (ms_mem ms)).
{ destruct HQM as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
  (* the journal's entry ghost set occurs in no conjunct (YCbqG.ajournal_xb), so it is given *)
  apply (arodata_ok_cf_of_journal SEGS B PST ARcfx (@wle SEGS) STK (spZ regs) FP ly S Hp W mem md [] ly S
    (remove Z.eq_dec (p - 16) Hp) W (ms_mem ms) mdc 0 [] HJ RELRO_SEG ERRNO_RELRO RELRO_TOP RO_READS_NW PST_aro HSK HARO). }
(* the journal at the call's relation RRZ (wle is inside it) *)
assert (HJR : ajournal_xwR (SK := SK) SEGS B PST ARcfx RRZ STK (spZ regs) FP ly S Hp W mem md [] ly S
  (remove Z.eq_dec (p - 16) Hp) W (ms_mem ms) mdc 0 []).
{ eapply ajournal_xwR_mono; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HJ]. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0. prreg HS (2%bv : bv 5) Rsp.
assert (Hra1 : raZ (ms_regs ms) = SIGMA AS_fuzz_realloc + 396) by (unfold raZ; rewrite Rra; vm_compute; reflexivity).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 64).
{ unfold spZ at 1. rewrite Rsp. first [rewrite Usp' | idtac]. rewrite unsigned_lit_small by lia. lia. }
assert (Hs01 : s0Z (ms_regs ms) = n) by (unfold s0Z; rewrite Rs0; exact Un).
(* the call's trace is a FIXED trace (HU0 / HU1): the text admits it (admits_ct_fix) and it leaves the post's budget
   (ajournal_xw_fix1R), so the journal after the call is ajournal_xR at RRZ *)
assert (HTRF : In (call_trace ly cf_pc_realloc_ra0 (ms_regs ms) []) (u_fix (as_universe B))).
{ unfold call_trace. destruct (frame0_ok ly (ms_regs ms)); [|exact HU0].
  unfold unwind_of_chain in *. cbn [flat_map app] in *. rewrite Hra1. exact HU1. }
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (YGcallRkKeep.aj_realloc_x_cfR_keep SEGS B PST LAWS (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW WFL XSL HU
    0 (SIGMA AS___wrap_realloc) AREALx []
    W E _ ms STK (spZ regs) FP ly S Hp W mem md [] ly S (remove Z.eq_dec (p - 16) Hp) mdc 0
    (p - 16) (k + 16) (n + 16) (-64) (ew E 2) _ [] HS eq_refl eq_refl HJR).
  - exact Hab.
  - exact Hshown.
  - rewrite Ra0, Up. first [reflexivity | unfold w64; f_equal; lia].
  - rewrite Ra1, Un. first [reflexivity | unfold w64; f_equal; lia].
  - lia.
  - exact Hlive.
  - exact (st_ok_restrict_reg SEGS (w_H W) E _ _ 2%bv HS).
  - reflexivity.
  - exact Usp'.
  - reflexivity.
  - lia.
  - lia.
  - rewrite Rgp, (proj1 AG 3%nat ltac:(lia)), E3. exact Hgp.
  - rewrite Rtp, (proj1 AG 4%nat ltac:(lia)), E4. exact Htp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (L := A_prog_listing) (PI := PA)); [lia | reflexivity].
  - exact HQMm.
  - cbv beta. split; [exact HQT | split; [exact HROOM | exact HADM]].
  - unfold chain_pre. split; [rewrite Hra1; vm_compute; discriminate|].
    assert (Hbn : bad_next (spZ (ms_regs ms)) (ly_top ly) (s0Z (ms_regs ms)) = true).
    { unfold bad_next. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. rewrite Hsp1, Hs01.
      lia. }
    destruct (frame0_ok ly (ms_regs ms)); [rewrite Hbn|]; reflexivity.
  - exact (admits_ct_fix _ _ _ _ _ _ HTRF).
  - intros _ i Hi. rewrite Hrq in Hi by lia. replace (p - 16 + i) with (p - 16 + i) by lia. exact (HFP i Hi). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfrs2 & HPREr & Htrr &
  (pq & q & Hpq & Hpin & Hqres & Hqiff & (trc & Hpath & Hgf) & Hleaf) & HARM).
apply (ajournal_xw_fix1R HTRF) in HJ2.
pose proof Hleaf as (ly' & regs' & mem' & md' & Ec & _ & _ & _ & _ & _ & _ & HMN).
unfold cfg_at in Ec. injection Ec as _ _ Emem _. subst mem'.
pose proof (ajxR_ar HJ2) as HAR2. pose proof (ajxR_pres HJ2) as HJpres2.
assert (Hres_rng : 0 <= res < 2 ^ 64).
{ destruct HARM as [(-> & _) | (H4096 & _ & _ & (b1 & b2 & _ & Eab4) & _)]; [lia|].
  assert (Hin4 : In (res, n + 16) (ablocks B ly2 S2))
    by (rewrite Eab4; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 res (n + 16) HAR2 Hin4) as (_ & _ & Hc' & _).
  rewrite Hrq in Hc' by lia. lia. }
assert (Hkc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs + -64 - ASTACK <= a < spZ regs + -64) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ destruct HARM as [(_ & _ & _ & _ & (K & _) & _) | (_ & _ & _ & _ & _ & (K & _))]; exact K. }
assert (Hki : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ destruct HARM as [(_ & _ & _ & _ & (_ & _ & K & _) & _) | (_ & _ & _ & _ & _ & (_ & _ & K & _))]; exact K. }
assert (KPr : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Hx. destruct (PST_ok a Hx) as [H1 H2]. exact (Hki a H1 H2 (PST_errno a Hx)). }
(* back at +0x18c: the frame, the five statics and g_most kept *)
jafter_call_keep_pi HS 60%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3; 4; 5; 6; 7; 9]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRKX : tq); [|specialize (HS2 HRKX); clear HRKX] end.
{ cbn [ms_mem restrict].
  pose proof (ra_obj_img 14%nat ltac:(lia)) as I14. rewrite ra_val in I14. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in I14.
  assert (KSt : forall j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j ->
    mbyte SEGS (mrestrict (w_H W2) mem2) (A_prog_val (A_OBJ j) + o) =
    mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (A_prog_val (A_OBJ j) + o)).
  { intros j o Hj Ho. apply (YCbq.mbyte_of_aview SEGS). apply KPr. apply PST_cells; assumption. }
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (ra_kept_gen E _ _ 2 (spZ regs)); [exact Usp' | |].
    + intros a Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hkc; [lia | rewrite Has; lia].
    + intros a Ha. apply (apresent_writable SEGS). apply HJpres2. lia.
  - exact (ra_kept_st E _ _ 7 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KSt 7%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 8 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KSt 8%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 9 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KSt 9%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 10 8 8 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KSt 10%nat o ltac:(lia) Ho)).
  - exact (ra_kept_st E _ _ 11 1 1 _ ltac:(lia) HEI ltac:(lia) ltac:(cbn; lia) (fun o Ho => KSt 11%nat o ltac:(lia) Ho)).
  - apply (ra_kept_gen E _ _ (A_OBJ 14) (VAL (A_OBJ 14))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia].
    intros a Ha. apply (YCbq.mbyte_of_aview SEGS). rewrite ra_val in Ha.
    replace a with (A_prog_val (A_OBJ 14) + (a - A_prog_val (A_OBJ 14))) by lia.
    destruct (MOST_ok (a - A_prog_val (A_OBJ 14)) ltac:(lia)) as (M1 & M2 & M3). exact (Hki _ M1 M2 M3). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 60 (map (getr regs2) CLOB)) as EU eqn:HEU in HS.
assert (HEI2 : img_env VAL A_LIM EU) by (rewrite HEU; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (AG2 : env_agree 40 E0 EU) by (rewrite HEU; apply env_agree_havoc_ge; [lia | exact AG]).
assert (E64 : ew EU 64 = w64 res) by (rewrite HEU; unfold havoc; cbn [ew]; exact Hres).
clear HEU.
assert (SHOK2 : sh_ok SEGS RA_Bx [] EU (mrestrict (w_H W2) mem2)) by constructor.
assert (HPM2 : ra_P mem mem2) by (intros H; exact (HMN (HPM H))).
assert (KL : forall L, ra_keepl W2 mem2 mem2 L) by (intros L a _; reflexivity).
(* the old block's bytes at the call are its bytes at the entry (ra_off) *)
assert (HOLD : forall i, 0 <= i < k + 16 -> aview SEGS (w_H W) (ms_mem ms) (p - 16 + i) = aview SEGS (w_H W) mem (p - 16 + i)).
{ intros i Hi. apply KP; [lia | lia | exact (HXo i Hi)]. }
(* RUN is read for the runner's tables only; the branch is at the call's relation RRZ (YSRrG.paj_branchR) *)
pose proof (paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem)) as RUN.
pose proof (YSRrG.paj_branchR (L := A_prog_listing) (PI := PA) RRZ) as BR.
psrr_branch_tok RUN BR HS SHOK2 RA_Bspan.
- (* taken: res = 0, the REFUSED arm *)
  rewrite branch_eq_U, U_SLit, U_SOff, E64 in Hc. replace (zcanon 0) with 0 in Hc by reflexivity. unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by exact Hres_rng.
  rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc. rewrite Hc in *.
  destruct HARM as [(_ & EHp2 & Eab2 & Ebl2 & Kc & Herr & Hoom & Hrefused) | (H4096 & _)]; [|exfalso; clear - H4096; lia].
  subst Hp2.
  assert (Hcopy : forall i, 0 <= i < k -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)).
  { intros i Hi. destruct Kc as (_ & K2 & _).
    replace (p + i) with (p - 16 + (16 + i)) by lia.
    rewrite (K2 (p - 16) (k + 16) (16 + i) Hab ltac:(rewrite Hrq by lia; lia) ltac:(intros [])).
    exact (HOLD (16 + i) ltac:(lia)). }
  apply (KN W2 ly2 S2 regs2 mem2 md2 (Z_to_bv 64 (BASE + 17496)) Hwle2); try assumption.
  + split; [exact HPREr|]. split; [exact HTRF|]. exists pq, q.
    repeat (split; [assumption|]). split; [exists trc; split; assumption | exact Hleaf].
  + exists EU. refine (conj HEI2 (conj AG2 (conj E64 (conj HS (conj SHOK2 (conj HJ2 (conj HPM2 (KL _)))))))).
- (* not taken: res <> 0, the SUCCESS arm *)
  rewrite branch_eq_U, U_SLit, U_SOff, E64 in Hc. replace (zcanon 0) with 0 in Hc by reflexivity. unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by exact Hres_rng.
  rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc.
  destruct HARM as [(Hr0 & _) | (H4096 & Hal_r & EHp2 & Eab & Hcopy0 & Kc)]; [exfalso; clear - Hr0 Hc; lia|].
  subst Hp2.
  assert (Hcopy : forall i, 0 <= i < Z.min k n -> aview SEGS (w_H W2) mem2 (res + 16 + i) = aview SEGS (w_H W) mem (p + i)).
  { intros i Hi. replace (res + 16 + i) with (res + (16 + i)) by lia.
    rewrite (Hcopy0 (16 + i) ltac:(lia)). replace (p - 16 + (16 + i)) with (p - 16 + (16 + i)) by lia.
    replace (p + i) with (p - 16 + (16 + i)) by lia. exact (HOLD (16 + i) ltac:(lia)). }
  apply (KS W2 ly2 S2 regs2 mem2 md2 (Z_to_bv 64 (BASE + 17496)) res Hwle2); try assumption.
  + split; [exact HPREr|]. split; [exact HTRF|]. exists pq, q.
    repeat (split; [assumption|]). split; [exists trc; split; assumption | exact Hleaf].
  + exists EU. refine (conj HEI2 (conj AG2 (conj E64 (conj HS (conj SHOK2 (conj HJ2 (conj HPM2 (KL _)))))))).
Qed.

(* ---- reading a symbolic state (FuzzMalloc.v.wip's fm_* helpers, restated over st_ok_pi) ---- *)
Definition ra_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma ra_cv_ok : forall E ss ms j off w c, st_ok_pi SEGS VAL E ss ms -> ra_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold ra_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (ra_region_ok E ss ms r HS Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs c Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma ra_U_range : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. unfold U. pose proof (bv_unsigned_in_range _ (sv_denot E e)) as H. exact H. Qed.
Lemma ra_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma ra_val_cv : forall E ss ms j off (w : N) e v, st_ok_pi SEGS VAL E ss ms ->
  ra_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) -> U E e = v -> Z.of_N w <= 8 ->
  0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) (bv_unsigned (ew E j) + off) (N.to_nat w) v.
Proof.
intros E ss ms j off w e v HS H HU Hw Hv.
exact (val_of_chunk_ok SEGS E _ _ off w e v (ra_cv_ok E ss ms j off (Z.of_N w) _ HS H) (ra_denot_U E e v HU) Hv Hw).
Qed.
Lemma ra_byte_pi : forall E ss ms j off e, st_ok_pi SEGS VAL E ss ms ->
  ra_cv (ss_mem ss) j off 1 = Some (YP09.mkChunk off (CVal 1 e)) ->
  mbyte SEGS (ms_mem ms) (bv_unsigned (ew E j) + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros E ss ms j off e HS H. unfold ra_cv in H.
destruct (find_region (ss_mem ss) (Some j) off 1) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (ra_region_ok E ss ms r HS Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn in Hb1. injection Hb1 as <-.
cbn [YP09.c_off base_val] in Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. unfold YP09.byte_of_word, U.
rewrite Z.shiftr_0_r. reflexivity.
Qed.
Lemma ra_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma ra_U_srl : forall E a s, 0 <= s < 64 -> U E (SAlu ALU_SRL a (SLit s)) = Z.shiftr (U E a) s.
Proof.
intros E a s Hs. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id s) by (unfold M64; lia).
replace (Z.land s 63) with s by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
pose proof (ra_U_range E a) as Ha.
apply zcanon_id. unfold M64. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (U E a)); [apply Z.div_le_upper_bound; nia | lia].
Qed.

(* 8 bytes written one by one, byte k being v >> 8k, are v little endian (S1Ledger's prh_val_mem_hdr8) *)
Lemma ra_val_mem_hdr8 : forall (m : word -> option byte) (b v : Z), 0 <= v < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> mbyte SEGS m (b + Z.of_nat k) = Some (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)))) ->
  val_mem SEGS m b 8 v.
Proof. intros m b v Hv H k Hk. rewrite (le_byte_small v 8 k ltac:(cbn; lia) Hk). exact (H k Hk). Qed.
(* a head word written by the eight `sb` of e's bytes (`srli` by 8k) at offsets o .. o + 7 of atom j's base *)
Lemma ra_hdr_of_pi : forall E ss ms (j : nat) o e b v, st_ok_pi SEGS VAL E ss ms -> bv_unsigned (ew E j) + o = b ->
  ra_cv (ss_mem ss) j o 1 = Some (YP09.mkChunk o (CVal 1 e)) ->
  (forall k, (1 <= k < 8)%nat ->
     ra_cv (ss_mem ss) j (o + Z.of_nat k) 1 =
       Some (YP09.mkChunk (o + Z.of_nat k) (CVal 1 (SAlu ALU_SRL e (SLit (8 * Z.of_nat k)))))) ->
  U E e = v -> val_mem SEGS (ms_mem ms) b 8 v.
Proof.
intros E ss ms j o e b v HS Hb C0 Ck Hv.
pose proof (ra_U_range E e) as Rv. rewrite Hv in Rv.
apply ra_val_mem_hdr8; [exact Rv|]. intros k Hk. destruct k as [|k].
- pose proof (ra_byte_pi E ss ms j o e HS C0) as V. rewrite Hb, Hv in V. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.add_0_r.
  exact V.
- pose proof (ra_byte_pi E ss ms j _ _ HS (Ck (S k) ltac:(lia))) as V. rewrite Z.add_assoc, Hb, ra_U_srl, Hv in V by lia. exact V.
Qed.
(* the shadow bytes of a block's head miss the image, the block's bytes and the stack (FuzzMalloc.v.wip's fm_not_shadow) *)
Lemma ra_not_shadow : forall b len a, in_app b len -> b + len <= alloc_ceiling -> 0 <= len ->
  (a < kLowMemEnd \/ (b <= a < b + len) \/ alloc_ceiling <= a) -> ~ (shadow_addr b <= a < shadow_addr b + 2).
Proof.
intros b len a Happ Hc Hl Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF.
assert (Hb8 : 0 <= b / 8) by (apply Z.div_pos; lia).
assert (Hbc : b / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hc8 : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.mod_pos_bound b 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
rewrite C5 in Ha. lia.
Qed.
(* a run keeps the listed ranges when none of its write windows meets them *)
Lemma ra_keepl_step : forall (W2 : world SEGS) E rs (mr mA mB : word -> option byte) L,
  frame_of E rs (mrestrict (w_H W2) mA) (mrestrict (w_H W2) mB) ->
  (forall a, Exists (in_zr a) L -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
  ra_keepl W2 mr mA L -> ra_keepl W2 mr mB L.
Proof.
intros W2 E rs mr mA mB L HF Hn HK a Ha. destruct (Hn a Ha) as [Hr Hw].
rewrite (ra_aview_of_frame W2 E rs mA mB a HF Hw Hr). exact (HK a Ha).
Qed.

(* ---- the U values the REFUSED arm's tests and stores take (alloc.c :70-78 refused(n), :48-56 own) ---- *)
Definition ra_heldA : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 35 0)) (SMd M_MUL (SOff 37 0) (SLit 18446744073709551615)).
Definition ra_liveK : sv := SAlu ALU_ADD (SOff 35 0) (SMd M_MUL (SOff 37 0) (SLit (-1))).
Definition ra_held : sv := SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU ra_heldA ra_liveK)) ra_heldA.
Definition ra_live2 : sv := SAlu ALU_ADD (SOff 35 0) (SMd M_MUL (SOff 37 0) (SLit 18446744073709551616)).
Section uv.
Variables (E : env) (n live k : Z).
Hypotheses (Un : U E (SOff 11 0) = n) (Ul : U E (SOff 35 0) = live) (Uk : U E (SOff 37 0) = k).
Hypotheses (Hk : 0 <= k <= live) (Hn : 0 <= n) (Hlk : live - k + n < 2 ^ 64).
Lemma ra_U_liveK : U E ra_liveK = live - k.
Proof using Un Ul Uk Hk Hn Hlk.
unfold ra_liveK. rewrite U_SAlu, U_SMd, U_SLit, Ul, Uk. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_r by lia. symmetry. apply (Z.mod_unique _ _ k); lia.
Qed.
Lemma ra_U_heldA : U E ra_heldA = live - k + n.
Proof using Un Ul Uk Hk Hn Hlk.
unfold ra_heldA. rewrite !U_SAlu, U_SMd, U_SLit, Un, Ul, Uk. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia. symmetry. apply (Z.mod_unique _ _ k); lia.
Qed.
Lemma ra_U_held : U E ra_held = live - k + n.
Proof using Un Ul Uk Hk Hn Hlk.
unfold ra_held. rewrite !U_SAlu, U_SLit, ra_U_heldA, ra_U_liveK. cbn [zalu_raw].
replace (zcanon (if live - k + n <? live - k then 1 else 0)) with 0
  by (destruct (Z.ltb_spec (live - k + n) (live - k)); [lia | reflexivity]).
replace (zcanon (zcanon 0 - 0)) with 0 by reflexivity. rewrite Z.lor_0_l. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ra_U_live2 : U E ra_live2 = live.
Proof using Un Ul Uk Hk Hn Hlk.
unfold ra_live2. rewrite U_SAlu, U_SMd, U_SLit, Ul, Uk. cbn [zalu_raw zmd_raw].
change (zcanon 18446744073709551616) with 0. rewrite Z.mul_0_r. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply zcanon_id. unfold M64. pose proof (ra_U_range E (SOff 35 0)) as R. rewrite Ul in R. lia.
Qed.
End uv.

(* the same readers at a state the runner stopped at a call (plain st_ok) *)
Lemma ra_byte_st : forall E ss ms j off e, st_ok SEGS E ss ms ->
  ra_cv (ss_mem ss) j off 1 = Some (YP09.mkChunk off (CVal 1 e)) ->
  mbyte SEGS (ms_mem ms) (bv_unsigned (ew E j) + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros E ss ms j off e HS H. unfold ra_cv in H.
destruct (find_region (ss_mem ss) (Some j) off 1) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn in Hb1. injection Hb1 as <-.
cbn [YP09.c_off base_val] in Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. unfold YP09.byte_of_word, U.
rewrite Z.shiftr_0_r. reflexivity.
Qed.
Lemma ra_hdr_of_st : forall E ss ms (j : nat) o e b v, st_ok SEGS E ss ms -> bv_unsigned (ew E j) + o = b ->
  ra_cv (ss_mem ss) j o 1 = Some (YP09.mkChunk o (CVal 1 e)) ->
  (forall k, (1 <= k < 8)%nat ->
     ra_cv (ss_mem ss) j (o + Z.of_nat k) 1 =
       Some (YP09.mkChunk (o + Z.of_nat k) (CVal 1 (SAlu ALU_SRL e (SLit (8 * Z.of_nat k)))))) ->
  U E e = v -> val_mem SEGS (ms_mem ms) b 8 v.
Proof.
intros E ss ms j o e b v HS Hb C0 Ck Hv.
pose proof (ra_U_range E e) as Rv. rewrite Hv in Rv.
apply ra_val_mem_hdr8; [exact Rv|]. intros k Hk. destruct k as [|k].
- pose proof (ra_byte_st E ss ms j o e HS C0) as V. rewrite Hb, Hv in V. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.add_0_r.
  exact V.
- pose proof (ra_byte_st E ss ms j _ _ HS (Ck (S k) ltac:(lia))) as V. rewrite Z.add_assoc, Hb, ra_U_srl, Hv in V by lia. exact V.
Qed.
(* n bytes kept byte by byte keep a value *)
Lemma ra_val_mem_keep : forall (m m' : word -> option byte) (a : Z) (n : nat) (v : Z),
  val_mem SEGS m a n v ->
  (forall k, (k < n)%nat -> mbyte SEGS m' (a + Z.of_nat k) = mbyte SEGS m (a + Z.of_nat k)) ->
  val_mem SEGS m' a n v.
Proof. intros m m' a n v Hv He k Hk. rewrite (He k Hk). exact (Hv k Hk). Qed.
(* a static's value read off a symbolic state (its region's chunk at offset 0) *)
Lemma ra_static_val : forall E ss ms (j : nat) (w : N) e v, st_ok_pi SEGS VAL E ss ms -> img_env VAL A_LIM E ->
  (j < 39)%nat -> ra_cv (ss_mem ss) (A_OBJ j) 0 (Z.of_N w) = Some (YP09.mkChunk 0 (CVal w e)) -> U E e = v ->
  Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) (A_prog_val (A_OBJ j)) (N.to_nat w) v.
Proof.
intros E ss ms j w e v HS HEI Hj Hc HU Hw Hv.
pose proof (ra_val_cv E ss ms (A_OBJ j) 0 w e v HS Hc HU Hw Hv) as V.
rewrite (HEI (A_OBJ j) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r in V. exact V.
Qed.
(* the facts at a `ret` the arms hand to their continuation: ra, the callee-saved registers, a0, the five statics,
   g_most, and an 8-byte head word *)
Definition ra_retf (regs regs' : bvmap 5 word) (r0 : Z) (W2 : world SEGS) (m : word -> option byte)
  (cnt fail live peak ran most hb hv : Z) : Prop :=
  getr regs' 1 = getr regs 1 /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 r0 /\
  val_mem SEGS (mrestrict (w_H W2) m) (A_prog_val (A_OBJ 7)) 8 cnt /\
  val_mem SEGS (mrestrict (w_H W2) m) (A_prog_val (A_OBJ 8)) 8 fail /\
  val_mem SEGS (mrestrict (w_H W2) m) (A_prog_val (A_OBJ 9)) 8 live /\
  val_mem SEGS (mrestrict (w_H W2) m) (A_prog_val (A_OBJ 10)) 8 peak /\
  val_mem SEGS (mrestrict (w_H W2) m) (A_prog_val (A_OBJ 11)) 1 ran /\
  val_mem SEGS (mrestrict (w_H W2) m) (A_prog_val (A_OBJ 14)) 8 most /\
  val_mem SEGS (mrestrict (w_H W2) m) hb 8 hv.

Ltac ra_lits_g :=
  repeat match goal with |- context [@pa_val ?r ?L ?P ?j] =>
    let v := eval vm_compute in (@pa_val r L P j) in change (@pa_val r L P j) with v end;
  repeat match goal with |- context [A_prog_val ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v end.
(* ---- the tactics of the post-call arms (the journal ends at the realloc's post state; ra_keepl, not ra_off) ---- *)
(* an address of a kept range in none of a run's write windows: the frame, the statics (image, PST, never errno),
   g_most (no window), the old head [p - 16, p - 8) or the new head *)
Ltac ra_nwE :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; ra_at Hr;
           first [ exfalso; ra_lits_in Hr; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia
                 | exfalso; match goal with Ha : as_errno ?Bx <= ?a < as_errno ?Bx + 4 |- _ =>
                     apply (PST_errno a); [ra_pst_lit_tac Hr | exact Ha] end ] |]);
  destruct Hin.
Ltac ra_nwL :=
  let a := fresh "a" in let Ha := fresh "Ha" in let x := fresh "x" in let Hx := fresh "Hx" in
  intros a Ha; apply Exists_exists in Ha as (x & Hx & Ha); cbn [In] in Hx;
  repeat match type of Hx with
  | _ \/ _ => destruct Hx as [Hx | Hx]; [subst x; unfold in_zr in Ha; cbn [fst snd] in Ha;
                                         split; [unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia | ra_nwE] |]
  | _ = _ => subst x; unfold in_zr in Ha; cbn [fst snd] in Ha;
             split; [unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia | ra_nwE]
  | False => destruct Hx
  end.
(* one run of the post-call arms: the write premise, the new env's agreement, the kept ranges *)
Ltac ra_stepj RUN E0 HS HJ SHOK HPM AG AGn KL KLn blk :=
  paj_run_tok_x_inv RUN HS HJ SHOK HPM RA_Bspan; [ra_wr blk|];
  ra_newenv 40%nat E0 HS AG AGn;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
  lazymatch type of KL with ra_keepl _ ?mr _ ?L =>
    pose proof (ra_keepl_step Wx Ex rs mr mA mB L HFr ltac:(ra_nwL) KL) as KLn; clear HFr KL end end.

(* a write of the old head: the footprint FP, the block (p - 16, k + 16) of the current allocator state *)
Ltac ra_hblk p k HFP Hab Hrq H :=
  lazymatch type of H with _ <= ?a < _ =>
  left; unfold awr_byte; right; left;
  split; [ replace a with (p - 16 + (a - (p - 16))) by lia; apply HFP; lia
         | exists (p - 16), (k + 16); split; [exact Hab | rewrite Hrq by lia; lia] ] end.
(* ---- REFUSED (+0x224 .. the `ret`): refused (n) after disown (merged alloc.c:121-125: g_peak := max (g_peak,
   g_live - k + n), g_ran_out := 1 when n <= g_most), then own (b, old): the two store checks on b, the 8 head bytes
   of k, __asan_poison_memory_region (b, 16), g_live += k (back to live) and its dead peak store, return NULL ---- *)
Definition ra_hdrw : YP09.region := YP09.mkRegion (Some 10%nat) (-16) (-8) (-16) (-8) [].
Lemma ra_arm_refused : forall STK FP ly S Hp (W : world SEGS) regs mem md ly2 S2 (W2 : world SEGS) kj mem2 ms mdc Q
    p k n cnt fail live peak ran most,
  apoison_realizes_x SEGS B ARcfx 16 (SIGMA AS___asan_poison_memory_region) ->
  ESTACK + 64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 10 = w64 p -> getr regs 11 = w64 n ->
  In (p - 16, k + 16) (ablocks B ly2 S2) -> 0 <= k ->
  (forall i, 0 <= i < k + 16 -> inFP FP (p - 16 + i)) ->
  (forall h, In h (remove Z.eq_dec (p - 16) Hp) -> ~ (p - 16 <= h < p + k)) ->
  0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 -> k <= live < 2 ^ 64 -> live <= peak < 2 ^ 64 -> (ran = 0 \/ ran = 1) ->
  0 <= most < 2 ^ 64 -> 0 <= n -> live - k + n < 2 ^ 64 ->
  ra_cutj (fun E => ew E 64 = w64 0) STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_rN []
    ly S Hp W mem md ly2 S2 (remove Z.eq_dec (p - 16) Hp) W2 kj mem2 [(p, k); (as_errno B, 4)] ms mdc ->
  (forall regs' mem' md',
     ra_retf regs regs' 0 W2 mem' ((cnt + 1) mod 2 ^ 64) fail live (Z.max peak (live - k + n))
       (if n <=? most then 1 else ran) most (p - 16) k ->
     ajournal_xR (SK := SK) SEGS B PST ARcfx RRZ STK (spZ regs) FP ly S Hp W mem md [] ly2 S2
       ((p - 16) :: remove Z.eq_dec (p - 16) Hp) W2 mem' md' kj ->
     ra_P mem mem' -> ra_keepl W2 mem2 mem' [(p, k); (as_errno B, 4)] ->
     Q W2 (mkCfg (mkst regs' (v_jalr (getr regs' 1) 0) mem' (seg_rom SEGS)) md')) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ly2 S2 W2 kj mem2 ms mdc Q p k n cnt fail live peak ran most APOISONx H64 Hlo
  Hgp Htp H10 H11 Hab Hk HFP HHP Rc Rf Rl Rp Rr Rm Hn0 Hlk (E & HEI & AG & E64 & HS & SHOK & HJ & HPM & KL) KR.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E0 1 = getr regs 1) by (subst E0; exact (RA_E_reg _ _ 1 1%bv eq_refl)).
assert (E3 : ew E0 3 = getr regs 3) by (subst E0; exact (RA_E_reg _ _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4) by (subst E0; exact (RA_E_reg _ _ 4 4%bv eq_refl)).
assert (E10 : ew E0 10 = Z_to_bv 64 p) by (subst E0; rewrite (RA_E_reg _ _ 10 10%bv eq_refl), H10; reflexivity).
assert (E11 : ew E0 11 = Z_to_bv 64 n) by (subst E0; rewrite (RA_E_reg _ _ 11 11%bv eq_refl), H11; reflexivity).
destruct (RA_E_extra regs cnt fail live peak k ran most) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39).
fold E0 in E32, E33, E34, E35, E36, E37, E38, E39.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (@alloc_ceiling_lt rc) as Hcl. pose proof (@alloc_ceiling_value rc) as Hcv.
pose proof (pal_env B PAL) as HENV.
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_pres HJ) as HJpres.
pose proof (ajxR_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hrq : forall x, 0 <= x -> req_size (x + 16) = x + 16)
  by (intros x Hx; unfold req_size; destruct (Z.eqb_spec (x + 16) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly2 S2 _ W2 (ms_mem ms) mdc (p - 16) (k + 16) HAR2 Hab)
  as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
rewrite Hrq in Hbceil, Happ, Hbpres by lia.
pose proof (ra_blk_off_img ly2 S2 _ W2 (ms_mem ms) mdc (p - 16) (k + 16) HAR2 Hab) as Hoff. rewrite Hrq in Hoff by lia.
assert (U0p : bv_unsigned (ew E0 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Up : bv_unsigned (ew E 10) = p) by (rewrite (proj1 AG 10%nat ltac:(lia)); exact U0p).
assert (Usp' : bv_unsigned (ew E 2) = spZ regs) by (rewrite (proj1 AG 2%nat ltac:(lia)); exact Usp).
assert (Herr : forall i, 0 <= i < 4 -> YImgTop.IMG_LO <= as_errno B + i < YImgTop.IMG_TOP)
  by (intros i Hi; apply ra_img_range; apply (proj1 (proj2 HENV)); lia).
pose proof (proj1 HENV) as [He0 He1]. unfold kLowMemEnd in He1.
pose proof (Herr 0 ltac:(lia)) as Herr0. pose proof (Herr 3 ltac:(lia)) as Herr3. rewrite Z.add_0_r in Herr0.
(* the old block's shadow (the allocator's law: no hidden head inside it), so the head's 16 bytes are addressable *)
destruct (alx_shadow _ _ _ LAWS ly2 S2 _ W2 (ms_mem ms) mdc (p - 16) (k + 16) HAR2 Hab) as [Hbs _].
{ intros h Hh. rewrite Hrq by lia. replace (p - 16 + (k + 16)) with (p + k) by lia. exact (HHP h Hh). }
rewrite Hrq in Hbs by lia.
assert (SHOK1 : sh_ok SEGS RA_Bx ra_SH1 E (mrestrict (w_H W2) (ms_mem ms))).
{ unfold sh_ok, ra_SH1. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W2) (ms_mem ms) E RA_Bx 10%nat (p - 16) (k + 16) p (-16) 0).
  - eapply block_shadow_range; [exact Hbs | lia | lia].
  - exact (ra_U0 E0 E 32 SHADOW_OFF AG ltac:(lia) E32 ltac:(unfold SHADOW_OFF; lia)).
  - rewrite U_SOff, Up, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - lia.
  - lia.
  - intros x Hx. change (Z.min (-16) 0) with (-16) in Hx. change (Z.max (-16) 0) with 0 in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia. }
clear SHOK. rename SHOK1 into SHOK.
(* the old head, writable again: own (b, old) rewrites it *)
pose proof (st_ok_pi_add_region _ _ _ ra_hdrw HS eq_refl
  ltac:(unfold region_ok, ra_hdrw; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
          ms_mem restrict]; rewrite Up; split; [lia|]; split; [lia|]; split; [|constructor];
        intros q Hq; apply (apresent_writable SEGS); apply Hbpres; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val ra_hdrw];
        rewrite Up, Usp', !HEI by (unfold A_TEXT, A_LIM; lia); ra_lits;
        unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff;
        repeat match goal with |- _ /\ _ => split end; try exact I; ra_lits_g; lia)) as HS1.
clear HS. rename HS1 into HS.
(* the runs, the branches and the return at the call's relation RRZ (the R runner YC1fPx.paj_run_x_m_invR, the R
   branch YSRrG.paj_branchR; the return lifts paj_ret_at by YA0nH.SRr_SRr') *)
pose proof (paj_run_x_m_invR (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem) RRZ (YA0nH.wle'_refl SEGS _) (YA0nH.wle'_trans SEGS _)) as RUN.
pose proof (YSRrG.paj_branchR (L := A_prog_listing) (PI := PA) RRZ) as BR.
pose proof (fun Wx Ex ssx msx mdx Qx H1 H2 H3 H4 => YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf Wx (mkCfg msx mdx) Qx
  (paj_ret_at (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) Wx Ex ssx msx mdx Qx H1 H2 H3 H4)) as RET.
assert (AGr : env_agree 32 (Ereg regs (map (Z_to_bv 64) (RA_X cnt fail live peak k ran most))) E0).
{ subst E0. unfold RA_E. split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
(* ---- refused (n): held = g_live + n (g_live = live - k now), the peak test ---- *)
assert (Hn64 : n < 2 ^ 64) by lia.
assert (UA : forall Ex, env_agree 40 E0 Ex ->
  U Ex (SOff 11 0) = n /\ U Ex (SOff 35 0) = live /\ U Ex (SOff 37 0) = k /\ U Ex (SOff 36 0) = peak /\
  U Ex (SOff 39 0) = most /\ U Ex (SOff 33 1) = (cnt + 1) mod 2 ^ 64 /\ U Ex (SOff 34 0) = fail /\
  U Ex (SOff 38 0) = ran /\ bv_unsigned (ew Ex 10) = p /\ bv_unsigned (ew Ex 2) = spZ regs /\
  ew Ex 3 = getr regs 3 /\ ew Ex 4 = getr regs 4 /\ ew Ex 1 = getr regs 1).
{ intros Ex AGx.
  split; [exact (ra_U0 E0 Ex 11 n AGx ltac:(lia) E11 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 35 live AGx ltac:(lia) E35 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 37 k AGx ltac:(lia) E37 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 36 peak AGx ltac:(lia) E36 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 39 most AGx ltac:(lia) E39 ltac:(lia))|].
  split; [exact (ra_U_off E0 Ex 33 cnt 1 AGx ltac:(lia) E33 Rc)|].
  split; [exact (ra_U0 E0 Ex 34 fail AGx ltac:(lia) E34 Rf)|].
  split; [exact (ra_U0 E0 Ex 38 ran AGx ltac:(lia) E38 ltac:(lia))|].
  split; [rewrite (proj1 AGx 10%nat ltac:(lia)); exact U0p|].
  split; [rewrite (proj1 AGx 2%nat ltac:(lia)); exact Usp|].
  split; [rewrite (proj1 AGx 3%nat ltac:(lia)); exact E3|].
  split; [rewrite (proj1 AGx 4%nat ltac:(lia)); exact E4|].
  rewrite (proj1 AGx 1%nat ltac:(lia)); exact E1. }
(* ---- refused (n): held = g_live + n (g_live = live - k now), the peak test (+0x240) ---- *)
ra_stepj RUN E0 HS HJ SHOK HPM AG AG1 KL KL1 ltac:(fun H => ra_hblk p k HFP Hab Hrq H).
destruct (UA _ AG1) as (Un1 & Ul1 & Uk1 & _).
psrr_branch_tok RUN BR HS SHOK RA_Bspan.
all: fold ra_heldA ra_liveK in Hc. all: fold ra_held in Hc.
all: rewrite branch_geu_U, (proj1 (proj2 (proj2 (proj2 (UA _ AG1))))), (ra_U_held _ n live k Un1 Ul1 Uk1 ltac:(lia) Hn0 Hlk) in Hc.
all: lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc
  | negb _ = false => apply negb_false_iff, Z.ltb_lt in Hc
  end.
all: rename Hc into Hb1. all: clear Un1 Ul1 Uk1.
(* ---- the g_most test (+0x250): g_ran_out := 1 when n <= g_most ---- *)
all: ra_stepj RUN E0 HS HJ SHOK HPM AG1 AG2 KL1 KL2 ltac:(fun H => ra_hblk p k HFP Hab Hrq H).
all: psrr_branch_tok RUN BR HS SHOK RA_Bspan.
all: rewrite branch_ltu_U, (proj1 (proj2 (proj2 (proj2 (proj2 (UA _ AG2)))))), (proj1 (UA _ AG2)) in Hc.
all: lazymatch type of Hc with
  | (_ <? _) = true => apply Z.ltb_lt in Hc
  | (_ <? _) = false => apply Z.ltb_ge in Hc
  end.
all: rename Hc into Hb2.
(* ---- own (b, old): the two store checks on b (shadow 0 by ra_SH1), the 8 head bytes of k, up to the poison ---- *)
all: ra_stepj RUN E0 HS HJ SHOK HPM AG2 AG3 KL2 KL3 ltac:(fun H => ra_hblk p k HFP Hab Hrq H).
(* ---- own: __asan_poison_memory_region (b, 16) at +0x2c0 (return +0x2c4) ---- *)
all: prreg HS (10%bv : bv 5) Pa0. all: prreg HS (11%bv : bv 5) Pa1. all: prreg HS (1%bv : bv 5) Pra.
all: prreg HS (3%bv : bv 5) Pgp. all: prreg HS (4%bv : bv 5) Ptp.
all: destruct (UA _ AG3) as (_ & _ & Uk3 & _ & _ & _ & _ & _ & Up3 & Usp3 & E33' & E43' & _).
all: lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  assert (Hhd2 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msx)) (p - 16) 8 k)
    by (apply (ra_hdr_of_st Ex ssx (restrict (w_H W2) msx) 10 (-16) (SOff 37 0) (p - 16) k HS);
        [rewrite Up3; lia | vm_compute; reflexivity
        | intros kk Hkk; destruct kk as [|[|[|[|[|[|[|[|kk]]]]]]]]; try lia; vm_compute; reflexivity
        | exact Uk3]) end.
all: eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf); [ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf);
  eapply (YGcallMxmn.aj_poison_x_mR SEGS B PST ARcfx 16 LAWS (@pa_segs_low _ _ PA) RRZ
    (SIGMA AS___asan_poison_memory_region) APOISONx W2 _ _ _ STK (spZ regs) FP ly S Hp W mem md
    [] ly2 S2 (remove Z.eq_dec (p - 16) Hp) _ kj (p - 16) (k + 16) (-64) _ _ HS);
  [ reflexivity | reflexivity | exact HJ
  | rewrite Pa0, Up3; first [reflexivity | unfold w64; f_equal; lia]
  | rewrite Pa1; reflexivity | reflexivity | exact Hab | rewrite Hrq by lia; lia
  | exact (st_ok_restrict_reg SEGS (w_H W2) _ _ _ 2%bv HS) | reflexivity | exact Usp3 | reflexivity | lia
  | rewrite Hes; lia | rewrite Pgp, E33'; exact Hgp | rewrite Ptp, E43'; exact Htp | exact Pra
  | apply (ret_ok_codeptr_v (L := A_prog_listing) (PI := PA)); [lia | reflexivity] ] | ].
all: cbv beta. all: intros W3 c3 _ (EW3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hsh3 & Hkp3 & Hpr3 & HMN3).
all: subst W3.
all: pose proof (ajxR_ar HJ3) as HAR3. all: pose proof (ajxR_pres HJ3) as HJpres3.
all: destruct (alx_blocks _ _ _ LAWS ly2 S2 _ W2 mem3 md3 (p - 16) (k + 16) HAR3 Hab) as (_ & _ & _ & _ & Hbpres3 & _).
all: rewrite Hrq in Hbpres3 by lia.
all: change (16 / 8) with 2 in Hkp3.
(* back at +0x2c4: every region kept (the poison writes only the head's two shadow bytes and the callee's stack) *)
all: jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W2) mem3) HP3 [1; 2; 3; 4; 5; 6; 7]%nat HS4.
all: match type of HS4 with ?tq -> _ => assert (HRKX : tq); [ cbn [ms_mem restrict];
  pose proof (ra_obj_img 14%nat ltac:(lia)) as I14; rewrite ra_val in I14; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in I14;
  assert (KSt : forall j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j ->
    mbyte SEGS (mrestrict (w_H W2) mem3) (A_prog_val (A_OBJ j) + o) =
    mbyte SEGS (mrestrict (w_H W2) (ms_mem ms2)) (A_prog_val (A_OBJ j) + o))
  by (intros j o Hj Ho; pose proof (ra_obj_img j ltac:(lia)) as Ij; rewrite ra_val in Ij;
      unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Ij;
      assert (Hw : ra_w j <= 8) by (unfold ra_w; destruct (j =? 11)%nat; lia);
      apply (YCbq.mbyte_of_aview SEGS); apply Hkp3; [lia | rewrite Hes; lia |];
      apply (ra_not_shadow (p - 16) (k + 16)); [exact Happ | lia | lia | left; unfold kLowMemEnd; lia]);
  repeat apply Forall_cons; try apply Forall_nil;
  [ apply (ra_kept_gen _ _ _ 2 (spZ regs)); [exact Usp3 | |];
    [ intros a Ha; apply (YCbq.mbyte_of_aview SEGS); apply Hkp3; [lia | rewrite Hes; lia |];
      apply (ra_not_shadow (p - 16) (k + 16)); [exact Happ | lia | lia | right; right; lia]
    | intros a Ha; apply (apresent_writable SEGS); apply HJpres3; lia ]
  | apply (ra_kept_st _ _ _ 7 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 7%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 8 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 8%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 9 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 9%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 10 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 10%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 11 1 1 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 11%nat o ltac:(lia) Ho)]
  | apply (ra_kept_gen _ _ _ (A_OBJ 14) (VAL (A_OBJ 14))); [match goal with HEIx : img_env _ _ _ |- bv_unsigned (ew ?Ex _) = _ => lazymatch goal with HEIy : img_env _ _ Ex |- _ => apply HEIy end end; unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia];
    intros a Ha; rewrite ra_val in Ha; apply (YCbq.mbyte_of_aview SEGS); apply Hkp3; [lia | rewrite Hes; lia |];
    apply (ra_not_shadow (p - 16) (k + 16)); [exact Happ | lia | lia | left; unfold kLowMemEnd; lia] ]
  | specialize (HS4 HRKX); clear HRKX] end.
all: rewrite <- restrict_mkst_fx in HS4. all: clear HS. all: rename HS4 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ey _ _ =>
  assert (HEI4 : img_env VAL A_LIM Ey) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (AG4 : env_agree 40 E0 Ey) by (apply env_agree_havoc_ge; [lia | exact AG3]);
  assert (SHOK4 : sh_ok SEGS RA_Bx [] Ey (mrestrict (w_H W2) mem3)) by apply Forall_nil;
  let E4 := fresh "E4" in set (E4 := Ey) in *; clearbody E4 end.
all: assert (HPM4 : ra_P mem mem3) by (intros H; exact (HMN3 (HPM H))).
all: assert (KMid : ra_keepl W2 mem2 mem3 [(p, k); (as_errno B, 4)])
  by (intros a Ha; rewrite <- (KL3 a Ha); apply Exists_exists in Ha as (x & Hx & Ha); cbn [In] in Hx;
      destruct Hx as [<- | [<- | []]]; unfold in_zr in Ha; cbn [fst snd] in Ha;
      (apply Hkp3; [unfold kLowMemEnd in *; lia | rewrite Hes; lia |];
       apply (ra_not_shadow (p - 16) (k + 16)); [exact Happ | lia | lia | ]);
      [right; left; lia | left; unfold kLowMemEnd in *; lia]).
all: clear SHOK HPM KL3 HJ. all: rename SHOK4 into SHOK. all: rename HPM4 into HPM. all: rename HJ3 into HJ.
all: assert (Hhd3 : val_mem SEGS (mrestrict (w_H W2) mem3) (p - 16) 8 k)
  by (apply (ra_val_mem_keep _ _ _ _ _ Hhd2); intros kk Hkk; apply (YCbq.mbyte_of_aview SEGS); apply Hkp3;
      [lia | rewrite Hes; lia | apply (ra_not_shadow (p - 16) (k + 16)); [exact Happ | lia | lia | right; left; lia]]).
all: assert (KL4 : ra_keepl W2 mem3 mem3 [(p, k); (as_errno B, 4); (p - 16, 8)]) by (intros a _; reflexivity).
(* the machine state back from the call as a variable (the runner's post tactic clears a variable state) *)
all: set (ms3 := mkst regs3 (Z_to_bv 64 (BASE + 17808)) mem3 (seg_rom SEGS)) in *.
all: assert (Hm3 : ms_mem ms3 = mem3) by reflexivity.
all: rewrite <- Hm3 in HJ, HPM, SHOK, KL4. all: clearbody ms3.
(* ---- g_live += k (back to live), the dead peak store's test (+0x2d4): peak' >= live ---- *)
all: ra_stepj RUN E0 HS HJ SHOK HPM AG4 AG5 KL4 KL5 ltac:(fun H => ra_hblk p k HFP Hab Hrq H).
all: psrr_branch_tok RUN BR HS SHOK RA_Bspan.
all: fold ra_heldA ra_liveK in Hc. all: fold ra_held in Hc.
all: change (SAlu ALU_ADD (SOff 35 0) (SMd M_MUL (SOff 37 0) (SLit 18446744073709551616))) with ra_live2 in Hc.
all: destruct (UA _ AG5) as (Un5 & Ul5 & Uk5 & Upk5 & _).
all: rewrite branch_geu_U, (ra_U_live2 _ n live k Un5 Ul5 Uk5 ltac:(lia) Hn0 Hlk) in Hc.
all: try rewrite (ra_U_held _ n live k Un5 Ul5 Uk5 ltac:(lia) Hn0 Hlk) in Hc. all: try rewrite Upk5 in Hc.
all: lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc
  | negb _ = false => exfalso; apply negb_false_iff, Z.ltb_lt in Hc; lia
  end.
(* ---- return NULL: the epilogue and `ret` ---- *)
all: ra_stepj RUN E0 HS HJ SHOK HPM AG5 AG6 KL5 KL6 ltac:(fun H => ra_hblk p k HFP Hab Hrq H).
all: eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
all: intros mat'.
all: destruct (UA _ AG6) as (Un6 & Ul6 & Uk6 & Upk6 & Um6 & Uc6 & Uf6 & Ur6 & Up6 & Usp6 & _ & _ & E16).
all: prreg HS (1%bv : bv 5) R1. all: prreg HS (10%bv : bv 5) R10.
all: lazymatch type of HS with st_ok_pi _ _ ?Ey _ _ =>
  assert (HEI6 : img_env VAL A_LIM Ey) by assumption end.
all: apply KR; [ | apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARcfx LAWS (@pa_segs_low _ _ PA) RRZ); exact HJ
               | exact HPM
               | intros a Ha; rewrite (KL6 a), Hm3; [exact (KMid a Ha)|];
                 apply Exists_exists in Ha as (x & Hx & Hax); apply Exists_exists; exists x; split; [|exact Hax];
                 destruct Hx as [<- | [<- | []]]; cbn; auto ].
all: unfold ra_retf.
all: split; [rewrite R1; first [exact E16 | rewrite E16; reflexivity]|].
all: split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS);
  [exact (YP03.env_agree_trans 32 _ _ _ AGr (YP03.env_agree_le 32 40 _ _ ltac:(lia) AG6)) | vm_compute; reflexivity]|].
all: split; [rewrite R10; reflexivity|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 7 8 (SOff 33 1)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity | exact Uc6 | cbn; lia
  | pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64) ltac:(lia)); cbn; lia]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 8 8 (SOff 34 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity | exact Uf6 | cbn; lia | cbn; lia]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 9 8 ra_live2); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
  | exact (ra_U_live2 _ n live k Un6 Ul6 Uk6 ltac:(lia) Hn0 Hlk) | cbn; lia | cbn; lia]|].
(* g_peak: unchanged when held <= peak (the bgeu at +0x240 taken), held otherwise *)
all: split; [first
  [ eapply (ra_static_val _ _ (restrict (w_H W2) _) 10 8 (SOff 36 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
      | rewrite Upk6; symmetry; apply Z.max_l; lia | cbn; lia | cbn; lia]
  | eapply (ra_static_val _ _ (restrict (w_H W2) _) 10 8 ra_held); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
      | rewrite (ra_U_held _ n live k Un6 Ul6 Uk6 ltac:(lia) Hn0 Hlk); symmetry; apply Z.max_r; lia | cbn; lia | cbn; lia] ]|].
(* g_ran_out: 1 when n <= g_most (the bltu at +0x250 not taken), unchanged otherwise *)
all: split; [first
  [ eapply (ra_static_val _ _ (restrict (w_H W2) _) 11 1 (SOff 38 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
      | rewrite Ur6; destruct (Z.leb_spec n most); [lia | reflexivity] | cbn; lia | cbn; destruct (n <=? most); lia]
  | eapply (ra_static_val _ _ (restrict (w_H W2) _) 11 1 (SLit 1)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
      | rewrite U_SLit; destruct (Z.leb_spec n most); [reflexivity | lia] | cbn; lia | cbn; destruct (n <=? most); lia] ]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 14 8 (SOff 39 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity | exact Um6 | cbn; lia | cbn; lia]|].
all: apply (ra_val_mem_keep _ _ _ _ _ Hhd3); intros kk Hkk; apply (YCbq.mbyte_of_aview SEGS); rewrite <- Hm3; apply KL6.
all: apply Exists_exists; exists (p - 16, 8); split; [cbn; auto | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* ---- SUCCESS (+0x190 .. the `ret`): own (nb, n): the two store checks on nb, the 8 head bytes of n,
   __asan_poison_memory_region (nb, 16), g_live += n, g_peak := max (g_peak, g_live), return nb + 16 ---- *)
Definition RA_NBF : afact := mkAF 4096 (2 ^ 47 - 2 ^ 23) 4.
Definition ra_blk : YP09.region := YP09.mkRegion (Some 64%nat) 0 8 0 8 [].
Definition ra_SHs : list shent := [mkSHE 64 0 16].
(* a write of the new head: a block of the current allocator state that is new, or the old one (realloc in place,
   then the footprint FP covers it) *)
Ltac ra_nblk res n HNEW Hin2 Hrq H :=
  lazymatch type of H with _ <= ?a < _ =>
  left; unfold awr_byte; destruct HNEW as [Hnew | Hfp];
  [ right; right; left; exists res, (n + 16); split; [exact Hin2|]; split; [exact Hnew | rewrite Hrq by lia; lia]
  | right; left; split; [ replace a with (res + (a - res)) by lia; apply Hfp; lia
                        | exists res, (n + 16); split; [exact Hin2 | rewrite Hrq by lia; lia] ] ] end.
Ltac ra_stepj80 RUN Es HS HJ SHOK HPM AG AGn KL KLn blk :=
  paj_run_tok_x_inv RUN HS HJ SHOK HPM RA_Bspan; [ra_wr blk|];
  ra_newenv 80%nat Es HS AG AGn;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
  lazymatch type of KL with ra_keepl _ ?mr _ ?L =>
    pose proof (ra_keepl_step Wx Ex rs mr mA mB L HFr ltac:(ra_nwL) KL) as KLn; clear HFr KL end end.

Lemma ra_arm_success : forall STK FP ly S Hp (W : world SEGS) regs mem md ly2 S2 (W2 : world SEGS) kj mem2 ms mdc Q
    k n cnt fail live peak ran most res Hp2,
  apoison_realizes_x SEGS B ARcfx 16 (SIGMA AS___asan_poison_memory_region) ->
  ESTACK + 64 <= STK -> alloc_ceiling <= spZ regs - STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 11 = w64 n ->
  In (res, n + 16) (ablocks B ly2 S2) -> 0 <= n -> 4096 <= res -> res mod 16 = 0 ->
  (~ In (res, n + 16) (ablocks B ly S) \/ (forall i, 0 <= i < n + 16 -> inFP FP (res + i))) ->
  (forall h, In h Hp2 -> ~ (res <= h < res + n + 16)) ->
  0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 -> 0 <= k <= live -> live < 2 ^ 64 -> live <= peak < 2 ^ 64 ->
  (ran = 0 \/ ran = 1) -> 0 <= most < 2 ^ 64 -> live - k + n < 2 ^ 64 ->
  ra_cutj (fun E => ew E 64 = w64 res) STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_rS []
    ly S Hp W mem md ly2 S2 Hp2 W2 kj mem2 [(res + 16, n)] ms mdc ->
  (forall regs' mem' md',
     ra_retf regs regs' (res + 16) W2 mem' ((cnt + 1) mod 2 ^ 64) fail (live - k + n) (Z.max peak (live - k + n))
       ran most res n ->
     ajournal_xR (SK := SK) SEGS B PST ARcfx RRZ STK (spZ regs) FP ly S Hp W mem md [] ly2 S2 (res :: Hp2) W2 mem' md' kj ->
     ra_P mem mem' -> ra_keepl W2 mem2 mem' [(res + 16, n)] ->
     Q W2 (mkCfg (mkst regs' (v_jalr (getr regs' 1) 0) mem' (seg_rom SEGS)) md')) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ly2 S2 W2 kj mem2 ms mdc Q k n cnt fail live peak ran most res Hp2 APOISONx H64 Hlo
  Hgp Htp H11 Hin2 Hn0 Hr4096 Hr16 HNEW HHP Rc Rf Rk Rl Rp Rr Rm Hlk (Es & HEIs & AGes & E64 & HS & SHOK & HJ & HPM & KL) KR.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (subst E0; rewrite (RA_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E0 1 = getr regs 1) by (subst E0; exact (RA_E_reg _ _ 1 1%bv eq_refl)).
assert (E3 : ew E0 3 = getr regs 3) by (subst E0; exact (RA_E_reg _ _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4) by (subst E0; exact (RA_E_reg _ _ 4 4%bv eq_refl)).
assert (E11 : ew E0 11 = Z_to_bv 64 n) by (subst E0; rewrite (RA_E_reg _ _ 11 11%bv eq_refl), H11; reflexivity).
destruct (RA_E_extra regs cnt fail live peak k ran most) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39).
fold E0 in E32, E33, E34, E35, E36, E37, E38, E39.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (@alloc_ceiling_lt rc) as Hcl. pose proof (@alloc_ceiling_value rc) as Hcv.
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_pres HJ) as HJpres.
pose proof (ajxR_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hrq : forall x, 0 <= x -> req_size (x + 16) = x + 16)
  by (intros x Hx; unfold req_size; destruct (Z.eqb_spec (x + 16) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly2 S2 _ W2 (ms_mem ms) mdc res (n + 16) HAR2 Hin2)
  as (_ & _ & Hbceil & Happ & Hbpres & _).
rewrite Hrq in Hbceil, Happ, Hbpres by lia.
pose proof (ra_blk_off_img ly2 S2 _ W2 (ms_mem ms) mdc res (n + 16) HAR2 Hin2) as Hoff. rewrite Hrq in Hoff by lia.
assert (Ures : bv_unsigned (ew Es 64) = res) by (rewrite E64; unfold w64; apply unsigned_lit_small; lia).
assert (Usps : bv_unsigned (ew Es 2) = spZ regs) by (rewrite (proj1 AGes 2%nat ltac:(lia)); exact Usp).
pose proof (pal_env B PAL) as HENV.
assert (Hn64 : n < 2 ^ 64) by lia.
assert (AGr : env_agree 32 (Ereg regs (map (Z_to_bv 64) (RA_X cnt fail live peak k ran most))) E0).
{ subst E0. unfold RA_E. split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
assert (UA : forall Ex, env_agree 80 Es Ex ->
  U Ex (SOff 11 0) = n /\ U Ex (SOff 35 0) = live /\ U Ex (SOff 37 0) = k /\ U Ex (SOff 36 0) = peak /\
  U Ex (SOff 39 0) = most /\ U Ex (SOff 33 1) = (cnt + 1) mod 2 ^ 64 /\ U Ex (SOff 34 0) = fail /\
  U Ex (SOff 38 0) = ran /\ bv_unsigned (ew Ex 64) = res /\ bv_unsigned (ew Ex 2) = spZ regs /\
  ew Ex 3 = getr regs 3 /\ ew Ex 4 = getr regs 4 /\ ew Ex 1 = getr regs 1 /\ env_agree 40 E0 Ex).
{ intros Ex AGx. assert (AG0 : env_agree 40 E0 Ex)
    by exact (YP03.env_agree_trans 40 _ _ _ AGes (YP03.env_agree_le 40 80 _ _ ltac:(lia) AGx)).
  split; [exact (ra_U0 E0 Ex 11 n AG0 ltac:(lia) E11 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 35 live AG0 ltac:(lia) E35 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 37 k AG0 ltac:(lia) E37 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 36 peak AG0 ltac:(lia) E36 ltac:(lia))|].
  split; [exact (ra_U0 E0 Ex 39 most AG0 ltac:(lia) E39 ltac:(lia))|].
  split; [exact (ra_U_off E0 Ex 33 cnt 1 AG0 ltac:(lia) E33 Rc)|].
  split; [exact (ra_U0 E0 Ex 34 fail AG0 ltac:(lia) E34 Rf)|].
  split; [exact (ra_U0 E0 Ex 38 ran AG0 ltac:(lia) E38 ltac:(lia))|].
  split; [rewrite (proj1 AGx 64%nat ltac:(lia)); exact Ures|].
  split; [rewrite (proj1 AG0 2%nat ltac:(lia)); exact Usp|].
  split; [rewrite (proj1 AG0 3%nat ltac:(lia)); exact E3|].
  split; [rewrite (proj1 AG0 4%nat ltac:(lia)); exact E4|].
  split; [rewrite (proj1 AG0 1%nat ltac:(lia)); exact E1 | exact AG0]. }
assert (AG : env_agree 80 Es Es) by (split; [intros; reflexivity | reflexivity]).
(* the new block's shadow (no hidden head inside it), so the head's 16 bytes are addressable *)
destruct (alx_shadow _ _ _ LAWS ly2 S2 _ W2 (ms_mem ms) mdc res (n + 16) HAR2 Hin2) as [Hbs _].
{ intros h Hh. rewrite Hrq by lia. pose proof (HHP h Hh). lia. }
rewrite Hrq in Hbs by lia.
(* atom 64's fact, the head region, the head's shadow entry *)
pose proof (st_ok_pi_add_fact _ _ _ 64 RA_NBF HS
  ltac:(unfold afact_ok, RA_NBF; cbn [af_lo af_hi af_al2]; rewrite Ures; change (2 ^ 4) with 16;
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ;
        split; [lia | split; [exact Hr16 | lia]])) as HS1.
pose proof (st_ok_pi_add_region _ _ _ ra_blk HS1 eq_refl
  ltac:(unfold region_ok, ra_blk; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
          ms_mem restrict]; rewrite Ures; split; [lia|]; split; [lia|]; split; [|constructor];
        intros q Hq; apply (apresent_writable SEGS); apply Hbpres; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val ra_blk];
        rewrite Ures, Usps, !HEIs by (unfold A_TEXT, A_LIM; lia); ra_lits;
        unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff;
        repeat match goal with |- _ /\ _ => split end; try exact I; ra_lits_g; lia)) as HS2.
clear HS HS1. rename HS2 into HS.
assert (SHOK1 : sh_ok SEGS RA_Bx ra_SHs Es (mrestrict (w_H W2) (ms_mem ms))).
{ unfold sh_ok, ra_SHs. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W2) (ms_mem ms) Es RA_Bx 64%nat res (n + 16) res 0 16).
  - eapply block_shadow_range; [exact Hbs | lia | lia].
  - exact (ra_U0 E0 Es 32 SHADOW_OFF AGes ltac:(lia) E32 ltac:(unfold SHADOW_OFF; lia)).
  - rewrite U_SOff, Ures, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - lia.
  - lia.
  - intros x Hx. change (Z.min 0 16) with 0 in Hx. change (Z.max 0 16) with 16 in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia. }
clear SHOK. rename SHOK1 into SHOK.
(* the runs, the branch and the return at the call's relation RRZ (as ra_arm_refused) *)
pose proof (paj_run_x_m_invR (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS PST_ok
  (ra_P mem) (ra_PLAW mem) RRZ (YA0nH.wle'_refl SEGS _) (YA0nH.wle'_trans SEGS _)) as RUN.
pose proof (YSRrG.paj_branchR (L := A_prog_listing) (PI := PA) RRZ) as BR.
pose proof (fun Wx Ex ssx msx mdx Qx H1 H2 H3 H4 => YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf Wx (mkCfg msx mdx) Qx
  (paj_ret_at (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) Wx Ex ssx msx mdx Qx H1 H2 H3 H4)) as RET.
(* ---- own (nb, n): the two store checks on nb (shadow 0 by ra_SHs), the 8 head bytes of n, up to the poison ---- *)
ra_stepj80 RUN Es HS HJ SHOK HPM AG AG1 KL KL1 ltac:(fun H => ra_nblk res n HNEW Hin2 Hrq H).
(* ---- own: __asan_poison_memory_region (nb, 16) at +0x1fc (return +0x200) ---- *)
prreg HS (10%bv : bv 5) Pa0. prreg HS (11%bv : bv 5) Pa1. prreg HS (1%bv : bv 5) Pra.
prreg HS (3%bv : bv 5) Pgp. prreg HS (4%bv : bv 5) Ptp.
destruct (UA _ AG1) as (Un1 & _ & _ & _ & _ & _ & _ & _ & Ur1 & Usp1 & E31 & E41 & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  assert (Hhd2 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msx)) res 8 n)
    by (apply (ra_hdr_of_st Ex ssx (restrict (w_H W2) msx) 64 0 (SOff 11 0) res n HS);
        [rewrite Ur1; lia | vm_compute; reflexivity
        | intros kk Hkk; destruct kk as [|[|[|[|[|[|[|[|kk]]]]]]]]; try lia; vm_compute; reflexivity
        | exact Un1]) end.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf); [ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf);
  eapply (YGcallMxmn.aj_poison_x_mR SEGS B PST ARcfx 16 LAWS (@pa_segs_low _ _ PA) RRZ
    (SIGMA AS___asan_poison_memory_region) APOISONx W2 _ _ _ STK (spZ regs) FP ly S Hp W mem md
    [] ly2 S2 Hp2 _ kj res (n + 16) (-64) _ _ HS);
  [ reflexivity
  | reflexivity
  | exact HJ
  | rewrite Pa0; first [exact E64 | rewrite (proj1 AG1 64%nat ltac:(lia)); exact E64]
  | rewrite Pa1; reflexivity
  | reflexivity
  | exact Hin2
  | rewrite Hrq by lia; lia
  | exact (st_ok_restrict_reg SEGS (w_H W2) _ _ _ 2%bv HS)
  | reflexivity
  | exact Usp1
  | reflexivity
  | lia
  | rewrite Hes; lia
  | rewrite Pgp, E31; exact Hgp
  | rewrite Ptp, E41; exact Htp
  | exact Pra
  | apply (ret_ok_codeptr_v (L := A_prog_listing) (PI := PA)); [lia | reflexivity] ] | ].
cbv beta. intros W3 c3 _ (EW3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hsh3 & Hkp3 & Hpr3 & HMN3).
subst W3.
pose proof (ajxR_ar HJ3) as HAR3. pose proof (ajxR_pres HJ3) as HJpres3.
change (16 / 8) with 2 in Hkp3.
(* back at +0x200: every region but the new head kept (its window would need a shadow entry the poison voids) *)
jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W2) mem3) HP3 [1; 2; 3; 4; 5; 6; 7]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRKX : tq); [ cbn [ms_mem restrict];
  pose proof (ra_obj_img 14%nat ltac:(lia)) as I14; rewrite ra_val in I14; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in I14;
  assert (KSt : forall j o, (7 <= j <= 11)%nat -> 0 <= o < ra_w j ->
    mbyte SEGS (mrestrict (w_H W2) mem3) (A_prog_val (A_OBJ j) + o) =
    mbyte SEGS (mrestrict (w_H W2) (ms_mem ms0)) (A_prog_val (A_OBJ j) + o))
  by (intros j o Hj Ho; pose proof (ra_obj_img j ltac:(lia)) as Ij; rewrite ra_val in Ij;
      unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Ij;
      assert (Hw : ra_w j <= 8) by (unfold ra_w; destruct (j =? 11)%nat; lia);
      apply (YCbq.mbyte_of_aview SEGS); apply Hkp3; [lia | rewrite Hes; lia |];
      apply (ra_not_shadow res (n + 16)); [exact Happ | lia | lia | left; unfold kLowMemEnd; lia]);
  repeat apply Forall_cons; try apply Forall_nil;
  [ apply (ra_kept_gen _ _ _ 2 (spZ regs)); [exact Usp1 | |];
    [ intros a Ha; apply (YCbq.mbyte_of_aview SEGS); apply Hkp3; [lia | rewrite Hes; lia |];
      apply (ra_not_shadow res (n + 16)); [exact Happ | lia | lia | right; right; lia]
    | intros a Ha; apply (apresent_writable SEGS); apply HJpres3; lia ]
  | apply (ra_kept_st _ _ _ 7 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 7%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 8 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 8%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 9 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 9%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 10 8 8 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 10%nat o ltac:(lia) Ho)]
  | apply (ra_kept_st _ _ _ 11 1 1 _); [lia | assumption | lia | cbn; lia | exact (fun o Ho => KSt 11%nat o ltac:(lia) Ho)]
  | apply (ra_kept_gen _ _ _ (A_OBJ 14) (VAL (A_OBJ 14)));
    [match goal with |- bv_unsigned (ew ?Ex _) = _ => lazymatch goal with HEIy : img_env _ _ Ex |- _ => apply HEIy end end;
     unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia];
    intros a Ha; rewrite ra_val in Ha; apply (YCbq.mbyte_of_aview SEGS); apply Hkp3; [lia | rewrite Hes; lia |];
    apply (ra_not_shadow res (n + 16)); [exact Happ | lia | lia | left; unfold kLowMemEnd; lia] ]
  | specialize (HS4 HRKX); clear HRKX] end.
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ey _ _ =>
  assert (HEI4 : img_env VAL A_LIM Ey) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (AG4 : env_agree 80 Es Ey) by (apply env_agree_havoc_ge; [lia | exact AG1]);
  assert (SHOK4 : sh_ok SEGS RA_Bx [] Ey (mrestrict (w_H W2) mem3)) by apply Forall_nil;
  let E5 := fresh "Ey" in set (E5 := Ey) in *; clearbody E5 end.
assert (HPM4 : ra_P mem mem3) by (intros H; exact (HMN3 (HPM H))).
assert (KMid : ra_keepl W2 mem2 mem3 [(res + 16, n)])
  by (intros a Ha; rewrite <- (KL1 a Ha); apply Exists_exists in Ha as (x & Hx & Ha); cbn [In] in Hx;
      destruct Hx as [<- | []]; unfold in_zr in Ha; cbn [fst snd] in Ha;
      apply Hkp3; [lia | rewrite Hes; lia |];
      apply (ra_not_shadow res (n + 16)); [exact Happ | lia | lia | right; left; lia]).
clear SHOK HPM KL1 HJ. rename SHOK4 into SHOK. rename HPM4 into HPM. rename HJ3 into HJ.
assert (Hhd3 : val_mem SEGS (mrestrict (w_H W2) mem3) res 8 n)
  by (apply (ra_val_mem_keep _ _ _ _ _ Hhd2); intros kk Hkk; apply (YCbq.mbyte_of_aview SEGS); apply Hkp3;
      [lia | rewrite Hes; lia | apply (ra_not_shadow res (n + 16)); [exact Happ | lia | lia | right; left; lia]]).
assert (KL4 : ra_keepl W2 mem3 mem3 [(res + 16, n); (res, 8)]) by (intros a _; reflexivity).
set (ms3 := mkst regs3 (Z_to_bv 64 (BASE + 17612)) mem3 (seg_rom SEGS)) in *.
assert (Hm3 : ms_mem ms3 = mem3) by reflexivity.
rewrite <- Hm3 in HJ, HPM, SHOK, KL4. clearbody ms3.
(* ---- g_live += n, the peak test (+0x214) ---- *)
ra_stepj80 RUN Es HS HJ SHOK HPM AG4 AG5 KL4 KL5 ltac:(fun H => ra_nblk res n HNEW Hin2 Hrq H).
psrr_branch_tok RUN BR HS SHOK RA_Bspan.
all: fold ra_heldA in Hc.
all: destruct (UA _ AG5) as (Un5 & Ul5 & Uk5 & Upk5 & _).
all: rewrite branch_geu_U, Upk5, (ra_U_heldA _ n live k Un5 Ul5 Uk5 ltac:(lia) Hn0 Hlk) in Hc.
all: lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc
  | negb _ = false => apply negb_false_iff, Z.ltb_lt in Hc
  end.
(* ---- g_peak := g_live when it is larger, return nb + 16 ---- *)
all: ra_stepj80 RUN Es HS HJ SHOK HPM AG5 AG6 KL5 KL6 ltac:(fun H => ra_nblk res n HNEW Hin2 Hrq H).
all: eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
all: intros mat'.
all: destruct (UA _ AG6) as (Un6 & Ul6 & Uk6 & Upk6 & Um6 & Uc6 & Uf6 & Ur6 & Ures6 & Usp6 & _ & _ & E16 & AG06).
all: prreg HS (1%bv : bv 5) R1. all: prreg HS (10%bv : bv 5) R10.
all: lazymatch type of HS with st_ok_pi _ _ ?Ey _ _ =>
  assert (HEI6 : img_env VAL A_LIM Ey) by assumption end.
all: apply KR; [ | apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARcfx LAWS (@pa_segs_low _ _ PA) RRZ); exact HJ
               | exact HPM
               | intros a Ha; rewrite (KL6 a), Hm3; [exact (KMid a Ha)|];
                 apply Exists_exists in Ha as (x & Hx & Hax); apply Exists_exists; exists x; split; [|exact Hax];
                 destruct Hx as [<- | []]; cbn; auto ].
all: unfold ra_retf.
all: split; [rewrite R1; first [exact E16 | rewrite E16; reflexivity]|].
all: split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS);
  [exact (YP03.env_agree_trans 32 _ _ _ AGr (YP03.env_agree_le 32 40 _ _ ltac:(lia) AG06)) | vm_compute; reflexivity]|].
all: split; [rewrite R10; first [rewrite Ures6; reflexivity | unfold w64; f_equal; rewrite Ures6; lia
                                | rewrite unsigned_lit_small; [reflexivity | lia]]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 7 8 (SOff 33 1)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity | exact Uc6 | cbn; lia
  | pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64) ltac:(lia)); cbn; lia]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 8 8 (SOff 34 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity | exact Uf6 | cbn; lia | cbn; lia]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 9 8 ra_heldA); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
  | exact (ra_U_heldA _ n live k Un6 Ul6 Uk6 ltac:(lia) Hn0 Hlk) | cbn; lia | cbn; lia]|].
all: split; [first
  [ eapply (ra_static_val _ _ (restrict (w_H W2) _) 10 8 (SOff 36 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
      | rewrite Upk6; symmetry; apply Z.max_l; lia | cbn; lia | cbn; lia]
  | eapply (ra_static_val _ _ (restrict (w_H W2) _) 10 8 ra_heldA); [exact HS | exact HEI6 | lia | vm_compute; reflexivity
      | rewrite (ra_U_heldA _ n live k Un6 Ul6 Uk6 ltac:(lia) Hn0 Hlk); symmetry; apply Z.max_r; lia | cbn; lia | cbn; lia] ]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 11 1 (SOff 38 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity | exact Ur6 | cbn; lia | cbn; lia]|].
all: split; [eapply (ra_static_val _ _ (restrict (w_H W2) _) 14 8 (SOff 39 0)); [exact HS | exact HEI6 | lia | vm_compute; reflexivity | exact Um6 | cbn; lia | cbn; lia]|].
all: apply (ra_val_mem_keep _ _ _ _ _ Hhd3); intros kk Hkk; apply (YCbq.mbyte_of_aview SEGS); rewrite <- Hm3; apply KL6.
all: apply Exists_exists; exists (res, 8); split; [cbn; auto | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* ---- CHOSEN-FAIL's `ret` (+0x30c): the five statics at the stop (g_count + 1, g_fail_at = SIZE_MAX, the rest
   unchanged), a0 = 0, ra and the callee-saved registers kept ---- *)
Lemma ra_arm_fail : forall STK FP ly S Hp (W : world SEGS) regs mem md ms mdc Q k cnt fail live peak ran most X,
  64 <= STK ->
  0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 -> 0 <= live < 2 ^ 64 -> 0 <= peak < 2 ^ 64 -> (ran = 0 \/ ran = 1) ->
  0 <= most < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  ra_cut STK (spZ regs) FP (RA_E regs (RA_X cnt fail live peak k ran most)) ss_cf_ret [] ly S Hp W mem md Hp X ms mdc ->
  (forall regs' mem' md',
     getr regs' 1 = getr regs 1 -> aregs_preserved regs regs' -> getr regs' 10 = w64 0 ->
     val_mem SEGS (mrestrict (w_H W) mem') (A_prog_val (A_OBJ 7)) 8 ((cnt + 1) mod 2 ^ 64) ->
     val_mem SEGS (mrestrict (w_H W) mem') (A_prog_val (A_OBJ 8)) 8 (2 ^ 64 - 1) ->
     val_mem SEGS (mrestrict (w_H W) mem') (A_prog_val (A_OBJ 9)) 8 live ->
     val_mem SEGS (mrestrict (w_H W) mem') (A_prog_val (A_OBJ 10)) 8 peak ->
     val_mem SEGS (mrestrict (w_H W) mem') (A_prog_val (A_OBJ 11)) 1 ran ->
     ajournal_x (SK := SK) SEGS B PST ARcfx STK (spZ regs) FP ly S Hp W mem md [] ly S Hp W mem' md' 0 ->
     ra_P mem mem' -> ra_off W mem mem' X ->
     Q W (mkCfg (mkst regs' (v_jalr (getr regs' 1) 0) mem' (seg_rom SEGS)) md')) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros STK FP ly S Hp W regs mem md ms mdc Q k cnt fail live peak ran most X H64 Rc Rf Rl Rp Rr Rm Rk
  (E & HEI & AG & HS & SHOK & HJ & HPM & KP) KR.
set (E0 := RA_E regs (RA_X cnt fail live peak k ran most)) in *.
assert (E1 : ew E0 1 = getr regs 1) by (subst E0; exact (RA_E_reg _ _ 1 1%bv eq_refl)).
destruct (RA_E_extra regs cnt fail live peak k ran most) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39).
fold E0 in E32, E33, E34, E35, E36, E37, E38, E39.
assert (AGr : env_agree 32 (Ereg regs (map (Z_to_bv 64) (RA_X cnt fail live peak k ran most))) E0).
{ subst E0. unfold RA_E. split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
pose proof (paj_ret_at (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)) as RET.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
apply KR.
- rewrite R1, (proj1 AG 1%nat ltac:(lia)), E1. first [reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
- eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS);
    [exact (YP03.env_agree_trans 32 _ _ _ AGr (YP03.env_agree_le 32 40 _ _ ltac:(lia) AG)) | vm_compute; reflexivity].
- rewrite R10. reflexivity.
- eapply (ra_static_val _ _ (restrict (w_H W) _) 7 8 (SOff 33 1)); [exact HS | exact HEI | lia | vm_compute; reflexivity
    | exact (ra_U_off E0 E 33 cnt 1 AG ltac:(lia) E33 Rc) | cbn; lia
    | pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64) ltac:(lia)); cbn; lia].
- eapply (ra_static_val _ _ (restrict (w_H W) _) 8 8 (SLit (2 ^ 64 - 1))); [exact HS | exact HEI | lia | vm_compute; reflexivity
    | rewrite U_SLit; unfold zcanon, M64; reflexivity | cbn; lia | cbn; lia].
- eapply (ra_static_val _ _ (restrict (w_H W) _) 9 8 (SOff 35 0)); [exact HS | exact HEI | lia | vm_compute; reflexivity
    | exact (ra_U0 E0 E 35 live AG ltac:(lia) E35 Rl) | cbn; lia | cbn; lia].
- eapply (ra_static_val _ _ (restrict (w_H W) _) 10 8 (SOff 36 0)); [exact HS | exact HEI | lia | vm_compute; reflexivity
    | exact (ra_U0 E0 E 36 peak AG ltac:(lia) E36 Rp) | cbn; lia | cbn; lia].
- eapply (ra_static_val _ _ (restrict (w_H W) _) 11 1 (SOff 38 0)); [exact HS | exact HEI | lia | vm_compute; reflexivity
    | exact (ra_U0 E0 E 38 ran AG ltac:(lia) E38 ltac:(lia)) | cbn; lia | cbn; lia].
- apply (ajournal_x_materialize (SK := SK) SEGS B PST ARcfx LAWS (@pa_segs_low _ _ PA)). exact HJ.
- exact HPM.
- exact KP.
Qed.

(* ==== THE TOP THEOREM: fuzz_realloc on A' against the text tfuzz_realloc_specX (lib/A/PRH_FnAlloc.v on the AL
   base, the kit's caa965672d21; on this tree PRH_FnAlloc.v:627, the SRr' form with the hull budget and use), at the generated PrhImg prh_img_A and a Theorem Labs lane's room invariant. The CfImg stays the Section's
   {ci}: its two runtime call targets are named premises CF_unpoison / CF_poison, the final instance closes them by computation. ==== *)
#[local] Existing Instance prh_img_A.
Lemma ra_trace_eq : forall pc0 r, unwind_of_chain pc0 [(0, r, 0)] = prh_trace pc0 r [].
Proof. intros pc0 r. reflexivity. Qed.
Lemma ra_pi_vals : pi_g_count = A_prog_val (A_OBJ 7) /\ pi_g_fail = A_prog_val (A_OBJ 8) /\
  pi_g_live = A_prog_val (A_OBJ 9) /\ pi_g_peak = A_prog_val (A_OBJ 10) /\ pi_g_ran_out = A_prog_val (A_OBJ 11) /\
  pi_g_own_ran_out = A_prog_val (A_OBJ 13) /\ pi_g_most = A_prog_val (A_OBJ 14) /\
  pi_gz_count = 8%nat /\ pi_gz_fail = 8%nat /\ pi_gz_live = 8%nat /\ pi_gz_peak = 8%nat /\ pi_gz_ran_out = 1%nat /\
  pi_gz_own_ran_out = 1%nat /\ pi_gz_most = 8%nat.
Proof. vm_compute. repeat split. Qed.
Lemma ra_ret_realloc : @pi_ret_realloc prh_img_A = SIGMA AS_fuzz_realloc + 396.
Proof. vm_compute. reflexivity. Qed.
Lemma ra_stk : @STK_fuzz_realloc prh_img_A = 16480 /\ @STK_fuzz_malloc prh_img_A = 16416.
Proof. split; vm_compute; reflexivity. Qed.
(* a journal at a smaller static set is one at a larger (only the image clause reads PST) *)
(* over any world relation R ({R}, read off the journal): the pre-call journals at wle and the post-call ones at RRZ *)
Lemma ra_journal_pst_mono : forall {R : world SEGS -> world SEGS -> Prop} P1 P2 STK sp0 FP ly S Hp (W : world SEGS) mem md
    own ly' S' Hp' (W' : world SEGS) mem' md' k,
  (forall a, Exists (in_zr a) P1 -> Exists (in_zr a) P2) ->
  ajournal_xR (SK := SK) SEGS B P1 ARcfx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR (SK := SK) SEGS B P2 ARcfx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros R P1 P2 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k Hsub HJ.
unfold ajournal_xR, ajournal_xwR.
exact (ajxR_intro (ajxR_ar HJ) (ajxR_ly HJ) (ajxR_secs HJ) (ajxR_rel HJ) (ajxR_io HJ) (ajxR_frs HJ) (ajxR_nev HJ)
  (ajxR_k HJ) (ajxR_hi HJ) (ajxR_blk HJ) (fun a Hi Hns He Hnp Hsp => ajxR_img HJ a Hi Hns He (fun H => Hnp (Hsub a H)) Hsp)
  (ajxR_frm HJ) (ajxR_gone HJ) (ajxR_pres HJ) (ajxR_stk HJ) (ajxR_extra HJ) (ajxR_qt HJ) (ajxR_wild HJ)).
Qed.
(* the journal's image clause: an image byte no allocator owns, not errno, not a static of the walk *)
Lemma ra_journal_img : forall {R : world SEGS -> world SEGS -> Prop} STK sp0 FP ly S Hp (W : world SEGS) mem md own ly' S'
    Hp' (W' : world SEGS) mem' md' k a,
  ajournal_xR (SK := SK) SEGS B PST ARcfx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ~ YI16.sink_open_fp FP -> in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a HJ Hcl Hi Hns He Hnp.
exact (ajxR_img HJ a Hi Hns He Hnp (fp_spares_closed FP a Hcl)).
Qed.
Lemma ra_cell_kept : forall (W W' : world SEGS) mem mem' a (w : nat) v,
  (forall o, 0 <= o < Z.of_nat w -> aview SEGS (w_H W') mem' (a + o) = aview SEGS (w_H W) mem (a + o)) ->
  val_mem SEGS (mrestrict (w_H W) mem) a w v -> val_mem SEGS (mrestrict (w_H W') mem') a w v.
Proof.
intros W W' mem mem' a w v K Hv. apply (ra_val_mem_keep _ _ _ _ _ Hv). intros kk Hkk.
apply (YCbq.mbyte_of_aview SEGS). apply K. lia.
Qed.
Lemma ra_garr8_keep : forall (m m' : word -> option byte) base l,
  garr8 SEGS m base l ->
  (forall j, (j < length l)%nat -> mbyte SEGS m' (base + Z.of_nat j) = mbyte SEGS m (base + Z.of_nat j)) ->
  garr8 SEGS m' base l.
Proof.
intros m m' base l H K j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. specialize (Hv 0%nat Hkk).
replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) in * by lia.
rewrite (K j Hj). exact Hv.
Qed.

(* mbyte_of_aview at two addresses *)
Lemma ra_mbyte_of_aview2 : forall H H' (m m' : word -> option byte) a a',
  aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H' m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in E; try discriminate;
  [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma ra_le1 : forall z, 0 <= z < 256 -> le_byte z 1 0 = z.
Proof.
intros z Hz. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.
(* the new block's bytes on realloc's success: the first min (k, n) are the old bytes, the rest readable
   (FuzzReallocB.v.wip's rb_bytes_success) *)
Lemma ra_bytes_success : forall (m0 m3 : word -> option byte) p base (old : list Z) k n,
  garr8 SEGS m0 p old -> Z.of_nat (length old) = k -> 0 <= k -> 0 <= n ->
  (forall i, 0 <= i < Z.min k n -> mbyte SEGS m3 (base + i) = mbyte SEGS m0 (p + i)) ->
  (forall i, 0 <= i < n -> exists b, mbyte SEGS m3 (base + i) = Some b) ->
  exists rest, Z.of_nat (length rest) = n - Z.min k n /\ garr8 SEGS m3 base (firstn (Z.to_nat (Z.min k n)) old ++ rest).
Proof.
intros m0 m3 p base old k n Hg Hl Hk Hn Hcp Hpr.
set (f := fun j : nat => match mbyte SEGS m3 (base + Z.min k n + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end).
exists (map f (seq 0 (Z.to_nat (n - Z.min k n)))).
split; [rewrite length_map, length_seq; lia|].
intros j Hj. rewrite length_app, length_map, length_seq, length_firstn in Hj.
destruct (Nat.lt_ge_cases j (Z.to_nat (Z.min k n))) as [Hlt|Hge].
- rewrite app_nth1 by (rewrite length_firstn; lia).
  assert (E : nth j (firstn (Z.to_nat (Z.min k n)) old) 0 = nth j old 0).
  { rewrite <- (firstn_skipn (Z.to_nat (Z.min k n)) old) at 2. rewrite app_nth1; [reflexivity | rewrite length_firstn; lia]. }
  rewrite E. destruct (Hg j ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. specialize (Hv 0%nat Hkk).
  replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) by lia.
  replace (p + Z.of_nat j + Z.of_nat 0) with (p + Z.of_nat j) in Hv by lia.
  rewrite (Hcp (Z.of_nat j) ltac:(lia)). exact Hv.
- rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Nat.min (Z.to_nat (Z.min k n)) (length old)) with (Z.to_nat (Z.min k n)) by lia.
  rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. cbn [Nat.add]. unfold f.
  replace (base + Z.min k n + Z.of_nat (j - Z.to_nat (Z.min k n))) with (base + Z.of_nat j) by lia.
  destruct (Hpr (Z.of_nat j) ltac:(lia)) as (b & Hb). rewrite Hb.
  pose proof (bv_unsigned_in_range _ b) as Hbr. unfold bv_modulus in Hbr. change (2 ^ Z.of_N 8) with 256 in Hbr.
  split; [|lia].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
  replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) by lia. rewrite Hb.
  rewrite ra_le1 by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* a block of both states, not the footprint's block, keeps its bytes (the journal's block clause) *)
Lemma ra_journal_blk : forall {R : world SEGS -> world SEGS -> Prop} STK sp0 ly S Hp (W : world SEGS) mem md ly' S' Hp'
    (W' : world SEGS) mem' md' kk q mq b m i,
  ajournal_xR (SK := SK) SEGS B PST ARcfx R STK sp0 (ablocks_fp [(q, mq)]) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk ->
  ARcfx ly S Hp W mem md -> In (q, mq) (ablocks B ly S) -> In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') ->
  (b, m) <> (q, mq) -> 0 <= i < req_size m ->
  aview SEGS (w_H W') mem' (b + i) = aview SEGS (w_H W) mem (b + i).
Proof.
intros R STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' kk q mq b m i HJ HAR Hq Hb Hb' Hne Hi.
apply (ajxR_blk HJ b m i Hb Hb' Hi).
intros (r & Hr & Hx). destruct Hr as [<- | []]. cbn [fst snd] in Hx.
pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md _ _ _ _ HAR Hb Hq Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the top-level conjuncts of a hypothesis (a syntactic `_ /\ _` only), then the goal BY ITS TYPE: the kit's ec_conj_split /
   ec_conj_pick (lib/A/Prog/Ent102CallA.v), as a Theorem Labs lane's FuzzStrdup.v copies them (sd_conj_split / sd_conj_pick).
   fuzz_malloc's post is read through it, so a conjunct the kit adds to that post (the kit's outcome conjunct) cannot
   shift the others. *)
Ltac ra_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Rc" in let H2 := fresh "Rc" in destruct H as [H1 H2]; ra_conj_split H1; ra_conj_split H2
  | _ => idtac
  end.
Ltac ra_conj_pick H := ra_conj_split H; assumption.

Section top.
(* g_own_ran_out (A_OBJ 13) and g_most (A_OBJ 14): image bytes no allocator owns and not errno; the walk never writes
   either, so they are not in the walk's static set and every journal of the walk keeps them; the walk's static set
   is a part of the prh_pst. The instance proves these by computation and its image binding. *)
Hypothesis OWN_ok : (in_img SEGS (A_prog_val (A_OBJ 13))) /\ (~ Exists (in_zr (A_prog_val (A_OBJ 13))) (as_owned_static B)) /\
  (~ (as_errno B <= A_prog_val (A_OBJ 13) < as_errno B + 4)).
Hypothesis PST_sub : forall a, Exists (in_zr a) PST -> Exists (in_zr a) (@prh_pst prh_img_A).
Hypothesis PST_own_out : ~ Exists (in_zr (A_prog_val (A_OBJ 13))) PST.
Hypothesis PST_most_out : forall o, 0 <= o < 8 -> ~ Exists (in_zr (A_prog_val (A_OBJ 14) + o)) PST.
(* the callee texts: fuzz_malloc's (the kit's, AL1 proves it), __asan_(un)poison_memory_region's (YGcfHp.v,
   a Theorem Labs lane's poison102 at #102), the realloc wrapper's KEEP ROW at every ghost set and headroom (the keep row
   YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep; its discharge, arealloc_realizes_cf_k_of_parts_keep, is the
   top-level assembler's), the argument the call rule YGcallRkKeep.aj_realloc_x_cfR_keep takes as it stands *)
Hypothesis FMALLOC : tfuzz_malloc_specX (fx := fx) (rc := rc) (cp := CfParams_preset) (PI := prh_img_A)
  (RL := prh_room_live_a8 (cp := CfParams_preset)) (L := A_prog_listing) (PA := PI_prog_A) B ARcfx SK.
Hypothesis AUNPOISON : aunpoison_realizes_cf SEGS B.
Hypothesis APOISON : apoison_realizes_cf SEGS B.
Hypothesis AREAL_cf : forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep SEGS B Hp (SIGMA AS___wrap_realloc) k.
Hypothesis CF_unpoison : cf_pc_unpoison = SIGMA AS___asan_unpoison_memory_region.
Hypothesis CF_poison : cf_pc_poison = SIGMA AS___asan_poison_memory_region.
Lemma ra_AUNPOISONx : aunpoison_realizes_x SEGS B ARcfx 16 (SIGMA AS___asan_unpoison_memory_region).
Proof. rewrite <- CF_unpoison. exact (aunpoison_realizes_cf_xs SEGS B AUNPOISON). Qed.
Lemma ra_APOISONx : apoison_realizes_x SEGS B ARcfx 16 (SIGMA AS___asan_poison_memory_region).
Proof. rewrite <- CF_poison. exact (apoison_realizes_cf_xs SEGS B APOISON). Qed.
(* the two cells the walk never writes, kept by its journal *)
Lemma ra_own_most_kept : forall {R : world SEGS -> world SEGS -> Prop} STK sp0 FP ly S Hp (W : world SEGS) mem md ly' S'
    Hp' (W' : world SEGS) mem' md' k,
  ajournal_xR (SK := SK) SEGS B PST ARcfx R STK sp0 FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  (forall o, prh_own (PI := prh_img_A) (L := A_prog_listing) (PA := PA) W mem o ->
             prh_own (PI := prh_img_A) (L := A_prog_listing) (PA := PA) W' mem' o) /\
  (forall m, prh_most (PI := prh_img_A) (L := A_prog_listing) (PA := PA) W mem m ->
             prh_most (PI := prh_img_A) (L := A_prog_listing) (PA := PA) W' mem' m).
Proof.
intros R STK sp0 FP ly S Hp W mem md ly' S' Hp' W' mem' md' k HJ Hcl.
destruct ra_pi_vals as (_ & _ & _ & _ & _ & Po & Pm & _ & _ & _ & _ & _ & Go & Gm).
split.
- intros o [Ho Ro]. split; [|exact Ro]. rewrite Po, Go in *.
  apply (ra_cell_kept W W' mem mem' _ 1 o); [|exact Ho]. intros oo Hoo. cbn in Hoo.
  replace oo with 0 by lia. rewrite Z.add_0_r. destruct OWN_ok as (O1 & O2 & O3).
  exact (ra_journal_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hcl O1 O2 O3 PST_own_out).
- intros m [Hm Rm]. split; [|exact Rm]. rewrite Pm, Gm in *.
  apply (ra_cell_kept W W' mem mem' _ 8 m); [|exact Hm]. intros oo Hoo. cbn in Hoo.
  destruct (MOST_ok oo ltac:(lia)) as (M1 & M2 & M3).
  exact (ra_journal_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hcl M1 M2 M3 (PST_most_out oo ltac:(lia))).
Qed.

(* the hidden heads of the other harness blocks (all but the head at x) lie outside a block (b, m) of a later state *)
Lemma ra_heads_apart : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own ly' S' Hp' (W' : world SEGS) mem' md' b m x,
  ARcfx ly' S' Hp' W' mem' md' -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly' S') ->
  (forall a ka, In (a, ka) Lam -> a - 16 <> x -> (a - 16, ka + 16) <> (b, m) /\ In (a - 16, ka + 16) (ablocks B ly' S')) ->
  forall h, In h Hp -> h <> x -> ~ (b <= h < b + m).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly' S' Hp' W' mem' md' b m x HAR HL Hin Htr h Hh Hhx Hr.
pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HL) as HP.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a ka] & Eh & Hak). cbn [fst] in Eh.
change (@cf_head CfParams_preset) with 16 in Eh. subst h.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL Hak) as (Hka & _).
destruct (Htr a ka Hak Hhx) as [E Hin'].
pose proof (sep_blocks_x SEGS B ARcfx LAWS ly' S' Hp' W' mem' md' _ _ _ _ HAR Hin' Hin E) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
assert (0 < req_size (ka + 16)) by (unfold req_size; destruct (Z.eqb_spec (ka + 16) 0); lia).
assert (m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
lia.
Qed.

Theorem fuzz_realloc_holds_Ap :
  tfuzz_realloc_specX (fx := fx) (rc := rc) (ci := ci) (cp := CfParams_preset) (PI := prh_img_A)
    (RL := prh_room_live_a8 (cp := CfParams_preset)) (L := A_prog_listing) (PA := PI_prog_A) B ARcfx SK.
Proof.
unfold tfuzz_realloc_specX, fpostmR, fQmn, fpostR, apost_base_xR.
intros ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own
  [HPRE (HRO & Hsptop & Hraceil & Hfrm)] HRL HMU Hsec H24 HHB HU0 HU1 H10 H11 Hn0 Hnmax HL Hold Hlive.
change (@cf_head CfParams_preset) with 16 in *.
destruct ra_stk as [HSTK HSTKm]. rewrite HSTK in HPRE |- *.
pose proof HPRE as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hcm : cf_malloc_max <= 2 ^ 30) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hlo : alloc_ceiling <= spZ regs - 16480) by lia.
assert (Himg : forall a, in_img SEGS a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP) by (intros a Ha; exact (pa_img_range a Ha)).
destruct ra_pi_vals as (Pc & Pf & Pl & Pp & Pr & Po & Pm & Gc & Gf & Gl & Gp & Gr & Go & Gm).
unfold cfg_at. change (w64 (pa_sigma AS_fuzz_realloc)) with (Z_to_bv 64 (BASE + RA_PC)).
(* F12 ROUTE (b): ONE lift at the entry (YGcfRhLift.ra_rh_of_SRr). The segments before the realloc call stay plain SRr
   with the primed text's post as their continuation; the call (ra_seg_realloc) and its arms are SRr' at RZ_cf; the
   other path ends (p = 0's tail call, CHOSEN-FAIL) return through SRr'_ret, their wle journals lifted to wle' *)
apply YGcfRhLift.ra_rh_of_SRr.
destruct (Z.eq_dec p 0) as [Hp0|Hp0].
{ (* ===== p = NULL: the frame pops and fuzz_malloc (n) is tail-called with the caller's ra ===== *)
  subst p. rewrite Z.eqb_refl in HHB |- *.
  pose proof (ra_cut_entry0 16480 ly S Hp W regs mem md ch HPRE ltac:(lia)) as HC0.
  assert (K00 : ra_frame0 (spZ regs) W mem mem) by (intros a _ _; reflexivity).
  apply (ra_seg_z0 16480 ly S Hp W regs mem md _ _ _ ltac:(lia) Hlo H10 HC0 K00). intros ms1 mdc1 HC1 K01.
  apply (ra_seg_z1 16480 ly S Hp W regs mem md _ _ _ ltac:(lia) Hlo HC1 K01). intros ms2 mdc2 HC2 K02.
  destruct HC2 as (E & HEI & AG & HS & SHOK & HJ0 & HPM & KP).
  pose proof (ra_journal_pst_mono PST (@prh_pst prh_img_A) _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ PST_sub HJ0) as HJ.
  set (E0 := RA_E regs []) in *.
  assert (EL : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E j = getr regs r).
  { intros j r Hj Hr. rewrite (proj1 AG j ltac:(lia)). subst E0. exact (RA_E_reg regs [] j r Hr). }
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
  pose proof (EL 1%nat 1%bv ltac:(lia) eq_refl) as E1. pose proof (EL 3%nat 3%bv ltac:(lia) eq_refl) as E3.
  pose proof (EL 4%nat 4%bv ltac:(lia) eq_refl) as E4. pose proof (EL 8%nat 8%bv ltac:(lia) eq_refl) as E8.
  pose proof (EL 11%nat 11%bv ltac:(lia) eq_refl) as E11.
  assert (AGr : env_agree 32 (Ereg regs (map (Z_to_bv 64) [])) E).
  { split; [intros i Hi; rewrite (proj1 AG i ltac:(lia)); subst E0; unfold RA_E;
            rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | exact (proj2 AG)]. }
  (* the statics, the heads and the read-only view keep their entry values: the arm writes only its frame *)
  assert (KIMG : forall a, (a < YImgTop.IMG_TOP) -> 0 <= a -> aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
  { intros a Ha Ha0. apply K02; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia. }
  prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2.
  eapply SRr_mono;
  [ eapply (aj_call_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARcfx LAWS (@pa_segs_low _ _ PA) W E _ ms2
     16480 (spZ regs) [] ly S Hp W mem md [] ly S Hp mdc2 0 (@STK_fuzz_malloc prh_img_A) [] 0 (ew E 2) (getr regs 1) ch _
     HS eq_refl HJ) | ].
  { exact (st_ok_restrict_reg SEGS (w_H W) _ _ _ 2%bv HS). }
  { reflexivity. }
  { exact Usp. }
  { reflexivity. }
  { lia. }
  { rewrite HSTKm. lia. }
  { rewrite HSTKm. lia. }
  { rewrite R3, E3. exact Hgp. }
  { rewrite R4, E4. exact Htp. }
  { rewrite R1, E1. reflexivity. }
  { exact Hra. }
  { exact Hra4. }
  { unfold s0Z. rewrite R8, E8, Z.add_0_r.
    apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply K02; lia. }
  { intros HPRE1.
    assert (Esp : spZ (ms_regs ms2) = spZ regs).
    { unfold spZ at 1. rewrite R2. first [exact Usp | cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact Usp]. }
    assert (Era : raZ (ms_regs ms2) = raZ regs) by (unfold raZ; rewrite R1, E1; reflexivity).
    lazymatch goal with |- SRr ?sg ?w (mkCfg (mkst ?rx _ ?mx _) ?dx) ?Q =>
      change (SRr sg w (cfg_at SEGS (SIGMA AS_fuzz_malloc) rx mx dx) Q);
      apply (FMALLOC ly S Hp W rx mx dx ch n Lam peak cnt fail ran most own) end.
    - split; [exact HPRE1|]. split; [|split; [rewrite Esp; exact Hsptop | split; [rewrite Era; exact Hraceil | exact Hfrm]]].
      intros a Hro Hno Herr. rewrite KIMG; [exact (HRO a Hro Hno Herr) | |];
        destruct Hro as [(sg & Hsg & _ & Hr) | Hr];
        first [pose proof (Himg a (ex_intro _ sg (conj Hsg Hr))) | pose proof (Himg a (pa_relro_img a Hr))];
        unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia.
    - exact HRL.
    - exact HMU.
    - exact Hsec.
    - exact H24.
    - exact HHB.
    - rewrite R10, E11. exact H11.
    - exact Hn0.
    - exact Hnmax.
    - apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W _ Lam peak cnt fail ran most own HL).
      + intros a Ha. pose proof (Himg a (S1ImgA.pst_in_img_A a Ha)). apply KIMG; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia.
      + intros a ka i Hin Hi.
        destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL Hin) as (Hka & Hb & _).
        change (@cf_head CfParams_preset) with 16 in Hb |- *.
        destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a - 16) (ka + 16) (conj HAR HXS) Hb) as (_ & Hb4 & Hbc & _).
        assert (Hrq : req_size (ka + 16) = ka + 16) by (unfold req_size; destruct (Z.eqb_spec (ka + 16) 0); lia).
        rewrite Hrq in Hbc. apply K02; lia.
      + intros a ka _ Hb. exact Hb.
      + apply Permutation_refl.
    - exact Hlive. }
  { intros a (r & [] & _). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJo & HJi & HP2 & HQ & HMN).
  (* the path end: back to the primed post, the tail call's wle journal lifted to wle' *)
  apply (YSRrG.SRr'_ret SEGS YGcfRehidePost.RZ_cf). cbv beta.
  exists ly2, S2, Hp2, regs2, mem2, md2, (0 + k1).
  split; [exact Hc2|].
  split; [unfold ajournal_xR; eapply ajournal_xwR_mono; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HJo]|].
  split.
  { eapply (aregs_preserved_trans regs _ regs2); [|exact HP2].
    eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HS); [exact AGr | vm_compute; reflexivity]. }
  split; [|intros Hmn; exact (HMN (HPM Hmn))].
  (* fuzz_malloc's post BY NAME (ra_conj_pick): each conjunct of realloc's p = 0 arm is the conjunct of malloc's post at
     n with the same statement (the result register, room_live_cf, the hull use, the two position arms,
     prh_alloc_post) *)
  destruct HQ as (res & HMP).
  exists res. split; [ra_conj_pick HMP|]. split; [ra_conj_pick HMP|]. split; [ra_conj_pick HMP|].
  split; [ra_conj_pick HMP|].
  split; [intros Hr _; revert Hr; ra_conj_pick HMP|]. split; [intros _ Hpn; exfalso; exact (Hpn eq_refl)|].
  (* THE OUTCOME at p = 0: the tail call's outcome is fuzz_malloc's (the same event HMal (n + 16), res and S'); the
     p <> 0 clause is vacuous *)
  split; [intros _; ra_conj_pick HMP|]. split; [intros Hpn; exfalso; exact (Hpn eq_refl)|].
  left. split; [reflexivity | ra_conj_pick HMP]. }
(* ===== p <> NULL ===== *)
destruct Hold as [(Hp0' & _) | (HinL & Hold & Hlen)]; [exfalso; exact (Hp0 Hp0') |].
replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
rewrite (proj2 (Z.eqb_neq p 0) Hp0) in HHB.
set (FP := ablocks_fp [(p - 16, k + 16)]).
assert (Hrq : forall x, 0 <= x -> req_size (x + 16) = x + 16)
  by (intros x Hx; unfold req_size; destruct (Z.eqb_spec (x + 16) 0); lia).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran p k most own HL HinL) as (Hk0 & Hab & Hhp & Hp16 & Hhd).
change (@cf_head CfParams_preset) with 16 in Hab, Hhp, Hhd.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (k + 16) (conj HAR HXS) Hab)
  as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
rewrite Hrq in Hbceil, Happ, Hbpres by lia.
pose proof (ra_blk_off_img ly S Hp W mem md (p - 16) (k + 16) (conj HAR HXS) Hab) as Hoff. rewrite Hrq in Hoff by lia.
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HL) as (Rl & Rp & Rc & Rf & Rr).
pose proof (PRH_Base.prh_ledger_most B ly S Hp W mem Lam peak cnt fail ran most own HL) as [HMm Rm].
pose proof (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt fail ran most own HL) as HOw.
set (live := Ledger.lsum Lam) in *.
assert (HkL : k <= live).
{ pose proof (prh_ledger_sizes B ly S Hp W mem Lam peak cnt fail ran most own HL) as Hsz.
  apply in_split in HinL as (l1 & l2 & EL). subst live. rewrite EL in Hsz |- *. rewrite prh_lsum_split.
  apply Forall_app in Hsz as [H1 H2]. inversion H2 as [|? ? _ H3]; subst.
  pose proof (prh_lsum_nonneg (l1 ++ l2) (proj2 (Forall_app _ _ _) (conj H1 H3))). lia. }
assert (HG : ra_glob W mem cnt fail live peak ran most).
{ unfold ra_glob. rewrite <- Pc, <- Pf, <- Pl, <- Pp, <- Pr, <- Pm.
  rewrite <- Gc at 1. rewrite <- Gf at 1. rewrite <- Gl at 1. rewrite <- Gp at 1. rewrite <- Gr at 1. rewrite <- Gm at 1.
  refine (conj (prh_ledger_count B ly S Hp W mem Lam peak cnt fail ran most own HL)
         (conj (prh_ledger_fail B ly S Hp W mem Lam peak cnt fail ran most own HL)
         (conj (prh_ledger_live B ly S Hp W mem Lam peak cnt fail ran most own HL)
         (conj (prh_ledger_peak B ly S Hp W mem Lam peak cnt fail ran most own HL)
         (conj (prh_ledger_ran B ly S Hp W mem Lam peak cnt fail ran most own HL)
         (conj HMm _)))))). lia. }
pose proof (ra_cut_entry 16480 ly S Hp W regs mem md ch p k cnt fail live peak ran most FP HPRE ltac:(lia)
  H10 Hab Hk0 Hhd HG) as HC.
(* the heap bytes the walk keeps: the old user bytes, every other harness head *)
assert (HXno : forall i, 0 <= i < k + 16 -> ~ (shadow_addr (p - 16) <= p - 16 + i < shadow_addr (p - 16) + 2)).
{ intros i Hi. apply (ra_not_shadow (p - 16) (k + 16)); [exact Happ | lia | lia | right; left; lia]. }
assert (HFP : forall i, 0 <= i < k + 16 -> inFP FP (p - 16 + i)).
{ intros i Hi. exists (p - 16, p - 16 + req_size (k + 16)). split; [left; reflexivity | rewrite Hrq by lia; cbn; lia]. }
assert (Hcl : ~ YI16.sink_open_fp FP).
{ apply sink_closed_ablocks_fp. constructor; [cbn; lia | constructor]. }
apply (ra_seg_count 16480 FP ly S Hp W regs mem md _ _ _ k cnt fail live peak ran most _ ltac:(lia) Hlo Rc Rf HC).
- (* ===== CHOSEN-FAIL ===== *)
  intros Hcf ms1 mdc1 HC1.
  apply (ra_seg_fail 16480 FP ly S Hp W regs mem md _ _ _ k cnt fail live peak ran most _ ltac:(lia) Hlo HC1).
  intros ms2 mdc2 HC2.
  apply (ra_arm_fail 16480 FP ly S Hp W regs mem md _ _ _ k cnt fail live peak ran most _ ltac:(lia)
    Rc Rf ltac:(lia) ltac:(lia) Rr Rm ltac:(lia) HC2).
  intros regs' mem' md' R1 HP' R10 Mc Mf Ml Mp Mr HJ'0 HPM' KP'.
  (* the path end: the arm's wle journal lifted to wle', back to the primed post *)
  assert (HJ' : ajournal_xR (SK := SK) SEGS B PST ARcfx RRZ 16480 (spZ regs) FP ly S Hp W mem md [] ly S Hp W mem' md' 0)
    by (unfold ajournal_xR; eapply ajournal_xwR_mono; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HJ'0]).
  destruct (ra_own_most_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' Hcl) as [KO KM].
  apply (YSRrG.SRr'_ret SEGS YGcfRehidePost.RZ_cf). cbv beta.
  exists ly, S, Hp, regs', mem', md', 0.
  split; [rewrite R1, Hra; reflexivity|].
  split; [exact (ra_journal_pst_mono PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PST_sub HJ')|].
  split; [exact HP'|].
  split; [|exact HPM'].
  assert (KEEP : forall a, 4096 <= a < alloc_ceiling -> (a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a) ->
    aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) by (intros a Ha Hi; exact (KP' a Ha Hi (fun H => H))).
  exists 0. split; [exact R10|]. split; [exact HRL|].
  (* the hull use: the chosen failure makes no allocator call, the state is the entry's *)
  split; [exact (PresetHullBudget.hull_used_refl S _)|].
  split; [intros _ sm x os i H0 hist Hpos _; exists hist; cbn [length]; rewrite Nat.add_0_r; exact Hpos|].
  split; [intros H; exfalso; exact (H eq_refl)|]. split; [intros H; exfalso; exact (H eq_refl)|].
  (* THE OUTCOME: p <> 0, and the injected failure is this call's (cnt = fail), so the clause's cnt <> fail is false *)
  split; [intros Hp00; exfalso; exact (Hp0 Hp00)|].
  split; [intros _ sm x os i H0 hist _ _ _ Hcnf; exfalso; exact (Hcnf Hcf)|].
  right; left. split; [exact Hp0|]. split; [exact Hcf|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold bytes_at in *. apply (ra_garr8_keep (mrestrict (w_H W) mem)); [exact Hold|].
    intros j Hj. apply (YCbq.mbyte_of_aview SEGS). rewrite <- Hlen in Hk0.
    apply KEEP; [lia | unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia]. }
  apply (prh_ledger_frame B ly S Hp W mem ly S Hp W _ Lam peak cnt fail ran peak _ _ _ most own HL).
  + apply (prh_glob_final_le W mem W mem' live peak cnt fail ran live ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own
      (prh_ledger_glob B ly S Hp W mem Lam peak cnt fail ran most own HL)); rewrite ?Pc, ?Pf, ?Pl, ?Pp, ?Pr, ?Gc, ?Gf, ?Gl, ?Gp, ?Gr.
    * exact Ml.
    * lia.
    * exact Mp.
    * exact Mc.
    * pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64) ltac:(lia)). lia.
    * unfold SIZE_MAXZ. exact Mf.
    * unfold SIZE_MAXZ. lia.
    * exact Mr.
    * exact Rr.
    * exact (KM most (conj HMm Rm)).
    * exact (KO own HOw).
  + intros a ka i Hin Hi. apply (YCbq.mbyte_of_aview SEGS).
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL Hin) as (Hka & Haba & _).
    change (@cf_head CfParams_preset) with 16 in Haba |- *.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a - 16) (ka + 16) (conj HAR HXS) Haba) as (_ & Ha4096 & Hac & _).
    pose proof (ra_blk_off_img ly S Hp W mem md _ _ (conj HAR HXS) Haba) as Hoa. rewrite Hrq in Hac, Hoa by lia.
    apply KEEP; [lia | unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia].
  + intros a ka _ H. exact H.
  + apply Permutation_refl.
- (* ===== g_count <> g_fail_at: disown, then the realloc call ===== *)
  intros Hcf ms1 mdc1 HC1.
  (* the live-bytes premise is owed only where the allocator is called (the text's `cnt <> fail ->` guard) *)
  specialize (Hlive Hcf).
  destruct (prh_live_room B ly S Hp W mem Lam peak cnt fail ran n most own HL (prh_ablocks_nonneg_cf B ly S Hp W mem md HAR) Hlive)
    as [Hlr1 Hlr2].
  change (@cf_head CfParams_preset) with 16 in Hlr1. fold live in Hlr1, Hlr2.
  assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
  apply (ra_seg_toobig 16480 FP ly S Hp W regs mem md _ _ _ k n cnt fail live peak ran most _ ltac:(lia) Hlo H11 Hn0
    ltac:(lia) HC1). intros ms2 mdc2 HC2.
  apply (ra_seg_unp_args 16480 FP ly S Hp W regs mem md _ _ _ k cnt fail live peak ran most _ ltac:(lia) Hlo HC2).
  intros ms3 mdc3 HC3.
  apply (ra_seg_unpoison 16480 FP ly S Hp W regs mem md _ _ _ p k cnt fail live peak ran most _ ra_AUNPOISONx
    ltac:(lia) Hlo Hgp Htp H10 Hhp Hab Hk0 HC3). intros ms4 mdc4 HC4.
  apply (ra_seg_head 16480 FP ly S Hp W regs mem md _ _ _ k cnt fail live peak ran most _ _ ltac:(lia) Hlo HC4).
  intros ms5 mdc5 HC5.
  apply (ra_seg_live 16480 FP ly S Hp W regs mem md _ _ _ k cnt fail live peak ran most _ _ ltac:(lia) Hlo HC5).
  intros ms6 mdc6 HC6.
  pose proof (YGcfRoomLive.room_live_room_k S HRL) as HRK.
  (* the call's admission and the admission at entry, from the primed text's hull budget (PresetHullPay) *)
  pose proof (PresetHullPay.hull_adm_of_budget_re S (k + 16) (n + 16) HHB) as HADM.
  assert (HQM : QM_cf S) by exact (QM_cf_of_room SEGS B ly S Hp W mem md HAR HQT (YGcfRoomLive.room_live_room S HRL)
    (PresetHullPay.hull_ok_of_budget S _ HHB)).
  assert (HROOM : ROOM_cf_k S (RK_realloc + 0)) by (rewrite Nat.add_0_r; exact HRK).
  pose proof (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ HAR) as HUNI.
  (* the room invariant across the realloc's model path (YGcfRoomLive.room_live_realloc_keep) *)
  assert (HRLK : forall pq q trc S2, In (call_trace ly cf_pc_realloc_ra0 (ms_regs ms6) []) (as_universe B) ->
    apath (ReallocP.realloc_tree_with malloc_cf free_cf pq (n + 16) (call_trace ly cf_pc_realloc_ra0 (ms_regs ms6) []) S)
      trc (q, S2) -> YGcfRoomLive.room_live_cf S2).
  { intros pq q trc S2 Htr Hpath.
    eapply (YGcfRoomLive.room_live_realloc_keep (cp := CfParams_preset) (as_universe B)
      (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) pq (n + 16) _ S trc q S2
      HUNI (admits_fix _ _ _ HUNI Htr)).
    - lia.
    - exact Hlive.
    - exact (amc_wf _ _ _ _ _ (proj1 HAR)).
    - exact HQT.
    - split; [exact Hsec | vm_compute; reflexivity].
    - split; [lia | vm_compute; first [reflexivity | discriminate]].
    - lia.
    - exact HRL.
    - exact Hpath. }
  (* the realloc call: the plain segments' continuation is the primed post (the entry lift), so SRr_ret, then the
     call and its arms in SRr' *)
  apply SRr_ret. cbv beta.
  eapply (ra_seg_realloc 16480 FP ly S Hp W regs mem md _ _ _ p k n cnt fail live peak ran most _ AREAL_cf
    ltac:(lia) Hlo Hgp Htp H10 H11 Hab Hk0 Hn0 Hnmax Hlive HQM HROOM HADM (ra_aro_entry W mem HRO) Hcl HU0
    ltac:(rewrite ra_trace_eq, <- ra_ret_realloc; exact HU1) HFP
    ?[HXo] HC6).
  [HXo]: { intros i Hi [H|H]; [exact H | exact (HXno i Hi H)]. }
  + (* ===== REFUSED: the realloc returned NULL ===== *)
    intros W2 ly2 S2 regs2 mem2 md2 raw Hwle (HPREr & Htrr & pq & q & Hpq & Hpin & Hqres & Hqiff & (trc & Hpath & Hgf) & Hleaf)
      Eab2 Ebl2 Efr2 Herr Hmt Hcopy ms7 mdc7 HC7.
    assert (Hq0 : q = PNull) by (apply Hqiff; reflexivity). subst q.
    pose proof HC7 as (E7 & _ & _ & _ & _ & _ & HJ7 & _). pose proof (ajxR_ar HJ7) as HAR7.
    assert (Hab2 : In (p - 16, k + 16) (ablocks B ly2 S2)) by (rewrite Eab2; exact Hab).
    assert (HHPr : forall h, In h (remove Z.eq_dec (p - 16) Hp) -> ~ (p - 16 <= h < p + k)).
    { intros h Hh. apply in_remove in Hh as [Hh Hne]. replace (p + k) with (p - 16 + (k + 16)) by lia.
      apply (ra_heads_apart ly S Hp W mem Lam peak cnt fail ran most own ly2 S2 _ W2 _ _ (p - 16) (k + 16) (p - 16) HAR7 HL Hab2);
        [| exact Hh | exact Hne].
      intros a ka Hak Hax. split; [intros E; injection E as E1 _; lia|].
      rewrite Eab2. destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL Hak) as (_ & Hb & _).
      change (@cf_head CfParams_preset) with 16 in Hb. exact Hb. }
    apply (ra_arm_refused 16480 FP ly S Hp W regs mem md ly2 S2 W2 _ mem2 ms7 mdc7 _ p k n cnt fail live peak ran most
      ra_APOISONx ltac:(lia) Hlo Hgp Htp H10 H11 Hab2 Hk0 HFP HHPr Rc Rf ltac:(lia) ltac:(lia) Rr Rm Hn0 ltac:(lia) HC7).
    intros regs' mem' md' (R1 & HP' & R10 & Mc & Mf & Ml & Mp & Mr & Mm & Mh) HJ' HPM' KL'.
    destruct (ra_own_most_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' Hcl) as [KO KM].
    exists ly2, S2, ((p - 16) :: remove Z.eq_dec (p - 16) Hp), regs', mem', md', (0 + (st_nev S2 - st_nev S)).
    split; [rewrite R1, Hra; reflexivity|].
    split; [exact (ra_journal_pst_mono PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PST_sub HJ')|].
    split; [exact HP'|].
    split; [|exact HPM'].
    exists 0. split; [exact R10|]. split; [exact (HRLK pq PNull trc S2 Htrr Hpath)|].
    (* the hull use: the realloc step's secs post (A14) *)
    split; [exact (PresetHullBudget.hull_used_of_call_re (k + 16) (n + 16) S PNull S2
      (YGcfSecsStep.secs_realloc_step pq (n + 16) _ S trc (PNull, S2) Hpath))|].
    split.
    { intros _ sm x os i H0 hist Hpos _. exists hist. cbn [length]. rewrite Nat.add_0_r.
      exact (PresetRoomPosKeep.room_pos_keep_realloc_null SEGS B ly S (remove Z.eq_dec (p - 16) Hp) W
        (ms_regs ms6) (ms_mem ms6) mdc6 [] sm x os i H0 hist pq (n + 16) _ trc S2
        (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREr) ltac:(lia) Hlive Htrr Hpath Hpos). }
    split; [intros H; exfalso; exact (H eq_refl)|]. split; [intros H; exfalso; exact (H eq_refl)|].
    (* THE OUTCOME: p <> 0; at a consumer allocation of the run whose next event is this call's HRe (k + 16) (n + 16),
       with the position at the call's state S, the realloc's NULL (its witness Hmt, both steps on granted paths: the kit's
       machine-level refusal prh_granted_null) is impossible (PRH_Refute.prh_refute_at), so this arm does not arise
       there *)
    split; [intros Hp00; exfalso; exact (Hp0 Hp00)|].
    split.
    { intros _ sm x os i H0 hist Hpos Hrun Hcons _. exfalso.
      apply PRH_Base.prh_run_at_one in Hrun.
      exact (PRH_Refute.prh_refute_at _ sm x os i (length [PresetReqAt.HRe (k + 16) (n + 16)])
        (PresetReqAt.HRe (k + 16) (n + 16)) H0 hist S Hcons (Nat.lt_0_succ 0) Hrun eq_refl Hpos (amc_wf _ _ _ _ _ (proj1 HAR))
        (or_intror (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ Hmt))))). }
    right; right; left.
    split; [exact Hp0|]. split; [exact Hcf|]. split; [reflexivity|].
    (* the ledger: refused (n) at g_live - k, then own (b, old) restores g_live (S1Ledger's prh_ledger_reown) *)
    pose proof (KM most (conj HMm Rm)) as KM'. pose proof (KO own HOw) as KO'.
    assert (HG' : prh_glob (L := A_prog_listing) (PA := PA) W2 mem' (Ledger.lsum Lam)
      (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam - k + n))) ((cnt + 1) mod 2 ^ 64) fail (if n <=? most then 1 else ran)
      most own).
    { fold live. replace (Z.min SIZE_MAXZ (live - k + n)) with (live - k + n) by (unfold SIZE_MAXZ; lia).
      unfold prh_glob. rewrite Pl, Pp, Pc, Pf, Pr, Gl, Gp, Gc, Gf, Gr.
      pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64) ltac:(lia)).
      repeat match goal with |- _ /\ _ => split end; try assumption; try lia; destruct (n <=? most); lia. }
    destruct (prh_ledger_reown B ly S Hp W mem ly2 S2 ((p - 16) :: remove Z.eq_dec (p - 16) Hp) W2 mem' Lam p k peak cnt fail ran _ _ _ _ most own HL HinL HG') as [Hperm HL'].
    { intros a ka i Hak Hap Hi. apply (YCbq.mbyte_of_aview SEGS).
      destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL Hak) as (Hka & Hb & _).
      change (@cf_head CfParams_preset) with 16 in Hb |- *.
      replace (a - 16 + i) with ((a - 16) + i) by lia.
      apply (ra_journal_blk _ _ ly S Hp W mem md ly2 S2 _ W2 mem' md' _ (p - 16) (k + 16) (a - 16) (ka + 16) i HJ'
        (conj HAR HXS) Hab Hb ltac:(rewrite Eab2; exact Hb)); [intros E; injection E as E1 _; lia | rewrite Hrq by lia; lia]. }
    { change (@cf_head CfParams_preset) with 16. exact Mh. }
    { intros a ka _ Hb. rewrite Eab2. exact Hb. }
    { reflexivity. }
    split; [exact Hperm|]. split; [rewrite Eab2; reflexivity|].
    split.
    { unfold bytes_at in *. apply (ra_garr8_keep (mrestrict (w_H W) mem)); [exact Hold|].
      intros j Hj. apply (YCbq.mbyte_of_aview SEGS). rewrite <- Hlen in Hk0.
      rewrite (KL' (p + Z.of_nat j)); [exact (Hcopy (Z.of_nat j) ltac:(lia)) |].
      apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
    split.
    { (* the primed text's WORLD-FREE refusal state, from the refusal witness (realloc_cf_refused_state,
         YGcfRealloc.v) at the call state's shape *)
      exact (realloc_cf_refused_state (n + 16) _ S S2
        (YGcfPath.shape_cf_of_WfP_cf (as_universe B) 0 0 0 S (amc_wf _ _ _ _ _ (proj1 HAR))) Hmt). }
    split.
    { intros kk Hkk. rewrite (KL' (as_errno B + Z.of_nat kk)); [exact (Herr kk Hkk) |].
      apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
    exact HL'.
  + (* ===== SUCCESS: the realloc returned a new block nb ===== *)
    intros W2 ly2 S2 regs2 mem2 md2 raw nb Hwle (HPREr & Htrr & pq & q & Hpq & Hpin & Hqres & Hqiff & (trc & Hpath & Hgf) & Hleaf)
      Hnb4 Hnb16 Efr2 (b1 & b2 & Eb1 & Eb2) Hcopy ms7 mdc7 HC7.
    pose proof HC7 as (E7 & _ & _ & _ & _ & _ & HJ7 & _). pose proof (ajxR_ar HJ7) as HAR7.
    assert (Hin2 : In (nb, n + 16) (ablocks B ly2 S2))
      by (rewrite Eb2; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    destruct (alx_blocks _ _ _ LAWS ly2 S2 _ W2 _ _ nb (n + 16) HAR7 Hin2) as (_ & _ & _ & _ & _ & Hpw2).
    (* the new block is not one of the blocks the realloc left alone *)
    assert (Hfresh : ~ In (nb, n + 16) (b1 ++ b2)).
    { intros Hx. rewrite Eb2, app_assoc, map_app in Hpw2. cbn [map] in Hpw2.
      pose proof (prh_pw_last zdisjoint _ _ Hpw2 _ (in_map (fun x => (fst x, req_size (snd x))) _ _ Hx)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd by lia. lia. }
    apply in_split in HinL as (l1 & l2 & EL).
    assert (HNDL : NoDup (map fst Lam)) by exact (prh_ledger_nodup B ly S Hp W mem Lam peak cnt fail ran most own HL).
    rewrite EL in HNDL.
    assert (Hrest : forall a ka, In (a, ka) (l1 ++ l2) -> a <> p).
    { intros a ka Hak Hap. subst a. apply (prh_lam_rest_notin l1 l2 p k HNDL).
      apply in_map_iff. exists (p, ka). split; [reflexivity | exact Hak]. }
    assert (Hold2 : forall a ka, In (a, ka) Lam -> a <> p -> In (a - 16, ka + 16) (b1 ++ b2)).
    { intros a ka Hak Hap. destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL Hak) as (_ & Hb & _).
      change (@cf_head CfParams_preset) with 16 in Hb. rewrite Eb1 in Hb.
      apply in_app_or in Hb as [Hb|[Hb|Hb]]; [apply in_or_app; left; exact Hb | injection Hb as E1 _; lia
      | apply in_or_app; right; exact Hb]. }
    assert (Hkept2 : forall x, In x (b1 ++ b2) -> In x (ablocks B ly2 S2)).
    { intros x Hx. rewrite Eb2, app_assoc. apply in_or_app. left. exact Hx. }
    assert (HHPs : forall h, In h (remove Z.eq_dec (p - 16) (remove Z.eq_dec (p - 16) Hp)) -> ~ (nb <= h < nb + n + 16)).
    { intros h Hh. apply in_remove in Hh as [Hh _]. apply in_remove in Hh as [Hh Hne].
      replace (nb + n + 16) with (nb + (n + 16)) by lia.
      apply (ra_heads_apart ly S Hp W mem Lam peak cnt fail ran most own ly2 S2 _ W2 _ _ nb (n + 16) (p - 16) HAR7 HL Hin2);
        [| exact Hh | exact Hne].
      intros a ka Hak Hax. assert (Hap : a <> p) by lia. pose proof (Hold2 a ka Hak Hap) as Hx.
      split; [intros E; rewrite E in Hx; exact (Hfresh Hx) | exact (Hkept2 _ Hx)]. }
    assert (HNEW : ~ In (nb, n + 16) (ablocks B ly S) \/ (forall i, 0 <= i < n + 16 -> inFP FP (nb + i))).
    { destruct (decide ((nb, n + 16) = (p - 16, k + 16))) as [E|E].
      - right. injection E as E1 E2. intros i Hi. exists (p - 16, p - 16 + req_size (k + 16)).
        split; [left; reflexivity | rewrite Hrq by lia; cbn; lia].
      - left. rewrite Eb1. intros Hx. apply in_app_or in Hx as [Hx|[Hx|Hx]];
          [apply Hfresh; apply in_or_app; left; exact Hx | exact (E (eq_sym Hx)) | apply Hfresh; apply in_or_app; right; exact Hx]. }
    rewrite <- EL in HNDL.
    apply (ra_arm_success 16480 FP ly S Hp W regs mem md ly2 S2 W2 _ mem2 ms7 mdc7 _ k n cnt fail live peak ran most nb _
      ra_APOISONx ltac:(lia) Hlo Hgp Htp H11 Hin2 Hn0 Hnb4 Hnb16 HNEW HHPs Rc Rf ltac:(lia) ltac:(lia) ltac:(lia) Rr Rm
      ltac:(lia) HC7).
    intros regs' mem' md' (R1 & HP' & R10 & Mc & Mf & Ml & Mp & Mr & Mm & Mh) HJ' HPM' KL'.
    destruct (ra_own_most_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' Hcl) as [KO KM].
    rewrite prh_remove_idem in HJ'.
    exists ly2, S2, (nb :: remove Z.eq_dec (p - 16) Hp), regs', mem', md', (0 + (st_nev S2 - st_nev S)).
    split; [rewrite R1, Hra; reflexivity|].
    split; [exact (ra_journal_pst_mono PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PST_sub HJ')|].
    split; [exact HP'|].
    split; [|exact HPM'].
    assert (Hqn : q <> PNull) by (intros Hq; apply Hqiff in Hq; lia).
    (* the position after the grant HRe (k + 16) (n + 16) (PresetRoomPosKeep.room_pos_keep_realloc): the transfer arm and the
       outcome clause both state it *)
    assert (HPOS : forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i [PresetReqAt.HRe (k + 16) (n + 16)] ->
      exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HRe (k + 16) (n + 16)])%nat H0 hist' S2).
    { intros sm x os i H0 hist Hpos Hrun. apply PRH_Base.prh_run_at_one in Hrun.
      assert (Hpqn : pq <> PNull) by (intros ->; cbn in Hpq; lia).
      cbn [length]. rewrite Nat.add_1_r.
      eapply (PresetRoomPosKeep.room_pos_keep_realloc SEGS B ly S (remove Z.eq_dec (p - 16) Hp) W
        (ms_regs ms6) (ms_mem ms6) mdc6 [] sm x os i H0 hist pq (k + 16) (n + 16) _ trc q S2
        (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREr) HRK); [lia | exact Hlive | exact (admits_fix _ _ S HUNI Htrr)
        | exact Hpin | exact Hpqn | exact Hpath | exact Hqn | exact Hpos | exact Hrun]. }
    exists (nb + 16). split; [exact R10|]. split; [exact (HRLK pq q trc S2 Htrr Hpath)|].
    (* the hull use: the realloc step's secs post (A14) *)
    split; [exact (PresetHullBudget.hull_used_of_call_re (k + 16) (n + 16) S q S2
      (YGcfSecsStep.secs_realloc_step pq (n + 16) _ S trc (q, S2) Hpath))|].
    split; [intros H; exfalso; lia|]. split; [intros _ H; exfalso; exact (Hp0 H)|].
    split; [intros _ _; exact HPOS|].
    (* THE OUTCOME: p <> 0 and the instance granted (res = nb + 16 >= 4096 + 16), at the position after HRe *)
    split; [intros Hp00; exfalso; exact (Hp0 Hp00)|].
    split; [intros _ sm x os i H0 hist Hpos Hrun _ _; split; [lia | exact (HPOS sm x os i H0 hist Hpos Hrun)]|].
    right; right; right.
    split; [exact Hp0|]. split; [exact Hcf|]. split; [lia|]. split; [rewrite Z.add_mod by lia; rewrite Hnb16; reflexivity|].
    replace (nb + 16 - 16) with nb by lia.
    assert (HLB : prh_lblocks B ly S Hp W mem (l1 ++ (p, k) :: l2)) by (rewrite <- EL; exact (proj2 (proj1 (prh_ledger_iff B _ _ _ _ _ _ _ _ _ _ _ _) HL))).
    assert (Hfr : ~ In (nb + 16) (map fst (l1 ++ l2))).
    { change (@cf_head CfParams_preset) with 16 in *.
      exact (prh_fresh_realloc_app B ly S Hp W mem ly2 S2 l1 l2 p k nb n b1 b2 HLB Hn0 Eb1 Eb2 Hpw2). }
    exists l1, l2. split; [exact EL|]. split; [exact Hfr|]. split; [reflexivity|].
    split.
    { exists b1, b2. split; [exact Eb1|]. split; [exact Hfresh|].
      rewrite Eb2, app_assoc. apply Permutation_sym, Permutation_cons_append. }
    pose proof (ajxR_ar HJ') as HAR8.
    destruct (alx_blocks _ _ _ LAWS ly2 S2 _ W2 mem' md' nb (n + 16) HAR8 Hin2) as (_ & _ & _ & _ & Hbpres8 & _).
    rewrite Hrq in Hbpres8 by lia.
    destruct (alx_hshadow _ _ _ LAWS ly2 S2 _ W2 mem' md' nb (n + 16) HAR8 Hin2 ltac:(left; reflexivity)) as [Hbs Hhv].
    change (@cf_head CfParams_preset) with 16 in Hbs, Hhv. rewrite Hrq in Hbs, Hhv by lia.
    replace (n + 16 - 16) with n in Hbs, Hhv by lia.
    split.
    { unfold bytes_at in *.
      apply (ra_bytes_success (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem') p (nb + 16) old k n Hold Hlen Hk0 Hn0).
      - intros i Hi. apply ra_mbyte_of_aview2. rewrite (KL' (nb + 16 + i)).
        + exact (Hcopy i Hi).
        + apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      - intros i Hi. assert (Hai : nb <= nb + 16 + i < nb + (n + 16)) by lia.
        destruct (Hbpres8 (nb + 16 + i) Hai) as [[Hh [bb Hb]] _]. exists bb.
        unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
    split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
    split; [intros Hn; apply Hhv; lia|].
    (* the ledger: (p, k) leaves, (nb + 16, n) joins (S1Ledger's prh_ledger_move) *)
    rewrite EL in HL.
    assert (Hlsum : Ledger.lsum (l1 ++ l2) + n = live - k + n) by (subst live; rewrite EL, prh_lsum_split; lia).
    apply (prh_ledger_move B ly S Hp W mem ly2 S2 _ W2 mem' l1 l2 p k nb n peak cnt fail ran _ _ _ _ most own HL).
    * rewrite Hlsum.
      apply (prh_glob_final W mem W2 mem' (live) peak cnt fail ran (live - k + n) ((cnt + 1) mod 2 ^ 64) fail ran most own);
        [rewrite <- EL in HL; subst live; exact (prh_ledger_glob B ly S Hp W mem Lam peak cnt fail ran most own HL) | | | | | | | | | | | ];
        rewrite ?Pl, ?Pp, ?Pc, ?Pf, ?Pr, ?Gl, ?Gp, ?Gc, ?Gf, ?Gr;
        first [assumption | exact (KM most (conj HMm Rm)) | exact (KO own HOw) | lia
              | pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64) ltac:(lia)); lia].
    * intros a ka i Hak Hi. apply (YCbq.mbyte_of_aview SEGS).
      rewrite <- EL in HL.
      assert (HakL : In (a, ka) Lam) by (rewrite EL; apply in_app_or in Hak as [H|H]; apply in_or_app; [left | right; right]; exact H).
      destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL HakL) as (Hka & Hb & _).
      change (@cf_head CfParams_preset) with 16 in Hb |- *.
      pose proof (Hold2 a ka HakL (Hrest a ka Hak)) as Hx.
      apply (ra_journal_blk _ _ ly S Hp W mem md ly2 S2 _ W2 mem' md' _ (p - 16) (k + 16) (a - 16) (ka + 16) i HJ'
        (conj HAR HXS) Hab Hb (Hkept2 _ Hx)); [intros E; injection E as E1 _; exact (Hrest a ka Hak ltac:(lia)) | rewrite Hrq by lia; lia].
    * intros a ka Hak Hb. change (@cf_head CfParams_preset) with 16 in *.
      exact (prh_blocks_kept_realloc B ly S ly2 S2 b1 b2 p k (nb, n + 16) a ka Eb1 Eb2 (Hrest a ka Hak) Hb).
    * exact Hn0.
    * change (@cf_head CfParams_preset) with 16. exact Hin2.
    * change (@cf_head CfParams_preset) with 16. rewrite Z.add_mod by lia. rewrite Hnb16. reflexivity.
    * exact Mh.
    * change (@cf_head CfParams_preset) with 16. exact Hfr.
    * reflexivity.
Qed.

End top.
End f.
End d.
