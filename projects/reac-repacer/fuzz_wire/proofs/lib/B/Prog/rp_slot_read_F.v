(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: the footprint walk of reac-repacer/fuzz_uci's rp_hot_clamp in image A, against the frozen
   lib/A/Prog/rp_hot_clamp_F_c.v rp_hot_clamp_contract_F. It follows lib/Prog/rp_hot_clamp.v (the plain walk: one
   continuation-style lemma per field; its f_pf .. f_sv, model_split, f_mn_range, sx32_int and lts_lit / ltu_lit reused
   by name, its mcase / br / join tactics copied, join extended to the walk's invariant) in the footprint style of
   proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F.v and reac_decode_F.v (origin/ossv/recipes 88154566652a:
   StepF's step, one rng fact per access; rd_all, addr_four, lts_sm and the one-byte shadow window copied from that
   unit's ReacDecodeLib.v and reac_decode_F.v; rw_cells_app from lib/Prog/check_clamp.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/rp_hot_clamp_FW.v, with its module paths and numbers changed; 606 of its 675 lines of code are new or changed and 473 lines of the source are left out. *)
(* rp_slot_read_F: the footprint walk of rp_slot_read in image B (fuzz_wire.asan-ubsan, entry 0x815ec, 0x250 bytes),
   against the frozen lib/B/Prog/rp_slot_read_F_c.v rp_slot_read_F_holds_stmt: the callee rp_slot_width is taken by
   its footprint contract rp_slot_width_contract_F (lib/B/Prog/rp_slot_width_F_c.v), the statement's premise.
   The segment split and the loop invariant are those of the plain walk lib/Prog/rp_slot_read.v, whose pure lemmas
   (braid_pos_lin, out_pref, sample_val, sw_geom, ...) are used from there by name; the UBSan checks of the loop are
   refuted as in the released lib/U/Prog/rp_slot_read.v; the call into a footprint callee after the register saves
   follows libreac/fuzz_decode's released lib/B/Prog/reac_decode_F.v.
   The code:
     +0x00 .. +0x24  the frame [sp - 96, sp): ra, s0 .. s7 saved at sp' + 0x58 .. sp' + 0x18 (sp' = sp - 96); the
                     first 24 bytes are the braid offsets pos[0..2];
     +0x28 .. +0x40  s0 := v, s1 := slot, s3 := the shadow base (the GOT word 0x98878, then the cell 0xa07f8),
                     s2 := f, a2 := slot;
     +0x44           `jal rp_slot_width` (0x8151c), taken by its contract on [sp - 128, sp - 96);
     +0x48           `bltz a0` to +0x204 (a0 := 0, epilogue) when the width is negative;
     +0x4c / +0x54   the UBSan checks of f (NULL, f + 50 wrapping), refuted by f <> 0 and f + 51 <= 2^64;
     +0x58 .. +0x98  the loop's fixed registers (t5 = ~(f + 50), t6 = (v <> 0) && v aligned, s4 = a1 = v);
     +0x9c .. +0x11c the braid offsets of sample s: pos[0] and pos[1] stored at +0xcc / +0xd4 (+0xe8 / +0xf4 for an
                     odd slot), pos[2] at +0x108, all three read back (+0x100 .. +0x118), with the UBSan checks of
                     the arithmetic, of the pos[] slot addresses and of f + 50 + pos[k];
     +0x120 .. +0x160 the three braid bytes, each behind its shadow byte; the slow paths (+0x1c4 .. +0x1e4) fall back
                     into the loop, since the byte is addressable, so no __asan_report_load1 is reached;
     +0x164 .. +0x174 the UBSan checks of v + 4 s;
     +0x178 .. +0x188 the shadow byte of v + 4 s; its slow path (+0x1e8 .. +0x1f0) is taken back, since the four
                     bytes are addressable, so __asan_report_store4 is not reached;
     +0x18c .. +0x1bc the sample, `sw` into v[s], the loop test; +0x1fc a0 := 1; +0x208 .. +0x230 the epilogue.
   The frame lies in application memory, the shadow bytes do not, so the frame and v stores leave the shadow bytes of
   f's and v's ranges unchanged (addr_munch). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_clean_len_c
  rp_frame_channels_c rp_slot_width_F_c rp_slot_read_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c rp_slot_read_c rp_slot_read.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read.

(* ---- shadow and window facts (libreac/fuzz_decode lib/B/Prog/ReacDecodeLib.v) ---- *)

Lemma rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma lts_sm : forall (x : Z) (k : byte), 0 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma app_win : forall s d x, 0 < d <= 2^32 -> app_mem (s - d) -> app_mem (s - 1) -> s - d <= x < s -> app_mem x.
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros s d x Hd H1 H2 Hx. lia. Qed.

Lemma shadow_not_app : forall a, app_mem a -> ~ app_mem (a / 8 + ASAN_K).
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_range : forall a, app_mem a -> 0 <= a / 8 + ASAN_K < 2^64.
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha. Z.div_mod_to_equations. lia.
Qed.

Lemma mrd_munch : forall W m m' a, munch W m m' -> 0 <= a < 2^64 -> outside W a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof.
  intros W m m' a MU Ha Ho. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W ((p + i) / 8 + ASAN_K)) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & H1 & H2 & H) MU D.
  split; [exact H0 | split; [exact H1 | split; [exact H2 | ]]].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  unfold shadow_addr in *. rewrite (mrd_munch W m m' _ MU (shadow_range _ Ha) (D i Hi)). exact Hb.
Qed.

(* The 19 runtime cells of this image's AsanCells.asan_cells lie in [GOT_CELL_K, MIDEND + 8). *)
Lemma asan_cells_munch : forall m m' lo hi, asan_cells m -> munch [(lo, hi)] m m' ->
  MIDEND + 8 <= lo \/ hi <= GOT_CELL_K -> asan_cells m'.
Proof.
  unfold asan_cells.
  intros m m' lo hi
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19) MU D.
  unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND, GOT_HIEND, MIDBEG,
    GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, GOT_REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET, REAL_BCMP in *.
  repeat (match goal with |- _ /\ _ => split end);
    (eapply bytes_tp; [exact MU | | eassumption]); rewrite ?length_le8, ?length_le4; cbn [length]; lia.
Qed.

Lemma addr_one : forall m p n i, addressable m p n -> 0 <= i < n ->
  app_mem (p + i) /\ exists k, mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ (p + i) mod 8 < bv_signed k).
Proof.
  intros m p n i (H0 & H1 & H2 & H) Hi. destruct (H i Hi) as (Ha & k & Hk & Hok).
  split; [exact Ha|]. exists k. unfold shadow_addr in Hk. split; [exact Hk|].
  unfold shadow_ok in Hok. lia.
Qed.

Lemma addr_four : forall m p n a, addressable m p n -> p <= a -> a + 4 <= p + n ->
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ a mod 8 + 3 < bv_signed k).
Proof.
  intros m p n a (H0 & H1 & H2 & H) Ha Hn.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Mb.
  destruct (Z_le_gt_dec (a mod 8) 4) as [L|L].
  - destruct (H (a + 3 - p) ltac:(lia)) as (Hap & k & Hk & Hok).
    replace (p + (a + 3 - p)) with (a + 3) in Hk, Hok by lia.
    assert (E1 : (a + 3) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (a + 3) mod 8 = a mod 8 + 3) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
    exists k. split; [exact Hk | lia].
  - destruct (H (a + (7 - a mod 8) - p) ltac:(lia)) as (Hap & k & Hk & Hok).
    replace (p + (a + (7 - a mod 8) - p)) with (a + (7 - a mod 8)) in Hk, Hok by lia.
    assert (E1 : (a + (7 - a mod 8)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (a + (7 - a mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
    exists k. split; [exact Hk | lia].
Qed.

(* ---- own window facts ---- *)

(* A sub-range of an addressable range is addressable. *)
Lemma addr_sub : forall m p n o k, addressable m p n -> 0 <= o -> 0 <= k -> o + k <= n ->
  addressable m (p + o) k.
Proof.
  intros m p n o k (H0 & H1 & H2 & H) Ho Hk Hn.
  split; [lia | split; [lia | split; [lia | ]]].
  intros i Hi. replace (p + o + i) with (p + (o + i)) by lia. apply H. lia.
Qed.

(* The shadow byte of an application byte lies outside a window of application bytes. *)
Lemma sh_out1 : forall lo hi a, (forall x, lo <= x < hi -> app_mem x) -> app_mem a ->
  outside [(lo, hi)] (a / 8 + ASAN_K).
Proof.
  intros lo hi a H1 Ha. pose proof (shadow_not_app a Ha) as N. cbn [outside].
  split; [|exact I]. intros Hx. apply N, H1. exact Hx.
Qed.

Lemma sh_out2 : forall lo hi c d a, (forall x, lo <= x < hi -> app_mem x) -> (forall x, c <= x < d -> app_mem x) ->
  app_mem a -> outside [(lo, hi); (c, d)] (a / 8 + ASAN_K).
Proof.
  intros lo hi c d a H1 H2 Ha. pose proof (shadow_not_app a Ha) as N. cbn [outside].
  split; [|split; [|exact I]]; intros Hx; apply N; [apply H1 | apply H2]; exact Hx.
Qed.

Lemma addr_app : forall m p n x, addressable m p n -> p <= x < p + n -> app_mem x.
Proof.
  intros m p n x (_ & _ & _ & H) Hx. destruct (H (x - p) ltac:(lia)) as [Ha _].
  replace (p + (x - p)) with x in Ha by lia. exact Ha.
Qed.

Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. lia.
Qed.

(* ---- the shadow checks of the loop body, one lemma per check (reac_decode_F.v bc1F .. bm1F form) ---- *)

(* +0x120 .. +0x130: a2 := f + 50 + pos[1]; its shadow byte; slow path +0x1c4 .. +0x1cc. *)
Lemma bk1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x15 + bv_unsigned x12 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y12 y21 y23 : word, bv_unsigned y12 = A -> ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 x22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81720) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8170c) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RS CONT.
  pose proof (u64_range x15) as R15. pose proof (u64_range x12) as R12. unfold ASAN_K in M.
  step. gen_add x15 x12 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* +0x134 .. +0x148: a3 := f + 50 + pos[0]; its shadow byte; s5 := f[pos[1]] (`lbu` at +0x144); slow path
   +0x1d0 .. +0x1d8. *)
Lemma bk0F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x15 + bv_unsigned x13 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x12 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y12 y13 y23 : word, bv_unsigned y13 = A -> ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 (zxb b) x22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81738) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81720) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD RS RD CONT.
  pose proof (u64_range x15) as R15. pose proof (u64_range x13) as R13. unfold ASAN_K in M.
  step. gen_add x15 x13 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned x12) 1 RD ltac:(lia)) as RW.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x12 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* +0x14c .. +0x160: a2 := f + 50 + pos[2]; its shadow byte; a3 := f[pos[0]] (`lbu` at +0x15c); slow path
   +0x1dc .. +0x1e4. *)
Lemma bk2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x15 + bv_unsigned x22 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x13 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y12 y22 y23 : word, bv_unsigned y12 = A -> ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 (zxb b) x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81750) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81738) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD RS RD CONT.
  pose proof (u64_range x15) as R15. pose proof (u64_range x22) as R22. unfold ASAN_K in M.
  step. gen_add x15 x22 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned x13) 1 RD ltac:(lia)) as RW.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x13 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* +0x178 .. +0x188: the shadow byte of v + 4 s (a1); a2 := f[pos[2]] (`lb` at +0x184); slow path +0x1e8 .. +0x1f0,
   whose `blt` (a1 & 7) + 3 < k is taken back to +0x18c. *)
Lemma bstF : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x11 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  bv_unsigned x12 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y22 y23 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (sxb b) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81778) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81764) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA M SK ED MD RS RD CONT.
  pose proof (u64_range x11) as RX. unfold ASAN_K in M.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned x12) 1 RD ltac:(lia)) as RW.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x12 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, EA, (lts_sm (A mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(* ---- the loop ---- *)

(* Rewrite bv_unsigned (Z_to_bv 64 z) to z, innermost first, where lia proves z in range (lib/Prog/rp_slot_read.v). *)
Ltac rw_inner_lit :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (unsigned_lit z) by lia
      end
  end.

(* A branch whose operands are Z_to_bv literals of open Z expressions: not taken (lib/U/Prog/rp_slot_read.v). *)
Ltac cond_false :=
  symmetry; unfold bv_ltu, bv_eqb, bv_lts, bv_leu; fold_lit_ux;
  rewrite ?Z.shiftl_mul_pow2 by lia; rw_inner_lit;
  first [ apply (proj2 (Bool.negb_false_iff _));
          first [ apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.leb_le; lia ]
        | apply Z.ltb_ge; lia | apply Z.eqb_neq; lia | apply Z.leb_gt; lia ].

Ltac if_false_lit :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | cond_false]
  end.

(* bv_unsigned <reg> = <value>, with the 32-bit wraps of addiw / addw removed (lib/U/Prog/rp_slot_read.v). *)
Ltac reg_eq_tac :=
  rw_inner_lit;
  try (rewrite zb_lxor_ones by lia);
  rw_inner_lit;
  rewrite ?Z.shiftl_mul_pow2 by lia;
  try (match goal with
       | |- context [bv_swrap 32 ?z] =>
           replace (bv_swrap 32 z) with z by (symmetry; apply swrap32_id; lia)
       end);
  rw_inner_lit; lia.

Section SR.
Variables (RNG : ExecF.footprint) (ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 s8 s9 s10 s11 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
Variables (f v nch slot lo : Z).

Local Notation SP := (bv_unsigned sp).
Local Notation LEN := (Z.of_nat (length bs)).

Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hslot : 0 <= slot < nch.
Hypothesis Hlen : 52 + 36 * nch <= LEN.
Hypothesis Hf : 0 < f.
Hypothesis Hfb : f + LEN <= 2^64.
Hypothesis HDJf : f + LEN <= SP - 128 \/ SP <= f.
Hypothesis Hv : 0 < v.
Hypothesis Hv4 : v mod 4 = 0.
Hypothesis Hv48 : v + 48 <= 2^64.
Hypothesis HDJv : v + 48 <= SP - 128 \/ SP <= v.
Hypothesis HDJfv : v + 48 <= f \/ f + LEN <= v.
Hypothesis Hlo0 : 0 <= lo.
Hypothesis HSPlo : lo + 128 <= SP.
Hypothesis APW : forall x, SP - 128 <= x < SP -> app_mem x.
Hypothesis AF : addressable m f LEN.
Hypothesis AV : addressable m v 48.
Hypothesis RR : ExecF.rng RNG f LEN.
Hypothesis RSR : ExecF.rng RNG (shadow_addr f) (shadow_addr (f + LEN - 1) - shadow_addr f + 1).
Hypothesis RO : ExecF.rng RNG v 48.
Hypothesis RSO : ExecF.rng RNG (shadow_addr v) (shadow_addr (v + 48 - 1) - shadow_addr v + 1).
Hypothesis RSTK : ExecF.rng RNG (SP - 128) 128.

Definition PostOK : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' S0 S1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                  S2 S3 S4 S5 S6 S7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo SP /\
    munch [(SP - 128, SP); (v, v + 48)] m m' /\ bytes_at rsegs m' v (PSR.rp_slot_bytes bs nch slot).

Definition INVR (mk : word -> option byte) (j : nat) : Prop :=
  bytes_at rsegs mk f bs /\
  (exists junk, rw_cells rsegs mk (SP + -96)
     [CB 24 junk; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]) /\
  stk rsegs mk lo (SP + -96) /\ wr_at rsegs mk v 48 /\
  munch [(SP - 128, SP); (v, v + 48)] m mk /\ wmono rsegs m mk /\
  bytes_at rsegs mk v (PR.out_pref bs nch slot j).

Local Notation STATE pc mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 :=
  (MS (mkR (Z_to_bv 64 529972) (Z_to_bv 64 (SP + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

(* After the stores into pos[0..2]: fold the three cells before C8 S7 back into the frame's 24-byte block. *)
Ltac merge_pos :=
  lazymatch goal with
  | H : rw_cells ?segs ?mk ?A (?c0 :: ?c1 :: ?c2 :: C8 S7 :: ?post) |- _ =>
      apply (rw_cells_merge segs mk A [] [c0; c1; c2] (C8 S7 :: post)) in H;
      cbn [app cells_size csize Nat.add] in H
  end.

(* Re-pack the loop invariant for the memory the pos stores left. *)
Ltac repack_inv ss :=
  lazymatch goal with
  | HB : bytes_at rsegs ?mk f bs, FRh : rw_cells rsegs ?mk _ _, STh : stk rsegs ?mk _ _,
    HWh : wr_at rsegs ?mk v 48, MUh : munch _ _ ?mk, WMh : wmono rsegs _ ?mk,
    HOh : bytes_at rsegs ?mk v _ |- _ =>
      assert (INVn : INVR mk (Z.to_nat ss)) by
        (unfold INVR; split; [exact HB|]; split; [eexists; exact FRh|];
         split; [exact STh|]; split; [exact HWh|]; split; [exact MUh|];
         split; [exact WMh | exact HOh])
  end.

(* +0x1c0 .. +0x230: a0 := 1 and the epilogue. *)
Lemma sr_exit : forall (mk : word -> option byte) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23
                        x28 x29 x30 x31 : word),
  INVR mk 12 ->
  ExecF.evtF rsegs RNG PostOK (STATE 0x817ac mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23
                                 x28 x29 x30 x31).
Proof.
  intros mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31
    (HBB & (junk & FR) & ST & HW & MU & WM & HOUT).
  pose proof (u64_range sp) as Rsp.
  do 14 step.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold PostOK. do 15 eexists. split; [reflexivity|].
  split; [exact WM|]. split; [exact ST|]. split; [exact MU|].
  rewrite <- PR.out_pref_full. exact HOUT.
Qed.

(* +0x120 .. +0x1bc: the three braid bytes and their shadow bytes, the UBSan checks of v + 4 s, the shadow byte of
   v + 4 s, the sample and its store into v[s], the loop test. pos[0..2] are in a3, a2, s6. *)
Lemma sr_tail : forall (x6 x7 x8 x9 x10 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  bv_unsigned x6 = 18446744073709551608 -> bv_unsigned x7 = SP + -96 -> bv_unsigned x8 = v ->
  bv_unsigned x9 = slot mod 2 -> bv_unsigned x10 = nch -> bv_unsigned x15 = f + 50 ->
  bv_unsigned x16 = slot - slot mod 2 -> bv_unsigned x17 = 1 -> bv_unsigned x18 = 18446744073709551607 ->
  bv_unsigned x28 = 18446744073709551599 -> bv_unsigned x29 = 18446744073692774400 ->
  bv_unsigned x30 = 18446744073709551615 - (f + 50) -> bv_unsigned x31 = 1 ->
  forall (s : Z) (mk : word -> option byte) (x5 x11 x12 x13 x14 x20 x21 x22 x23 : word),
  0 <= s < 12 ->
  bv_unsigned x5 = 12 - s -> bv_unsigned x11 = v + 4 * s -> bv_unsigned x14 = s -> bv_unsigned x20 = v + 4 * s ->
  bv_unsigned x13 = 3 * (s * nch + (slot - slot mod 2)) + (3 + slot mod 2) ->
  bv_unsigned x12 = 3 * (s * nch + (slot - slot mod 2)) + 5 * (slot mod 2) ->
  bv_unsigned x22 = 3 * (s * nch + (slot - slot mod 2)) + (1 + slot mod 2) ->
  INVR mk (Z.to_nat s) ->
  (forall (mk' : word -> option byte) (y5 y11 y12 y13 y14 y20 y21 y22 y23 : word),
     s + 1 < 12 ->
     bv_unsigned y5 = 12 - (s + 1) -> bv_unsigned y11 = v + 4 * (s + 1) -> bv_unsigned y14 = s + 1 ->
     bv_unsigned y20 = v + 4 * (s + 1) ->
     INVR mk' (Z.to_nat (s + 1)) ->
     ExecF.evtF rsegs RNG PostOK (STATE 0x81688 mk' y5 x6 x7 x8 x9 x10 y11 y12 y13 y14 x15 x16 x17 x18 y20 y21 y22 y23
                                    x28 x29 x30 x31)) ->
  ExecF.evtF rsegs RNG PostOK (STATE 0x8170c mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23
                                 x28 x29 x30 x31).
Proof.
  intros x6 x7 x8 x9 x10 x15 x16 x17 x18 x28 x29 x30 x31 H6 H7 H8 H9 H10 H15 H16 H17 H18 H28 H29 H30 H31.
  intros s mk x5 x11 x12 x13 x14 x20 x21 x22 x23 Hs H5 H11 H14 H20 H13 H12 H22 INV CONT.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound slot 2 ltac:(lia)) as Rmod.
  assert (Hsl2 : slot - slot mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (Hsl0 : 0 <= slot - slot mod 2) by (Z.div_mod_to_equations; lia).
  assert (Hsn0 : 0 <= s * nch) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hsn : s * nch <= 11 * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  destruct INV as (HBB & (junk & FR) & ST & HW & MU & WM & HOUT).
  pose proof (PR.out_pref_len bs nch slot (Z.to_nat s)) as OL. rewrite (Z2Nat.id s) in OL by lia.
  apply PR.wv in H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H20, H22, H28, H29, H30, H31.
  subst x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x28 x29 x30 x31.
  (* the shadow bytes of f's and v's ranges are those of m: the run wrote only application bytes *)
  assert (AVA : forall x, v <= x < v + 48 -> app_mem x) by (intros x Hx; exact (addr_app m v 48 x AV Hx)).
  pose proof (addr_munch _ m mk f LEN AF MU
    (fun i Hi => sh_out2 _ _ _ _ _ APW AVA (addr_app m f LEN (f + i) AF ltac:(lia)))) as AFk.
  pose proof (addr_munch _ m mk v 48 AV MU
    (fun i Hi => sh_out2 _ _ _ _ _ APW AVA (addr_app m v 48 (v + i) AV ltac:(lia)))) as AVk.
  (* the three braid bytes: shadow byte, data byte, and their footprint ranges *)
  remember (3 * (s * nch + (slot - slot mod 2))) as g eqn:Eg.
  assert (Hg : 0 <= g /\ g + 6 <= 36 * nch) by lia.
  destruct (addr_one mk f LEN (50 + (g + (3 + slot mod 2))) AFk ltac:(lia)) as (_ & k0 & MK0 & SK0).
  destruct (addr_one mk f LEN (50 + (g + 5 * (slot mod 2))) AFk ltac:(lia)) as (_ & k1 & MK1 & SK1).
  destruct (addr_one mk f LEN (50 + (g + (1 + slot mod 2))) AFk ltac:(lia)) as (_ & k2 & MK2 & SK2).
  replace (f + (50 + (g + (3 + slot mod 2)))) with (f + 50 + (g + (3 + slot mod 2))) in MK0, SK0 by lia.
  replace (f + (50 + (g + 5 * (slot mod 2)))) with (f + 50 + (g + 5 * (slot mod 2))) in MK1, SK1 by lia.
  replace (f + (50 + (g + (1 + slot mod 2)))) with (f + 50 + (g + (1 + slot mod 2))) in MK2, SK2 by lia.
  pose proof (bytes_nth mk f bs (Z.to_nat (50 + (g + (3 + slot mod 2)))) HBB ltac:(lia)) as FD0.
  pose proof (bytes_nth mk f bs (Z.to_nat (50 + (g + 5 * (slot mod 2)))) HBB ltac:(lia)) as FD1.
  pose proof (bytes_nth mk f bs (Z.to_nat (50 + (g + (1 + slot mod 2)))) HBB ltac:(lia)) as FD2.
  rewrite Z2Nat.id in FD0, FD1, FD2 by lia.
  replace (f + (50 + (g + (3 + slot mod 2)))) with (f + 50 + (g + (3 + slot mod 2))) in FD0 by lia.
  replace (f + (50 + (g + 5 * (slot mod 2)))) with (f + 50 + (g + 5 * (slot mod 2))) in FD1 by lia.
  replace (f + (50 + (g + (1 + slot mod 2)))) with (f + 50 + (g + (1 + slot mod 2))) in FD2 by lia.
  assert (RS0 : ExecF.rng RNG ((f + 50 + (g + (3 + slot mod 2))) / 8 + 2147450880) 1)
    by (eapply rng_sub'; [exact RSR|]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (RS1 : ExecF.rng RNG ((f + 50 + (g + 5 * (slot mod 2))) / 8 + 2147450880) 1)
    by (eapply rng_sub'; [exact RSR|]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (RS2 : ExecF.rng RNG ((f + 50 + (g + (1 + slot mod 2))) / 8 + 2147450880) 1)
    by (eapply rng_sub'; [exact RSR|]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (RD0 : ExecF.rng RNG (f + 50 + (g + (3 + slot mod 2))) 1) by (eapply rng_sub'; [exact RR|]; lia).
  assert (RD1 : ExecF.rng RNG (f + 50 + (g + 5 * (slot mod 2))) 1) by (eapply rng_sub'; [exact RR|]; lia).
  assert (RD2 : ExecF.rng RNG (f + 50 + (g + (1 + slot mod 2))) 1) by (eapply rng_sub'; [exact RR|]; lia).
  (* the shadow byte of v + 4 s *)
  destruct (addr_four mk v 48 (v + 4 * s) AVk ltac:(lia) ltac:(lia)) as (kv & MKv & SKv).
  assert (RSv : ExecF.rng RNG ((v + 4 * s) / 8 + 2147450880) 1)
    by (eapply rng_sub'; [exact RSO|]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  (* +0x120 .. +0x160 *)
  eapply bk1F with (A := f + 50 + (g + 5 * (slot mod 2)));
    [ rewrite !unsigned_lit by lia; lia | lia | exact MK1 | exact SK1 | exact RS1 | intros p12 p21 p23 U12 ].
  eapply bk0F with (A := f + 50 + (g + (3 + slot mod 2))) (D := f + 50 + (g + 5 * (slot mod 2)));
    [ rewrite !unsigned_lit by lia; lia | lia | exact MK0 | exact SK0 | exact U12 | exact FD1 | exact RS0 | exact RD1
    | intros q12 q13 q23 U13 ].
  eapply bk2F with (A := f + 50 + (g + (1 + slot mod 2))) (D := f + 50 + (g + (3 + slot mod 2)));
    [ rewrite !unsigned_lit by lia; lia | lia | exact MK2 | exact SK2 | exact U13 | exact FD0 | exact RS2 | exact RD0
    | intros r12 r22 r23 U12' ].
  (* +0x164 .. +0x174: v + 4 s does not wrap, is not NULL, v is not NULL and is aligned *)
  step. if_false_lit.
  step. rewrite v_sltiu_b2z. rw_inner_lit. try change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [Z.b2z].
  step. step. if_false_lit. step. if_false_lit.
  (* +0x178 .. +0x188 *)
  eapply bstF with (A := v + 4 * s) (D := f + 50 + (g + (1 + slot mod 2)));
    [ rewrite unsigned_lit by lia; reflexivity | exact MKv | exact SKv | exact U12' | exact FD2 | exact RSv | exact RD2
    | intros t22 t23 ].
  clear MK0 MK1 MK2 SK0 SK1 SK2 FD0 FD1 FD2 RS0 RS1 RS2 RD0 RD1 RD2 MKv SKv RSv AFk AVk AVA U12 U13 U12'.
  remember (nth (Z.to_nat (50 + (g + (3 + slot mod 2)))) bs (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth (Z.to_nat (50 + (g + 5 * (slot mod 2)))) bs (Z_to_bv 8 0)) as b1 eqn:E1.
  remember (nth (Z.to_nat (50 + (g + (1 + slot mod 2)))) bs (Z_to_bv 8 0)) as b2 eqn:E2.
  pose proof (wr_at_store_ok rsegs mk v 48 (4 * s) 4%nat HW ltac:(lia) ltac:(cbn; lia)) as HS.
  (* +0x18c .. +0x1b4: the sample and its store *)
  do 11 step.
  (* the stored word is the sample, modulo 2^32 *)
  assert (BP0 : PSR.braid_pos s slot nch 0 = g + (3 + slot mod 2)) by (rewrite PR.braid_pos_lin by lia; rewrite Eg; reflexivity).
  assert (BP1 : PSR.braid_pos s slot nch 1 = g + 5 * (slot mod 2)) by (rewrite PR.braid_pos_lin by lia; rewrite Eg; reflexivity).
  assert (BP2 : PSR.braid_pos s slot nch 2 = g + (1 + slot mod 2)) by (rewrite PR.braid_pos_lin by lia; rewrite Eg; reflexivity).
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?W)) _) =>
    replace (le4 W) with (le4 (Z_to_bv 64 (PSR.rp_sample bs nch slot s))) end.
  2: { symmetry. apply PR.le4_eqm.
       cbv delta [sxb zxb]. rewrite !unsigned_lit_wrap, !PR.mod64_32.
       rewrite !PR.hi_lo, !PR.hi_mask. rewrite !Z.shiftl_mul_pow2 by lia.
       pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
       repeat rewrite (Z.mod_small _ (2^64)) by zrange.
       unfold PSR.rp_sample. cbv beta zeta. rewrite BP0, BP1, BP2, <- E0, <- E1, <- E2.
       rewrite <- Z.lor_assoc. apply PR.sample_val. }
  clear BP0 BP1 BP2 E0 E1 E2.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mk0 ?aa ?wb) _) =>
    assert (INV2 : INVR (write_to_mem mk0 aa wb) (S (Z.to_nat s)));
    [ unfold INVR; split; [|split; [|split; [|split; [|split; [|split]]]]]
    | set (mk2 := write_to_mem mk0 aa wb) in *; clearbody mk2 ]
  end.
  { apply bytes_at_write_other; [exact HBB | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  { eexists. apply rw_cells_frame;
      [exact FR | lia | rewrite length_le4; lia | cbn [cells_size csize Nat.add]; rewrite length_le4; lia]. }
  { apply stk_write; [exact ST | lia | rewrite length_le4; lia]. }
  { apply wr_at_write. exact HW. }
  { apply munch_write; [exact MU | lia | rewrite length_le4; lia | cbn [inside]; rewrite length_le4; lia]. }
  { apply wmono_write. exact WM. }
  { rewrite PR.out_pref_S. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split.
    - apply bytes_at_write_other;
        [exact HOUT | lia | rewrite length_le4; lia | rewrite PR.out_pref_len, length_le4; lia].
    - rewrite PR.out_pref_len, (Z2Nat.id s) by lia.
      apply bytes_at_write_same; [lia | rewrite length_le4; lia]. }
  clear HBB FR ST HW MU WM HOUT HS.
  step. step. if_cases HE.
  - (* another sample *)
    zify_cond HE. try rewrite !unsigned_lit in HE by lia.
    eapply CONT; [ lia | reg_eq_tac | reg_eq_tac | reg_eq_tac | reg_eq_tac | ].
    replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) by lia. exact INV2.
  - (* the twelfth sample is written: leave the loop *)
    zify_cond HE. try rewrite !unsigned_lit in HE by lia.
    apply sr_exit. replace 12%nat with (S (Z.to_nat s)) by lia. exact INV2.
Qed.

(* +0x9c .. +0x11c: the braid offsets of sample s, stored into pos[0..2] and read back, with the UBSan checks of the
   arithmetic, of the pos[] slot addresses and of f + 50 + pos[k]; then sr_tail. *)
Lemma sr_loop : forall (x6 x7 x8 x9 x10 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  bv_unsigned x6 = 18446744073709551608 -> bv_unsigned x7 = SP + -96 -> bv_unsigned x8 = v ->
  bv_unsigned x9 = slot mod 2 -> bv_unsigned x10 = nch -> bv_unsigned x15 = f + 50 ->
  bv_unsigned x16 = slot - slot mod 2 -> bv_unsigned x17 = 1 -> bv_unsigned x18 = 18446744073709551607 ->
  bv_unsigned x28 = 18446744073709551599 -> bv_unsigned x29 = 18446744073692774400 ->
  bv_unsigned x30 = 18446744073709551615 - (f + 50) -> bv_unsigned x31 = 1 ->
  forall (K : nat) (s : Z) (mk : word -> option byte) (x5 x11 x12 x13 x14 x20 x21 x22 x23 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 ->
  bv_unsigned x5 = 12 - s -> bv_unsigned x11 = v + 4 * s -> bv_unsigned x14 = s -> bv_unsigned x20 = v + 4 * s ->
  INVR mk (Z.to_nat s) ->
  ExecF.evtF rsegs RNG PostOK (STATE 0x81688 mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23
                                 x28 x29 x30 x31).
Proof.
  intros x6 x7 x8 x9 x10 x15 x16 x17 x18 x28 x29 x30 x31 H6 H7 H8 H9 H10 H15 H16 H17 H18 H28 H29 H30 H31 K.
  induction K as [K IH] using lt_wf_ind.
  intros s mk x5 x11 x12 x13 x14 x20 x21 x22 x23 HK Hs H5 H11 H14 H20 INV.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound slot 2 ltac:(lia)) as Rmod.
  assert (Hsl2 : slot - slot mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (Hsl0 : 0 <= slot - slot mod 2) by (Z.div_mod_to_equations; lia).
  assert (Hsn0 : 0 <= s * nch) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hsn : s * nch <= 11 * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  destruct INV as (HBB & (junk & FR) & ST & HW & MU & WM & HOUT).
  pose proof (PR.out_pref_len bs nch slot (Z.to_nat s)) as OL. rewrite (Z2Nat.id s) in OL by lia.
  apply PR.wv in H5, H6, H7, H8, H9, H10, H11, H14, H15, H16, H17, H18, H20, H28, H29, H30, H31.
  subst x5 x6 x7 x8 x9 x10 x11 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31.
  (* +0x9c .. +0xc0: g = 3 (s nch + slot - slot mod 2), with the two int-overflow checks *)
  step. rw_inner_lit. step. rw_inner_lit.
  replace (bv_swrap 32 (s * nch)) with (s * nch) by (symmetry; apply swrap32_id; lia).
  step. rw_inner_lit. if_false_lit. step. rw_inner_lit.
  replace (bv_swrap 32 (s * nch + 0)) with (s * nch + 0) by (symmetry; apply swrap32_id; lia).
  step. rw_inner_lit. step. rw_inner_lit.
  replace (bv_swrap 32 (s * nch + (slot - slot mod 2))) with (s * nch + (slot - slot mod 2))
    by (symmetry; apply swrap32_id; lia).
  step. rw_inner_lit. if_false_lit. step. rw_inner_lit.
  replace (bv_swrap 32 (s * nch + (slot - slot mod 2) + 0)) with (s * nch + (slot - slot mod 2) + 0)
    by (symmetry; apply swrap32_id; lia).
  step. rw_inner_lit. step. rw_inner_lit.
  step. if_cases HP.
  - (* an odd slot: pos[0] = g + 4, pos[1] = g + 5, s5 = 2 *)
    zify_cond HP. assert (HM2 : slot mod 2 = 1) by lia.
    do 2 step. step. rw_inner_lit. if_false_lit. do 2 step. step. rw_inner_lit. if_false_lit. step.
    (* +0x100 .. +0x11c: pos[2] = g + s5, the three offsets read back, f + 50 + pos[k] does not wrap *)
    step. step. step. step. rw_inner_lit. if_false_lit.
    step. step. rw_inner_lit. if_false_lit.
    step. step. rw_inner_lit. if_false_lit.
    merge_pos. repack_inv s.
    eapply sr_tail with (s := s).
    all: try (solve [ assumption | reg_eq_tac ]).
    intros mk' y5 y11 y12 y13 y14 y20 y21 y22 y23 Hlt Hy5 Hy11 Hy14 Hy20 INV'.
    eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1) mk');
      [ reflexivity | lia | exact Hy5 | exact Hy11 | exact Hy14 | exact Hy20 | exact INV' ].
  - (* an even slot: pos[0] = g + 3, pos[1] = g, s5 = 1 *)
    zify_cond HP. assert (HM2 : slot mod 2 = 0) by lia.
    do 2 step. step. rw_inner_lit. if_false_lit. step. step. rw_inner_lit. if_false_lit. do 2 step.
    step. step. step. step. rw_inner_lit. if_false_lit.
    step. step. rw_inner_lit. if_false_lit.
    step. step. rw_inner_lit. if_false_lit.
    merge_pos. repack_inv s.
    eapply sr_tail with (s := s).
    all: try (solve [ assumption | reg_eq_tac ]).
    intros mk' y5 y11 y12 y13 y14 y20 y21 y22 y23 Hlt Hy5 Hy11 Hy14 Hy20 INV'.
    eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1) mk');
      [ reflexivity | lia | exact Hy5 | exact Hy11 | exact Hy14 | exact Hy20 | exact INV' ].
Qed.

End SR.

Ltac curmemF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* ---- the walk ---- *)

Theorem rp_slot_read_holds_F : rp_slot_read_F_holds_stmt.
Proof.
  unfold rp_slot_read_F_holds_stmt. intros HSW.
  unfold rp_slot_width_contract_F, RP_SLOT_WIDTH, RP_SLOT_WIDTH_STK, RP_SLOT_WIDTH_FRAME, RP_FRAME_CHANNELS_FRAME,
    RP_SW_OFF, RP_SW_LEN in HSW.
  unfold rp_slot_read_contract_F, RP_SLOT_READ, RP_SLOT_READ_STK, RP_SLOT_READ_FRAME, RP_SLOT_WIDTH_STK,
    RP_SLOT_WIDTH_FRAME, RP_FRAME_CHANNELS_FRAME, RP_SLOT_READ_VLEN, RP_AUDIO_OFF.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    HM HT HK ST LO APS1 APS2 CELLS OC HB HV HU RFR RGOT RCELL OCON RCON RBUF RV.
  change (96 + (16 + 16)) with 128 in *.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof (u64_range a3) as Ra3.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold off_stk, GOT_CELL_K, MIDEND in OC.
  pose proof (conj HM (conj HT (conj HK CELLS))) as PK. clear HM HT HK CELLS.
  unfold WIRE_RFC_CONSTS in OCON, RCON. rewrite !Forall_cons_iff in OCON, RCON. cbn [fst snd] in OCON, RCON.
  destruct OCON as (OM & OK & OT & _). destruct RCON as (RM & RK & RT & _).
  unfold off_stk, A_M, A_T, A_K36 in OM, OK, OT.
  unfold GOT_CELL_K in RGOT. unfold CELL_K in RCELL.
  (* +0x0 .. +0x24: the frame and the nine register saves *)
  carve_frame 96%nat ST.
  do 10 step.
  destruct PK as (HM & HT & HK & CELLS).
  curmemF ltac:(fun mm => assert (CELLS1 : asan_cells mm)
    by (eapply asan_cells_munch; [exact CELLS | exact MU | unfold MIDEND, GOT_CELL_K; lia])).
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  (* +0x28 .. +0x40: s0 := v, s1 := slot, the shadow base through its GOT word, s2 := f, a2 := slot *)
  do 5 step. clear RDG RDS CK GCK. do 3 step.
  match goal with MU' : munch _ m ?m1 |- _ => rename m1 into mf end.
  pose proof (bytes_tp m mf _ _ A_M (le8 (Z_to_bv 64 KM)) MU ltac:(rewrite length_le8; unfold A_M; lia) HM) as HM1.
  pose proof (bytes_tp m mf _ _ A_T (le8 (Z_to_bv 64 KT)) MU ltac:(rewrite length_le8; unfold A_T; lia) HT) as HT1.
  pose proof (bytes_tp m mf _ _ A_K36 (le8 (Z_to_bv 64 K36)) MU ltac:(rewrite length_le8; unfold A_K36; lia) HK) as HK1.
  (* +0x44: rp_slot_width by its footprint contract on [sp - 128, sp - 96) *)
  eapply evtF_cut.
  { eapply HSW with (lo := lo) (bs := bs).
    - exact HM1.
    - exact HT1.
    - exact HK1.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp + -96 - (16 + 16)) with (bv_unsigned sp - 128) by lia.
      exact APS1.
    - rewrite unsigned_lit by lia. apply (app_win (bv_unsigned sp) 128); [lia | exact APS1 | exact APS2 | lia].
    - exact CELLS1.
    - unfold off_stk, GOT_CELL_K. rewrite unsigned_lit by lia. lia.
    - unfold off_stk, CELL_K. rewrite unsigned_lit by lia. lia.
    - intros HN. destruct (HB HN) as (HLEN & BB & DB & AB & NZ). unfold off_stk in DB.
      pose proof (bytes_at_bound _ _ _ _ BB) as BBB.
      split; [lia|]. split; [eapply bytes_tp; [exact MU | lia | exact BB]|].
      split; [unfold off_stk; rewrite unsigned_lit by lia; lia|].
      eapply addr_munch; [eapply addr_sub; [exact AB | lia | lia | lia] | exact MU |].
      intros i Hi. apply sh_out1.
      + intros x Hx. apply (app_win (bv_unsigned sp) 128); [lia | exact APS1 | exact APS2 | lia].
      + apply (addr_app m (bv_unsigned a0) (Z.of_nat (length bs))); [exact AB | lia].
    - intros HN. destruct (HB HN) as (HLEN & BB & DB & AB & NZ).
      pose proof (bytes_at_bound _ _ _ _ BB) as BBB. split; lia.
    - rewrite unsigned_lit by lia. eapply ExecF.rng_sub; [exact RFR | lia | lia].
    - exact RGOT.
    - exact RCELL.
    - unfold WIRE_RFC_CONSTS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        cbn [fst snd]; unfold off_stk, A_M, A_T, A_K36; rewrite unsigned_lit by lia; lia.
    - unfold WIRE_RFC_CONSTS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        cbn [fst snd]; assumption.
    - intros HN. destruct (HB HN) as (HLEN & BB & DB & AB & NZ). destruct (RBUF HN) as (RB & RS).
      eapply ExecF.rng_sub; [exact RB | lia | lia].
    - intros HN. destruct (HB HN) as (HLEN & BB & DB & AB & NZ). destruct (RBUF HN) as (RB & RS).
      eapply rng_sub; [exact RS | unfold shadow_addr; Z.div_mod_to_equations; lia
                                | unfold shadow_addr; Z.div_mod_to_equations; lia]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2
    & WM2 & ST2).
  rewrite (unsigned_lit (bv_unsigned sp + -96)) in MU2, ST2 by lia.
  replace (ret_pc (Z_to_bv 64 529972)) with (Z_to_bv 64 529972) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (MU3 : munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m2).
  { eapply munch_trans; [exact MU|].
    apply (munch_weaken [(bv_unsigned sp + -96 - (16 + 16), bv_unsigned sp + -96)]); [|exact MU2].
    intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; [lia | exact I]. }
  assert (WM3 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FR2.
  clear FR MU WM MU2 WM2 HM1 HT1 HK1 CELLS1.
  pose proof (PR.sw_model_range (bv_unsigned a1) bs (bv_signed a2)) as SWR.
  (* +0x48: `bltz a0` *)
  step. if_cases HOK.
  - (* +0x204: the width is negative, nothing is read and nothing is written *)
    zify_cond HOK.
    assert (HNEG : PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) = -1)
      by (destruct SWR as [E|E]; [exact E | try rewrite unsigned_lit in HOK by lia; lia]).
    do 12 step.
    replace (PSR.rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)) with 0
      by (unfold PSR.rp_slot_read_model; rewrite HNEG; reflexivity).
    rewrite HNEG. cbn [Z.leb].
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evtF_done. do 15 eexists. split; [reflexivity|].
    split; [exact WM3|]. split; [exact ST2|]. exact MU3.
  - (* +0x4c .. +0x98: the width is a channel count; the loop reads and writes the twelve samples *)
    zify_cond HOK.
    assert (HM0 : 2 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) <= 40)
      by (destruct SWR as [E|E]; [rewrite E in HOK; rewrite ?unsigned_lit in HOK by lia; lia | lia]).
    destruct (PR.sw_geom (bv_unsigned a1) bs (bv_signed a2) ltac:(lia) ltac:(lia)) as (G1 & G2 & G3 & G4).
    assert (HN50 : 50 <= bv_unsigned a1) by lia.
    destruct (HB HN50) as (HLEN & BB & DB & AB & NZ). unfold off_stk in DB.
    destruct (HV ltac:(lia)) as (HW & DJV & DJFV & AVV). unfold off_stk in DJV.
    destruct (HU ltac:(lia)) as (HU51 & HV0 & HV4).
    destruct (RBUF HN50) as (RB & RBS). destruct (RV ltac:(lia)) as (RVV & RVS).
    pose proof (bytes_at_bound _ _ _ _ BB) as BBB.
    pose proof HW as HWc. destruct HWc as (HW1 & HW2 & _).
    assert (Ea2 : bv_unsigned a2 = bv_signed a2).
    { pose proof (u64_range a2) as R2. pose proof G3 as G3'.
      unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in G3' |- *.
      change (2 ^ Z.of_N 64) with (2^64) in G3' |- *.
      revert G3'. Z.div_mod_to_equations. lia. }
    assert (L1 : Z.land (bv_unsigned a2) 1 = bv_signed a2 mod 2)
      by (rewrite PR.land_1 by lia; rewrite Ea2; reflexivity).
    assert (L2 : Z.land (bv_unsigned a2) 18446744073709551614 = bv_signed a2 - bv_signed a2 mod 2)
      by (rewrite PR.land_m2 by lia; rewrite Ea2; reflexivity).
    assert (L4 : Z.land (bv_unsigned a3) 3 = 0)
      by (replace 3 with (2^2 - 1) by reflexivity; rewrite zb_land_mask by lia; exact HV4).
    pose proof (Z.mod_pos_bound (bv_signed a2) 2 ltac:(lia)) as Rm2.
    (* +0x4c / +0x54: f is not NULL and f + 50 does not wrap *)
    step. if_false_lit.
    step. step. if_false_lit.
    (* +0x58 .. +0x98: the loop's fixed registers *)
    do 17 step.
    rewrite ?L1, ?L2, ?L4. rewrite ?v_sltu_b2z, ?v_sltiu_b2z. rw_inner_lit.
    try change (bv_wrap 64 1) with 1.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned a3))) by lia.
    try rewrite (proj2 (Z.ltb_lt 0 1)) by lia.
    cbn [Z.b2z].
    eapply evtF_mono.
    + eapply sr_loop with (RNG := RNG) (ra := ra) (sp := sp) (S0 := s0) (S1 := s1) (S2 := s2) (S3 := s3) (S4 := s4)
        (S5 := s5) (S6 := s6) (S7 := s7) (m := m) (bs := bs) (f := bv_unsigned a0) (v := bv_unsigned a3)
        (nch := PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (slot := bv_signed a2)
        (lo := lo) (K := 12%nat) (s := 0).
      all: try assumption.
      all: try (solve [ lazymatch goal with |- @eq Z (bv_unsigned _) _ => idtac end;
                        first [ reflexivity | rewrite unsigned_lit_wrap; reflexivity | reg_eq_tac ] ]).
      all: try (solve [ intros x Hx; apply (app_win (bv_unsigned sp) 128); [lia | exact APS1 | exact APS2 | lia] ]).
      all: try (solve [ lia ]).
      (* the loop invariant at the first sample *)
      unfold INVR. split; [|split; [|split; [|split; [|split; [|split]]]]].
      * eapply bytes_at_transport; [exact BB | exact MU3 | cbn [disjoint_from]; split; [lia | exact I]].
      * eexists. exact FR2.
      * exact ST2.
      * eapply wr_at_transport; [exact HW | exact WM3].
      * eapply munch_weaken; [| exact MU3].
        intros x Hx; cbn [outside] in *; split; [apply (proj1 Hx) | exact I].
      * exact WM3.
      * change (Z.to_nat 0) with 0%nat. unfold PR.out_pref. cbn [seq flat_map]. apply bytes_at_nil. lia.
    + intros ms' (t0'' & t1'' & t2'' & b1' & b2' & b3' & b4' & b5' & b6' & b7' & t3'' & t4'' & t5'' & t6'' & m'
        & -> & W' & S' & U' & B').
      replace (PSR.rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)) with 1
        by (unfold PSR.rp_slot_read_model; rewrite (proj2 (Z.ltb_ge _ 0)) by lia; reflexivity).
      rewrite (proj2 (Z.leb_le 0 (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)))) by lia.
      do 15 eexists. split; [reflexivity|].
      split; [exact W'|]. split; [exact S'|]. split; [exact U' | exact B'].
Qed.
