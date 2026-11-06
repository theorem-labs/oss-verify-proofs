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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/rp_hot_clamp_FW.v, with its module paths and numbers changed; 508 of its 575 lines of code are new or changed and 475 lines of the source are left out. *)
(* rp_slot_read_F: the footprint walk of fuzz_wire.asan's rp_slot_read (image A, entry 0x8160c, 0x1b0 bytes), against the
   frozen lib/A/Prog/rp_slot_read_F_c.v rp_slot_read_F_holds_stmt: rp_slot_width is taken by its footprint contract
   rp_slot_width_contract_F (rp_slot_width_F_c.v), the statement's premise. The segment split, the loop invariant and the
   sample arithmetic are those of the plain walk lib/Prog/rp_slot_read.v (its sw_model_range, sw_geom, braid_pos_lin,
   out_pref, le4_eqm, hi_lo, hi_mask, sample_val, seqz5 reused by name); the shadow checks, the transports over the
   frame's munch and the call into a footprint callee after the register saves follow libreac/fuzz_decode's released
   lib/A/Prog/reac_decode_F.v and its lib/A/Prog/ReacDecodeLib.v (rd_all, lts_sm, app_win, shadow_not_app,
   shadow_range, mrd_munch, addr_munch, asan_cells_munch, addr_one, addr_four copied; asan_cells_munch here over this
   image's 19 cells).
   The code:
     +0x00 .. +0x18  frame [sp - 48, sp): ra, s0 .. s4; +0x1c .. +0x34 s0 := v, s2 := slot, s3 := the shadow base (the
                     GOT word 0x987e8, then the cell 0xa0778), s1 := f;
     +0x38           `jal rp_slot_width` (0x81554) on (f, n, slot), its window [sp - 80, sp - 48): the six saves come
                     first, so the window premise off [GOT_CELL_K, MIDEND + 8) keeps asan_cells at the call;
     +0x3c           `bltz a0` to +0x16c: a0 := 0, the epilogue (+0x170 .. +0x18c), nothing read or written;
     +0x40 .. +0x90  the braid bases (f + 50, slot mod 2, 3 * width, 5 * (slot mod 2), the 0xff000000 mask), a3 := 12;
     +0x94 .. +0x128 one sample per turn: the shadow byte of the low, middle and high braid byte and of v[s], each with
                     its slow path (+0x130 .. +0x15c), the three byte loads, the 24-bit sample, `sw` to v[s] (+0x11c);
     +0x12c          `j` to +0x164: a0 := 1, the epilogue.
   The premises `addressable` of the frame bytes and of v give each shadow byte k with k = 0 or (a mod 8) < k (the loads)
   and (a mod 8) + 3 < k (the 4-byte store, addr_four), so no report call (0x8176c, 0x8179c .. 0x817b8) is reached. The
   frame and v lie in application memory, the shadow bytes do not, so the run's own stores leave every shadow byte as
   it was (addr_munch_app). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_clean_len_c
  rp_frame_channels_c rp_slot_width_F_c rp_slot_read_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c rp_slot_read_c rp_slot_read.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read.

Lemma firstn1_skipn : forall (bs : list byte) i d, (i < length bs)%nat -> firstn 1 (skipn i bs) = [nth i bs d].
Proof.
  induction bs as [|b bs IH]; intros i d H; cbn in H; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

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

(* The 19 runtime cells lie in [GOT_CELL_K, MIDEND + 8); a store window off that span keeps them. *)
Lemma asan_cells_munch : forall m m' lo hi, asan_cells m -> munch [(lo, hi)] m m' ->
  MIDEND + 8 <= lo \/ hi <= GOT_CELL_K -> asan_cells m'.
Proof.
  unfold asan_cells, MIDEND, GOT_CELL_K.
  intros m m' lo hi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17
    & C18 & C19) MU D.
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

(* An address that is not application memory is outside a stack window whose two ends are. *)
Lemma win_out : forall s d x, 0 < d <= 2^32 -> app_mem (s - d) -> app_mem (s - 1) -> ~ app_mem x ->
  ~ (s - d <= x < s).
Proof. intros s d x Hd H1 H2 Hx Hw. apply Hx. apply (app_win s d); [exact Hd | exact H1 | exact H2 | exact Hw]. Qed.

(* Addressability survives a run whose writes stay in application memory: the shadow bytes are not. *)
Lemma addr_munch_app : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall x, ~ app_mem x -> outside W x) -> addressable m' p n.
Proof.
  intros W m m' p n A MU D. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. apply D. destruct A as (_ & _ & _ & H). destruct (H i Hi) as (Ha & _).
  exact (shadow_not_app _ Ha).
Qed.

Lemma addr_sub : forall m p n q k, addressable m p n -> p <= q -> 0 <= k -> q + k <= p + n -> addressable m q k.
Proof.
  intros m p n q k (H0 & H1 & H2 & H) Hq Hk Hn. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply H. lia.
Qed.

(* The shadow byte of a, p <= a < p + n, lies in the shadow range of [p, p + n). *)
Lemma rng_shadow_one : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> ExecF.rng RNG (a / 8 + ASAN_K) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in H.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Lemma shadow_rng_sub : forall RNG p n q k,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) -> p <= q -> 0 < k -> q + k <= p + n ->
  ExecF.rng RNG (shadow_addr q) (shadow_addr (q + k - 1) - shadow_addr q + 1).
Proof.
  intros RNG p n q k H Hq Hk Hn. unfold shadow_addr in *.
  assert (L1 : p / 8 <= q / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (q + k - 1) / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (L3 : q / 8 <= (q + k - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* ---- the four checks of one sample (0x816a0 .. 0x81704) ---- *)

(* +0x94 .. +0xa4: the shadow byte of the low braid byte A = t2 + a5; slow path +0x130 .. +0x138 (report at +0x19c). *)
Lemma c1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22
    x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x7 + bv_unsigned x15 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 y30 : word, evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 x18
     (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 y30 x31) F (Z_to_bv 64 530100) fc None mm
     (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880)
    x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 530080) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc mm Q k A EA RA M SK RGS CONT.
  pose proof (u64_range x7) as R7. pose proof (u64_range x15) as R15. unfold ASAN_K in M, RGS.
  step. gen_add x7 x15 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  + rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  + rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0xa8 .. +0xc4: the middle braid byte's address A = a2 + (a5 + t3) and its shadow byte, the load of the low byte
   (at D = a6 + a5); slow path +0x13c .. +0x144 (report at +0x1a8). *)
Lemma c2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22
    x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x12 + (bv_unsigned x15 + bv_unsigned x28) = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x16 + bv_unsigned x15 = D -> D < 2^64 -> mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG D 1 ->
  (forall y11 y18 y31 : word, bv_unsigned y11 = A ->
     evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 y18 (Z_to_bv 64 2147450880)
     x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 (zxb b) y31) F (Z_to_bv 64 530132) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880)
    x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 530100) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc mm Q k b A D EA RA M SK ED RD MD RGS RGD CONT.
  pose proof (u64_range x12) as R12. pose proof (u64_range x15) as R15. pose proof (u64_range x16) as R16.
  pose proof (u64_range x28) as R28. unfold ASAN_K in M, RGS.
  step. gen_add x15 x28 w1 U1.
  step. gen_add x16 x15 w2 U2. rewrite ED in U2.
  step. gen_add x12 w1 w U. rewrite U1, EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm w2 _ _ MD U2) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  + rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  + rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* +0xc8 .. +0xdc: the high braid byte's address A = t1 + a5 and its shadow byte, the load of the middle byte (at a1);
   slow path +0x148 .. +0x150 (report at +0x190). *)
Lemma c3F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22
    x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x6 + bv_unsigned x15 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D -> mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG D 1 ->
  (forall y18 y31 : word,
     evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 x13 x14 x15 x16 x17 y18
     (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 y31) F (Z_to_bv 64 530156) fc None mm
     (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880)
    x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 530132) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc mm Q k b A D EA RA M SK ED MD RGS RGD CONT.
  pose proof (u64_range x6) as R6. pose proof (u64_range x15) as R15. pose proof (u64_range x11) as R11.
  unfold ASAN_K in M, RGS.
  step. gen_add x6 x15 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x11 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  + rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  + rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0xe0 .. +0xf4: the shadow byte of v[s] (at W = a0) for the 4-byte store, the load of the high byte (at
   D = a7 + a5, signed); slow path +0x154 .. +0x15c: (W & 7) + 3 < k goes back to +0xf8, else the report at +0x160. *)
Lemma c4F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22
    x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte)
    (Q : machine_state -> Prop) (k b : byte) (W D : Z),
  bv_unsigned x10 = W ->
  mrd rsegs mm (wa (W / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ W mod 8 + 3 < bv_signed k) ->
  bv_unsigned x17 + bv_unsigned x15 = D -> D < 2^64 -> mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (W / 8 + ASAN_K) 1 -> ExecF.rng RNG D 1 ->
  (forall y18 y20 : word,
     evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 y18 (Z_to_bv 64 2147450880)
     y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (sxb b)) F (Z_to_bv 64 530180) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880)
    x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 530156) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc mm Q k b W D EW M SK ED RD MD RGS RGD CONT.
  pose proof (u64_range x10) as R10. pose proof (u64_range x15) as R15. pose proof (u64_range x17) as R17.
  unfold ASAN_K in M, RGS.
  step. gen_add x17 x15 w U. rewrite ED in U.
  step. gen_shr x10 g G. rewrite EW in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm w _ _ MD U) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound W 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  + rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  + rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, EW, (lts_sm (W mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

(* lib/Prog/rp_slot_read.v rw_inner_lit: rewrite bv_unsigned (Z_to_bv 64 z) to z, innermost first, where lia proves z
   in range. *)
Ltac rw_inner_lit :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (unsigned_lit z) by lia
      end
  end.

(* ---- the loop: twelve samples, 0x816a0 .. 0x81738, then 0x81770 .. 0x81798 ---- *)

Section Loop.
Variables (RNG : ExecF.footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
Variables (f v nch slot lo : Z).

Local Notation SP := (bv_unsigned sp).
Local Notation LEN := (Z.of_nat (length bs)).

Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hslot : 0 <= slot < nch.
Hypothesis Hlen : 50 + 36 * nch <= LEN.
Hypothesis Hf : 0 <= f.
Hypothesis Hfb : f + LEN <= 2^64.
Hypothesis HDJf : f + LEN <= SP - 80 \/ SP <= f.
Hypothesis Hv : 0 <= v.
Hypothesis Hv48 : v + 48 <= 2^64.
Hypothesis HDJv : v + 48 <= SP - 80 \/ SP <= v.
Hypothesis HDJfv : v + 48 <= f \/ f + LEN <= v.
Hypothesis Hlo0 : 0 <= lo.
Hypothesis HSPlo : lo + 80 <= SP.
Hypothesis APS1 : app_mem (SP - 80).
Hypothesis APS2 : app_mem (SP - 1).
Hypothesis AF : addressable m f LEN.
Hypothesis AV : addressable m v 48.
Hypothesis RF : ExecF.rng RNG f LEN.
Hypothesis RFS : ExecF.rng RNG (shadow_addr f) (shadow_addr (f + LEN - 1) - shadow_addr f + 1).
Hypothesis RVV : ExecF.rng RNG v 48.
Hypothesis RVS : ExecF.rng RNG (shadow_addr v) (shadow_addr (v + 48 - 1) - shadow_addr v + 1).
Hypothesis RFR : ExecF.rng RNG (SP - 80) 80.

Definition PostL : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo SP /\
    munch [(SP - 80, SP); (v, v + 48)] m m' /\ bytes_at rsegs m' v (PSR.rp_slot_bytes bs nch slot).

Definition INVR (mk : word -> option byte) (j : nat) : Prop :=
  bytes_at rsegs mk f bs /\ rw_cells rsegs mk (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs mk lo (SP + -48) /\ wr_at rsegs mk v 48 /\
  munch [(SP - 80, SP); (v, v + 48)] m mk /\ wmono rsegs m mk /\
  bytes_at rsegs mk v (PR.out_pref bs nch slot j).

Local Notation STATE pc mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 :=
  (MS (mkR (Z_to_bv 64 529992) (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 2147450880) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

(* The shadow bytes are outside the run's two write windows: both are application memory. *)
Lemma out2 : forall x, ~ app_mem x -> outside [(SP - 80, SP); (v, v + 48)] x.
Proof.
  intros x Hx. cbn [outside]. split; [exact (win_out SP 80 x ltac:(lia) APS1 APS2 Hx)|]. split; [|exact I].
  intros Hw. apply Hx. destruct AV as (_ & _ & _ & AB). destruct (AB (x - v) ltac:(lia)) as (Ha & _).
  replace (v + (x - v)) with x in Ha by lia. exact Ha.
Qed.

(* 0x81770 .. 0x81798: a0 = 1, the six saved registers back, the frame given back, return. *)
Lemma sr_exit : forall (mk : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 : word),
  INVR mk 12 -> evtF rsegs RNG PostL (STATE 530288 mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29
    x30 x31).
Proof.
  intros mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 (HBB & FR & ST & HW & MU & WM & HOUT).
  pose proof (u64_range sp) as Rsp.
  do 10 step.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold PostL. do 15 eexists. split; [reflexivity|].
  split; [exact WM|]. split; [exact ST|]. split; [exact MU|].
  rewrite <- PR.out_pref_full. exact HOUT.
Qed.

Lemma sr_loop : forall (x5 x6 x7 x9 x12 x14 x16 x17 x28 x29 : word),
  bv_unsigned x6 = f + 50 + slot mod 2 + 1 -> bv_unsigned x7 = f + 50 + slot mod 2 + 3 ->
  bv_unsigned x12 = f + 50 -> bv_unsigned x14 = 3 * nch ->
  bv_unsigned x16 = f + 50 + slot mod 2 + 3 -> bv_unsigned x17 = f + 50 + slot mod 2 + 1 ->
  bv_unsigned x28 = 5 * (slot mod 2) -> bv_unsigned x29 = 18446744073692774400 ->
  forall (K : nat) (s : Z) (mk : word -> option byte) (x8 x10 x11 x13 x15 x18 x20 x30 x31 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 ->
  bv_unsigned x8 = v + 4 * s -> bv_unsigned x10 = v + 4 * s -> bv_unsigned x13 = 12 - s ->
  bv_unsigned x15 = 3 * (s * nch + (slot - slot mod 2)) ->
  INVR mk (Z.to_nat s) ->
  evtF rsegs RNG PostL (STATE 530080 mk x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31).
Proof.
  intros x5 x6 x7 x9 x12 x14 x16 x17 x28 x29 H6 H7 H12 H14 H16 H17 H28 H29 K.
  induction K as [K IH] using lt_wf_ind.
  intros s mk x8 x10 x11 x13 x15 x18 x20 x30 x31 HK Hs H8 H10 H13 H15 INV.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound slot 2 ltac:(lia)) as Rmod.
  assert (Hsl2 : slot - slot mod 2 <= nch - 2) by (clear - Hev Hslot Rmod; Z.div_mod_to_equations; lia).
  assert (Hsl0 : 0 <= slot - slot mod 2) by (Z.div_mod_to_equations; lia).
  assert (Hsn0 : 0 <= s * nch) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hsn : s * nch <= 11 * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  destruct INV as (HBB & FR & ST & HW & MU & WM & HOUT).
  assert (AFk : addressable mk f LEN) by (eapply addr_munch_app; [exact AF | exact MU | exact out2]).
  assert (AVk : addressable mk v 48) by (eapply addr_munch_app; [exact AV | exact MU | exact out2]).
  (* the three braid bytes *)
  assert (RD : forall k, 0 <= k < 3 ->
    mrd rsegs mk (wa (f + (50 + (3 * (s * nch + (slot - slot mod 2)) +
      (if k =? 0 then 3 + slot mod 2 else if k =? 1 then 5 * (slot mod 2) else 1 + slot mod 2)))))
    = Some (nth (Z.to_nat (50 + PSR.braid_pos s slot nch k)) bs (Z_to_bv 8 0))).
  { intros k Hk. rewrite <- PR.braid_pos_lin by lia.
    pose proof (bytes_nth mk f bs (Z.to_nat (50 + PSR.braid_pos s slot nch k)) HBB) as R.
    rewrite Z2Nat.id in R by (rewrite PR.braid_pos_lin by lia;
      destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); lia).
    apply R. rewrite PR.braid_pos_lin by lia.
    destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); lia. }
  pose proof (RD 0 ltac:(lia)) as RD0. pose proof (RD 1 ltac:(lia)) as RD1.
  pose proof (RD 2 ltac:(lia)) as RD2. cbn [Z.eqb Pos.eqb] in RD0, RD1, RD2. clear RD.
  remember (nth (Z.to_nat (50 + PSR.braid_pos s slot nch 0)) bs (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth (Z.to_nat (50 + PSR.braid_pos s slot nch 1)) bs (Z_to_bv 8 0)) as b1 eqn:E1.
  remember (nth (Z.to_nat (50 + PSR.braid_pos s slot nch 2)) bs (Z_to_bv 8 0)) as b2 eqn:E2.
  (* +0x94: the shadow byte of the low byte *)
  destruct (addr_one mk f LEN (50 + (3 * (s * nch + (slot - slot mod 2)) + (3 + slot mod 2))) AFk ltac:(lia))
    as (_ & k0 & MK0 & SK0).
  eapply (c1F RNG) with (A := f + (50 + (3 * (s * nch + (slot - slot mod 2)) + (3 + slot mod 2))));
    [ lia | lia | exact MK0 | exact SK0 | eapply rng_shadow_one; [exact RFS | lia] | intros y11 y30 ].
  clear MK0 SK0.
  (* +0xa8: the shadow byte of the middle byte, the low byte *)
  destruct (addr_one mk f LEN (50 + (3 * (s * nch + (slot - slot mod 2)) + 5 * (slot mod 2))) AFk ltac:(lia))
    as (_ & k1 & MK1 & SK1).
  eapply (c2F RNG) with (A := f + (50 + (3 * (s * nch + (slot - slot mod 2)) + 5 * (slot mod 2))))
    (D := f + (50 + (3 * (s * nch + (slot - slot mod 2)) + (3 + slot mod 2))));
    [ lia | lia | exact MK1 | exact SK1 | lia | lia | exact RD0
    | eapply rng_shadow_one; [exact RFS | lia] | eapply ExecF.rng_sub; [exact RF | lia | lia]
    | intros z11 z18 z31 Z11 ].
  clear MK1 SK1.
  (* +0xc8: the shadow byte of the high byte, the middle byte *)
  destruct (addr_one mk f LEN (50 + (3 * (s * nch + (slot - slot mod 2)) + (1 + slot mod 2))) AFk ltac:(lia))
    as (_ & k2 & MK2 & SK2).
  eapply (c3F RNG) with (A := f + (50 + (3 * (s * nch + (slot - slot mod 2)) + (1 + slot mod 2))))
    (D := f + (50 + (3 * (s * nch + (slot - slot mod 2)) + 5 * (slot mod 2))));
    [ lia | lia | exact MK2 | exact SK2 | exact Z11 | exact RD1
    | eapply rng_shadow_one; [exact RFS | lia] | eapply ExecF.rng_sub; [exact RF | lia | lia]
    | intros u18 u31 ].
  clear MK2 SK2.
  (* +0xe0: the shadow byte of v[s], the high byte *)
  destruct (addr_four mk v 48 (v + 4 * s) AVk ltac:(lia) ltac:(lia)) as (k3 & MK3 & SK3).
  eapply (c4F RNG) with (W := v + 4 * s)
    (D := f + (50 + (3 * (s * nch + (slot - slot mod 2)) + (1 + slot mod 2))));
    [ exact H10 | exact MK3 | exact SK3 | lia | lia | exact RD2
    | eapply rng_shadow_one; [exact RVS | lia] | eapply ExecF.rng_sub; [exact RF | lia | lia]
    | intros w18 w20 ].
  clear MK3 SK3.
  (* +0xf8 .. +0x128: the sample, the store, the next pointers *)
  pose proof (wr_at_store_ok rsegs mk v 48 (4 * s) 4%nat HW ltac:(lia) ltac:(cbn; lia)) as HS.
  apply PR.wv in H8, H10, H13, H14, H15, H29. subst x8 x10 x13 x14 x15 x29.
  do 10 step.
  (* the stored word is the sample, modulo 2^32 *)
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?W)) _) =>
    replace (le4 W) with (le4 (Z_to_bv 64 (PSR.rp_sample bs nch slot s))) end.
  2: { symmetry. apply PR.le4_eqm.
       cbv delta [sxb zxb]. rewrite !unsigned_lit_wrap, !PR.mod64_32.
       rewrite !PR.hi_lo, !PR.hi_mask. rewrite !Z.shiftl_mul_pow2 by lia.
       pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
       repeat rewrite (Z.mod_small _ (2^64)) by zrange.
       unfold PSR.rp_sample. cbv beta zeta. rewrite <- E0, <- E1, <- E2.
       apply PR.sample_val. }
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mk0 ?aa ?wb) _) =>
    assert (INV2 : INVR (write_to_mem mk0 aa wb) (S (Z.to_nat s)));
    [ unfold INVR; split; [|split; [|split; [|split; [|split; [|split]]]]]
    | set (mk2 := write_to_mem mk0 aa wb) in *; clearbody mk2 ]
  end.
  { apply bytes_at_write_other; [exact HBB | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  { apply rw_cells_frame;
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
  clear HBB FR ST HW MU WM HOUT HS AFk AVk.
  step. step. step. if_cases HE.
  - (* another sample *)
    zify_cond HE. try rewrite !unsigned_lit in HE by lia.
    eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1) mk2);
      [ reflexivity | lia
      | repeat (rewrite unsigned_lit by lia); lia
      | repeat (rewrite unsigned_lit by lia); lia
      | repeat (rewrite unsigned_lit by lia); lia
      | repeat (rewrite unsigned_lit by lia);
        replace ((s + 1) * nch) with (s * nch + nch) by ring; lia
      | replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) by lia; exact INV2 ].
  - (* the twelfth sample is written: leave the loop *)
    zify_cond HE. try rewrite !unsigned_lit in HE by lia.
    step. apply sr_exit. replace 12%nat with (S (Z.to_nat s)) by lia. exact INV2.
Qed.

End Loop.

Ltac curmemF k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Theorem rp_slot_read_holds_F : rp_slot_read_F_holds_stmt.
Proof.
  unfold rp_slot_read_F_holds_stmt. intros HSW.
  unfold rp_slot_width_contract_F, RP_SLOT_WIDTH, RP_SLOT_WIDTH_STK, RP_SLOT_WIDTH_FRAME, RP_FRAME_CHANNELS_FRAME,
    RP_SW_OFF, RP_SW_LEN in HSW.
  unfold rp_slot_read_contract_F, RP_SLOT_READ, RP_SLOT_READ_STK, RP_SLOT_READ_FRAME, RP_SLOT_WIDTH_STK,
    RP_SLOT_WIDTH_FRAME, RP_FRAME_CHANNELS_FRAME, RP_SLOT_READ_VLEN, RP_AUDIO_OFF.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    HM HT HK ST LO APS1 APS2 CELLS OC HB HV RFR RGOT RCELL OCON RCON RBUF RV.
  change (48 + (16 + 16)) with 80 in *.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof (u64_range a3) as Ra3.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold off_stk, GOT_CELL_K, MIDEND in OC.
  pose proof (conj HM (conj HT (conj HK CELLS))) as PK. clear HM HT HK CELLS.
  unfold WIRE_RFC_CONSTS in OCON, RCON. rewrite !Forall_cons_iff in OCON, RCON. cbn [fst snd] in OCON, RCON.
  destruct OCON as (OM & OK & OT & _). destruct RCON as (RM & RK & RT & _).
  unfold off_stk, A_M, A_T, A_K36 in OM, OK, OT.
  unfold GOT_CELL_K in RGOT. unfold CELL_K in RCELL.
  carve_frame 48%nat ST.
  do 9 step.
  destruct PK as (HM & HT & HK & CELLS).
  curmemF ltac:(fun mm => assert (CELLS1 : asan_cells mm)
    by (eapply asan_cells_munch; [exact CELLS | exact MU | unfold MIDEND, GOT_CELL_K; lia])).
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 3 step. clear RDG RDS CK GCK. do 3 step.
  match goal with MU' : munch _ m ?m1 |- _ => rename m1 into mf end.
  pose proof (bytes_tp m mf _ _ A_M (le8 (Z_to_bv 64 KM)) MU ltac:(rewrite length_le8; unfold A_M; lia) HM) as HM1.
  pose proof (bytes_tp m mf _ _ A_T (le8 (Z_to_bv 64 KT)) MU ltac:(rewrite length_le8; unfold A_T; lia) HT) as HT1.
  pose proof (bytes_tp m mf _ _ A_K36 (le8 (Z_to_bv 64 K36)) MU ltac:(rewrite length_le8; unfold A_K36; lia) HK) as HK1.
  (* +0x38: rp_slot_width by its footprint contract on [sp - 80, sp - 48) *)
  eapply evtF_cut.
  { eapply HSW with (lo := lo) (bs := bs).
    - exact HM1.
    - exact HT1.
    - exact HK1.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp + -48 - (16 + 16)) with (bv_unsigned sp - 80) by lia.
      exact APS1.
    - rewrite unsigned_lit by lia. apply (app_win (bv_unsigned sp) 80); [lia | exact APS1 | exact APS2 | lia].
    - exact CELLS1.
    - unfold off_stk, GOT_CELL_K. rewrite unsigned_lit by lia. lia.
    - unfold off_stk, CELL_K. rewrite unsigned_lit by lia. lia.
    - intros HN. destruct (HB HN) as (HLEN & BB & DB & AB). unfold off_stk in DB.
      pose proof (bytes_at_bound _ _ _ _ BB) as BBB.
      split; [lia|]. split; [eapply bytes_tp; [exact MU | lia | exact BB]|].
      split; [unfold off_stk; rewrite unsigned_lit by lia; lia|].
      eapply addr_munch_app; [eapply addr_sub; [exact AB | lia | lia | lia] | exact MU |].
      intros x Hx. cbn [outside]. split; [|exact I].
      exact (win_out (bv_unsigned sp) 80 x ltac:(lia) APS1 APS2 Hx).
    - rewrite unsigned_lit by lia. eapply ExecF.rng_sub; [exact RFR | lia | lia].
    - exact RGOT.
    - exact RCELL.
    - unfold WIRE_RFC_CONSTS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        cbn [fst snd]; unfold off_stk, A_M, A_T, A_K36; rewrite unsigned_lit by lia; lia.
    - unfold WIRE_RFC_CONSTS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        cbn [fst snd]; assumption.
    - intros HN. destruct (HB HN) as (HLEN & BB & DB & AB). destruct (RBUF HN) as (RB & RS).
      eapply ExecF.rng_sub; [exact RB | lia | lia].
    - intros HN. destruct (HB HN) as (HLEN & BB & DB & AB). destruct (RBUF HN) as (RB & RS).
      destruct AB as (P0 & N0 & PE & _).
      apply (shadow_rng_sub RNG (bv_unsigned a0) (Z.of_nat (length bs))); [exact RS | lia | lia | lia]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2
    & WM2 & ST2).
  rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU2, ST2 by lia.
  replace (ret_pc (Z_to_bv 64 529992)) with (Z_to_bv 64 529992) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (MU3 : munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m2).
  { eapply munch_trans; [exact MU|].
    apply (munch_weaken [(bv_unsigned sp + -48 - (16 + 16), bv_unsigned sp + -48)]); [|exact MU2].
    intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; [lia | exact I]. }
  assert (WM3 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FR2.
  clear FR MU WM MU2 WM2 HM1 HT1 HK1 CELLS1.
  pose proof (PR.sw_model_range (bv_unsigned a1) bs (bv_signed a2)) as SWR.
  step. if_cases HOK.
  - (* +0x16c: the width is negative, nothing is read and nothing is written *)
    zify_cond HOK.
    assert (HNEG : PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) = -1)
      by (destruct SWR as [E|E]; [exact E | try rewrite unsigned_lit in HOK by lia; lia]).
    do 9 step.
    replace (PSR.rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)) with 0
      by (unfold PSR.rp_slot_read_model; rewrite HNEG; reflexivity).
    rewrite HNEG. cbn [Z.leb].
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evtF_done. do 15 eexists. split; [reflexivity|].
    split; [exact WM3|]. split; [exact ST2|]. exact MU3.
  - (* +0x40 .. +0x90: the width is a channel count; the loop reads and writes the twelve samples *)
    zify_cond HOK.
    assert (HM0 : 2 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) <= 40)
      by (destruct SWR as [E|E]; [rewrite E in HOK; rewrite ?unsigned_lit in HOK by lia; lia | lia]).
    destruct (PR.sw_geom (bv_unsigned a1) bs (bv_signed a2) ltac:(lia) ltac:(lia)) as (G1 & G2 & G3 & G4).
    assert (HN50 : 50 <= bv_unsigned a1) by lia.
    destruct (HB HN50) as (HLEN & BB & DB & AB). unfold off_stk in DB.
    destruct (HV ltac:(lia)) as (HW & DJV & DJFV & AVV). unfold off_stk in DJV.
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
    pose proof (Z.mod_pos_bound (bv_signed a2) 2 ltac:(lia)) as Rm2.
    do 21 step.
    rewrite ?L1, ?L2. rewrite ?Z.shiftl_mul_pow2 by lia.
    eapply evtF_mono.
    + eapply sr_loop with (RNG := RNG) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
        (m := m) (bs := bs) (f := bv_unsigned a0) (v := bv_unsigned a3)
        (nch := PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (slot := bv_signed a2)
        (lo := lo) (K := 12%nat) (s := 0).
      all: try lia.
      all: try assumption.
      all: try (solve [ lazymatch goal with |- @eq Z (bv_unsigned _) _ => idtac end; rw_inner_lit; lia ]).
      all: try (solve [ apply PR.seqz5; lia ]).
      all: try reflexivity.
      (* the loop invariant at the first sample *)
      unfold INVR. split; [|split; [|split; [|split; [|split; [|split]]]]].
      * eapply bytes_at_transport; [exact BB | exact MU3 | cbn [disjoint_from]; split; [lia | exact I]].
      * exact FR2.
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
