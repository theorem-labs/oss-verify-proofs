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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/rp_hot_clamp_FW.v, with its module paths, module names and numbers changed; 367 of its 442 lines of code are new or changed and 467 lines of the source are left out. *)
(* The footprint walk of reac-repacer/fuzz_wire's rp_meter_counter in image B, against the frozen
   lib/B/Prog/rp_meter_counter_F_c.v rp_meter_counter_contract_F (= lib/B/Prog/rp_meter_counter_cg.v
   wire_rp_meter_counter_holds_stmt). No released ASan walk of this function exists. The form of the file is
   reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_FW.v: a Section over the walk's states, one lemma per shadow check
   (ck_<pc>: the check returns to the access, so no report call is reached), segment lemmas with a continuation, and the
   contract proved over them; rd_all, shrd, shadow_frame, lts_sm and rng_one_shadow are copied from that file. The
   idioms of the early exits, the conditional reads and the conditional store are libreac/fuzz_decode's released
   lib/B/Prog/reac_frame_is_reac_F.v and reac_decode_F.v (if_cases / zify_cond on each branch, gen_addi / gen_shr /
   gen_add from this unit's lib/B/Prog/AsanKAProof.v, the store's facts moved by transport_chunks /
   footprint_after_store after the window is widened to ctr's two bytes), and lor_bytes16_z is this unit's
   lib/B/Prog/rp_counter_FW.v's. The model is the released plain contract's lib/Prog/rp_meter_counter_c.v (meter_eo,
   meter_ok, meter_value); its case lemmas eo_range .. ok_true are new. *)
(* rp_meter_counter of fuzz_wire.asan-ubsan (objdump of record sha256 440b9550f4f5; entry 0x81144, 0x1d0 bytes):
     0x81144 `addi sp, sp, -16`, 0x81148 `sd ra, 8(sp)`; 0x8114c / 0x81150 `li a3, 14` / `bltu a1, a3, 0x8128c`:
     n < 14 returns 0 (0x8128c `li a3, 0`, 0x81290 `mv a0, a3`, 0x81294 `ld ra, 8(sp)`, 0x81298 `addi sp, sp, 16`,
     0x8129c `ret`);
     0x81154 `beqz a0` and 0x81158 / 0x8115c `li a3, -12` / `bgeu a0, a3` (UBSan; `unimp` at 0x812a0): a0 <> 0 and
     f + 14 <= 2^64 (bytes_at's bound, length >= 14) make both fall through;
     0x81160 `auipc a3, 0x17`, 0x81164 `ld a3, 1816(a3)` (the GOT word 0x98878), 0x81168 `ld a4, 0(a3)` (the shadow base
     in 0xa07f8);
     0x8116c .. 0x8117c: the shadow byte of f + 12, `bnez a5, 0x812a4`, the check 0x812a4 / 0x812a8 returns to 0x81180
     (ck_8117c); 0x81180 `lbu a3, 0(a3)` (f[12]), 0x81184 / 0x81188 `li a5, 129` / `bne a3, a5, 0x811b0`;
     0x8118c / 0x81190 `li a3, -14` / `bltu a3, a0` (UBSan): falls through as above; 0x81194 .. 0x811a4: the shadow byte
     of f + 13 (ck_811a4); 0x811a8 `lbu a3, 0(a3)` (f[13]), 0x811ac `beqz a3, 0x811b8`;
     0x811b0 `li a5, 12`, 0x811b4 `j 0x811bc` / 0x811b8 `li a5, 16`: eo (seg_head);
     0x811bc .. 0x811cc `li a6, 1000`, `li a3, 0`, `bltu a1, a6, 0x81290`, `addi a6, a5, 6`, `bltu a1, a6, 0x81290`:
     n < 1000 returns 0, n < eo + 6 is never taken past n >= 1000;
     0x811d0 / 0x811d4 `not a3, a0` / `bltu a3, a5`, 0x811f8 `bgeu a5, a3`, 0x81220 `bltu a3, a1`, 0x8123c `bltu a3, a5`
     (UBSan): ~f >= 19 >= eo + 3 (bytes_at's bound, length >= 20) makes each fall through;
     0x811d8 .. 0x811e8 the shadow byte of f + eo (ck_811e8), 0x811ec `lbu a6, 0(a1)` (f[eo]), 0x811f0 / 0x811f4
     `li a7, 136` / `bne a6, a7, 0x8128c`; 0x811fc .. 0x8120c the shadow byte of f + eo + 1 (ck_8120c), 0x81210
     `lbu a1, 0(a1)` (f[eo + 1]), 0x81214 / 0x81218 `li a6, 25` / `bne a1, a6, 0x8128c`;
     0x8121c .. 0x81234 the shadow byte of f + eo + 2 (ck_81234); 0x81240 `beqz a2` and 0x81244 / 0x81248
     `andi a3, a2, 1` / `bnez a3` (UBSan): ctr <> 0 and ctr mod 2 = 0 make both fall through;
     0x8124c .. 0x81260 the shadow byte of f + eo + 3 (ck_81260), with 0x8125c `lbu a1, 0(a1)` (f[eo + 2]) before the
     check; 0x81264 .. 0x81274 the shadow byte of ctr (ck_81274: the 2-byte store check `andi a4, a2, 7`,
     `addi a4, a4, 1`, `blt a4, a3`), with 0x81270 `lbu a0, 0(a0)` (f[eo + 3]) before the check;
     0x81278 `slli a0, a0, 8`, 0x8127c `or a0, a0, a1`, 0x81280 `sh a0, 0(a2)`, 0x81284 `li a3, 1`, 0x81288 `j 0x81290`
     (seg_tail). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof rp_meter_counter_c rp_meter_counter_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_meter_counter_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

(* ---- memory, shadow and model helpers ---- *)

Lemma rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* a byte outside the window W of a run keeps its entry value (fuzz_uci rp_hot_clamp_FW.v shrd) *)
Lemma shrd : forall W m0 m S k (h : word), munch W m0 m -> outside W S ->
  mrd rsegs m0 (wa S) = Some k -> bv_unsigned h = S -> ov_read_bytes rsegs m h 1 = Some [k].
Proof.
  intros W m0 m S k h MU OUT M U. apply (rdw0 m h S k); [|exact U].
  unfold mrd in *. rewrite MU; [exact M|]. rewrite wa_unsigned; [exact OUT|]. rewrite <- U. apply u64_range.
Qed.

(* shadow bytes are not application memory: none lies in the frame (fuzz_uci rp_hot_clamp_FW.v shadow_frame) *)
Lemma shadow_frame : forall s x, app_mem (s + -16) -> app_mem (s - 1) -> app_mem x ->
  ~ (s + -16 <= shadow_addr x < s).
Proof.
  unfold app_mem, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros s x HA HB Hx.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lts_sm : forall (x : Z) (k : byte), 0 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

(* the shadow check of a 1-byte load at X, resp. of the 2-byte store at X, passes on shadow byte k *)
Definition shok1 (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 < bv_signed k.
Definition shok2 (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 + 1 < bv_signed k.

(* the shadow byte of a byte a inside an addressable range *)
Lemma ab_at : forall m p n a, addressable m p n -> p <= a < p + n ->
  app_mem a /\ exists k, mrd rsegs m (wa (shadow_addr a)) = Some k /\ shok1 k a.
Proof.
  intros m p n a (H0 & H1 & H2 & H) Ha.
  destruct (H (a - p) ltac:(lia)) as (Hap & k & Hk & Hok).
  replace (p + (a - p)) with a in Hap, Hk, Hok by lia.
  split; [exact Hap|]. exists k. split; [exact Hk|]. unfold shok1. unfold shadow_ok in Hok. lia.
Qed.

(* the shadow byte of ctr's two bytes: ctr is even, so both lie in one granule and the check of the store passes *)
Lemma ab_st2 : forall m c, addressable m c 2 -> c mod 2 = 0 ->
  app_mem c /\ exists k, mrd rsegs m (wa (shadow_addr c)) = Some k /\ shok2 k c.
Proof.
  intros m c (H0 & H1 & H2 & H) Hc.
  destruct (H 0 ltac:(lia)) as (Ha0 & _). rewrite Z.add_0_r in Ha0.
  destruct (H 1 ltac:(lia)) as (Ha1 & k & Hk & Hok).
  assert (E1 : (c + 1) / 8 = c / 8) by (Z.div_mod_to_equations; lia).
  assert (E2 : (c + 1) mod 8 = c mod 8 + 1) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
  split; [exact Ha0|]. exists k. split; [exact Hk|]. unfold shok2. lia.
Qed.

(* the one-byte window of the shadow range of [p, p + n) at the shadow byte of a (fuzz_uci rp_hot_clamp_FW.v) *)
Lemma rng_one_shadow : forall RNG p n a,
  rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> rng RNG (shadow_addr a) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in *.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply rng_sub; [exact H | lia | lia].
Qed.

(* the model's cases (lib/Prog/rp_meter_counter_c.v meter_eo, meter_ok, meter_value) *)
Lemma eo_range : forall n bs, PMC.meter_eo n bs = 12%nat \/ PMC.meter_eo n bs = 16%nat.
Proof. intros n bs. unfold PMC.meter_eo. destruct (_ && _ && _); [right|left]; reflexivity. Qed.

Lemma eo_12a : forall n bs, PMC.meter_byte bs 12 <> 0x81 -> PMC.meter_eo n bs = 12%nat.
Proof.
  intros n bs H. unfold PMC.meter_eo. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.

Lemma eo_12b : forall n bs, PMC.meter_byte bs 13 <> 0 -> PMC.meter_eo n bs = 12%nat.
Proof.
  intros n bs H. unfold PMC.meter_eo. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.

Lemma eo_16 : forall n bs, 14 <= n -> PMC.meter_byte bs 12 = 0x81 -> PMC.meter_byte bs 13 = 0 ->
  PMC.meter_eo n bs = 16%nat.
Proof.
  intros n bs Hn H12 H13. unfold PMC.meter_eo.
  rewrite (proj2 (Z.ltb_lt 13 n) ltac:(lia)), H12, H13. reflexivity.
Qed.

Lemma ok_lt1000 : forall n bs, n < 1000 -> PMC.meter_ok n bs = false.
Proof.
  intros n bs H. unfold PMC.meter_ok. cbv zeta.
  rewrite (proj2 (Z.leb_gt 1000 n) H), andb_false_r. reflexivity.
Qed.

Lemma ok_88 : forall n bs, PMC.meter_byte bs (PMC.meter_eo n bs) <> 0x88 -> PMC.meter_ok n bs = false.
Proof.
  intros n bs H. unfold PMC.meter_ok. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.

Lemma ok_19 : forall n bs, PMC.meter_byte bs (PMC.meter_eo n bs + 1) <> 0x19 -> PMC.meter_ok n bs = false.
Proof.
  intros n bs H. unfold PMC.meter_ok. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.

(* the value `or a0, a0, a1` leaves after `slli a0, a0, 8` of two zero-extended bytes (this unit's
   lib/B/Prog/rp_counter_FW.v lor_bytes16_z) *)
Lemma lor_bytes16_z : forall x y : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x) = bv_unsigned x + 256 * bv_unsigned y.
Proof.
  intros x y. pose proof (byte_range x). pose proof (byte_range y).
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned y) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
Qed.

Lemma ok_true : forall n bs, 1000 <= n -> Z.of_nat (PMC.meter_eo n bs) + 6 <= n ->
  PMC.meter_byte bs (PMC.meter_eo n bs) = 0x88 -> PMC.meter_byte bs (PMC.meter_eo n bs + 1) = 0x19 ->
  PMC.meter_ok n bs = true.
Proof.
  intros n bs H1 H2 H3 H4. unfold PMC.meter_ok. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2), H3, H4. reflexivity.
Qed.

(* `not a3, a0`: the register ~f, named w with U : bv_unsigned w = 2^64 - 1 - f *)
Ltac gen_not x w U := match goal with
  | |- context [Z_to_bv 64 (Z.lxor (bv_unsigned x) 18446744073709551615)] =>
      rewrite (zb_lxor_ones (bv_unsigned x) (u64_range x));
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (18446744073709551615 - bv_unsigned x))
                  = 18446744073709551615 - bv_unsigned x)
        by (apply unsigned_lit; pose proof (u64_range x); lia);
      remember (Z_to_bv 64 (18446744073709551615 - bv_unsigned x)) as w eqn:Ew; clear Ew
  end.

(* a branch that the premises refute: its taken side is absurd *)
Ltac nobr := let H := fresh "HB" in if_cases H; zify_cond H; [exfalso; lia|].

(* ---- tactics of the shadow checks ---- *)

(* a 1-byte load check: `bnez k`; `andi t, x, 7`; `blt t, k, back` *)
Local Ltac chk1 HX C K :=
  unfold shok1 in C;
  lazymatch type of C with bv_signed ?k = 0 \/ _ =>
  lazymatch type of HX with bv_unsigned _ = ?X =>
    step; rewrite sxb_eq0; destruct C as [C|C];
    [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply K
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
      step; step;
      let MB := fresh "MB" in
      pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
      rewrite land7, HX; rewrite (lts_sm (X mod 8) k) by lia;
      rewrite (proj2 (Z.ltb_lt _ _) C); apply K ]
  end end.

(* the 2-byte store check: `bnez k`; `andi t, x, 7`; `addi t, t, 1`; `blt t, k, back` *)
Local Ltac chk2 HX C K :=
  unfold shok2 in C;
  lazymatch type of C with bv_signed ?k = 0 \/ _ =>
  lazymatch type of HX with bv_unsigned _ = ?X =>
    step; rewrite sxb_eq0; destruct C as [C|C];
    [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply K
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
      step; step; step;
      let MB := fresh "MB" in
      pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
      rewrite land7, HX; rewrite (lts_sm (X mod 8 + 1) k) by lia;
      rewrite (proj2 (Z.ltb_lt _ _) C); apply K ]
  end end.

Section Walk.
Variables (RNG : footprint) (Q : machine_state -> Prop)
  (ra sp1 gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32).

(* the states of the walk: sp1 is the frame's sp; r0 .. r7 are a0 .. a7 *)
Local Abbreviation ST pc m r0 r1 r2 r3 r4 r5 r6 r7 :=
  (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 r5 r6 r7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* ---- the seven shadow checks ---- *)

(* 0x8117c: `bnez a5` on the shadow byte of f + 12 (a3); its check (`andi a6, a3, 7`; `blt a6, a5`) returns to
   0x81180: the `jal __asan_report_load1` at 0x812b0 is not reached. *)
Lemma ck_8117c : forall m (r0 r1 r2 r3 r4 r6 r7 : word) (k : byte) X,
  bv_unsigned r3 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x81180 m r0 r1 r2 r3 r4 (sxb k) v r7)) ->
  evtF rsegs RNG Q (ST 0x8117c m r0 r1 r2 r3 r4 (sxb k) r6 r7).
Proof. intros m r0 r1 r2 r3 r4 r6 r7 k X HX C K. chk1 HX C K. Qed.

(* 0x811a4: `bnez a5` on the shadow byte of f + 13 (a3); its check (`andi a6, a3, 7`; `blt a6, a5`) returns to
   0x811a8: the `jal __asan_report_load1` at 0x812c0 is not reached. *)
Lemma ck_811a4 : forall m (r0 r1 r2 r3 r4 r6 r7 : word) (k : byte) X,
  bv_unsigned r3 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x811a8 m r0 r1 r2 r3 r4 (sxb k) v r7)) ->
  evtF rsegs RNG Q (ST 0x811a4 m r0 r1 r2 r3 r4 (sxb k) r6 r7).
Proof. intros m r0 r1 r2 r3 r4 r6 r7 k X HX C K. chk1 HX C K. Qed.

(* 0x811e8: `bnez a6` on the shadow byte of f + eo (a1); its check (`andi a7, a1, 7`; `blt a7, a6`) returns to
   0x811ec: the `jal __asan_report_load1` at 0x812d0 is not reached. *)
Lemma ck_811e8 : forall m (r0 r1 r2 r3 r4 r5 r7 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x811ec m r0 r1 r2 r3 r4 r5 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x811e8 m r0 r1 r2 r3 r4 r5 (sxb k) r7).
Proof. intros m r0 r1 r2 r3 r4 r5 r7 k X HX C K. chk1 HX C K. Qed.

(* 0x8120c: `bnez a6` on the shadow byte of f + eo + 1 (a1); its check (`andi a7, a1, 7`; `blt a7, a6`) returns to
   0x81210: the `jal __asan_report_load1` at 0x812e0 is not reached. *)
Lemma ck_8120c : forall m (r0 r1 r2 r3 r4 r5 r7 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x81210 m r0 r1 r2 r3 r4 r5 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x8120c m r0 r1 r2 r3 r4 r5 (sxb k) r7).
Proof. intros m r0 r1 r2 r3 r4 r5 r7 k X HX C K. chk1 HX C K. Qed.

(* 0x81234: `bnez a6` on the shadow byte of f + eo + 2 (a1); its check (`andi a7, a1, 7`; `blt a7, a6`) returns to
   0x81238: the `jal __asan_report_load1` at 0x812f0 is not reached. *)
Lemma ck_81234 : forall m (r0 r1 r2 r3 r4 r5 r7 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x81238 m r0 r1 r2 r3 r4 r5 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x81234 m r0 r1 r2 r3 r4 r5 (sxb k) r7).
Proof. intros m r0 r1 r2 r3 r4 r5 r7 k X HX C K. chk1 HX C K. Qed.

(* 0x81260: `bnez a3` on the shadow byte of f + eo + 3 (a0); its check (`andi a5, a0, 7`; `blt a5, a3`) returns to
   0x81264: the `jal __asan_report_load1` at 0x812fc is not reached. *)
Lemma ck_81260 : forall m (r0 r1 r2 r4 r5 r6 r7 : word) (k : byte) X,
  bv_unsigned r0 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x81264 m r0 r1 r2 (sxb k) r4 v r6 r7)) ->
  evtF rsegs RNG Q (ST 0x81260 m r0 r1 r2 (sxb k) r4 r5 r6 r7).
Proof. intros m r0 r1 r2 r4 r5 r6 r7 k X HX C K. chk1 HX C K. Qed.

(* 0x81274: `bnez a3` on the shadow byte of ctr (a2); its check (`andi a4, a2, 7`; `addi a4, a4, 1`; `blt a4, a3`)
   returns to 0x81278: the `jal __asan_report_store2` at 0x81310 is not reached. *)
Lemma ck_81274 : forall m (r0 r1 r2 r4 r5 r6 r7 : word) (k : byte) X,
  bv_unsigned r2 = X -> shok2 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x81278 m r0 r1 r2 (sxb k) v r5 r6 r7)) ->
  evtF rsegs RNG Q (ST 0x81274 m r0 r1 r2 (sxb k) r4 r5 r6 r7).
Proof. intros m r0 r1 r2 r4 r5 r6 r7 k X HX C K. chk2 HX C K. Qed.

(* apply a check lemma at its `bnez`: the access address is X, the check passes by C *)
Local Ltac ck L X C v :=
  refine (L _ _ _ _ _ _ _ _ _ X _ C _); [ first [eassumption | reflexivity | lia] | intros v ].

(* ---- the walk past n >= 14, from the load of f[12] on ---- *)

Variables (a0 a1 a2 a7 sp0 : word) (bs : list byte) (m0 : word -> option byte) (lo : Z) (jk : list byte).
Hypotheses (HN : 14 <= bv_unsigned a1) (L14 : (14 <= length bs)%nat)
  (L20 : 1000 <= bv_unsigned a1 -> (20 <= length bs)%nat)
  (BA : bytes_at rsegs m0 (bv_unsigned a0) bs)
  (APS1 : app_mem (bv_unsigned sp0 + -16)) (APS2 : app_mem (bv_unsigned sp0 - 1))
  (D12 : off_stk sp0 16 (bv_unsigned a0 + 12) 2)
  (D20 : 1000 <= bv_unsigned a1 -> off_stk sp0 16 (bv_unsigned a0 + 12) 8)
  (AB12 : addressable m0 (bv_unsigned a0 + 12) 2)
  (AB20 : 1000 <= bv_unsigned a1 -> addressable m0 (bv_unsigned a0 + 12) 8)
  (R12 : rng RNG (bv_unsigned a0 + 12) 2)
  (RS12 : rng RNG (shadow_addr (bv_unsigned a0 + 12))
            (shadow_addr (bv_unsigned a0 + 12 + 2 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1))
  (R20 : 1000 <= bv_unsigned a1 -> rng RNG (bv_unsigned a0 + 12) 8)
  (RS20 : 1000 <= bv_unsigned a1 ->
            rng RNG (shadow_addr (bv_unsigned a0 + 12))
              (shadow_addr (bv_unsigned a0 + 12 + 8 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1))
  (UCT : PMC.meter_ok (bv_unsigned a1) bs = true -> bv_unsigned a2 <> 0 /\ bv_unsigned a2 mod 2 = 0)
  (HW : PMC.meter_ok (bv_unsigned a1) bs = true -> wr_at rsegs m0 (bv_unsigned a2) 2)
  (DCT : PMC.meter_ok (bv_unsigned a1) bs = true -> off_stk sp0 16 (bv_unsigned a2) 2)
  (ACT : PMC.meter_ok (bv_unsigned a1) bs = true -> addressable m0 (bv_unsigned a2) 2)
  (RCT : PMC.meter_ok (bv_unsigned a1) bs = true -> rng RNG (bv_unsigned a2) 2)
  (RSCT : PMC.meter_ok (bv_unsigned a1) bs = true ->
            rng RNG (shadow_addr (bv_unsigned a2))
              (shadow_addr (bv_unsigned a2 + 2 - 1) - shadow_addr (bv_unsigned a2) + 1)).

(* the frame's window *)
Local Abbreviation FW := [(bv_unsigned sp0 + -16, bv_unsigned sp0)].

(* a shadow byte read in the walk's memory: its entry value, through the window *)
Lemma rdsh : forall m (h : word) X k, munch FW m0 m -> app_mem X ->
  mrd rsegs m0 (wa (shadow_addr X)) = Some k -> bv_unsigned h = shadow_addr X -> ov_read_bytes rsegs m h 1 = Some [k].
Proof.
  intros m h X k MU AX M U. apply (shrd _ m0 m (shadow_addr X) k h MU); [|exact M|exact U].
  cbn [outside]. split; [|exact I]. apply shadow_frame; assumption.
Qed.

(* a byte of f read in the walk's memory: its entry value, through the window *)
Lemma rdf : forall m (w : word) (i : nat), munch FW m0 m -> (i < length bs)%nat ->
  (bv_unsigned a0 + Z.of_nat i + 1 <= bv_unsigned sp0 + -16 \/ bv_unsigned sp0 <= bv_unsigned a0 + Z.of_nat i) ->
  bv_unsigned w = bv_unsigned a0 + Z.of_nat i -> ov_read_bytes rsegs m w 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m w i MU Hi D U.
  apply (shrd _ m0 m (bv_unsigned a0 + Z.of_nat i) _ w MU); [| apply bytes_nth; assumption | exact U].
  cbn [outside]. split; [lia | exact I].
Qed.

(* 0x81180-0x811b8: f[12], and f[13] when f[12] = 0x81, give eo (meter_eo): 16 when f[12] = 0x81 and f[13] = 0, else
   12. The continuation K is 0x811bc, with a5 = eo. *)
Lemma seg_head : forall m (w12 r6 : word) (k12 : byte),
  bv_unsigned w12 = bv_unsigned a0 + 12 -> munch FW m0 m ->
  (forall r3 r5 r6' : word, bv_unsigned r5 = Z.of_nat (PMC.meter_eo (bv_unsigned a1) bs) ->
     evtF rsegs RNG Q (ST 0x811bc m a0 a1 a2 r3 (Z_to_bv 64 2147450880) r5 r6' a7)) ->
  evtF rsegs RNG Q (ST 0x81180 m a0 a1 a2 w12 (Z_to_bv 64 2147450880) (sxb k12) r6 a7).
Proof.
  intros m w12 r6 k12 U12 MU K.
  pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1. pose proof (u64_range sp0) as Rsp.
  pose proof BA as (BA0 & BA1 & _).
  pose proof D12 as D12'. unfold off_stk in D12'.
  (* lbu a3, 0(a3): f[12]; li a5, 129; bne a3, a5 *)
  assert (RW : rng RNG (bv_unsigned w12) 1) by (apply (rng_sub RNG _ _ _ _ R12); lia).
  pose proof (rdf m w12 12 MU ltac:(lia) ltac:(lia) ltac:(lia)) as R. step. clear R RW.
  step. step. if_cases HC; zify_cond HC; rewrite ?zxb_u in HC.
  { (* f[12] <> 0x81: li a5, 12; j 0x811bc *)
    step. step. apply K.
    rewrite (eo_12a (bv_unsigned a1) bs ltac:(unfold PMC.meter_byte; lia)). reflexivity. }
  (* li a3, -14; bltu a3, a0 (UBSan): f + 14 <= 2^64 *)
  step. step. nobr.
  (* f + 13: addi a3, a0, 13; srli a5, a3, 3; add a5, a5, a4; lb a5, 0(a5); its check *)
  step. gen_addi a0 w13 U13. step. gen_shr w13 g13 G13. step. gen_addi g13 h13 H13.
  destruct (ab_at m0 _ 2 (bv_unsigned a0 + 13) AB12 ltac:(lia)) as (AP13 & k13 & MK13 & C13).
  pose proof (rng_one_shadow RNG _ 2 (bv_unsigned a0 + 13) RS12 ltac:(lia)) as RS13.
  assert (RH : rng RNG (bv_unsigned h13) 1)
    by (replace (bv_unsigned h13) with (shadow_addr (bv_unsigned a0 + 13)) by (unfold shadow_addr, ASAN_K; lia);
        exact RS13).
  pose proof (rdsh m h13 _ k13 MU AP13 MK13 ltac:(unfold shadow_addr, ASAN_K; lia)) as R. step. clear R RH.
  ck ck_811a4 (bv_unsigned a0 + 13) C13 v.
  (* lbu a3, 0(a3): f[13]; beqz a3 *)
  assert (RW : rng RNG (bv_unsigned w13) 1) by (apply (rng_sub RNG _ _ _ _ R12); lia).
  pose proof (rdf m w13 13 MU ltac:(lia) ltac:(lia) ltac:(lia)) as R. step. clear R RW.
  step. if_cases HD; zify_cond HD; rewrite ?zxb_u in HD.
  - (* f[13] = 0: li a5, 16 *)
    step. apply K.
    rewrite (eo_16 (bv_unsigned a1) bs HN ltac:(unfold PMC.meter_byte; lia) ltac:(unfold PMC.meter_byte; lia)).
    reflexivity.
  - (* f[13] <> 0: li a5, 12; j 0x811bc *)
    step. step. apply K.
    rewrite (eo_12b (bv_unsigned a1) bs ltac:(unfold PMC.meter_byte; lia)). reflexivity.
Qed.

(* 0x811bc-0x81288: n < 1000 returns 0; else the bytes eo, eo + 1 decide; when they match the counter is stored at
   ctr and the result is 1. The continuation K is the shared exit at 0x81290 (`mv a0, a3`). *)
Lemma seg_tail : forall m (r3 r5 r6 : word),
  bv_unsigned r5 = Z.of_nat (PMC.meter_eo (bv_unsigned a1) bs) ->
  rw_cells rsegs m (bv_unsigned sp0 + -16) [CB 8 jk; C8 ra] -> stk rsegs m lo (bv_unsigned sp0 + -16) ->
  munch FW m0 m -> wmono rsegs m0 m ->
  (forall m' (r0' r1' r3' r4' r5' r6' r7' : word),
     r3' = Z_to_bv 64 (if PMC.meter_ok (bv_unsigned a1) bs then 1 else 0) ->
     rw_cells rsegs m' (bv_unsigned sp0 + -16) [CB 8 jk; C8 ra] -> stk rsegs m' lo (bv_unsigned sp0 + -16) ->
     wmono rsegs m0 m' ->
     (if PMC.meter_ok (bv_unsigned a1) bs
      then munch [(bv_unsigned sp0 + -16, bv_unsigned sp0); (bv_unsigned a2, bv_unsigned a2 + 2)] m0 m' /\
           bytes_at rsegs m' (bv_unsigned a2) (le2 (Z_to_bv 64 (PMC.meter_value (bv_unsigned a1) bs)))
      else munch FW m0 m') ->
     evtF rsegs RNG Q (ST 0x81290 m' r0' r1' a2 r3' r4' r5' r6' r7')) ->
  evtF rsegs RNG Q (ST 0x811bc m a0 a1 a2 r3 (Z_to_bv 64 2147450880) r5 r6 a7).
Proof.
  intros m r3 r5 r6 E5 FR SK MU WM K.
  pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1. pose proof (u64_range a2) as Ra2.
  pose proof (u64_range sp0) as Rsp.
  pose proof BA as (BA0 & BA1 & _).
  remember (PMC.meter_eo (bv_unsigned a1) bs) as eo eqn:Eeo.
  assert (EO : eo = 12%nat \/ eo = 16%nat) by (subst eo; apply eo_range).
  (* li a6, 1000; li a3, 0; bltu a1, a6 *)
  step. step. step. if_cases H1; zify_cond H1.
  { (* n < 1000: the exit at 0x81290 with a3 = 0 *)
    assert (OK : PMC.meter_ok (bv_unsigned a1) bs = false) by (apply ok_lt1000; lia).
    eapply K; [rewrite OK; reflexivity | exact FR | exact SK | exact WM | rewrite OK; exact MU]. }
  pose proof (L20 H1) as L20'. pose proof (D20 H1) as D20'. pose proof (AB20 H1) as AB20'.
  pose proof (R20 H1) as R20'. pose proof (RS20 H1) as RS20'.
  unfold off_stk in D20'.
  assert (HA : bv_unsigned a0 + 20 <= 2^64) by lia.
  (* addi a6, a5, 6; bltu a1, a6: never taken past n >= 1000 *)
  step. gen_addi r5 w6 U6. step. nobr.
  (* not a3, a0; bltu a3, a5 (UBSan): ~f >= 19 > eo *)
  step. gen_not a0 wn UN. step. nobr.
  (* f + eo: add a1, a0, a5; srli a6, a1, 3; add a6, a6, a4; lb a6, 0(a6); its check *)
  step. gen_add a0 r5 we0 UE0. step. gen_shr we0 ge0 GE0. step. gen_addi ge0 he0 HE0.
  destruct (ab_at m0 _ 8 (bv_unsigned a0 + Z.of_nat eo) AB20' ltac:(lia)) as (AP0 & k0 & MK0 & C0).
  pose proof (rng_one_shadow RNG _ 8 (bv_unsigned a0 + Z.of_nat eo) RS20' ltac:(lia)) as RS0.
  assert (RH : rng RNG (bv_unsigned he0) 1)
    by (replace (bv_unsigned he0) with (shadow_addr (bv_unsigned a0 + Z.of_nat eo))
          by (unfold shadow_addr, ASAN_K; lia); exact RS0).
  pose proof (rdsh m he0 _ k0 MU AP0 MK0 ltac:(unfold shadow_addr, ASAN_K; lia)) as R. step. clear R RH.
  ck ck_811e8 (bv_unsigned a0 + Z.of_nat eo) C0 v0.
  (* lbu a6, 0(a1): f[eo]; li a7, 136; bne a6, a7 *)
  assert (RW : rng RNG (bv_unsigned we0) 1) by (apply (rng_sub RNG _ _ _ _ R20'); lia).
  pose proof (rdf m we0 eo MU ltac:(lia) ltac:(lia) ltac:(lia)) as R. step. clear R RW.
  step. step. if_cases H2; zify_cond H2; rewrite zxb_u in H2.
  { (* f[eo] <> 0x88: the exit at 0x8128c (`li a3, 0`) *)
    assert (OK : PMC.meter_ok (bv_unsigned a1) bs = false)
      by (apply ok_88; rewrite <- Eeo; unfold PMC.meter_byte; exact H2).
    step. eapply K; [rewrite OK; reflexivity | exact FR | exact SK | exact WM | rewrite OK; exact MU]. }
  (* bgeu a5, a3 (UBSan): eo < ~f *)
  step. nobr.
  (* f + eo + 1: addi a1, a1, 1; srli a6, a1, 3; add a6, a6, a4; lb a6, 0(a6); its check *)
  step. gen_addi we0 we1 UE1. step. gen_shr we1 ge1 GE1. step. gen_addi ge1 he1 HE1.
  destruct (ab_at m0 _ 8 (bv_unsigned a0 + Z.of_nat eo + 1) AB20' ltac:(lia)) as (AP1 & k1 & MK1 & C1).
  pose proof (rng_one_shadow RNG _ 8 (bv_unsigned a0 + Z.of_nat eo + 1) RS20' ltac:(lia)) as RS1.
  assert (RH : rng RNG (bv_unsigned he1) 1)
    by (replace (bv_unsigned he1) with (shadow_addr (bv_unsigned a0 + Z.of_nat eo + 1))
          by (unfold shadow_addr, ASAN_K; lia); exact RS1).
  pose proof (rdsh m he1 _ k1 MU AP1 MK1 ltac:(unfold shadow_addr, ASAN_K; lia)) as R. step. clear R RH.
  ck ck_8120c (bv_unsigned a0 + Z.of_nat eo + 1) C1 v1.
  (* lbu a1, 0(a1): f[eo + 1]; li a6, 25; bne a1, a6 *)
  assert (RW : rng RNG (bv_unsigned we1) 1) by (apply (rng_sub RNG _ _ _ _ R20'); lia).
  pose proof (rdf m we1 (eo + 1) MU ltac:(lia) ltac:(lia) ltac:(lia)) as R. step. clear R RW.
  step. step. if_cases H3; zify_cond H3; rewrite zxb_u in H3.
  { (* f[eo + 1] <> 0x19: the exit at 0x8128c *)
    assert (OK : PMC.meter_ok (bv_unsigned a1) bs = false)
      by (apply ok_19; rewrite <- Eeo; unfold PMC.meter_byte; exact H3).
    step. eapply K; [rewrite OK; reflexivity | exact FR | exact SK | exact WM | rewrite OK; exact MU]. }
  (* it counts *)
  assert (OK : PMC.meter_ok (bv_unsigned a1) bs = true)
    by (apply ok_true; rewrite <- ?Eeo; unfold PMC.meter_byte; lia).
  destruct (UCT OK) as (CNZ & CAL).
  pose proof (HW OK) as WA0. pose proof (DCT OK) as DC. pose proof (ACT OK) as ACT'.
  pose proof (RCT OK) as RC. pose proof (RSCT OK) as RSC.
  unfold off_stk in DC.
  (* addi a1, a5, 2; bltu a3, a1 (UBSan) *)
  step. gen_addi r5 w2 U2. step. nobr.
  (* f + eo + 2: add a1, a0, a1; srli a6, a1, 3; add a6, a6, a4; lb a6, 0(a6); its check *)
  step. gen_add a0 w2 we2 UE2. step. gen_shr we2 ge2 GE2. step. gen_addi ge2 he2 HE2.
  destruct (ab_at m0 _ 8 (bv_unsigned a0 + Z.of_nat eo + 2) AB20' ltac:(lia)) as (AP2 & k2 & MK2 & C2).
  pose proof (rng_one_shadow RNG _ 8 (bv_unsigned a0 + Z.of_nat eo + 2) RS20' ltac:(lia)) as RS2.
  assert (RH : rng RNG (bv_unsigned he2) 1)
    by (replace (bv_unsigned he2) with (shadow_addr (bv_unsigned a0 + Z.of_nat eo + 2))
          by (unfold shadow_addr, ASAN_K; lia); exact RS2).
  pose proof (rdsh m he2 _ k2 MU AP2 MK2 ltac:(unfold shadow_addr, ASAN_K; lia)) as R. step. clear R RH.
  ck ck_81234 (bv_unsigned a0 + Z.of_nat eo + 2) C2 v2.
  (* addi a5, a5, 3; bltu a3, a5 (UBSan) *)
  step. gen_addi r5 w3 U3. step. nobr.
  (* beqz a2; andi a3, a2, 1; bnez a3 (UBSan): ctr <> 0, ctr even *)
  step. nobr.
  assert (L1 : Z.land (bv_unsigned a2) 1 = 0)
    by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; exact CAL).
  step. rewrite ?L1. step. nobr.
  (* f + eo + 3: add a0, a0, a5; srli a3, a0, 3; add a3, a3, a4; lb a3, 0(a3) *)
  step. gen_add a0 w3 we3 UE3. step. gen_shr we3 ge3 GE3. step. gen_addi ge3 he3 HE3.
  destruct (ab_at m0 _ 8 (bv_unsigned a0 + Z.of_nat eo + 3) AB20' ltac:(lia)) as (AP3 & k3 & MK3 & C3).
  pose proof (rng_one_shadow RNG _ 8 (bv_unsigned a0 + Z.of_nat eo + 3) RS20' ltac:(lia)) as RS3.
  assert (RH : rng RNG (bv_unsigned he3) 1)
    by (replace (bv_unsigned he3) with (shadow_addr (bv_unsigned a0 + Z.of_nat eo + 3))
          by (unfold shadow_addr, ASAN_K; lia); exact RS3).
  pose proof (rdsh m he3 _ k3 MU AP3 MK3 ltac:(unfold shadow_addr, ASAN_K; lia)) as R. step. clear R RH.
  (* lbu a1, 0(a1): f[eo + 2]; then the check of f + eo + 3 *)
  assert (RW : rng RNG (bv_unsigned we2) 1) by (apply (rng_sub RNG _ _ _ _ R20'); lia).
  pose proof (rdf m we2 (eo + 2) MU ltac:(lia) ltac:(lia) ltac:(lia)) as R. step. clear R RW.
  ck ck_81260 (bv_unsigned a0 + Z.of_nat eo + 3) C3 v3.
  (* ctr: srli a3, a2, 3; add a3, a3, a4; lb a3, 0(a3) *)
  destruct (ab_st2 m0 _ ACT' CAL) as (APC & kc & MKC & CC).
  pose proof (rng_one_shadow RNG _ 2 (bv_unsigned a2) RSC ltac:(lia)) as RSC1.
  step. gen_shr a2 gc GC. step. gen_addi gc hc HC.
  assert (RH : rng RNG (bv_unsigned hc) 1)
    by (replace (bv_unsigned hc) with (shadow_addr (bv_unsigned a2)) by (unfold shadow_addr, ASAN_K; lia); exact RSC1).
  pose proof (rdsh m hc _ kc MU APC MKC ltac:(unfold shadow_addr, ASAN_K; lia)) as R. step. clear R RH.
  (* lbu a0, 0(a0): f[eo + 3]; then the check of ctr *)
  assert (RW : rng RNG (bv_unsigned we3) 1) by (apply (rng_sub RNG _ _ _ _ R20'); lia).
  pose proof (rdf m we3 (eo + 3) MU ltac:(lia) ltac:(lia) ltac:(lia)) as R. step. clear R RW.
  ck ck_81274 (bv_unsigned a2) CC v4.
  (* slli a0, a0, 8; or a0, a0, a1: the counter, meter_value *)
  step. step.
  unfold zxb. rewrite !zxb_u, lor_bytes16_z.
  replace (bv_unsigned (nth (eo + 2) bs (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (eo + 3) bs (Z_to_bv 8 0)))
    with (PMC.meter_value (bv_unsigned a1) bs)
    by (unfold PMC.meter_value, PMC.meter_byte; cbv zeta; rewrite <- Eeo; reflexivity).
  (* sh a0, 0(a2): ctr's two bytes; the window takes them first *)
  assert (WA : wr_at rsegs m (bv_unsigned a2) 2) by (eapply wr_at_transport; [exact WA0 | exact WM]).
  pose proof (wr_at_store_ok rsegs m (bv_unsigned a2) 2 0 2 WA ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r, (wa_of_var a2 (bv_unsigned a2) eq_refl) in HS.
  assert (MU2 : munch [(bv_unsigned sp0 + -16, bv_unsigned sp0); (bv_unsigned a2, bv_unsigned a2 + 2)] m0 m)
    by (apply (munch_weaken FW _ m0 m); [intros x Hx; cbn [outside] in *; tauto | exact MU]).
  clear MU.
  pose proof (bytes_at_write_same rsegs m (bv_unsigned a2) (le2 (Z_to_bv 64 (PMC.meter_value (bv_unsigned a1) bs)))
    ltac:(lia) ltac:(rewrite length_le2; lia)) as BW.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem m a2 ?bsx) _) =>
    replace (write_to_mem m a2 bsx) with (write_to_mem m (wa (bv_unsigned a2)) bsx)
      by (rewrite (wa_of_var a2 (bv_unsigned a2) eq_refl); reflexivity);
    transport_chunks rsegs m (bv_unsigned a2) bsx;
    footprint_after_store rsegs m (bv_unsigned a2) bsx;
    let m1 := fresh "m" in set (m1 := write_to_mem m (wa (bv_unsigned a2)) bsx) in *; clearbody m1
  end.
  (* li a3, 1; j 0x81290 *)
  step. step.
  eapply K; [rewrite OK; reflexivity | exact FR | exact SK | exact WM | rewrite OK; split; [exact MU2 | exact BW]].
Qed.

End Walk.

(* ---- the contract ---- *)

Theorem rp_meter_counter_holds_F : rp_meter_counter_contract_F.
Proof.
  unfold rp_meter_counter_contract_F, RP_METER_COUNTER, RP_METER_COUNTER_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    UNZ UCT HB HL20 HW ST HLO D12 D20 DCT APS1 APS2 CELLS DG DS A12 A20 ACT RFR RGC RCK R12 RS12 R20 RS20 RCT RSCT.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0.
  pose proof (u64_range a1) as Ra1. pose proof (u64_range a2) as Ra2.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct CELLS as (CK & GCK & _).
  unfold off_stk, GOT_CELL_K, CELL_K in DG, DS, CK, GCK, RGC, RCK. unfold ASAN_K in CK.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp) *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename m1 into mf end.
  lazymatch goal with FR : rw_cells _ _ _ [CB 8 ?j; C8 ra] |- _ => set (jk := j) in FR end.
  (* li a3, 14; bltu a1, a3 *)
  step. step. if_cases HL; zify_cond HL.
  - (* n < 14: li a3, 0; mv a0, a3; ld ra, 8(sp); addi sp, sp, 16; ret *)
    assert (OK : PMC.meter_ok (bv_unsigned a1) bs = false) by (apply ok_lt1000; lia).
    do 5 step. apply evtF_done. rewrite OK.
    do 15 eexists. split; [reflexivity|]. split; [exact WM|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|]. exact MU.
  - specialize (UNZ HL). destruct (HB HL) as (L14 & BA). specialize (D12 HL). specialize (A12 HL).
    specialize (R12 HL). specialize (RS12 HL).
    pose proof BA as (BA0 & BA1 & _).
    destruct (ab_at m _ 2 (bv_unsigned a0 + 12) A12 ltac:(lia)) as (AP12 & k12 & MK12 & C12).
    pose proof (rng_one_shadow RNG _ 2 (bv_unsigned a0 + 12) RS12 ltac:(lia)) as RS12'.
    (* beqz a0; li a3, -12; bgeu a0, a3 (UBSan): f <> 0, f + 14 <= 2^64 *)
    step. nobr.
    step. step. nobr.
    (* the shadow base through its GOT word *)
    pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
    pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
    step. step. step.
    clear RDG RDS.
    (* f + 12: addi a3, a0, 12; srli a5, a3, 3; add a5, a5, a4; lb a5, 0(a5); its check *)
    step. gen_addi a0 w12 U12. step. gen_shr w12 g12 G12. step. gen_addi g12 h12 H12.
    assert (RH : rng RNG (bv_unsigned h12) 1)
      by (replace (bv_unsigned h12) with (shadow_addr (bv_unsigned a0 + 12)) by (unfold shadow_addr, ASAN_K; lia);
          exact RS12').
    pose proof (shrd _ m mf (shadow_addr (bv_unsigned a0 + 12)) k12 h12 MU
      ltac:(cbn [outside]; split; [apply shadow_frame; assumption | exact I]) MK12
      ltac:(unfold shadow_addr, ASAN_K; lia)) as R.
    step. clear R RH.
    eapply ck_8117c with (X := bv_unsigned a0 + 12); [exact U12 | exact C12 | intros v].
    (* f[12], f[13]: eo *)
    eapply seg_head with (bs := bs) (m0 := m) (sp0 := sp); try eassumption.
    intros r3' r5' r6' E5.
    (* the rest: n >= 1000, the bytes at eo, the store *)
    eapply seg_tail with (bs := bs) (m0 := m) (sp0 := sp) (lo := lo) (jk := jk); try eassumption.
    intros m' r0' r1' r3'' r4' r5'' r6'' r7' E3 FR' ST' WM' MX. subst r3''.
    (* mv a0, a3; ld ra, 8(sp); addi sp, sp, 16; ret *)
    step. step. step. step. apply evtF_done.
    do 15 eexists. split; [reflexivity|]. split; [exact WM'|].
    split; [release_frame FR' ST' (bv_unsigned sp); exact ST'|]. exact MX.
Qed.

(* The statement of the footprint walk, as the close takes it. *)
Theorem wire_rp_meter_counter_holds : rp_meter_counter_cg.wire_rp_meter_counter_holds_stmt.
Proof. exact rp_meter_counter_holds_F. Qed.

Print Assumptions rp_meter_counter_holds_F.
