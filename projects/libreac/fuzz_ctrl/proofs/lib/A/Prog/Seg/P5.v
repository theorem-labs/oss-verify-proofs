(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Segment P5 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): [0x81b90, 0x81bd4], the run from
   the cut 0x81b90 to the cut 0x81bd8 (v1.8 [0x81b10, 0x81b54], IDENTICAL-RENUMBER: every pc +0x80; the eight
   frame-shadow store offsets move by the new frame layout, 360 -> 370, 362 -> 372, 366 -> 376, 370 -> 380,
   372 .. 375 -> 382 .. 385, because the code byte and the 32-byte scratch moved fr + 2960 -> fr + 3040 and
   fr + 2976 -> fr + 3056).  rule 24: no function proved (a slot segment).  With s3 = S(fr) (the shadow byte of the
   frame base fr) the code stores the frame shadow bytes S(fr)+370 <- 2, +372 <- 0, +376 <- 0, +380 <- 1, loads the
   pointer spilled at s1+280 (fr + 3040, set at 0x813dc: s5 + 864 with s5 = fr + 2176) and stores 0xee in that
   frame byte, stores 0 in the frame shadow bytes S(fr)+382..385 (so the 32 bytes at fr + 3056 are marked usable),
   loads the pointer spilled at s1+240 (fr + 3056, set at 0x813e4: s5 + 880) and calls __asan_memset(fr + 3056, 0,
   32) (0x81bd4) by its asan contract.  p5_evt is the Lib-level run (the nine one-byte stores, two loads and the
   memset call); the frame shadow bytes [S(fr)+370, S(fr)+386), the frame byte fr + 3040, the 32 destination bytes
   and the memset stack scratch [sp - 2208, sp) are the only writes.

   Cuts.  Both are SlotInv's official ones: the entry Inv_A81b90 and the exit Inv_A81bd8 (aslot push 11: both carry
   CUR g (c0 (g_in g)), IDBe g fr ID0 and FGBe g fr z72; Inv_A81bd8 no longer carries the reply call's side-stack
   package, which P6 rebuilds from FRA).  CUR is kept because the run keeps s6 / s9 (registers 22 / 25); the two
   buffers [fr + 2688, fr + 2726) and [fr + 2768, fr + 2840) are frame bytes below fr + 3040, apart from the frame
   shadow, the code byte, the memset destination and its scratch, so fl_bytes keeps them across both parts.  Aslot
   push 12 adds the spill [A + 144] = fr + 2688 (kept: s1 is unchanged and the slot is above the frame and above
   sp) and the 17 bytes at fr + 2691 addressable (kept: their shadow bytes S(fr) + 336 .. 338 are not written).
   Aslot push 13: PRO moves by P1's pro_fra across both parts at once (frame shadow S(fr) + 370 .. 385, frame bytes,
   and the callee window at or above stklo and below A; none is a PRO byte).

   mem_inv.  No cut carries it (push 5d).  The memset contract's mem_inv premise is met by p5_memset_ro, which runs
   the call on the normalized memory (MemNorm.evt_normalize from ro_agree; ro_agree holds after the stores because
   they write nothing below 0x5fe000, where every read-only image byte is) and carries its post back to the real
   memory (munch_rel, wmono_rel, ro_agree_same and the stk / rw_cells transports p5_stk_back / p5_rw_back).

   FRA moves across the stores (W1: the 16 frame shadow bytes and fr + 3040) by Tac_slot.sl_fr_meta, across the call
   (W2: the 32 bytes at fr + 3056 and the memset scratch) by Tac_slot.sl_fr_cl (FSREC by fra_fsrec_stklo), and to the
   materialized model by sl_fra_move; AH, the ownership and the stack bounds over each part by p5_ah
   (a_laws_store on the real arm, a_laws_fs_store with a_fs_ok_pres on the side arm); ENT by ent_store per part,
   then ent_mat.  The exit's spills [A + 232] / [A + 224] / [A + 192] are read off the slot window (p5_rd8_le8, a
   copy of A/Prog/reac_box_model_block.v's rd8_le8, so P5 does not import that callee proof), the
   reply window [sp - K, sp) is addressable by FRA's window-addressability conjunct (it is inside the slot window and
   apart from the frame, fra_frame), REAC_CTRL_PARSE_BC by FRA's frame_AG clause, and XC's code byte fr + 3040 is
   addressable because its shadow byte S(fr) + 380 holds 1. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.
Import ListNotations.
Open Scope Z_scope.

(* A one-byte store of a literal: le1 (Z_to_bv 64 z) is the byte list [Z_to_bv 8 z], the cell C1 the Lib engine's
   store bookkeeping (mem_after_store) expects. *)
Lemma p5_le1 : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal.
  apply Z_to_bv8_mod. rewrite unsigned_lit_wrap. apply mod_mod8_of_modw. lia.
Qed.

Ltac p5_sb :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (p5_le1 z); mem_after_store
  | _ => idtac
  end.

Lemma p5_rd1 : forall m a b, ov_read_bytes rsegs m a 1 = Some [b] -> mrd rsegs m a = Some b.
Proof.
  intros m a b H. rewrite ov_rdn, rdn_unfold in H. cbn [rdn] in H.
  destruct (mrd rsegs m a) as [b0|]; [injection H as ->; reflexivity | discriminate].
Qed.

Lemma p5_cells_read1 : forall m A cs k b, rw_cells rsegs m A cs -> cell_at cs k = Some (C1 b) ->
  mrd rsegs m (wa (A + Z.of_nat k)) = Some b.
Proof.
  intros m A cs k b (HC & _) Hc. apply p5_rd1. exact (cells_at_read rsegs m A cs k (C1 b) HC Hc).
Qed.

Lemma p5_cells_bytes : forall m A cs, rw_cells rsegs m A cs ->
  bytes_at rsegs m A (cells_bytes cs) /\ length (cells_bytes cs) = cells_size cs.
Proof. intros m A cs ((Hwf & Hb) & _). split; [exact Hb | apply cells_bytes_length; exact Hwf]. Qed.

(* A byte of a bytes_at range is present. *)
Lemma p5_ba_present : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  assert (Hj : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - a)) Hj) as E.
  rewrite Z2Nat.id in E by lia. replace (a + (x - a)) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:Eb; [exists b; exact E|].
  apply nth_error_None in Eb. lia.
Qed.

(* Eight present bytes read as one little-endian word (A/Prog/reac_box_model_block.v rd8_le8 and its three helpers,
   copied here so that P5, a slot segment, does not import that callee proof). *)
Lemma p5_ble_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma p5_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (p5_ble_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma p5_zle_ble : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite p5_ble_cons.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (p5_ble_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma p5_rd8_le8 : forall m a, 0 <= a -> a + 8 <= 2^64 ->
  (forall i, 0 <= i < 8 -> exists b, mrd rsegs m (wa (a + i)) = Some b) -> exists w, bytes_at rsegs m a (le8 w).
Proof.
  intros m a Ha Hl H.
  destruct (H 0 ltac:(lia)) as [b0 E0]. destruct (H 1 ltac:(lia)) as [b1 E1].
  destruct (H 2 ltac:(lia)) as [b2 E2]. destruct (H 3 ltac:(lia)) as [b3 E3].
  destruct (H 4 ltac:(lia)) as [b4 E4]. destruct (H 5 ltac:(lia)) as [b5 E5].
  destruct (H 6 ltac:(lia)) as [b6 E6]. destruct (H 7 ltac:(lia)) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (EL : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite <- store_bytes_8. cbn [width_bytes]. rewrite unsigned_lit_wrap.
    rewrite Z_to_le_bytes_mod by (cbn; lia).
    exact (p5_zle_ble [b0; b1; b2; b3; b4; b5; b6; b7]). }
  rewrite EL. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error]; simpl Z.of_nat;
    [rewrite Z.add_0_r in E0; replace (a + Z.of_nat 0) with a by lia; exact E0
    | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
Qed.

(* The 32 bytes at D (D mod 8 = 0) are addressable when their four shadow bytes T..T+3 (T = D/8 + K) read 0. *)
Lemma p5_addr32 : forall m D T,
  0 <= D -> D mod 8 = 0 -> D / 8 + ASAN_K = T -> app_ivl D (D + 33) ->
  (forall j, 0 <= j < 4 -> mrd rsegs m (wa (T + j)) = Some (Z_to_bv 8 0)) -> addressable m D 32.
Proof.
  intros m D T HD H8 HT Happ HZ.
  assert (Hend : app_mem (D + 32)) by (apply Happ; lia).
  split; [lia|]. split; [lia|].
  split; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia|].
  intros i Hi. split; [apply Happ; lia|].
  exists (Z_to_bv 8 0). split.
  - replace (shadow_addr (D + i)) with (T + i / 8).
    + apply HZ. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    + unfold shadow_addr. rewrite <- HT. Z.div_mod_to_equations. lia.
  - left. unfold bv_signed. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* Route (C) (a Theorem Labs lane's frozen form): every region present and writable at m still is at m1 across a run that
   writes the frame shadow bytes [S + 370, S + 386) (readable afterwards: bytes_at of the 392 frame shadow bytes) and
   one app byte Y.  No shadow byte is read: no premise. *)
Lemma p5_shadow_rw_on : forall m m1 S Y sh',
  munch [(S + 370, S + 386); (Y, Y + 1)] m m1 -> wmono rsegs m m1 ->
  bytes_at rsegs m1 S sh' -> length sh' = 392%nat -> ~ in_shadow Y ->
  forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m1.
Proof.
  intros m m1 S Y sh' MU WM HB HL HY P HSW a HPa Ha.
  destruct (HSW a HPa Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  pose proof (in_shadow_range a Ha) as Hr.
  destruct HB as (HS0 & HSl & HBn).
  destruct (Z_le_gt_dec (S + 370) a) as [Hge|Hlt];
    [destruct (Z_lt_ge_dec a (S + 386)) as [Hlt2|Hge2]|].
  - assert (Hj : (Z.to_nat (a - S) < length sh')%nat) by (rewrite HL; lia).
    pose proof (HBn (Z.to_nat (a - S)) Hj) as HmE.
    rewrite Z2Nat.id in HmE by lia. replace (S + (a - S)) with a in HmE by lia.
    destruct (nth_error sh' (Z.to_nat (a - S))) as [b'|] eqn:E; [exists b'; exact HmE|].
    exfalso. apply nth_error_None in E. lia.
  - assert (HaY : a <> Y) by (intro E; apply HY; rewrite <- E; exact Ha).
    assert (Hm : m1 (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    exists b. unfold mrd in *. rewrite Hm. exact Hb.
  - assert (HaY : a <> Y) by (intro E; apply HY; rewrite <- E; exact Ha).
    assert (Hm : m1 (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    exists b. unfold mrd in *. rewrite Hm. exact Hb.
Qed.

(* Every shadow byte stays readable (and writable) across a run that writes the frame shadow bytes
   [S + 370, S + 386) (readable afterwards: bytes_at of the 392 frame shadow bytes) and one app byte Y. *)
Lemma p5_shadow_rw : forall m m1 S Y sh',
  shadow_rw m -> munch [(S + 370, S + 386); (Y, Y + 1)] m m1 -> wmono rsegs m m1 ->
  bytes_at rsegs m1 S sh' -> length sh' = 392%nat -> ~ in_shadow Y -> shadow_rw m1.
Proof.
  intros m m1 S Y sh' HSW MU WM HB HL HY. exact (A.ShadowRwOn.shadow_rw_of_on_all m1 (p5_shadow_rw_on m m1 S Y sh'
    MU WM HB HL HY (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.

(* ---- The normalized-memory transports (the p6_ ones of Seg/P6.v, the p4_ ones of Seg/P4.v). ---- *)

Definition p5_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma p5_rsegs_below_gt : p5_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p5_find_below : forall segs top x n s,
  p5_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold p5_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* No byte at or above the image's top (0x5fe000) is read-only. *)
Lemma p5_ro_addr_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (p5_find_below sg 0x5fe000 x n s p5_rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

(* So every read-only address is below 0x5fe000. *)
Lemma p5_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 0x5fe000.
Proof.
  intros a H. destruct (Z_lt_le_dec (bv_unsigned a) 0x5fe000) as [L|L]; [exact L|].
  pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
  assert (Ea : wa (bv_unsigned a) = a) by (unfold wa; apply Z_to_bv_bv_unsigned).
  rewrite <- Ea in H. rewrite (p5_ro_addr_hi (bv_unsigned a) ltac:(lia)) in H. discriminate H.
Qed.

(* A byte read at or above 0x5fe000 is a byte of the memory map (no image segment reaches there). *)
Lemma p5_mrd_hi : forall m x b, 0x5fe000 <= x < 2 ^ 64 -> mrd rsegs m (wa x) = Some b -> m (wa x) = Some b.
Proof.
  intros m x b Hx H. unfold mrd in H. destruct (m (wa x)) as [c|] eqn:Em; [exact H|].
  exfalso. rewrite (MemNorm.seg_rom_unmapped rsegs (wa x)) in H; [discriminate H|].
  destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [s|] eqn:E; [|reflexivity].
  destruct (p5_find_below rsegs 0x5fe000 _ 1 s p5_rsegs_below_gt E ltac:(lia)) as [L|L]; [|discriminate L].
  rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma p5_wview_rel_hi : forall m m0 a, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (MemNorm.wview_rel_rw rsegs m m0 (wa a) HR (p5_ro_addr_hi a Ha)). split; auto.
Qed.

Lemma p5_stk_rel : forall m m0 lo hi, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (p5_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p5_stk_back : forall m m0 lo hi, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (p5_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p5_shadow_rw_rel : forall m m0, MemNorm.mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a ltac:(unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG; lia))
    as (Hw & b & Hb). split.
  - apply (proj2 (p5_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p5_addressable_rel : forall m m0 p n, MemNorm.mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma p5_cells_rel : forall m m0, MemNorm.mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 REL HAC. unfold asan_cells in HAC |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    apply (proj1 (MemNorm.bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma p5_rw_rel : forall m m0 a cs, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  rw_cells rsegs m a cs -> rw_cells rsegs m0 a cs.
Proof.
  intros m m0 a cs REL Ha [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj1 (MemNorm.bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - pose proof Hw as (Hw0 & Hw1 & _).
    apply (MemNorm.wr_at_norm rsegs m m0 _ _ REL Hw). intros i Hi. apply p5_ro_addr_hi. lia.
Qed.

Lemma p5_rw_back : forall m m0 a cs, MemNorm.mem_rel rsegs m m0 ->
  rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs REL [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (MemNorm.wr_at_rel rsegs m m0 _ _ REL Hw).
Qed.

(* The memset contract from ro_agree instead of mem_inv: the call runs on the normalized memory, where mem_inv
   holds (MemNorm.mem_inv_normalize), and MemNorm.evt_normalize carries it back (as Seg/P1.v p1_evt_ro). Its post is
   about the real memory: munch / wmono by munch_rel / wmono_rel, ro_agree by ro_agree_same, the stack window and
   the destination cells back across mem_rel. The destination is above the image (0x5fe000), so its cells cross
   to the normalized memory. *)
Lemma p5_memset_ro : asan_memset_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
  0x5fe000 <= bv_unsigned a0 ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  bv_unsigned a2 <= 2 ^ 40 -> addressable m (bv_unsigned a0) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) ->
  (bv_unsigned a0 + bv_unsigned a2 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= bv_unsigned a0) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMSET_K <= bv_unsigned sp ->
  HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
  asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
  evt rsegs
    (fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)] m m' /\
       wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       (exists zs, rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) zs]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO.
  unfold asan_memset_contract in MSET. cbv zeta in MSET.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAEv : APPMEM_END = 0x800000000000) by reflexivity.
  eapply evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    apply (MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNorm.normalize rsegs m) junk lo).
    + exact (p5_rw_rel m _ _ _ REL HD0 RWd).
    + exact HN.
    + exact (p5_addressable_rel m _ _ _ REL HAD).
    + exact HEND.
    + exact HD7.
    + exact HDRT.
    + exact HSEP.
    + exact (p5_stk_rel m _ lo (bv_unsigned sp) REL ltac:(lia) ltac:(lia) ST).
    + exact HLO.
    + exact HHM.
    + exact HAE.
    + exact (p5_cells_rel m _ REL HAC).
    + exact (p5_shadow_rw_rel m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
  - intros s (s0' & HQ & MR & RS). unfold asan_memset_post in HQ.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    -> & MU0 & WM0 & _ & ST0 & RW0 & _ & _).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', ms.
    split; [reflexivity|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p5_stk_back ms m0' lo (bv_unsigned sp) Hmem ltac:(lia) ltac:(lia) ST0)|].
    eexists. exact (p5_rw_back ms m0' _ _ Hmem RW0).
Qed.

(* Route (C) (a Theorem Labs lane's frozen form; the 09:58Z ruling for a run with a callee contract: p5_memset_ro stays as it
   is): the shadow the call needs is the memset's, asan_memset_shadow_R at p5_memset_ro's own a0 / a2. *)
Definition p5_memset_ro_shadow_R (a0 a2 : word) : Z -> Prop := fun a => asan_memset_shadow_R a0 a2 a.

Lemma p5_memset_ro_on : asan_memset_contract_on ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
  0x5fe000 <= bv_unsigned a0 ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  bv_unsigned a2 <= 2 ^ 40 -> addressable m (bv_unsigned a0) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) ->
  (bv_unsigned a0 + bv_unsigned a2 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= bv_unsigned a0) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMSET_K <= bv_unsigned sp ->
  HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
  asan_cells m -> A.ShadowRwOn.shadow_rw_on (p5_memset_ro_shadow_R a0 a2) m -> MemNorm.ro_agree rsegs m ->
  evt rsegs
    (fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)] m m' /\
       wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       (exists zs, rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) zs]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO.
  unfold asan_memset_contract_on in MSET. cbv zeta in MSET.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAEv : APPMEM_END = 0x800000000000) by reflexivity.
  eapply evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    apply (MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNorm.normalize rsegs m) junk lo).
    + exact (p5_rw_rel m _ _ _ REL HD0 RWd).
    + exact HN.
    + exact (p5_addressable_rel m _ _ _ REL HAD).
    + exact HEND.
    + exact HD7.
    + exact HDRT.
    + exact HSEP.
    + exact (p5_stk_rel m _ lo (bv_unsigned sp) REL ltac:(lia) ltac:(lia) ST).
    + exact HLO.
    + exact HHM.
    + exact HAE.
    + exact (p5_cells_rel m _ REL HAC).
    + exact (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
  - intros s (s0' & HQ & MR & RS). unfold asan_memset_post_on in HQ.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    -> & MU0 & WM0 & _ & ST0 & RW0 & _ & _).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', ms.
    split; [reflexivity|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p5_stk_back ms m0' lo (bv_unsigned sp) Hmem ltac:(lia) ltac:(lia) ST0)|].
    eexists. exact (p5_rw_back ms m0' _ _ Hmem RW0).
Qed.

(* The Lib-level run of the segment.  The stores need no mem_inv; ro_agree survives them (they write nothing below
   0x5fe000), and the memset runs by p5_memset_ro.  The post keeps the memory m1 between the stores and the call
   (FRA moves in two steps), the shadow byte S + 380 = 1 written by the stores and the presence of the code byte Y. *)
Lemma p5_evt : asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S Y D lo : Z) (sh jy junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 S ->
    0 <= A < 2 ^ 64 -> 0 <= spv < 2 ^ 64 -> 0 <= D < 2 ^ 64 ->
    ro_cells rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] ->
    ro_cells rsegs m (A + 240) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m S [CB 392 sh] ->
    rw_cells rsegs m Y [CB 1 jy] ->
    rw_cells rsegs m D [CB 32 junk] ->
    S + 392 <= A -> Y + 1 <= D -> (S + 392 <= Y \/ D + 32 <= S) -> (Y + 1 <= A + 240 \/ A + 288 <= Y) ->
    RT_HI <= S -> RT_HI <= Y -> app_mem Y -> 0x5fe000 <= S -> 0x5fe000 <= Y ->
    D mod 8 = 0 -> D / 8 + ASAN_K = S + 382 -> app_ivl D (D + 33) ->
    (D + 32 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81bd8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 370, S + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\ MemNorm.ro_agree rsegs m1 /\
         (exists sh', bytes_at rsegs m1 S sh' /\ length sh' = 392%nat) /\
         mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1) /\ (exists b, mrd rsegs m1 (wa Y) = Some b) /\
         munch [(D, D + 32); (spv - ASAN_MEMSET_K, spv)] m1 m' /\ wmono rsegs m1 m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\ (exists zs, rw_cells rsegs m' D [CB 32 zs]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b90) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S Y D lo sh jy junk -> -> -> HA HSP HD RO280 RO240 RWsh RWy RWd HSA HYD HSY HYA HRTS HRTY HappY
    HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof (munch_refl [(S + 370, S + 386); (Y, Y + 1)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WM1.
  (* li a0,2 ; li a1,1 ; sb a0,370(s3) ; sb zero,372(s3) ; sb zero,376(s3) ; sb a1,380(s3) *)
  step. step. step. p5_sb.
  step. p5_sb. step. p5_sb. step. p5_sb.
  (* li a0,-18 ; ld a1,280(s1) ; sb a0,0(a1) *)
  step. step. step. p5_sb.
  (* sb zero,382..385(s3) *)
  step. p5_sb. step. p5_sb. step. p5_sb. step. p5_sb.
  (* li a2,32 ; ld s5,240(s1) ; mv a0,s5 ; li a1,0 ; jal __asan_memset *)
  step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  (* the memset call's premises in the memory after the stores *)
  assert (Z0 : forall j, 0 <= j < 4 -> mrd rsegs m1 (wa (S + 382 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj' as [-> | [-> | [-> | ->]]].
    - replace (S + 382 + 0) with (S + Z.of_nat 382) by lia.
      apply (p5_cells_read1 m1 S _ 382 _ RWsh). reflexivity.
    - replace (S + 382 + 1) with (S + Z.of_nat 383) by lia.
      apply (p5_cells_read1 m1 S _ 383 _ RWsh). reflexivity.
    - replace (S + 382 + 2) with (S + Z.of_nat 384) by lia.
      apply (p5_cells_read1 m1 S _ 384 _ RWsh). reflexivity.
    - replace (S + 382 + 3) with (S + Z.of_nat 385) by lia.
      apply (p5_cells_read1 m1 S _ 385 _ RWsh). reflexivity. }
  assert (H380 : mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1)).
  { replace (S + 380) with (S + Z.of_nat 380) by lia.
    apply (p5_cells_read1 m1 S _ 380 _ RWsh). reflexivity. }
  assert (HYp : exists b, mrd rsegs m1 (wa Y) = Some b).
  { replace (wa Y) with (wa (Y + Z.of_nat 0)) by (f_equal; lia).
    eexists. apply (p5_cells_read1 m1 Y _ 0 _ RWy). reflexivity. }
  assert (HAD : addressable m1 D 32) by (apply (p5_addr32 m1 D (S + 382)); [lia | exact HD8 | exact HDS | exact HappD | exact Z0]).
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI in *. lia. }
  pose proof (p5_cells_bytes _ _ _ RWsh) as (HBsh & HLsh). cbn [cells_size csize Nat.add] in HLsh.
  assert (HSW1 : shadow_rw m1).
  { apply (p5_shadow_rw m m1 S Y _ HSW MU1 WM1 HBsh HLsh). intro HYs. exact (app_not_shadow Y HappY HYs). }
  (* the stores write nothing below 0x5fe000, so the read-only image bytes are kept *)
  assert (HRO1 : MemNorm.ro_agree rsegs m1).
  { apply (MemNorm.ro_agree_same rsegs m m1 HRO). intros a Ha. apply MU1.
    pose proof (p5_ro_lo a Ha) as Hlo. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  eapply evt_cut.
  { eapply (p5_memset_ro MSET) with (junk := junk) (lo := lo).
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact RWd.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact HAD.
    - rewrite !MState.unsigned_lit by lia. right. apply HappD. lia.
    - rewrite !MState.unsigned_lit by lia. right. apply HappD. lia.
    - rewrite !MState.unsigned_lit by lia. right. lia.
    - rewrite !MState.unsigned_lit by lia. exact HSEP.
    - rewrite !MState.unsigned_lit by lia. exact ST.
    - rewrite !MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !MState.unsigned_lit by lia. exact HAE.
    - exact HAC1.
    - exact HSW1.
    - exact HRO1. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & ROc & STc & (zs & RWc)).
  subst ms'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply MState.unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite ED in MUc, RWc. rewrite E32 in MUc, RWc. rewrite Esp in MUc, STc.
  replace (ret_pc (Z_to_bv 64 0x81bd8)) with (Z_to_bv 64 0x81bd8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. eexists. exists m1, m'. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact HRO1|].
  split; [eexists; split; [exact HBsh | exact HLsh]|].
  split; [exact H380|]. split; [exact HYp|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact ROc|].
  split; [exact STc | eexists; exact RWc].
Qed.

(* Route (C) (the 09:58Z ruling: p5_evt stays as it is).  The run reads no shadow byte; its frame-shadow stores
   (0x81b98 .. 0x81bc0) go through the rw_cells premise of the 392 frame-shadow bytes, not through shadow_rw.  The
   shadow it needs is the memset's at the call (a0 = D, a2 = 32), through p5_memset_ro_on's region. *)
Definition p5_evt_shadow_R (D : Z) : Z -> Prop := fun a => p5_memset_ro_shadow_R (Z_to_bv 64 D) (Z_to_bv 64 32) a.

Lemma p5_evt_on : asan_memset_contract_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S Y D lo : Z) (sh jy junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 S ->
    0 <= A < 2 ^ 64 -> 0 <= spv < 2 ^ 64 -> 0 <= D < 2 ^ 64 ->
    ro_cells rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] ->
    ro_cells rsegs m (A + 240) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m S [CB 392 sh] ->
    rw_cells rsegs m Y [CB 1 jy] ->
    rw_cells rsegs m D [CB 32 junk] ->
    S + 392 <= A -> Y + 1 <= D -> (S + 392 <= Y \/ D + 32 <= S) -> (Y + 1 <= A + 240 \/ A + 288 <= Y) ->
    RT_HI <= S -> RT_HI <= Y -> app_mem Y -> 0x5fe000 <= S -> 0x5fe000 <= Y ->
    D mod 8 = 0 -> D / 8 + ASAN_K = S + 382 -> app_ivl D (D + 33) ->
    (D + 32 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p5_evt_shadow_R D) m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81bd8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 370, S + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\ MemNorm.ro_agree rsegs m1 /\
         (exists sh', bytes_at rsegs m1 S sh' /\ length sh' = 392%nat) /\
         mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1) /\ (exists b, mrd rsegs m1 (wa Y) = Some b) /\
         munch [(D, D + 32); (spv - ASAN_MEMSET_K, spv)] m1 m' /\ wmono rsegs m1 m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\ (exists zs, rw_cells rsegs m' D [CB 32 zs]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b90) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S Y D lo sh jy junk -> -> -> HA HSP HD RO280 RO240 RWsh RWy RWd HSA HYD HSY HYA HRTS HRTY HappY
    HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof (munch_refl [(S + 370, S + 386); (Y, Y + 1)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WM1.
  (* li a0,2 ; li a1,1 ; sb a0,370(s3) ; sb zero,372(s3) ; sb zero,376(s3) ; sb a1,380(s3) *)
  step. step. step. p5_sb.
  step. p5_sb. step. p5_sb. step. p5_sb.
  (* li a0,-18 ; ld a1,280(s1) ; sb a0,0(a1) *)
  step. step. step. p5_sb.
  (* sb zero,382..385(s3) *)
  step. p5_sb. step. p5_sb. step. p5_sb. step. p5_sb.
  (* li a2,32 ; ld s5,240(s1) ; mv a0,s5 ; li a1,0 ; jal __asan_memset *)
  step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  (* the memset call's premises in the memory after the stores *)
  assert (Z0 : forall j, 0 <= j < 4 -> mrd rsegs m1 (wa (S + 382 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj' as [-> | [-> | [-> | ->]]].
    - replace (S + 382 + 0) with (S + Z.of_nat 382) by lia.
      apply (p5_cells_read1 m1 S _ 382 _ RWsh). reflexivity.
    - replace (S + 382 + 1) with (S + Z.of_nat 383) by lia.
      apply (p5_cells_read1 m1 S _ 383 _ RWsh). reflexivity.
    - replace (S + 382 + 2) with (S + Z.of_nat 384) by lia.
      apply (p5_cells_read1 m1 S _ 384 _ RWsh). reflexivity.
    - replace (S + 382 + 3) with (S + Z.of_nat 385) by lia.
      apply (p5_cells_read1 m1 S _ 385 _ RWsh). reflexivity. }
  assert (H380 : mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1)).
  { replace (S + 380) with (S + Z.of_nat 380) by lia.
    apply (p5_cells_read1 m1 S _ 380 _ RWsh). reflexivity. }
  assert (HYp : exists b, mrd rsegs m1 (wa Y) = Some b).
  { replace (wa Y) with (wa (Y + Z.of_nat 0)) by (f_equal; lia).
    eexists. apply (p5_cells_read1 m1 Y _ 0 _ RWy). reflexivity. }
  assert (HAD : addressable m1 D 32) by (apply (p5_addr32 m1 D (S + 382)); [lia | exact HD8 | exact HDS | exact HappD | exact Z0]).
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI in *. lia. }
  pose proof (p5_cells_bytes _ _ _ RWsh) as (HBsh & HLsh). cbn [cells_size csize Nat.add] in HLsh.
  assert (HSW1 : A.ShadowRwOn.shadow_rw_on (p5_evt_shadow_R D) m1).
  { apply (p5_shadow_rw_on m m1 S Y _ MU1 WM1 HBsh HLsh); [|exact HSW].
    intro HYs. exact (app_not_shadow Y HappY HYs). }
  (* the stores write nothing below 0x5fe000, so the read-only image bytes are kept *)
  assert (HRO1 : MemNorm.ro_agree rsegs m1).
  { apply (MemNorm.ro_agree_same rsegs m m1 HRO). intros a Ha. apply MU1.
    pose proof (p5_ro_lo a Ha) as Hlo. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  eapply evt_cut.
  { eapply (p5_memset_ro_on MSET) with (junk := junk) (lo := lo).
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact RWd.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact HAD.
    - rewrite !MState.unsigned_lit by lia. right. apply HappD. lia.
    - rewrite !MState.unsigned_lit by lia. right. apply HappD. lia.
    - rewrite !MState.unsigned_lit by lia. right. lia.
    - rewrite !MState.unsigned_lit by lia. exact HSEP.
    - rewrite !MState.unsigned_lit by lia. exact ST.
    - rewrite !MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !MState.unsigned_lit by lia. exact HAE.
    - exact HAC1.
    - exact HSW1.
    - exact HRO1. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & ROc & STc & (zs & RWc)).
  subst ms'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply MState.unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite ED in MUc, RWc. rewrite E32 in MUc, RWc. rewrite Esp in MUc, STc.
  replace (ret_pc (Z_to_bv 64 0x81bd8)) with (Z_to_bv 64 0x81bd8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. eexists. exists m1, m'. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact HRO1|].
  split; [eexists; split; [exact HBsh | exact HLsh]|].
  split; [exact H380|]. split; [exact HYp|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact ROc|].
  split; [exact STc | eexists; exact RWc].
Qed.

(* ---- The segment lemma seg_P5. ---- *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_parse_c
  reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 P1.
Import ListNotations.
(* FRA's FPState and getr are those of the image-A YK11; import it last (as P1.v does). *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
(* The write-set predicates, cells and run predicates of p5_evt and of SlotInv's cuts are lib.Lib's. *)
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.

(* The identity-reply call's stack need (the window of the exit cut's side-stack package). *)
Module RIR5 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_reply_c.

(* mkR_of made concrete, so that the run lemma's register file is p5_evt's mkR (Seg/P1.v p1_mkR_of). *)
Lemma p5_mkR_of : forall regs, Regs6ss.mkR_of regs = LFr.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
  (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
  (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
  (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Two word_mem values at the same address agree mod 2^64 (Seg/P2.v p2_wm_congr). *)
Lemma p5_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864) (Seg/P2.v p2_fs_meta_range). *)
Lemma p5_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The registered globals of frame_AG lie in [0x21140, 0x9f8e8) (a Theorem Labs lane's F37.v f37_ag_range): v1.9.0's
   round_trip.box .. CTRL_FRAMES + 264 (lib/A/FrameAPI.v, equal to the v1.9 ELF's asan_globals). *)
Lemma p5_ag_range : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (0x21140 <=? fst p) && (fst p + snd p <=? 0x9f8e8)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (lo, len) Hin). cbn [fst snd] in Hall.
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* A range of registered-global bytes is addressable (FRA's frame_AG clause, byte by byte; Seg/P11.v p11_ag). *)
Lemma p5_ag : forall m p n,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall a, p <= a < p + n -> in_globals AF.frame_AG a) ->
  addressable m p n.
Proof.
  intros m p n HAG Hp Hn Hpn Hin. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hpn|].
  intros i Hi. destruct (HAG (p + i) (Hin (p + i) ltac:(lia))) as (_ & _ & _ & H).
  specialize (H 0 ltac:(lia)). rewrite Z.add_0_r in H. exact H.
Qed.

(* The frame-shadow byte x is the shadow byte of the frame byte fr + 8 (x - S(fr)) (Seg/P1.v p1_sfr_shadow). *)
Lemma p5_sfr_shadow : forall fr x, x = shadow_addr (fr + 8 * (x - Sfr fr)).
Proof.
  intros fr x. unfold Sfr, shadow_addr.
  replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with (fr + (x - (fr / 8 + ASAN_K)) * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* Two values of the same register, both in range, are equal (Seg/P6.v p6_rg_inj). *)
Lemma p5_rg_inj : forall regs r A A', rg regs r A -> rg regs r A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A = A'.
Proof.
  intros regs r A A' H H' HA HA'. unfold rg in *. rewrite H in H'.
  apply (f_equal (bv_unsigned (n:=64))) in H'. rewrite !MState.unsigned_lit in H' by lia. exact H'.
Qed.

(* The munch / outside flavours of Tac_slot (fr_munch_ul, fr_outside_lib). *)
Ltac p5_mu H := first [exact H | exact (proj1 (fr_munch_ul _ _ _) H) | exact (proj2 (fr_munch_ul _ _ _) H)].
Ltac p5_lf := first [ lazymatch goal with |- LFr.outside _ _ => idtac end
                    | apply (proj2 (fr_outside_lib _ _)) | apply (proj1 (fr_outside_lib _ _)) ].
(* An outside goal over a two-range write list, each range closed by lia. *)
Ltac p5_out2 := p5_lf; cbn [LFr.outside]; split; [lia|]; split; [lia | exact I].

(* addressable survives a run whose writes miss the shadow bytes of the range (Seg/P6.v p6_addr_keep). *)
Lemma p5_addr_keep : forall W m m' p n,
  addressable m p n -> LFr.munch W m m' ->
  (forall i, 0 <= i < n -> LFr.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|].
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa_unsigned by lia. exact (HW i Hi).
Qed.

Section P5W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* AH, the runtime's ownership and the stack bounds across a run whose writes are frame bytes, frame-shadow bytes or
   bytes of the entry-anchored slot window, each present afterwards: a_laws_store on the real arm (all of them are
   a_store_ok there), a_laws_fs_store on the side arm (the frame and its shadow are side-stack bytes and their
   shadow, the window is above stklo; a_fs_ok_pres keeps the side stack's metadata, which no such write touches). *)
Lemma p5_ah : forall g fr regs mem mem' md W,
  FRA B APIf ra g fr [] regs mem md ->
  LFr.munch W mem mem' -> LFr.wmono rsegs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> LFr.outside W x \/
     ((fr <= x < fr + FRAME_BYTES \/ Sfr fr <= x < Sfr fr + FRAME_SHADOW \/ g_S g - AF.SLOT_STACK <= x < g_S g) /\
      exists b, mbyte rsegs mem' x = Some b)) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs mem mem' md W HFRA MU WM HW.
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (Hwrit : forall x, 0 <= x < 2^64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
  { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
  destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs Hrec]]]].
  - (* real arm: every write is a frame byte, the shadow byte of one, or a window byte, all a_store_ok *)
    assert (Hmc : forall x, 0 <= x < 2^64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok. destruct (HW x Hx) as [Ho | (Hreg & _)].
      - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
      - exfalso. apply Hnok. destruct Hreg as [Hf | [Hs | Hw]].
        + right. left. specialize (Hreal x Hf). lia.
        + right. right. right. exists (fr + 8 * (x - Sfr fr)).
          split; [exact (p5_sfr_shadow fr x)|]. right. left.
          specialize (Hreal (fr + 8 * (x - Sfr fr)) ltac:(lia)). lia.
        + right. left. lia. }
    exact (p1_laws_store APIf ([] ++ g_H g) mem mem' md HAH Hmc Hwrit).
  - (* side arm: the frame lies in the side stack FS, its shadow is FS's shadow, the window is above stklo *)
    destruct (Hfs fr ltac:(lia)) as (FS & HFSr & HFSw & HFSlo & HFShi).
    destruct (p1_laws_fs_place APIf ([] ++ g_H g) mem md FS HAH HFSw HFSr) as (HGTFS & HFSend & HFSmod & HFSapp).
    pose proof (p1_fs_ok_of_state APIf ([] ++ g_H g) mem md FS HAH HFSw HFSr) as Hfsok0.
    pose proof (Hfsb FS HFSw HFSr) as HFSfr.
    assert (HFS64 : 0 <= FS /\ FS + AC.FS_SIZE <= 2 ^ 64).
    { pose proof (HFSapp FS ltac:(lia)) as Alo. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as Ahi.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Alo, Ahi. lia. }
    assert (HinFS : forall a, fr <= a < fr + FRAME_BYTES -> FS <= a < FS + AC.FS_SIZE).
    { intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hbw & Hb1 & Hb2).
      pose proof (p5_wm_congr mem _ b FS Hbw HFSw) as X. rewrite !Z.mod_small in X by lia.
      subst b. lia. }
    assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
    { intros x Hx. rewrite (p5_sfr_shadow fr x). apply shadow_of_app. apply Happ. lia. }
    (* every present byte stays present: outside W by munch, in W by the premise *)
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
              exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq (b & Hb). destruct (HW q Hq) as [Ho | (_ & Hb')]; [|exact Hb'].
      exists b. unfold mbyte in Hb |- *. rewrite MU; [exact Hb|].
      rewrite MState.unsigned_lit by exact Hq. exact Ho. }
    (* the side stack's metadata is below the frames, app memory, and below stklo, so W misses it *)
    assert (Hmeta : forall q, fs_meta FS q -> LFr.outside W q).
    { intros q Hq. pose proof (p5_fs_meta_range _ _ Hq) as Hqr.
      assert (Hqa : app_mem q) by (apply HFSapp; lia).
      assert (Hq64 : 0 <= q < 2 ^ 64).
      { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as Htop.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Htop. lia. }
      destruct (HW q Hq64) as [Ho | (Hreg & _)]; [exact Ho | exfalso].
      destruct Hreg as [Hf | [Hs | Hw]].
      + lia.
      + exact (app_not_shadow q Hqa (HshIS q Hs)).
      + lia. }
    assert (Hfsok' : AC.a_fs_ok mem' FS).
    { apply (a_fs_ok_pres W mem mem' FS Hfsok0 MU Hwrit Hpres Hmeta); lia. }
    assert (Hmc : forall x, 0 <= x < 2^64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              ~ (FS <= x < FS + AC.FS_SIZE) ->
              ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ x = shadow_addr b) ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok Hnfs Hnsh. destruct (HW x Hx) as [Ho | (Hreg & _)].
      - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
      - exfalso. destruct Hreg as [Hf | [Hs | Hw]].
        + apply Hnfs. apply HinFS. exact Hf.
        + apply Hnsh. exists (fr + 8 * (x - Sfr fr)). split; [apply HinFS; lia | exact (p5_sfr_shadow fr x)].
        + apply Hnok. right. left. lia. }
    exact (p1_laws_fs_store APIf ([] ++ g_H g) mem mem' md FS HAH HFSw HFSr Hmc Hwrit Hfsok').
Qed.

Ltac p5_lia :=
  unfold app_mem, HIGHMEM_BEG, LOWMEM_END, APPMEM_END, ASAN_K, ASAN_MEMSET_K, AF.SLOT_STACK, AC.GT, RT_HI, RT_LO,
    FN_STACK in *; lia.

Lemma seg_P5 : asan_memset_contract ->
  Hcut B APIf ra (Inv_A81bd8 B APIf ra) -> Hcut B APIf ra (Inv_A81b90 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros MSET Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & HCUR & HPRO & HSP144 & HAD17 & HSP208 &
    HADF & HADI & HIDB & HFGB &
    (A0 & jy & junk & HrA & HA0 & HQ280 & HQ240 & RWy & RWd & HAF)).
  subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  unfold rg in Hr19, Hr8, Hr9, Hr26, HrA.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKv : RIR5.REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HMK : ASAN_MEMSET_K = 2208) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HLE : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (HAEv : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HASK : ASAN_K = 0x7fff8000) by reflexivity.
  (* frame-base bounds from the header word's bytes_at *)
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2^64).
  { unfold q64 in Hhdr1. apply bytes_at_bound in Hhdr1. rewrite length_le8 in Hhdr1. lia. }
  assert (Hfr8 : fr mod 8 = 0). { pose proof Hfrm as Hfrm0. Z.div_mod_to_equations. lia. }
  (* the real-stack low bound is in high memory; the spill base A is above it *)
  assert (Hstkhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH)).
  assert (HAlo : HIGHMEM_BEG <= A) by lia.
  assert (HAr : 0 <= A < 2 ^ 64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  (* the cut's s1 = A0 is FRA's spill base A *)
  assert (HA0A : A0 = A).
  { pose proof HQ280 as HQb. unfold q64 in HQb. apply bytes_at_bound in HQb. rewrite length_le8 in HQb.
    apply (p5_rg_inj regs 9 A0 A); [exact HrA | exact Hr9 | lia | exact HAr]. }
  subst A0.
  (* the spill [A1 + 144] of the cut is at FRA's spill base: A1 = A (A1 mod 2^64 = A, and both spills are in
     range) *)
  destruct HSP144 as (A1 & HrA1 & HQ144).
  assert (HA1 : A1 = A).
  { unfold rg in HrA1.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HrA1)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by lia.
    pose proof HQ144 as HQb. unfold q64 in HQb. apply bytes_at_bound in HQb. rewrite length_le8 in HQb.
    pose proof Hspill as HSb. unfold q64 in HSb. apply bytes_at_bound in HSb. rewrite length_le8 in HSb.
    clear - E0 HQb HSb. revert E0 HQb HSb. Z.div_mod_to_equations. lia. }
  subst A1.
  (* push 14D: the spill [A2 + 192] = fragb fr likewise *)
  destruct HSP208 as (A2 & HrA2 & HQ208).
  assert (HA2 : A2 = A).
  { unfold rg in HrA2.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HrA2)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by lia.
    pose proof HQ208 as HQb. unfold q64 in HQb. apply bytes_at_bound in HQb. rewrite length_le8 in HQb.
    pose proof Hspill as HSb. unfold q64 in HSb. apply bytes_at_bound in HSb. rewrite length_le8 in HSb.
    clear - E0 HQb HSb. revert E0 HQb HSb. Z.div_mod_to_equations. lia. }
  subst A2.
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. apply (p5_rg_inj regs 9 A' A); [exact HA' | exact Hr9 | exact HA'r | exact HAr]. }
  (* the frame: app memory above the image, placed against the windows below sp *)
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hapart & _ & _ & _).
  rewrite Haspz in Hwlo, Hwstk, Hapart.
  assert (Hspr : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; unfold AC.aspZ; apply u64_range).
  assert (HSEP0 : fr + FRAME_BYTES <= sp - ASAN_MEMSET_K \/ sp <= fr) by (apply Hapart; lia).
  assert (HSEP : fr + 3056 + 32 <= sp - ASAN_MEMSET_K \/ sp <= fr + 3056) by lia.
  assert (HloHM : HIGHMEM_BEG <= sp - FN_STACK) by lia.
  assert (HspAE : sp <= APPMEM_END) by lia.
  pose proof (Happ fr ltac:(lia)) as Happ0. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Happ1.
  assert (Hfrtop : fr + FRAME_BYTES <= APPMEM_END) by (unfold app_mem in Happ1; lia).
  assert (HappY : app_mem (fr + 3040)) by (apply Happ; lia).
  (* the frame's 380 shadow bytes are shadow memory, apart from the frame *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx. rewrite (p5_sfr_shadow fr x). apply shadow_of_app. apply Happ. lia. }
  pose proof (HshIS (Sfr fr) ltac:(lia)) as Hin0. pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as Hin391.
  assert (HSlo : LOWMEM_END <= Sfr fr)
    by (unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in Hin0; lia).
  assert (HShi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in Hin391; lia).
  assert (HSfr : fr + FRAME_BYTES <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= fr) by (unfold app_mem in Happ0, Happ1; lia).
  assert (HD8 : (fr + 3056) mod 8 = 0).
  { replace (fr + 3056) with (fr + 382 * 8) by lia. rewrite Z.mod_add by lia. exact Hfr8. }
  assert (HDS : (fr + 3056) / 8 + ASAN_K = Sfr fr + 382).
  { unfold Sfr, shadow_addr. replace (fr + 3056) with (fr + 382 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (HYS : shadow_addr (fr + 3040) = Sfr fr + 380).
  { unfold Sfr, shadow_addr. replace (fr + 3040) with (fr + 380 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (HappD : app_ivl (fr + 3056) (fr + 3056 + 33)) by (intros a Ha; apply Happ; lia).
  destruct Hsh as (sh & Hshb & Hshl).
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as Hshadow_rw.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  (* the 380 frame shadow bytes as one writable cell *)
  assert (RWsh : LStep.rw_cells rsegs mem (Sfr fr) [LCells.CB 392 sh]).
  { split; [split|].
    - cbn [LCells.cells_wf LCells.cell_wf]. split; [rewrite Hshl, FRAME_SHADOW_val; reflexivity | exact I].
    - cbn [LCells.cells_bytes LCells.cbytes]. rewrite app_nil_r. exact Hshb.
    - cbn [LCells.cells_size LCells.csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi.
      exact (proj1 (Hshadow_rw (Sfr fr + i) (HshIS (Sfr fr + i) ltac:(lia)))). }
  pose proof (ro_c8 _ _ _ HQ280) as RO280. pose proof (ro_c8 _ _ _ HQ240) as RO240.
  (* run the segment *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81b90) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81bd8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       exists m1, LFr.munch [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 /\
         LFr.wmono rsegs mem m1 /\ ro_agree rsegs m1 /\
         (exists sh', bytes_at rsegs m1 (Sfr fr) sh' /\ length sh' = 392%nat) /\
         mrd rsegs m1 (wa (Sfr fr + 380)) = Some (Z_to_bv 8 1) /\
         (exists b, mrd rsegs m1 (wa (fr + 3040)) = Some b) /\
         LFr.munch [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' /\
         LFr.wmono rsegs m1 mem' /\ ro_agree rsegs mem' /\
         stk rsegs mem' (sp - FN_STACK) sp /\ (exists zs, LStep.rw_cells rsegs mem' (fr + 3056) [LCells.CB 32 zs]))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite p5_mkR_of.
    eapply evt_mono.
    + apply (p5_evt MSET) with (spv := sp) (A := A) (S := Sfr fr) (Y := fr + 3040) (D := fr + 3056)
        (lo := sp - FN_STACK) (sh := sh) (jy := jy) (junk := junk).
      all: try assumption.
      all: p5_lia.
    + intros ms' (R & m1 & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU1 & WM1 & RO1 & HSH1 &
                  H380 & HYp & MU2 & WM2 & RO2 & ST2 & RWz).
      exists R, (Z_to_bv 64 0x81bd8), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
      exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [exact RO1|]. split; [exact HSH1|].
      split; [exact H380|]. split; [exact HYp|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact RO2|]. split; [exact ST2 | exact RWz].
  - intros R pc' mem' regs'' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K22 & K25 & m1 & MU1 & WM1 & RO1 & HSH1 &
      H380 & (bY & HYb) & MU2 & WM2 & RO2 & STk & (zs & RWk)) Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    (* the memset's destination after the call: present and writable *)
    pose proof (LFr.stk_of_rw_cells rsegs mem' (fr + 3056) [LCells.CB 32 zs] RWk) as HDst.
    change (Z.of_nat (LCells.cells_size [LCells.CB 32 zs])) with 32 in HDst.
    (* ---- part 1: the stores, mem -> m1, W1 = the frame shadow bytes [S(fr)+370, +386) and fr + 3040 ---- *)
    assert (HW1 : forall x, 0 <= x < 2 ^ 64 ->
              LFr.outside [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] x \/
              ((fr <= x < fr + FRAME_BYTES \/ Sfr fr <= x < Sfr fr + FRAME_SHADOW \/ g_S g - AF.SLOT_STACK <= x < g_S g) /\
               exists b, mbyte rsegs m1 x = Some b)).
    { intros x Hx.
      destruct (Z.eq_dec x (fr + 3040)) as [->|HnY].
      - right. split; [left; lia|]. exists bY. exact HYb.
      - destruct (Z_lt_le_dec x (Sfr fr + 370)) as [Hl|Hl]; [left; p5_out2|].
        destruct (Z_lt_le_dec x (Sfr fr + 386)) as [Hh|Hh]; [|left; p5_out2].
        right. split; [right; left; lia|].
        destruct HSH1 as (sh' & Hsb' & Hsl').
        destruct (p5_ba_present m1 (Sfr fr) sh' x Hsb' ltac:(rewrite Hsl'; lia)) as (b & Hb).
        exists b. exact Hb. }
    destruct (p5_ah g fr regs mem m1 md _ HFRA MU1 WM1 HW1) as (HAH1 & Hown1 & HSTK1 & HSTKhi1).
    assert (HFRA1 : FRA B APIf ra g fr [] regs m1 md).
    { apply (sl_fr_meta B APIf ra empty FF g fr [] regs regs mem m1 md
               [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] HFRA).
      - p5_mu MU1.
      - exact WM1.
      - exact RO1.
      - unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
          RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
          RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from].
        repeat split; (lia || exact I).
      - exact HAH1.
      - exact HSTK1.
      - exact Happ.
      - exact HGT.
      - destruct HSH1 as (sh1 & Hsb1 & Hsl1). exists sh1. split; [exact Hsb1|].
        rewrite Hsl1, FRAME_SHADOW_val. reflexivity.
      - intros x Hx Hnb Hns. p5_out2.
      - intros A' HA' HA'r x Hx. pose proof (HA9 A' HA' HA'r) as ->. p5_out2.
      - intros x Hx. p5_out2.
      - intros A' HA' HA'r x Hx. pose proof (HA9 A' HA' HA'r) as ->. p5_out2.
      - intros x Hx. destruct (Z.eq_dec x (fr + 3040)) as [->|HnY].
        + right. exists bY. apply p5_mrd_hi; [lia | exact HYb].
        + left. p5_out2.
      - intros a Hin. apply (addr1_munch [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 a);
          [p5_mu MU1 | | exact (HAG a Hin)].
        pose proof (p5_ag_range a Hin) as Har.
        assert (HshA : LOWMEM_END <= shadow_addr a < Sfr fr + 370).
        { unfold Sfr, shadow_addr. rewrite HASK, HLE. Z.div_mod_to_equations. lia. }
        unfold app_mem in HappY. p5_out2.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    (* ---- part 2: the call, m1 -> mem', W2 = the 32 bytes at fr + 3056 and the memset scratch ---- *)
    assert (HW2 : forall x, 0 <= x < 2 ^ 64 ->
              LFr.outside [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] x \/
              ((fr <= x < fr + FRAME_BYTES \/ Sfr fr <= x < Sfr fr + FRAME_SHADOW \/ g_S g - AF.SLOT_STACK <= x < g_S g) /\
               exists b, mbyte rsegs mem' x = Some b)).
    { intros x Hx.
      assert (HinD : fr + 3056 <= x < fr + 3088 -> exists b, mbyte rsegs mem' x = Some b).
      { intros HxD. destruct HDst as (_ & _ & HDs). destruct (HDs x ltac:(lia)) as (_ & b & Hb).
        exists b. exact Hb. }
      assert (HinS : sp - ASAN_MEMSET_K <= x < sp -> exists b, mbyte rsegs mem' x = Some b).
      { intros HxS. destruct STk as (_ & _ & HSv). destruct (HSv x ltac:(lia)) as (_ & b & Hb).
        exists b. exact Hb. }
      destruct (Z_lt_le_dec x (fr + 3056)) as [H1|H1];
      destruct (Z_lt_le_dec x (fr + 3088)) as [H2|H2];
      destruct (Z_lt_le_dec x (sp - ASAN_MEMSET_K)) as [H3|H3];
      destruct (Z_lt_le_dec x sp) as [H4|H4];
      first [ left; p5_out2
            | right; split; [left; lia | apply HinD; lia]
            | right; split; [right; right; lia | apply HinS; lia] ]. }
    destruct (p5_ah g fr regs m1 mem' md _ HFRA1 MU2 WM2 HW2) as (HAH2 & Hown2 & HSTK2 & HSTKhi2).
    pose proof HFRA1 as HF1.
    destruct HF1 as (A1 & sp1 & s51 & HRT1 & HAH1f & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr21 & Hspm1 & Haspz1 &
      Hstklo1 & Hr41 & Hr81 & Hr91 & Hr31 & Hr191 & Hr261 & Hfrm1 & Hs51 & HAm1 & HAS1 & Hspa1 & Hfa1 & HA4161 &
      HS41 & HAPP1 & Hspill1 & Hsel1 & Hfr241 & Hloc1 & Hhdr11 & Hhdr21 &
      Hsh1 & Hwin1 & Hsaved1 & Herrno1 & HAG1 & HWA1 & HSHI11 & HSHI21 & HSHI31 & Hhb1 & Hlive1).
    (* the entry-anchored slot window after the call *)
    assert (HWIN2 : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (fl_stk [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' _ _ Hwin1 MU2 WM2).
      intros x Hx. destruct Hwin1 as (Hw0 & Hw1 & _).
      destruct (HW2 x ltac:(lia)) as [Ho | (_ & b & Hb)]; [left; exact Ho | right; exists b; exact Hb]. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr [] regs regs'' m1 mem' md
               [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] HFRA1).
      - p5_mu MU2.
      - exact WM2.
      - exact RO2.
      - cbn [all_app]. split; [|split; [|exact I]]; intros a Ha.
        + apply Happ. lia.
        + unfold app_mem. right. lia.
      - unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
          RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
          RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from].
        repeat split; (lia || exact I).
      - exact HAH2.
      - exact HSTK2.
      - intros x Hx. p5_out2.
      - intros x Hx. destruct HSEP0; p5_out2.
      - intros A' HA' HA'r x Hx. pose proof (HA9 A' HA' HA'r) as ->. p5_out2.
      - intros x Hx. p5_out2.
      - intros x Hx. destruct HSfr; p5_out2.
      - intros A' HA' HA'r x Hx. pose proof (HA9 A' HA' HA'r) as ->. p5_out2.
      - exact HWIN2.
      - apply (fra_fsrec_stklo B APIf ra g fr [] regs m1 mem' md
                 [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] HFRA1); [p5_mu MU2|].
        intros x Hx Hnb. rewrite HSTK1 in Hx. p5_out2.
      - exact E2.
      - exact E3.
      - exact E4.
      - exact E8.
      - exact E9.
      - exact E19.
      - exact E26. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity. exact Hmat. }
    (* ENT: each part writes only the frame, its shadow and the slot window below S (ent_store), then ent_mat *)
    assert (HENT1 : ENT APIf g [] m1 md).
    { eapply ent_store;
        [exact HENT | exact HFRA | p5_mu MU1 | | exact HSTK1 | exact HSTKhi1
        | exact (fun a _ Ho => proj2 (Hown1 a) Ho)].
      intros x Hx. destruct (HW1 x Hx) as [Ho | ([Hf | [Hs | Hw]] & _)].
      - left. p5_lf. exact Ho.
      - right. right. left. exact Hf.
      - right. right. right. exact Hs.
      - right. left. exact Hw. }
    assert (HENT2 : ENT APIf g [] mem' md).
    { eapply ent_store;
        [exact HENT1 | exact HFRA1 | p5_mu MU2 | | exact HSTK2 | exact HSTKhi2
        | exact (fun a _ Ho => proj2 (Hown2 a) Ho)].
      intros x Hx. destruct (HW2 x Hx) as [Ho | ([Hf | [Hs | Hw]] & _)].
      - left. p5_lf. exact Ho.
      - right. right. left. exact Hf.
      - right. right. right. exact Hs.
      - right. left. exact Hw. }
    assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT2 | exact Hmat]).
    pose proof HFRA' as HF'.
    destruct HF' as (Af & spf & s5f & HRTf & HAHf & Hrof & Hsnf & Hhaltf & Hgimgf & Hr2f & Hspmf & Haspzf &
      Hstklof & Hr4f & Hr8f & Hr9f & Hr3f & Hr19f & Hr26f & Hfrmf & Hs5f & HAmf & HASf & Hspaf & Hfaf & HA416f &
      HS4f & HAPPf & Hspillf & Hself & Hfr24f & Hlocf & Hhdr1f & Hhdr2f &
      Hshf & Hwinf & Hsavedf & Herrnof & HAGf & HWAf & HSHI1f & HSHI2f & HSHI3f & Hhbf & Hlivef).
    (* ---- the exit cut Inv_A81bd8 ---- *)
    rewrite <- SEGS. apply Hexit.
    exists regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hgn|].
    split.
    { (* our[] at fr + 2624: app bytes below the code byte, apart from the shadow and from the scratch *)
      unfold OURb in *. eapply fl_bytes; [eapply fl_bytes; [exact HOUR | exact MU1 |] | exact MU2 |];
        rewrite OUR_length; intros x Hx.
      - assert (Hxs : ~ (Sfr fr + 370 <= x < Sfr fr + 386))
          by (intro Hc; exact (app_not_shadow x (Happ x ltac:(lia)) (HshIS x ltac:(lia)))).
        cbn [outside]. split; [lia|]. split; [lia | exact I].
      - cbn [outside]. split; [lia|]. split; [destruct HSEP0; lia | exact I]. }
    split.
    { (* CUR: the run keeps s6 (x22) and s9 (x25) *)
      destruct HCUR as (Hc0 & H22 & H25). split; [exact Hc0|].
      unfold rg in *. split; [rewrite E22; exact H22 | rewrite E25; exact H25]. }
    split.
    { (* push 13: PRO across both parts (the frame shadow [S(fr) + 370, S(fr) + 386), the frame bytes fr + 3040 and
         [fr + 3056, fr + 3088), the callee window at or above stklo and below A: P1's pro_fra) *)
      set (Wp := [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1); (fr + 3056, fr + 3056 + 32);
                  (sp - ASAN_MEMSET_K, sp)]).
      assert (MUp : LibFr.munch Wp mem mem').
      { apply (LibFr.munch_trans Wp mem m1 mem').
        - eapply LibFr.munch_weaken; [| exact MU1]. intros x Hx. subst Wp. cbn [LibFr.outside] in Hx |- *.
          destruct Hx as (H1 & H2 & _ & _ & _). split; [exact H1|]. split; [exact H2 | exact I].
        - eapply LibFr.munch_weaken; [| exact MU2]. intros x Hx. subst Wp. cbn [LibFr.outside] in Hx |- *.
          destruct Hx as (_ & _ & H3 & H4 & _). split; [exact H3|]. split; [exact H4 | exact I]. }
      apply (pro_fra B APIf ra g fr [] regs regs'' mem mem' md Wp A HFRA HPRO Hr9 HAr MUp E9).
      subst Wp. repeat apply Forall_cons; try apply Forall_nil; unfold pro_iv; cbn [fst snd];
        clear - Hwlo HFN HMK Hspa HFBv HFSv; lia. }
    split.
    { (* the spill [A + 144] = fr + 2688: s1 is kept, and [A + 144] is above the frame and above sp *)
      exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in HQ144 |- *.
      assert (HS1 : bytes_at rsegs m1 (A + 144) (le8 (Z_to_bv 64 (fr + 2688)))).
      { apply (fl_bytes [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (A + 144) _ HQ144);
          [p5_mu MU1|]. rewrite length_le8. intros x Hx. p5_out2. }
      apply (fl_bytes [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (A + 144) _ HS1);
        [p5_mu MU2|]. rewrite length_le8. intros x Hx. p5_out2. }
    split.
    { (* the 17 bytes at fr + 2691 stay addressable: their shadow bytes S(fr) + 336 .. 338 are written by neither
         part (the stores hit S(fr) + 370 .. 385) *)
      assert (Hsa : forall i, 0 <= i < 17 -> Sfr fr + 336 <= shadow_addr (fr + 2691 + i) <= Sfr fr + 338).
      { intros i Hi. clear - Hfr8 Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
      apply (p5_addr_keep [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (fr + 2691) 17);
        [| p5_mu MU2 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2].
      apply (p5_addr_keep [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (fr + 2691) 17 HAD17);
        [p5_mu MU1 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2]. }
    split.
    { (* push 14D: the spill [A + 192] = fragb fr, as [A + 144] *)
      exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in HQ208 |- *.
      assert (HS1 : bytes_at rsegs m1 (A + 192) (le8 (Z_to_bv 64 (fragb fr)))).
      { apply (fl_bytes [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (A + 192) _ HQ208);
          [p5_mu MU1|]. rewrite length_le8. intros x Hx. p5_out2. }
      apply (fl_bytes [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (A + 192) _ HS1);
        [p5_mu MU2|]. rewrite length_le8. intros x Hx. p5_out2. }
    split.
    { (* push 14D: (fragb fr, 72) stays addressable: its shadow bytes S(fr) + 346 .. 354 are written by neither
         part *)
      assert (Hsa : forall i, 0 <= i < 72 -> Sfr fr + 346 <= shadow_addr (fragb fr + i) <= Sfr fr + 354).
      { intros i Hi. clear - Hfr8 Hi. unfold fragb, Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
      apply (p5_addr_keep [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (fragb fr) 72);
        [| p5_mu MU2 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2].
      apply (p5_addr_keep [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (fragb fr) 72 HADF);
        [p5_mu MU1 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2]. }
    split.
    { (* push 14D: (fr + 2688, 38) stays addressable: its shadow bytes S(fr) + 336 .. 340 likewise *)
      assert (Hsa : forall i, 0 <= i < 38 -> Sfr fr + 336 <= shadow_addr (fr + 2688 + i) <= Sfr fr + 340).
      { intros i Hi. clear - Hfr8 Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
      apply (p5_addr_keep [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (fr + 2688) 38);
        [| p5_mu MU2 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2].
      apply (p5_addr_keep [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (fr + 2688) 38 HADI);
        [p5_mu MU1 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2]. }
    split.
    { (* IDBe: the 38 identity-record bytes at fr + 2688 are app bytes below fr + 3040, apart from the scratch *)
      unfold IDBe in *.
      assert (HID0 : length RcIdentModel.ID0 = 38%nat) by reflexivity.
      assert (HI1 : bytes_at rsegs m1 (fr + 2688) RcIdentModel.ID0).
      { apply (fl_bytes [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (fr + 2688) _ HIDB);
          [p5_mu MU1|]. rewrite HID0. intros x Hx.
        assert (Hxs : ~ (Sfr fr + 370 <= x < Sfr fr + 386))
          by (intro Hc; exact (app_not_shadow x (Happ x ltac:(lia)) (HshIS x ltac:(lia)))).
        p5_out2. }
      apply (fl_bytes [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (fr + 2688) _ HI1);
        [p5_mu MU2|]. rewrite HID0. intros x Hx. destruct HSEP0; p5_out2. }
    split.
    { (* FGBe: the 72 fragment-scratch bytes at fr + 2768, the same way *)
      unfold FGBe in *.
      assert (HF1 : bytes_at rsegs m1 (fr + 2768) z72).
      { apply (fl_bytes [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (fr + 2768) _ HFGB);
          [p5_mu MU1|]. rewrite z72_length. intros x Hx.
        assert (Hxs : ~ (Sfr fr + 370 <= x < Sfr fr + 386))
          by (intro Hc; exact (app_not_shadow x (Happ x ltac:(lia)) (HshIS x ltac:(lia)))).
        p5_out2. }
      apply (fl_bytes [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (fr + 2768) _ HF1);
        [p5_mu MU2|]. rewrite z72_length. intros x Hx. destruct HSEP0; p5_out2. }
    split.
    { (* XC: the spill [A + 280] is kept; the code byte's shadow byte S(fr) + 380 holds 1 *)
      split.
      - intros A' HA' HA'r.
        assert (EA : A' = A) by (apply (HA9 A'); [unfold rg in HA'; rewrite <- E9; exact HA' | exact HA'r]).
        subst A'. unfold q64 in *.
        assert (HQ1 : bytes_at rsegs m1 (A + 280) (le8 (Z_to_bv 64 (fr + 3040)))).
        { apply (fl_bytes [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (A + 280) _ HQ280);
            [p5_mu MU1|]. rewrite length_le8. intros x Hx. p5_out2. }
        apply (fl_bytes [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (A + 280) _ HQ1);
          [p5_mu MU2|]. rewrite length_le8. intros x Hx. p5_out2.
      - assert (HY1 : mrd rsegs mem' (wa (Sfr fr + 380)) = Some (Z_to_bv 8 1)).
        { unfold mrd in H380 |- *. rewrite (MU2 (wa (Sfr fr + 380))); [exact H380|].
          rewrite wa_unsigned by lia. cbn [LFr.outside]. split; [destruct HSfr; lia|]. split; [lia | exact I]. }
        split; [lia|]. split; [lia|]. split; [lia|].
        intros i Hi. assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
        split; [exact HappY|]. exists (Z_to_bv 8 1). split; [rewrite HYS; exact HY1|].
        assert (E1 : bv_signed (Z_to_bv 8 1) = 1) by (first [reflexivity | vm_compute; reflexivity]).
        unfold shadow_ok. right. rewrite E1. split; [|lia].
        replace (fr + 3040) with (fr + 380 * 8) by lia. rewrite Z.mod_add by lia. rewrite Hfr8. lia. }
    (* the spills [A + 232] / [A + 224] / [A + 192]: bytes of the slot window, readable after the run *)
    pose proof HWIN2 as (Hw0 & Hw1 & HWv).
    destruct (p5_rd8_le8 mem' (A + 232) ltac:(lia) ltac:(lia)
                (fun i Hi => proj2 (HWv (A + 232 + i) ltac:(lia)))) as (wpa & Hpa).
    destruct (p5_rd8_le8 mem' (A + 224) ltac:(lia) ltac:(lia)
                (fun i Hi => proj2 (HWv (A + 224 + i) ltac:(lia)))) as (wpp & Hpp).
    destruct (p5_rd8_le8 mem' (A + 192) ltac:(lia) ltac:(lia)
                (fun i Hi => proj2 (HWv (A + 192 + i) ltac:(lia)))) as (wf & Hpf).
    (* the reply window [sp - K, sp) is addressable: it is inside the slot window and apart from the frame
       (fra_frame), so FRA's window-addressability conjunct covers each of its bytes *)
    assert (HADW : addressable mem' (AC.aspZ regs'' - RIR5.REAC_CTRL_IDENTITY_REPLY_K)
                     RIR5.REAC_CTRL_IDENTITY_REPLY_K).
    { assert (Easp : AC.aspZ regs'' = sp) by (unfold AC.aspZ in *; rewrite E2; exact Haspz).
      rewrite Easp, HKv.
      split; [lia|]. split; [lia|]. split; [lia|].
      intros i Hi.
      assert (Hwi : g_S g - AF.SLOT_STACK <= sp - 9072 + i < g_S g) by lia.
      assert (Hnf : ~ (fr <= sp - 9072 + i < fr + FRAME_BYTES))
        by (destruct (Hapart 9072 ltac:(lia)) as [Hd|Hd]; lia).
      destruct (HWAf (sp - 9072 + i) Hwi Hnf) as (_ & _ & _ & Hb).
      pose proof (Hb 0 ltac:(lia)) as Hb0. rewrite Z.add_0_r in Hb0. exact Hb0. }
    exists A, (bv_unsigned wpa), (bv_unsigned wpp), (bv_unsigned wf).
    split; [unfold rg; rewrite E9; exact Hr9|].
    split; [exact HAr|].
    split; [apply u64_range|]. split; [apply u64_range|].
    split; [unfold q64; rewrite Z_to_bv_bv_unsigned; exact Hpa|].
    split; [unfold q64; rewrite Z_to_bv_bv_unsigned; exact Hpp|].
    split; [unfold q64; rewrite Z_to_bv_bv_unsigned; exact Hpf|].
    split; [exact HADW|].
    split.
    { (* REAC_CTRL_PARSE_BC (.str.4, 0x21200 in v1.9.0, 0x211e0 in v1.8) is the frame_AG global (REAC_CTRL_PARSE_BC, 7)
         of the image FrameAPI.v and reac_ctrl_parse_c.v both describe *)
      apply (p5_ag mem' reac_ctrl_parse_c.REAC_CTRL_PARSE_BC 6 HAGf);
        [unfold reac_ctrl_parse_c.REAC_CTRL_PARSE_BC; lia | lia
        | unfold reac_ctrl_parse_c.REAC_CTRL_PARSE_BC; lia |].
      intros a Ha. hnf. exists reac_ctrl_parse_c.REAC_CTRL_PARSE_BC, 7. split; [|lia].
      unfold reac_ctrl_parse_c.REAC_CTRL_PARSE_BC.
      unfold AF.frame_AG. cbn [In]. repeat (first [left; reflexivity | right]). }
    (* round 4: first.sroa.7's 35 bytes at fr + 2880 stay addressable: their shadow bytes S(fr) + 360 .. 364 are
       written by neither part (the stores hit S(fr) + 370 .. 385, the call writes application bytes) *)
    assert (Hsa : forall i, 0 <= i < 35 -> Sfr fr + 360 <= shadow_addr (fr + 2880 + i) <= Sfr fr + 364).
    { intros i Hi. clear - Hfr8 Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
    apply (p5_addr_keep [(fr + 3056, fr + 3056 + 32); (sp - ASAN_MEMSET_K, sp)] m1 mem' (fr + 2880) 35);
      [| p5_mu MU2 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2].
    apply (p5_addr_keep [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1)] mem m1 (fr + 2880) 35 HAF);
      [p5_mu MU1 | intros i Hi; pose proof (Hsa i Hi); destruct HSfr; p5_out2].
Qed.

End P5W.
