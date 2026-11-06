(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module paths, module names and numbers changed; 1340 of its 1484 lines of code are new or changed and 1653 lines of the source are left out. *)
(* Segment F1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, patched image A): the frame-loop head, turn j, from
   0x81d40 through the allocation call at 0x81da0 to its return point 0x81da4 (F2's entry).
     81d40 srli a0,s6,3; add a0,a0,s10; lb a0,0(a0); bnez a0,82978 -- the instrumented check of the byte at the
       input cursor s6 = p + c: the shadow byte at (s6 >> 3) + K is loaded and the code goes on when it is 0; the
       out-of-line piece 82978 (andi a1,s6,7; bge a1,a0,82cac; j 81d50) re-checks (s6 mod 8) < k and returns to
       81d50. The input is addressable (f1_IN), so the error path 0x82cb0 is not reached.
     81d50 lbu a0,0(s6) (the low length byte); addi s4,s6,1; li a1,1; bne s9,a1,81d6c.
       left = 1: 81d60 li s9,0; li a1,0; j 81d8c (h = 1, the high byte is not read).
     81d6c srli a1,s4,3; add a1,a1,s10; lb a1,0(a1); bnez a1,82990 -- the same check at s4 = p + c + 1, with the
       out-of-line piece 82990 (andi a2,s4,7; bge a2,a1,82cb8; j 81d7c); 0x82cbc is not reached.
     81d7c lbu a1,0(s4) (the high length byte); addi s9,s9,-2; addi s4,s6,2; slli a1,a1,8.
     81d8c or s2,a1,a0 (L, the little-endian u16); bltu s2,s9,81d98; 81d94 mv s2,s9, so s2 = len = min(L, left - h);
     81d98 sd s9,224(s1) (the spill of left - h); 81d9c mv a0,s2; 81da0 jal 0x5337c, the memory-checking runtime's
       malloc (AC.aa_malloc at as_malloc = 0x5337c).
   The allocation gives the block Phi = a0 of a_size len bytes; the exit cut 0x81da4 carries HB(Phi, len).

   Cuts: the official SlotInv.v Inv_A81d40_at (entry) and Inv_A81da4_at (exit, F2's entry); seg_F1 is the form
   S_F1 of forms-asan.md. The run 0x81d40 -> 0x5337c is a Lib.Exec.evt (Tac_b5.sl_run_lib); FRA and ENT move
   across its one store [A + 224, A + 232) by f1_fra_spill (Tac_b5.sl_stk_run / Tac_slot.ent_store, after
   a Theorem Labs lane's f4_fra_spill); the allocation is AC.aa_malloc on SlotInv.fra_call_pre, with the room premise from
   FRA's live-bytes bound (f1_place_room) and the per-class premises from ENT #14 (Tac_cls.sl_malloc_cls); FRA
   moves across it by Tac_slot.sl_mid_perm (f1_malloc_keep) and ENT by f1_ent_call_perm (a Theorem Labs lane's R7.v
   ent_call_perm). The instruction-level run lemmas and the room lemmas are a Theorem Labs lane's (a working branch
   b5a32896e10). rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_cls.
(* last, so that munch / wmono / outside / bytes_at and the step tactics of this file are lib/Lib's *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.

(* ---- arithmetic and byte helpers ---- *)

(* The instrumented check: `bnez` on the shadow byte is taken only when the byte is not 0. *)
Lemma f1_sxb_nz : forall k : byte, bv_signed k <> 0 -> negb (bv_eqb (sxb k) (Z_to_bv 64 0)) = true.
Proof.
  intros k Hk. pose proof (sbyte_range k) as Hr. unfold bv_eqb, sxb.
  rewrite (MState.unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  apply negb_true_iff, Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

(* `andi aX,p,7; bge aX,k` is not taken when the shadow byte k passes the check: p mod 8 < k (signed). *)
Lemma f1_bge_ok : forall (q : Z) (k : byte), 0 <= q < 2 ^ 63 -> q mod 8 < bv_signed k ->
  negb (bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 q)) 7)) (sxb k)) = false.
Proof.
  intros q k Hq Hk. rewrite MState.unsigned_lit by lia. rewrite land7 by lia.
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  rewrite lts_sxb by lia. rewrite (proj2 (Z.ltb_lt _ _) Hk). reflexivity.
Qed.

Lemma f1_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma f1_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof.
  intros x y Hx Hy Hn. unfold bv_eqb. rewrite !MState.unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x y) Hn). reflexivity.
Qed.

Lemma f1_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. apply MState.unsigned_lit. lia.
Qed.

Lemma f1_lor_shl8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = x * 256 + y.
Proof.
  intros x y Hx Hy.
  assert (Hlg : Z.log2 y < 8).
  { destruct (Z.eq_dec y 0) as [->|Hy0]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Hand : Z.land (Z.shiftl x 8) y = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8) as [Hl|Hg].
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 y n) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hand. rewrite <- Z.add_nocarry_lxor by exact Hand.
  rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* (b1 << 8) | b0 is the little-endian u16 of the two length bytes. *)
Lemma f1_L : forall b0 b1 : byte,
  Z.lor (Z.shiftl (bv_unsigned (zxb b1)) 8) (bv_unsigned b0) = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof.
  intros b0 b1. rewrite f1_zxb_u.
  pose proof (bv_unsigned_in_range 8 b0). pose proof (bv_unsigned_in_range 8 b1).
  change (bv_modulus 8) with 256 in *.
  rewrite f1_lor_shl8 by lia. lia.
Qed.

Lemma f1_firstn1 : forall (bs : list byte) (k : nat), (k < length bs)%nat ->
  firstn 1 (skipn k bs) = [nthb bs k].
Proof.
  induction bs as [|b bs IH]; intros [|k] H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [skipn nthb nth]. apply IH. cbn [length] in H. lia.
Qed.

(* One byte of a bytes_at list, as the engine's load reads it. *)
Lemma f1_byte1 : forall (m : word -> option byte) (p k : Z) (bs : list byte),
  bytes_at rsegs m p bs -> 0 <= k -> k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (p + k)) 1 = Some [nthb bs (Z.to_nat k)].
Proof.
  intros m p k bs H Hk Hl.
  rewrite (bytes_at_read rsegs m p bs k 1 H Hk ltac:(lia)).
  rewrite (f1_firstn1 bs (Z.to_nat k) ltac:(lia)). reflexivity.
Qed.

(* One instrumented 1-byte shadow read of an addressable byte X: the shadow byte is readable and passes. *)
Lemma f1_shadow1 : forall (m : word -> option byte) (X : Z), addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b] /\
    (bv_signed b = 0 \/ X mod 8 < bv_signed b).
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & _).
  exists b. split.
  - pose proof (ro_cells_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes Z.of_nat] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
Qed.

(* Every segment of the image ends below LOWMEM_END, so a read-only address is below it. *)
Local Definition f1_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma f1_rsegs_low : f1_tops rsegs LOWMEM_END = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma f1_find_below : forall segs top x n s,
  f1_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f1_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f1_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < LOWMEM_END.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f1_find_below rsegs LOWMEM_END (bv_unsigned a) 1 s f1_rsegs_low E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

(* addressable moves across a memory change that keeps the shadow bytes of the range only. *)
Lemma f1_addr_keep : forall (m m' : word -> option byte) (p n : Z),
  addressable m p n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) HK. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|].
  exists b. split; [|exact Hok].
  change (mbyte rsegs m' (shadow_addr (p + i)) = Some b). rewrite (HK i Hi). exact Hb.
Qed.

(* ---- the model run 0x81d40 -> the allocator entry 0x5337c ----
   The four lemmas below are one straight-line run of the engine. It reads the shadow bytes at
   (p + c) >> 3 + K and (p + c + 1) >> 3 + K, the input bytes at p + c and p + c + 1, and the instruction
   stream in [0x81d40, 0x81da4), [0x82978, 0x82984) and [0x82990, 0x8299c); it writes the 8 bytes
   [s1 + 224, s1 + 232) of the caller's spill area, and nothing else. *)

(* 0x81d40-0x81d4c with the out-of-line piece 0x82978-0x82980: the check of the byte at s6 passes. *)
Lemma f1_chk0 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (q : Z) (k : byte),
    s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 ASAN_K -> 0 <= q < 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k] ->
    (bv_signed k = 0 \/ q mod 8 < bv_signed k) ->
    (forall a0' a1' : word, evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x81d50) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q q k -> -> Hq HK Hk HC.
  assert (HK' : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 q) ≫ 3 + ASAN_K)) 1 = Some [k])
    by (rewrite MState.unsigned_lit by lia; exact HK).
  clear HK.
  step. step. step. step.
  destruct (Z.eq_dec (bv_signed k) 0) as [E0|E0].
  - rewrite (byte_s0 k E0).
    if_false_by (eq_refl : negb (bv_eqb (sxb (Z_to_bv 8 0)) (Z_to_bv 64 0)) = false).
    exact (HC _ _).
  - if_true_by (f1_sxb_nz k E0).
    step. step.
    destruct Hk as [Hk|Hk]; [contradiction|].
    if_false_by (f1_bge_ok q k Hq Hk).
    step.
    exact (HC _ _).
Qed.

(* 0x81d6c-0x81d78 with the out-of-line piece 0x82990-0x82998: the check of the byte at s4 passes. *)
Lemma f1_chk1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (q : Z) (k : byte),
    s4 = Z_to_bv 64 q -> s10 = Z_to_bv 64 ASAN_K -> 0 <= q < 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k] ->
    (bv_signed k = 0 \/ q mod 8 < bv_signed k) ->
    (forall a1' a2' : word, evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x81d7c) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q q k -> -> Hq HK Hk HC.
  assert (HK' : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 q) ≫ 3 + ASAN_K)) 1 = Some [k])
    by (rewrite MState.unsigned_lit by lia; exact HK).
  clear HK.
  step. step. step. step.
  destruct (Z.eq_dec (bv_signed k) 0) as [E0|E0].
  - rewrite (byte_s0 k E0).
    if_false_by (eq_refl : negb (bv_eqb (sxb (Z_to_bv 8 0)) (Z_to_bv 64 0)) = false).
    exact (HC _ _).
  - if_true_by (f1_sxb_nz k E0).
    step. step.
    destruct Hk as [Hk|Hk]; [contradiction|].
    if_false_by (f1_bge_ok q k Hq Hk).
    step.
    exact (HC _ _).
Qed.

(* 0x81d8c .. jal 0x5337c: s2 = min(L, rest) for L = a1 | a0, the spill [s1 + 224] = rest, a0 = s2,
   ra = 0x81da4. The only write of the segment is the 8 bytes at s1 + 224. *)
Lemma f1_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A lo hi rest : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 lo -> a1 = Z_to_bv 64 hi -> s9 = Z_to_bv 64 rest ->
    0 <= A -> A + 232 <= 2 ^ 64 -> 0 <= lo < 2 ^ 64 -> 0 <= hi < 2 ^ 64 -> 0 <= Z.lor hi lo < 2 ^ 64 ->
    0 <= rest < 2 ^ 64 ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.min (Z.lor hi lo) rest))
                          a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.min (Z.lor hi lo) rest)) s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6)
                    F (Z_to_bv 64 0x5337c) fc None (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 rest)))
                    (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d8c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A lo hi rest -> -> -> -> HA0 HA1 Hlo Hhi HL Hrest HS.
  step.
  rewrite (MState.unsigned_lit hi), (MState.unsigned_lit lo) by lia.
  step.
  destruct (Z_lt_le_dec (Z.lor hi lo) rest) as [Hlt|Hge].
  - if_true_by (eq_trans (f1_ltu _ _ HL Hrest) (proj2 (Z.ltb_lt _ _) Hlt)).
    step. step. step.
    rewrite (Z.min_l _ _ (Z.lt_le_incl _ _ Hlt)).
    apply evt_done. reflexivity.
  - if_false_by (eq_trans (f1_ltu _ _ HL Hrest) (proj2 (Z.ltb_ge _ _) Hge)).
    step. step. step. step.
    rewrite (Z.min_r _ _ Hge).
    apply evt_done. reflexivity.
Qed.

(* The whole run: p + c = q, left = n - c, h = min(2, left), L the u16 of the two length bytes,
   len = min(L, left - h). *)
Lemma f1_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A q left : Z) (b0 b1 k0 k1 : byte),
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 left -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= q -> q + left < 2 ^ 63 -> 1 <= left < 2 ^ 26 -> 0 <= A -> A + 232 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    (bv_signed k0 = 0 \/ q mod 8 < bv_signed k0) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left ->
       ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1] /\
       (bv_signed k1 = 0 \/ (q + 1) mod 8 < bv_signed k1) /\
       ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       s3 (Z_to_bv 64 (q + Z.min 2 left)) s5 s6 s7 s8 (Z_to_bv 64 (left - Z.min 2 left)) s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None
                  (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 (left - Z.min 2 left)))) (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A q left b0 b1 k0 k1 -> -> -> -> Hq0 Hq1 Hl HA0 HA1 HK0 Hk0 HB0 H2 HS.
  pose proof (bv_unsigned_in_range 8 b0) as Hb0. pose proof (bv_unsigned_in_range 8 b1) as Hb1.
  change (bv_modulus 8) with 256 in Hb0, Hb1.
  apply (f1_chk0 ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 q) s7 s8
           (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6 F fc m _ q k0 eq_refl eq_refl ltac:(lia) HK0 Hk0).
  intros a0' a1'.
  step. step. step. step.
  destruct (Z.eq_dec left 1) as [E1|E1].
  - (* left = 1: h = 1, len = 0, the high byte is not read *)
    subst left.
    if_false_by (eq_refl : negb (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 1)) = false).
    step. step. step.
    eapply evt_mono.
    { eapply f1_tail with (A := A) (lo := bv_unsigned b0) (hi := 0) (rest := 0);
        [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | | lia | exact HS].
      rewrite Z.lor_0_l. lia. }
    intros ms' ->. do 2 eexists.
    replace (Z.min (bv_unsigned b0 + (if 2 <=? 1 then 256 * bv_unsigned b1 else 0)) (1 - Z.min 2 1))
      with (Z.min (Z.lor 0 (bv_unsigned b0)) 0) by (rewrite Z.lor_0_l; cbn; lia).
    replace (1 - Z.min 2 1) with 0 by lia.
    replace (q + Z.min 2 1) with (q + 1) by lia.
    reflexivity.
  - (* left >= 2: h = 2 *)
    if_true_by (f1_ne left 1 ltac:(lia) ltac:(lia) E1).
    destruct (H2 ltac:(lia)) as (HK1 & Hk1 & HB1).
    apply (f1_chk1 ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb b0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3
             (Z_to_bv 64 (q + 1)) s5 (Z_to_bv 64 q) s7 s8 (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6
             F fc m _ (q + 1) k1 eq_refl eq_refl ltac:(lia) HK1 Hk1).
    intros a1'' a2''.
    step. step. step. step.
    eapply evt_mono.
    { eapply f1_tail with (A := A) (lo := bv_unsigned b0) (rest := left + -2);
        [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | | | lia | exact HS].
      - rewrite f1_zxb_u, Z.shiftl_mul_pow2 by lia. lia.
      - rewrite f1_L. lia. }
    intros ms' ->. do 2 eexists.
    rewrite f1_L.
    rewrite (proj2 (Z.leb_le 2 left)) by lia.
    replace (Z.min 2 left) with 2 by lia.
    replace (left - 2) with (left + -2) by lia.
    reflexivity.
Qed.

(* ---- the allocation room premise: the secondary-map placement bound a_place_room ---- *)

Lemma f1_rup_le : forall x a, 0 < a -> AC.a_rup x a <= x + a - 1.
Proof.
  intros x a Ha. unfold AC.a_rup. rewrite Z.mul_comm. apply Z.mul_div_le. exact Ha.
Qed.

Lemma f1_sec_map_le : forall n, 0 <= n -> AC.a_sec_map n <= n + 12294.
Proof.
  intros n Hn. unfold AC.a_sec_map.
  pose proof (f1_rup_le n 8 ltac:(lia)) as H1.
  pose proof (f1_rup_le (AC.a_rup n 8 + 4096) 4096 ltac:(lia)) as H2.
  lia.
Qed.

(* a_sec_blocks is stdpp's filter; its two cons cases. *)
Lemma f1_sec_cons_T : forall p n H, AC.A_PRIMARY_MAX < n ->
  AC.a_sec_blocks ((p, n) :: H) = (p, n) :: AC.a_sec_blocks H.
Proof.
  intros p n H Hn. unfold AC.a_sec_blocks, stdpp.base.filter, list_basics.list.list_filter.
  cbn [snd]. rewrite (proj2 (Z.ltb_lt _ _) Hn).
  lazymatch goal with |- context [@decide ?P ?D] => destruct (@decide P D) as [Hd|Hd] end;
    [reflexivity | exfalso; exact (Hd I)].
Qed.

Lemma f1_sec_cons_F : forall p n H, n <= AC.A_PRIMARY_MAX ->
  AC.a_sec_blocks ((p, n) :: H) = AC.a_sec_blocks H.
Proof.
  intros p n H Hn. unfold AC.a_sec_blocks, stdpp.base.filter, list_basics.list.list_filter.
  cbn [snd]. rewrite (proj2 (Z.ltb_ge _ _) Hn).
  lazymatch goal with |- context [@decide ?P ?D] => destruct (@decide P D) as [Hd|Hd] end;
    [exfalso; exact Hd | reflexivity].
Qed.

Lemma f1_live_cons : forall p n H, AC.a_live_bytes ((p, n) :: H) = n + AC.a_live_bytes H.
Proof. intros. reflexivity. Qed.

Lemma f1_live_nonneg : forall H, (forall p n, In (p, n) H -> 0 <= n) -> 0 <= AC.a_live_bytes H.
Proof.
  induction H as [|[p n] H IH]; intros Hnn; [cbn; lia|].
  rewrite f1_live_cons.
  assert (0 <= n) by (apply (Hnn p n); left; reflexivity).
  assert (0 <= AC.a_live_bytes H) by (apply IH; intros p' n' Hin; apply (Hnn p' n'); right; exact Hin).
  lia.
Qed.

Lemma f1_sec_count : forall H, (forall p n, In (p, n) H -> 0 <= n) ->
  64512 * Z.of_nat (length (AC.a_sec_blocks H)) <= AC.a_live_bytes H.
Proof.
  induction H as [|[p n] H IH]; intros Hnn; [cbn; lia|].
  assert (Hn : 0 <= n) by (apply (Hnn p n); left; reflexivity).
  assert (IH' : 64512 * Z.of_nat (length (AC.a_sec_blocks H)) <= AC.a_live_bytes H)
    by (apply IH; intros p' n' Hin; apply (Hnn p' n'); right; exact Hin).
  rewrite f1_live_cons.
  destruct (Z_lt_le_dec AC.A_PRIMARY_MAX n) as [Hl|Hl].
  - rewrite (f1_sec_cons_T p n H Hl). cbn [length]. unfold AC.A_PRIMARY_MAX in Hl. lia.
  - rewrite (f1_sec_cons_F p n H Hl). lia.
Qed.

Lemma f1_sec_mapped : forall H, (forall p n, In (p, n) H -> 0 <= n) ->
  AC.a_sec_mapped H <= AC.a_live_bytes H + 12294 * Z.of_nat (length (AC.a_sec_blocks H)).
Proof.
  induction H as [|[p n] H IH]; intros Hnn; [cbn; lia|].
  assert (Hn : 0 <= n) by (apply (Hnn p n); left; reflexivity).
  assert (Hnn' : forall p' n', In (p', n') H -> 0 <= n')
    by (intros p' n' Hin; apply (Hnn p' n'); right; exact Hin).
  assert (IH' : AC.a_sec_mapped H <= AC.a_live_bytes H + 12294 * Z.of_nat (length (AC.a_sec_blocks H)))
    by exact (IH Hnn').
  pose proof (f1_live_nonneg H Hnn') as Hpos.
  unfold AC.a_sec_mapped in *. rewrite f1_live_cons.
  destruct (Z_lt_le_dec AC.A_PRIMARY_MAX n) as [Hl|Hl].
  - rewrite (f1_sec_cons_T p n H Hl). cbn [map fold_right length snd].
    pose proof (f1_sec_map_le n Hn). lia.
  - rewrite (f1_sec_cons_F p n H Hl). lia.
Qed.

(* The allocation's placement room for a request of at most 65535 bytes (the u16 length): the secondary-map
   bound (with the v1.9 base's A_PLACE_OTHER / A_PLACE_OTHER_N reserve) holds with a wide margin, since the live
   heap is at most 5 * 2^30 bytes (FRA, from frame batch 2's alib_pre). *)
Lemma f1_place_room : forall H n, (forall p k, In (p, k) H -> 0 <= k) ->
  AC.a_live_bytes H <= 5 * 2 ^ 30 -> 0 <= n <= 65535 -> AC.a_place_room H n.
Proof.
  intros H n Hnn Hlive Hn. right.
  pose proof (f1_sec_count H Hnn) as Hc.
  pose proof (f1_sec_mapped H Hnn) as Hm.
  pose proof (f1_sec_map_le n ltac:(lia)) as Hs.
  set (c := Z.of_nat (length (AC.a_sec_blocks H))) in *.
  assert (Hc0 : 0 <= c) by (unfold c; lia).
  assert (Hcb : c <= 83220) by lia.
  assert (Hprod : (c + 8355) * (AC.a_sec_map n + 4096) <= (c + 8355) * 81925).
  { apply Z.mul_le_mono_nonneg_l; lia. }
  assert (Hprod2 : (c + 8355) * 81925 <= 91575 * 81925) by (apply Z.mul_le_mono_nonneg_r; lia).
  unfold AC.A_PLACE_HI, AC.A_PLACE_LO, AC.A_PLACE_OTHER, AC.A_PLACE_OTHER_N.
  change (2 ^ 41) with 2199023255552. lia.
Qed.

(* ---- memory-keeping helpers for the allocation call ---- *)

(* bytes_at survives a memory change that keeps each byte of its range. *)
Lemma f1_bkeep : forall (mem mem' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs.
Proof.
  intros mem mem' a bs HK (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi).
  change (mbyte rsegs mem' (a + Z.of_nat i) = mbyte rsegs mem (a + Z.of_nat i)).
  apply HK. lia.
Qed.

(* addressable from the per-byte facts. *)
Lemma f1_addr_join : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall a, p <= a < p + n -> addressable m a 1) -> addressable m p n.
Proof.
  intros m p n H1 H2 H3 H. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H (p + i) ltac:(lia)) as (_ & _ & _ & Ha). specialize (Ha 0 ltac:(lia)).
  rewrite Z.add_0_r in Ha. exact Ha.
Qed.

(* A range of image bytes, found by computation over the image's segments. *)
Lemma f1_img_seg : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs
    = true ->
  forall a, lo <= a < hi -> AC.a_in_img a.
Proof.
  intros lo hi H a Ha. apply existsb_exists in H as (s & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

(* errno [0x5db76c, 0x5db770) and the runtime's OOM flag 0x12aae0 are image bytes. *)
Lemma f1_errno_img : forall a, 0x5db76c <= a < 0x5db770 -> AC.a_in_img a.
Proof. apply f1_img_seg. vm_compute. reflexivity. Qed.

Lemma f1_oom_img : AC.a_in_img 0x12aae0.
Proof. apply (f1_img_seg 0x12aae0 0x12aae1); [vm_compute; reflexivity | lia]. Qed.

(* The registered globals of frame_AG lie in the image's segments and in [0x21140, 0x9f8e8). *)
Lemma f1_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => existsb (fun s => (Z.of_N (seg_base s) <=? fst p) &&
                   (fst p + snd p <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin). apply existsb_exists in Hall as (s & Hs & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
  exists s. split; [exact Hs | lia].
Qed.

Lemma f1_ag_range : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (0x21140 <=? fst p) && (fst p + snd p <=? 0x9f8e8)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin).
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. lia.
Qed.

(* ---- the segment ---- *)

Lemma f1_app_ivl : forall lo hi, HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> app_ivl lo hi.
Proof. intros lo hi H1 H2 a Ha. unfold app_mem. right. lia. Qed.

Lemma f1_id : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.
(* A spill word whose eight bytes read the same in m' (and the base register is kept) is still the spill. The
   spill's own existential base names the same A as FRA: the cell is inside [A, A + 416). *)
Lemma f1_spill_move : forall regs regs' A off v m m',
  spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END -> 0 <= off <= 408 ->
  getr regs' 9 = getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' A off v m m' (A' & H9' & Hq) H9 HA HAE Hoff E9 HK.
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A'.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  unfold q64 in *. apply (f1_bkeep m m'); [|exact Hq].
  rewrite length_le8. intros x Hx. apply HK. lia.
Qed.

(* stk survives a change that keeps each byte and the writability of the range. *)
Lemma f1_stk_keep : forall m m' lo hi, stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> mbyte rsegs m' a = mbyte rsegs m a) ->
  (forall a, lo <= a < hi -> writable_at rsegs m a -> writable_at rsegs m' a) ->
  stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) HB HW. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb). split.
  - exact (HW a Ha Hv).
  - exists b. rewrite <- fsf_mbyte_mrd. rewrite (HB a Ha). rewrite fsf_mbyte_mrd. exact Hb.
Qed.

(* The identity record of every turn has 38 bytes and the fragment record 72: the frame-loop state keeps both
   lengths across a turn (a Theorem Labs lane's R7tail.v r7t_fg_st_len / r7t_RS_len, after a Theorem Labs lane's Seg/R15.v). *)
Lemma f1_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, fg_class.
  change ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) with false. cbv iota.
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. rewrite !andb_true_iff in Efr. destruct Efr as [[[_ H1] H2] _].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hb : forall bs i, 0 <= bat bs i).
  { intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. }
  assert (Hbody : length (fg_body g) = Z.to_nat (fg_n g)).
  { unfold fg_body, bsl. rewrite length_firstn, length_skipn, Hg. lia. }
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. unfold fg_first. rewrite !length_app, Hbody, length_skipn, Hs. cbn [length].
    unfold bsl. rewrite length_firstn, length_skipn, Hg. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|cbn [fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hs; cbn [length]; lia].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as [_ H]. apply Z.leb_le in H. exact H. }
    assert (Hj : length (fg_join st g) = 72%nat).
    { unfold fg_join. unfold fg_T, fg_lf in HT. pose proof (Hb st 7).
      rewrite !length_app, Hbody, length_firstn, length_skipn, Hs. unfold fg_T, fg_lf. lia. }
    destruct (fg_close st g); cbn [negb fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hj; cbn [length]; lia.
Qed.

Lemma f1_id_len : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof.
  intros idb len g H. unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma f1_fgid_len : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof.
  intros idb len st g H. unfold fg_id.
  destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma f1_FS_len : forall inp j, length (t_ID inp j) = 38%nat /\ length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_ID, t_FG. induction j as [|j [IH1 IH2]]; [split; reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  assert (L1 : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                 (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat)
    by (apply f1_fgid_len, f1_id_len, IH1).
  assert (L2 : length (fg_st (t_len inp j) (fs_fg (fst_at inp j)) (t_g inp j)) = 72%nat)
    by (apply f1_fg_st_len; [exact IH2 | unfold t_g; apply fr50_length]).
  destruct (f_opens _ _); cbn [fs_id fs_fg]; split; assumption.
Qed.

(* The first fragment's body (SlotModel.fs_body) is a part of a 50-byte frame past its byte 27: at most 23 bytes. *)
Lemma f1_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens _ _); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* IFS (the identity record at fr + 2688, the fragment record at fr + 2768, the first-fragment spills [A + 104, A + 120)
   and the first fragment's body at fr + 2880, at most 23 bytes of the 35 addressable ones) moves to m' when those
   bytes and the shadow of the 35 body bytes read the same and the base register is kept. *)
Lemma f1_ifs_move : forall g fr j regs regs' A m m',
  IFS g fr j regs m -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END ->
  getr regs' 9 = getr regs 9 ->
  (forall x, fr + 2688 <= x < fr + 2915 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, A + 104 <= x < A + 120 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  IFS g fr j regs' m'.
Proof.
  intros g fr j regs regs' A m m' ((HID & Hidok) & (HFG & Hfgok) & (S104 & S112 & HBD & HAB & HFI))
    H9 HA HAE E9 KF KS KSH.
  destruct (f1_FS_len (g_in g) j) as (L1 & L2).
  pose proof (f1_body_len (g_in g) j) as L3.
  split; [split; [|exact Hidok]|split; [split; [|exact Hfgok]|]].
  - unfold IDBe in *. apply (f1_bkeep m m'); [|exact HID]. rewrite L1.
    intros x Hx. apply KF. lia.
  - unfold FGBe in *. apply (f1_bkeep m m'); [|exact HFG]. rewrite L2.
    intros x Hx. apply KF. lia.
  - split; [exact (f1_spill_move regs regs' A 104 _ m m' S104 H9 HA HAE ltac:(lia) E9
                     ltac:(intros x Hx; apply KS; lia))|].
    split; [exact (f1_spill_move regs regs' A 112 _ m m' S112 H9 HA HAE ltac:(lia) E9
                     ltac:(intros x Hx; apply KS; lia))|].
    split; [apply (f1_bkeep m m'); [|exact HBD]; intros x Hx; apply KF; lia|].
    split; [apply (f1_addr_keep m m' (fr + 2880) 35 HAB); intros i Hi; apply KSH; lia|].
    exact HFI.
Qed.

(* FLC (SlotInv.v, push 14D / 14E: the frame-loop pointer spills, record ranges and compare spills of b5_C / b5_PF
   that no frame-loop instruction writes) moves to m' when its save-area words and the shadow of the two frame
   records read the same. *)
Lemma flc_move : forall fr regs regs' A m m', FLC fr regs m -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  A + 416 <= APPMEM_END -> getr regs' 9 = getr regs 9 ->
  (forall x, A + 40 <= x < A + 216 \/ A + 248 <= x < A + 304 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  FLC fr regs' m'.
Proof.
  intros fr regs regs' A m m'
    (S256 & S184 & S192 & S80 & S88 & S96 & S272 & S264 & HA72 & HA38 & S72 & S64 & S56 & S48)
    H9 HA HAE E9 KB KS.
  assert (SPK : forall off v, 40 <= off <= 208 \/ 248 <= off <= 296 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hs. apply (f1_spill_move regs regs' A off v m m' Hs H9 HA HAE ltac:(lia) E9).
    intros x Hx. apply KB. lia. }
  split; [exact (SPK 256 _ ltac:(lia) S256)|].
  split; [exact (SPK 184 _ ltac:(lia) S184)|].
  split; [exact (SPK 192 _ ltac:(lia) S192)|].
  split; [exact (SPK 80 _ ltac:(lia) S80)|].
  split; [exact (SPK 88 _ ltac:(lia) S88)|].
  split; [exact (SPK 96 _ ltac:(lia) S96)|].
  split; [exact (SPK 272 _ ltac:(lia) S272)|].
  split; [exact (SPK 264 _ ltac:(lia) S264)|].
  split; [apply (f1_addr_keep m m' (fragb fr) 72 HA72); intros i Hi; apply KS; unfold fragb; lia|].
  split; [apply (f1_addr_keep m m' (fr + 2688) 38 HA38); intros i Hi; apply KS; lia|].
  split; [exact (SPK 72 _ ltac:(lia) S72)|].
  split; [exact (SPK 64 _ ltac:(lia) S64)|].
  split; [exact (SPK 56 _ ltac:(lia) S56) | exact (SPK 48 _ ltac:(lia) S48)].
Qed.

(* FLSH (push 13B / 14D: PRO /\ [A + 128] /\ stk fr /\ [A + 144] /\ the 17 bytes at fr + 2691) moves to m' when its
   save-area words, the shadow of our[] and of fr + 2691 .. fr + 2707, and the input block with its shadow read the
   same; the byte-backed frame comes from the caller (SlotInv.fra_stk at any FRA state). *)
Lemma flsh_move : forall g j fr regs regs' A m m', FLSH g j fr regs m -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  A + 416 <= APPMEM_END -> getr regs' 9 = getr regs 9 ->
  (forall x, A + 32 <= x < A + 216 \/ A + 248 <= x < A + 304 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2624 <= x < fr + 2708 -> mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  (forall x, g_p g <= x < g_p g + g_n g ->
     mbyte rsegs m' x = mbyte rsegs m x /\ mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  stk rsegs m' fr (fr + FRAME_BYTES) ->
  FLSH g j fr regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g j fr regs regs' A m m'
    ((S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248 & HA2624 & HPB & HPG & P184 & P256 & P264 & P272 &
      P32) &
     S128 & _ & S144 & HA2691)
    H9 HA HAE E9 KB KS KI HSTK.
  assert (SPK : forall off v, 32 <= off <= 208 \/ 248 <= off <= 296 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hs. apply (f1_spill_move regs regs' A off v m m' Hs H9 HA HAE ltac:(lia) E9).
    intros x Hx. apply KB. lia. }
  split.
  { split; [exact (SPK 40 _ ltac:(lia) S40)|].
    split; [exact (SPK 120 _ ltac:(lia) S120)|].
    split; [exact (SPK 136 _ ltac:(lia) S136)|].
    split; [exact (SPK 160 _ ltac:(lia) S160)|].
    split; [exact (SPK 168 _ ltac:(lia) S168)|].
    split; [exact (SPK 176 _ ltac:(lia) S176)|].
    split; [exact (SPK 208 _ ltac:(lia) S208)|].
    split; [exact (SPK 248 _ ltac:(lia) S248)|].
    split; [apply (f1_addr_keep m m' (fr + 2624) 6 HA2624); intros i Hi; apply KS; lia|].
    split.
    - apply (f1_bkeep m m'); [|exact HPB]. intros x Hx. rewrite <- g_n_len in Hx. exact (proj1 (KI x Hx)).
    - split.
      + intros Hn. destruct (HPG Hn) as (Hin & Had). split; [exact Hin|].
        apply (f1_addr_keep m m' _ _ Had). intros i Hi. exact (proj2 (KI (g_p g + i) ltac:(lia))).
      + split; [exact (SPK 184 _ ltac:(lia) P184)|].
        split; [exact (SPK 256 _ ltac:(lia) P256)|].
        split; [exact (SPK 264 _ ltac:(lia) P264)|].
        split; [exact (SPK 272 _ ltac:(lia) P272) | exact (SPK 32 _ ltac:(lia) P32)]. }
  split; [exact (SPK 128 _ ltac:(lia) S128)|].
  split; [exact HSTK|].
  split; [exact (SPK 144 _ ltac:(lia) S144)|].
  apply (f1_addr_keep m m' (fr + 2691) 17 HA2691). intros i Hi. apply KS. lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* ENT across a callee's a_call_post whose post heap H' is a permutation of hb' ++ g_H g (amalloc_ret's append
   order g_H g ++ [(q, n)], while ENT and the cut 0x81640 use prepend order). Tac_slot.ent_call copied with the
   heap steps changed: the frame clause and the not-owned laws are read on H' (an entry block is a
   block of H' by the permutation), and ENT's image clause, which names hb' ++ g_H g, meets the frame clause's H'
   through Tac_slot.ent_owned_img with the same memory and model on both sides (the AH of hb' ++ g_H g is
   a_laws_perm of the call's AH H'; the stack bottom and the 16 bytes at tp are equal by reflexivity). *)
Lemma f1_ent_call_perm : forall g fr hb hb' H' regs mem md regs' mem' md' touched K,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT API) (AC.aa_owned AC.ASYMS AsanRTInv.RT API)
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API)
    K (hb ++ g_H g) regs mem md touched H' regs' mem' md' ->
  Permutation (hb' ++ g_H g) H' ->
  0 <= K <= FN_STACK ->
  (forall a, touched a -> app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a) ->
  AC.a_errno_kept AC.ASYMS mem mem' ->
  ENT APIf g hb' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb hb' H' regs mem md regs' mem' md' touched K HENT HFRA Hcp Hperm HK Hto Hek.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HENT as HE0.
  destruct HE0 as (Hasp & Hgtp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hblks & Hcls).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) (hb ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh.
  pose proof Hcp as Hah'; apply AC.a_call_post_ah in Hah'.
  assert (HahP : AC.aa_AH AC.ASYMS AsanRTInv.RT API (hb' ++ g_H g) mem' md')
    by exact (AC.a_laws_perm _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H' (hb' ++ g_H g) mem' md' Hah'
                (Permutation_sym Hperm)).
  pose proof Hcp as Hsk; apply AC.a_call_post_stklo in Hsk.
  pose proof Hcp as Hskh; apply AC.a_call_post_stkhi in Hskh.
  pose proof Hcp as Hoom; apply AC.a_call_post_oom in Hoom.
  assert (Htp : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (Hfr : forall a, 0 <= a < 2 ^ 64 ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' a ->
            ~ AC.a_window K regs a -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
            a <> AC.as_oom AC.ASYMS -> ~ touched a ->
            mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (eapply AC.a_call_post_frame; exact Hcp).
  (* the callee's window is inside the slot window, so it is below S *)
  assert (Hwin2 : forall a, AC.a_window K regs a ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < g_S g).
  { intros a Ha. unfold AC.a_window in Ha. unfold FN_STACK in Hwlo.
    rewrite Haspz in Ha. rewrite Haspz in Hwlo. lia. }
  assert (Hoomimg : AC.a_in_img (AC.as_oom AC.ASYMS)) by exact oom_in_img.
  split; [exact Hasp|]. split; [exact Hgtp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|].
  split.
  { destruct Hmdl as (lz & mt & vm0 & fds0 & pins0 & Hmd & Hfd).
    destruct Hcp as (_ & _ & _ & (lz1 & mt1 & vm1 & Hmd1) & _).
    exists lz1, mt1, vm1, fds0, pins0. split; [|exact Hfd].
    exact (md_shape_step (g_md g) md md' lz mt vm0 fds0 (m_fs (g_md g)) pins0 lz1 mt1 vm1 Hmd Hmd1). }
  split; [rewrite Hsk; exact Hslo|].
  split; [rewrite Hskh; exact Hshi|].
  split.
  { intros q k i Hin Hni Hi.
    destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (_ & Hq4 & Hend & _ & Hall).
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & Hnimg & _ & _).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hinb : AC.in_blocks (g_H g) (q + i)) by (exists q, k; split; [exact Hin | lia]).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (Hinb2 : AC.in_blocks H' (q + i))
      by (exists q, k; split; [apply (Permutation_in _ Hperm); apply in_or_app; right; exact Hin | lia]).
    assert (Hn1 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md (q + i))
      by exact (proj1 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hn2 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' (q + i))
      by exact (proj1 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  H' mem' md' (q + i) Hah' (or_introl Hinb2))).
    assert (Hnw : ~ AC.a_window K regs (q + i)) by (intro Hw; pose proof (Hwin2 _ Hw); lia).
    assert (Hne : ~ (AC.a_errno AC.ASYMS <= q + i < AC.a_errno AC.ASYMS + 4))
      by (intro He; exact (Hnimg (errno_in_img (q + i) He))).
    assert (Hno : q + i <> AC.as_oom AC.ASYMS) by (intro He; apply Hnimg; rewrite He; exact Hoomimg).
    assert (Hnt : ~ touched (q + i)) by (intro Ht; exact (proj2 (proj2 (proj2 (Hto (q + i) Ht))) Hinb)).
    rewrite (proj1 (Hfr (q + i) Hqr Hn1 Hn2 Hnw Hne Hno Hnt)).
    exact (Hblk q k i Hin Hni Hi). }
  split.
  { intros a Hia Ho1 Ho2 Hg He.
    pose proof (img_below_GT a Hia) as Hag. unfold AC.GT in Hag.
    (* the two post lists own the same image bytes: same memory and model on both sides *)
    assert (Ho2h : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' a)
      by (intro X; apply Ho2;
          exact (proj1 (ent_owned_img APIf H' (hb' ++ g_H g) mem' md' mem' md' a Hah' HahP eq_refl
                          (fun _ _ => eq_refl) Hia) X)).
    assert (Ho2' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a)
      by (intro X; apply Ho2h;
          exact (proj1 (ent_owned_img APIf (hb ++ g_H g) H' mem md mem' md' a HAH Hah' Hsk Htp Hia) X)).
    destruct (Himg a Hia Ho1 Ho2' Hg He) as (Hm0 & Hw0).
    destruct (Z.eq_dec a (AC.as_oom AC.ASYMS)) as [Eo|Eo].
    - subst a. destruct Hek as (_ & Hoomb).
      split; [rewrite Hoomb; exact Hm0|].
      split; intro X; [exact (proj1 Hoom (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hoom X))].
    - destruct (Hfr a ltac:(lia) Ho2' Ho2h ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia) He Eo
                  ltac:(intro Ht; exact (proj1 (proj2 (proj2 (Hto a Ht))) Hia))) as (Hm & Hw).
      split; [rewrite Hm; exact Hm0|].
      split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Ha.
    assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END) by lia.
    assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md' <= a < APPMEM_END)
      by (rewrite Hsk; lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a)
      by exact (proj1 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  (hb ++ g_H g) mem md a HAH (or_intror (or_intror (or_intror Hst))))).
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' a)
      by exact (proj1 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  H' mem' md' a Hah' (or_intror (or_intror (or_intror Hst'))))).
    destruct (Hfr a ltac:(lia) Hno Hno' ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img a He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X; lia)
                ltac:(intro Ht; pose proof (proj1 (proj2 (Hto a Ht))); lia)) as (Hm & Hw).
    destruct (Habv a Ha) as (Hm0 & Hw0).
    split; [rewrite Hm; exact Hm0|].
    split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Hor.
    assert (Hb0 : 0 <= a)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT a Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hdiv : 0 <= a / 8 <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Hsh1 : in_shadow (shadow_addr a)).
    { apply shadow_of_app. destruct Hor as [Hi|Hr];
        [pose proof (img_below_GT a Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
        |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
    assert (Hsr : 0 <= shadow_addr a < 2 ^ 64)
      by (destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2); lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (proj1 (proj2 (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  (hb ++ g_H g) mem md a HAH)) Hi).
      - assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END) by lia.
        exact (proj2 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  (hb ++ g_H g) mem md a HAH (or_intror (or_intror (or_intror Hst))))). }
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (proj1 (proj2 (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  H' mem' md' a Hah')) Hi).
      - assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md' <= a < APPMEM_END)
          by (rewrite Hsk; lia).
        exact (proj2 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  H' mem' md' a Hah' (or_intror (or_intror (or_intror Hst'))))). }
    destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1.
    destruct (Hfr (shadow_addr a) ltac:(lia) Hno Hno'
                ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                      rewrite <- He in X; lia)
                ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
    rewrite Hm. exact (Hshd a Hor). }
  split.
  { (* ENT #13 (frame batch 2 item 9): an entry block's shadow byte, as Tac_slot.ent_call, with the post heap H'
       reached through the permutation *)
    intros q k i Hin Hni Hi.
    destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (_ & Hq4 & Hend & _ & Hall).
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & Hnimg & _ & _).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (Hinb2 : AC.in_blocks H' (q + i))
      by (exists q, k; split; [apply (Permutation_in _ Hperm); apply in_or_app; right; exact Hin | lia]).
    assert (Hsh1 : in_shadow (shadow_addr (q + i))) by exact (shadow_of_app (q + i) Happq).
    destruct (in_shadow_range (shadow_addr (q + i)) Hsh1) as (R1 & R2).
    pose proof Hsh1 as Hsh1'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1'.
    assert (Hn1 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md (shadow_addr (q + i)))
      by exact (proj2 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hn2 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' (shadow_addr (q + i)))
      by exact (proj2 (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                  H' mem' md' (q + i) Hah' (or_introl Hinb2))).
    destruct (Hfr (shadow_addr (q + i)) ltac:(lia) Hn1 Hn2
                ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                      rewrite <- He in X; lia)
                ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
    rewrite Hm. exact (Hblks q k i Hin Hni Hi). }
  (* ENT #14: it names only the ENTRY heap g_H g, so the same witness *)
  exact Hcls.
Qed.

(* ---- FRA and ENT across spill stores of the 416-byte save area [A, A + 416) ----
   Two store ranges [A + lo1, A + hi1) and [A + lo2, A + hi2) inside [A + 40, A + 304): app memory above stklo
   (stklo <= S - SLOT_STACK < sp <= A) and below the entry sp S, so a_store_ok for a_laws_store; they miss every
   FRA cell (the frame below A, the frame shadow below HIGHMEM_BEG, the words [A + 16, A + 32) and
   [A + 304, A + 312), the saved registers [S - 104, S) and the low runtime and image cells), lie inside the
   entry-anchored slot window (ent_store), and the FakeStack frame record is below stklo (fsrec_stklo).
   a Theorem Labs lane's f4_fra_spill (a working branch Seg/F4.v) with the two ranges as parameters. *)
Definition f1_Wsp (A lo1 hi1 lo2 hi2 : Z) : list (Z * Z) := [(A + lo1, A + hi1); (A + lo2, A + hi2)].


Lemma f1_fra_spill : forall g fr hb regs regs' mem mem' md md' Asp lo1 hi1 lo2 hi2,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 Asp -> 0 <= Asp < 2 ^ 64 ->
  40 <= lo1 -> hi1 <= 304 -> 40 <= lo2 -> hi2 <= 304 ->
  Frame.munch (f1_Wsp Asp lo1 hi1 lo2 hi2) mem mem' ->
  Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md md' Asp lo1 hi1 lo2 hi2 HFRA HENT H9 HA Hl1 Hh1 Hl2 Hh2 MU WM HWIN'
    Hmat E2 E3 E4 E8 E9 E19 E26.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HAsr : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HspN : HIGHMEM_BEG < sp) by lia.
  assert (HA0e : Asp = A0).
  { apply f1_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (HfrL : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = Asp).
  { intros A' HA' HA'r. apply f1_id; [lia | lia |]. rewrite <- HA'. exact H9. }
  unfold f1_Wsp in MU.
  set (W := [(Asp + lo1, Asp + hi1); (Asp + lo2, Asp + hi2)]) in MU.
  assert (HOUT : forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x).
  { intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. apply HOUT. lia. }
  assert (HAW : all_app W).
  { subst W. cbn [all_app].
    split; [apply f1_app_ivl; lia | split; [apply f1_app_ivl; lia | exact I]]. }
  assert (HD : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [exact I | left; lia]. }
  assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    subst W. cbn [Frame.outside]. repeat split; try exact I; intro HC; apply Hns;
      right; left; lia. }
  destruct (AC.a_laws_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md HAH Hmc Hwrit)
    as (HAH' & Hown & HSTKeq & HSTKhi).
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md W
             HFRA MU WM HRO HAW HD HAH' HSTKeq).
    - intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - intros x Hx. apply HOUT. lia.
    - intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I;
        revert Hx; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia.
    - intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - exact HWIN'.
    - intros Hrec. eapply fsrec_stklo; [exact Hrec | exact HAH | exact MU |].
      intros x Hx _. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
  - eapply ent_mat; [| exact Hmat].
    eapply ent_store with (W := W); [exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKhi |].
    + intros x Hx.
      destruct (Z_lt_le_dec x (Asp + 40)) as [H1|H1];
        [| destruct (Z_lt_le_dec x (Asp + 304)) as [H2|H2]].
      * left. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
      * right. left. lia.
      * left. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* Where a byte of the frame lies (FRA's frame-location disjunction made uniform): on the real stack at or above
   stklo, or in the side stack FS, which is above the image (GT) and below stklo. *)
Definition f1_loc (mem : word -> option byte) (md : Model) (a : Z) : Prop :=
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END \/
  (AC.a_in_fs AC.ASYMS mem a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).

(* Across the allocation call (amalloc_ret, a_call_post at AK_MALLOC with the new block (q, a_size n)): FRA moves
   to the post state with hb = [(q, a_size n)] (Tac_slot.sl_mid_perm), and the bytes the exit cut reads are kept:
   the frame (bytes, writability and shadow), the live blocks and their shadow, and the stack at or above sp with
   its shadow. A kept byte is not the allocator's before or after (a_laws_not_owned for blocks, FS and the real
   stack; a_laws_client for the sink cells and the shadow of the registered globals; frame_facts for RELRO), so
   not in the new block either (whose bytes were the allocator's), and lies off errno, the OOM flag and the
   allocator's window [sp - 4096, sp) (the frame by sl_frame_apart_win, the rest by position). *)
Lemma f1_malloc_keep : forall g fr regs mem md n regs' mem' md' q,
  FRA B APIf ra g fr [] regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API)
    (AC.aa_owned AC.ASYMS AsanRTInv.RT API)
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API)
    AC.AK_MALLOC (g_H g) regs mem md (fun a => q <= a < q + AC.a_size n) (g_H g ++ [(q, AC.a_size n)])
    regs' mem' md' ->
  (forall i, 0 <= i < AC.a_size n -> AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md (q + i)) ->
  FRA B APIf ra g fr (hb1 q (AC.a_size n)) regs' mem' md' /\
  (forall a, (fr <= a < fr + FRAME_BYTES \/ AC.in_blocks (g_H g) a \/ AC.aspZ regs <= a < APPMEM_END) ->
     mbyte rsegs mem' a = mbyte rsegs mem a) /\
  (forall a, fr <= a < fr + FRAME_BYTES -> writable_at rsegs mem a -> writable_at rsegs mem' a) /\
  (forall a, (fr <= a < fr + FRAME_BYTES \/ AC.in_blocks (g_H g) a \/
              AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END) ->
     mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr regs mem md n regs' mem' md' q HFRA Hcp Hownq.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & _ & Hown & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  pose proof (sl_frame_apart_win B APIf ra g fr [] regs mem md HFRA) as Hapart0.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & _).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (HFS : AC.FS_SIZE = 11571200) by reflexivity.
  assert (Eerr : AC.a_errno AC.ASYMS = 0x5db76c) by reflexivity.
  assert (Eoom : AC.as_oom AC.ASYMS = 0x12aae0) by reflexivity.
  assert (HK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (Hstkhi : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md HAH).
  rewrite Haspz in Hlo.
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2 ^ 64).
  { pose proof Hhdr1 as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (Hapart : forall a, fr <= a < fr + FRAME_BYTES -> ~ (sp - 4096 <= a < sp))
    by (intros a Ha; rewrite <- Haspz; exact (Hapart0 a Ha)).
  (* a side-stack byte lies above the image and below stklo *)
  assert (FSC : forall a, AC.a_in_fs AC.ASYMS mem a ->
             AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\ app_mem a).
  { intros a (bb & Hbr & Hwm & Hb1 & Hb2).
    destruct (AC.a_laws_fs_place _ _ _ _ _ ALAWS _ mem md bb HAH Hwm Hbr) as (Hg & Hfsk & _ & Hfa').
    split; [lia|]. apply Hfa'. lia. }
  (* every frame byte is located and application memory *)
  assert (FRAME : forall a, fr <= a < fr + FRAME_BYTES -> f1_loc mem md a /\ app_mem a).
  { intros a Ha. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha) as Hr. split; [left; exact Hr|]. unfold app_mem. right. lia.
    - destruct (FSC a (Hfs a Ha)) as (Ha1 & Ha2).
      split; [right; split; [exact (Hfs a Ha) | exact Ha1] | exact Ha2]. }
  pose proof Hcp as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof Hcp as Hkept; apply AC.a_call_post_regs in Hkept.
  pose proof Hcp as Hsk'; apply AC.a_call_post_stklo in Hsk'.
  pose proof (AC.a_call_post_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hfk.
  pose proof (AC.a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinw.
  pose proof (AC.a_call_post_win_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinp.
  pose proof Hcp as Hmod; apply AC.a_call_post_model in Hmod.
  assert (Htp16 : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  rewrite Eerr, Eoom in Hfk.
  assert (F2 : getr regs' 2 = getr regs 2) by exact (Hkept 2 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F3 : getr regs' 3 = getr regs 3) by exact (Hkept 3 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F4 : getr regs' 4 = getr regs 4) by exact (Hkept 4 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F8 : getr regs' 8 = getr regs 8) by exact (Hkept 8 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F9 : getr regs' 9 = getr regs 9) by exact (Hkept 9 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F19 : getr regs' 19 = getr regs 19) by exact (Hkept 19 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F26 : getr regs' 26 = getr regs 26) by exact (Hkept 26 ltac:(unfold AC.a_callee_saved; lia)).
  (* a byte that is not the allocator's before and after, off the window, errno and the flag, is kept; not the
     allocator's before means not in the new block (whose bytes were) *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md a ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, AC.a_size n)]) mem' md' a ->
      ~ (sp - 4096 <= a < sp) -> ~ (0x5db76c <= a < 0x5db76c + 4) -> a <> 0x12aae0 ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Ho1 Ho2 Hw He Hoo. apply (Hfk a Ha Ho1 Ho2); [| exact He | exact Hoo |].
    - unfold AC.a_window, AC.AK_MALLOC. rewrite Haspz. exact Hw.
    - cbv beta. intros Ht. apply Ho1. replace a with (q + (a - q)) by lia. apply Hownq. lia. }
  assert (FSPOST : forall a, AC.a_in_fs AC.ASYMS mem a -> AC.a_in_fs AC.ASYMS mem' a).
  { intros a (bb & Hbr & Hwm & Hb). exists bb. split; [exact Hbr|]. split; [|exact Hb].
    intros k Hk. rewrite (Htp16 (Z.of_nat k) ltac:(lia)). exact (Hwm k Hk). }
  (* a located byte and its shadow are not the allocator's, before or after *)
  assert (LOC : forall a, f1_loc mem md a ->
      0 <= a < 2 ^ 64 /\ AC.GT <= a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md (shadow_addr a) /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, AC.a_size n)]) mem' md' a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, AC.a_size n)]) mem' md' (shadow_addr a)).
  { intros a Hl.
    assert (Hpl : AC.in_blocks ([] ++ g_H g) a \/ AC.in_slack ([] ++ g_H g) a \/ AC.a_in_fs AC.ASYMS mem a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END).
    { destruct Hl as [Hs|[Hfs _]]; [right; right; right; exact Hs | right; right; left; exact Hfs]. }
    assert (Hql : AC.in_blocks (g_H g ++ [(q, AC.a_size n)]) a \/
                  AC.in_slack (g_H g ++ [(q, AC.a_size n)]) a \/ AC.a_in_fs AC.ASYMS mem' a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md' <= a < APPMEM_END).
    { rewrite Hsk'. destruct Hl as [Hs|[Hfs _]];
        [right; right; right; exact Hs | right; right; left; exact (FSPOST a Hfs)]. }
    destruct (AC.a_laws_not_owned _ _ _ _ _ ALAWS _ mem md a HAH Hpl) as (N1 & N2).
    destruct (AC.a_laws_not_owned _ _ _ _ _ ALAWS _ mem' md' a HAH' Hql) as (N3 & N4).
    split; [destruct Hl as [Hs|[_ Hs]]; lia|].
    split; [destruct Hl as [Hs|[_ Hs]]; lia|].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3 | exact N4]. }
  assert (KLOC : forall a, f1_loc mem md a -> ~ (sp - 4096 <= a < sp) ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Hl Hw. destruct (LOC a Hl) as (Hr & Hg & N1 & _ & N3 & _).
    apply KEEP; [exact Hr | exact N1 | exact N3 | exact Hw | lia | lia]. }
  assert (KST : forall a, AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END ->
      ~ (sp - 4096 <= a < sp) ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Hs Hw. apply KLOC; [left; exact Hs | exact Hw]. }
  assert (KSH : forall a, f1_loc mem md a -> app_mem a ->
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hl Hap. destruct (LOC a Hl) as (_ & _ & _ & N2 & _ & N4).
    pose proof (shadow_of_app a Hap) as Hsh1. pose proof (in_shadow_range _ Hsh1) as Hsr.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsh1.
    refine (proj1 (KEEP _ _ N2 N4 _ _ _)); lia. }
  assert (KFR : forall a, fr <= a < fr + FRAME_BYTES -> mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ha. destruct (FRAME a Ha) as (Hl & _). exact (proj1 (KLOC a Hl (Hapart a Ha))). }
  (* a side-stack byte is below stklo, so below the allocator's window *)
  assert (KFS : forall a, AC.a_in_fs AC.ASYMS mem a -> mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Hfs. destruct (FSC a Hfs) as (Hgt & _).
    assert (Hl : f1_loc mem md a) by (unfold f1_loc; right; split; [exact Hfs | exact Hgt]).
    exact (proj1 (KLOC a Hl ltac:(lia))). }
  assert (KCL : forall a, 0x5db770 <= a < 0x5fe000 -> AC.in_blocks AC.a_client a ->
      mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ha Hcl. refine (proj1 (KEEP a _ _ _ _ _ _)); [lia | | | lia | lia | lia].
    - exact (proj1 (AC.a_laws_client _ _ _ _ _ ALAWS _ mem md a HAH) Hcl).
    - exact (proj1 (AC.a_laws_client _ _ _ _ _ ALAWS _ mem' md' a HAH') Hcl). }
  (* the shadow byte of a registered global (an image byte) is not the allocator's, before or after *)
  assert (KAG : forall a, in_globals AF.frame_AG a ->
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hin. pose proof (f1_ag_img a Hin) as Himg. pose proof (f1_ag_range a Hin) as Hr.
    assert (Hsa : 0x7fff8000 + 16936 <= shadow_addr a <= 0x7fff8000 + 81693).
    { unfold shadow_addr. rewrite HK.
      pose proof (Z.div_le_mono 0x21140 a 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_le_mono a 0x9f8e8 8 ltac:(lia) ltac:(lia)) as D2.
      change (0x21140 / 8) with 16936 in D1. change (0x9f8e8 / 8) with 81693 in D2. lia. }
    refine (proj1 (KEEP _ _ _ _ _ _ _)); [lia | | | lia | lia | lia].
    - exact (proj1 (proj2 (AC.a_laws_client _ _ _ _ _ ALAWS _ mem md a HAH)) Himg).
    - exact (proj1 (proj2 (AC.a_laws_client _ _ _ _ _ ALAWS _ mem' md' a HAH')) Himg). }
  (* a byte of a live block and its shadow are kept *)
  assert (KBLK : forall a, AC.in_blocks (g_H g) a ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hb.
    pose proof Hb as (p0 & k0 & Hin0 & Hr0).
    destruct (AC.a_laws_blocks _ _ _ _ _ ALAWS _ mem md p0 k0 HAH Hin0) as (_ & Hp0 & Hpk & _ & Hbb).
    destruct (Hbb a Hr0) as (Hap & _ & Hnimg & _ & _).
    assert (Hb' : AC.in_blocks (g_H g ++ [(q, AC.a_size n)]) a).
    { exists p0, k0. split; [apply in_or_app; left; exact Hin0 | exact Hr0]. }
    destruct (AC.a_laws_not_owned _ _ _ _ _ ALAWS _ mem md a HAH (or_introl Hb)) as (N1 & N2).
    destruct (AC.a_laws_not_owned _ _ _ _ _ ALAWS _ mem' md' a HAH' (or_introl Hb')) as (N3 & N4).
    assert (Hne : ~ (0x5db76c <= a < 0x5db76c + 4)).
    { intros He. apply Hnimg. apply f1_errno_img. lia. }
    assert (Hno : a <> 0x12aae0).
    { intros ->. exact (Hnimg f1_oom_img). }
    split.
    - refine (proj1 (KEEP a _ N1 N3 _ Hne Hno)); lia.
    - pose proof (shadow_of_app a Hap) as Hsh1. pose proof (in_shadow_range _ Hsh1) as Hsr.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsh1.
      refine (proj1 (KEEP _ _ N2 N4 _ _ _)); lia. }
  (* the side-arm FakeStack record: the tp word, the class-6 flag byte and the slot's last word are kept *)
  assert (HREC : FSREC fr mem -> FSREC fr mem').
  { intros (FS & jx & Htpw & HFSr & Hj & Hfrj & Hflag & Htail).
    assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
    assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
    assert (Hfl : SMC.fs_flag FS 6 jx = FS + 36352 + jx) by (unfold SMC.fs_flag; cbn; lia).
    assert (Hfrv : fr = FS + 6328320 + jx * 4096) by (rewrite Hfrj; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
    rewrite HM6 in Hj.
    assert (KFS1 : forall x, FS <= x < FS + AC.FS_SIZE -> mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx. apply KFS. exists FS. split; [exact HFSr|]. split; [exact Htpw | exact Hx]. }
    exists FS, jx.
    split; [intros k Hk; rewrite (Htp16 (Z.of_nat k) ltac:(lia)); exact (Htpw k Hk)|].
    split; [exact HFSr|].
    split; [rewrite HM6; exact Hj|].
    split; [exact Hfrj|].
    split.
    - apply (f1_bkeep mem mem'); [|exact Hflag]. cbn [length]. intros x Hx. apply KFS1. lia.
    - apply (f1_bkeep mem mem'); [|exact Htail]. rewrite length_le8. intros x Hx. apply KFS1. lia. }
  split.
  { apply (sl_mid_perm B APIf ra g fr [] (hb1 q (AC.a_size n)) (g_H g ++ [(q, AC.a_size n)]) regs mem md
      regs' mem' md' (fun a => q <= a < q + AC.a_size n) AC.AK_MALLOC HFRA Hcp).
    - exact (Permutation_cons_append (g_H g) (q, AC.a_size n)).
    - cbn. lia.
    - destruct Hsn as ((Hthm & Hlkm) & Hhdm & Hfd).
      split; [split|split].
      + eapply YI14.val_mem_frame; [|exact Hthm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx. rewrite SEGS.
        apply KCL; [lia|]. exists 0x5db840, 131728. split; [|lia].
        unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
      + eapply YI14.val_mem_frame; [|exact Hlkm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx. rewrite SEGS.
        apply KCL; [lia|]. exists 0x5fbad8, 4320. split; [|lia].
        unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
      + intros k Hk. rewrite <- (Hhdm k Hk). rewrite SEGS, Hhead.
        apply KCL; [lia|]. exists 0x5fbad8, 4320. split; [|lia].
        unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
      + destruct Hmod as (lz & mt & vm' & Emd). rewrite Emd.
        change (m_fds (with_vm_backing lz mt (with_vmmaps vm' md))) with (m_fds md). exact Hfd.
    - intros a Hin. pose proof (Hgimg a Hin) as E. rewrite SEGS in E |- *. rewrite <- E.
      assert (Har : 0x9e348 <= a < 0xa07c8).
      { destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        destruct Hil as [Ex|[]]; injection Ex as <- <-; lia. }
      refine (proj1 (KEEP a _ _ _ _ _ _)); [lia | | | lia | lia | lia].
      + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
      + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
    - unfold q64 in *. apply (f1_bkeep mem mem'); [|exact Hhdr1].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - unfold q64 in *. apply (f1_bkeep mem mem'); [|exact Hhdr2].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - intros A0 HA0 HA0r.
      assert (EA0 : A0 = A).
      { unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (f1_bkeep mem mem'); [|exact Hspill].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - intros A0 HA0 HA0r v Hv.
      assert (EA0 : A0 = A).
      { unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (f1_bkeep mem mem'); [|exact Hv].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - intros A0 HA0 HA0r.
      assert (EA0 : A0 = A).
      { unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (f1_bkeep mem mem'); [|exact Hfr24].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - destruct Hsh as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
      apply (f1_bkeep mem mem'); [|exact Hshb]. rewrite Hshl. intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Ex : x = shadow_addr (fr + 8 * (x - Sfr fr))).
      { unfold shadow_addr at 1. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
      destruct (FRAME _ Hin) as (Hl & Hap).
      rewrite Ex. exact (KSH _ Hl Hap).
    - apply (f1_bkeep mem mem'); [|exact Hsaved]. intros x Hx.
      unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - unfold stk in Hwin |- *. destruct Hwin as (Hw0 & Hw1 & Hw).
      split; [exact Hw0|]. split; [exact Hw1|]. intros a Ha.
      destruct (Hw a Ha) as (Hwv & bb & Hbb).
      destruct (Z_lt_ge_dec a (sp - 4096)) as [Hlt|Hge]; [|destruct (Z_lt_ge_dec a sp) as [Hlt2|Hge2]].
      + destruct (KST a ltac:(lia) ltac:(lia)) as (Em & Ew).
        split; [exact (proj1 Ew Hwv)|]. exists bb. change (mbyte rsegs mem' a = Some bb). rewrite Em. exact Hbb.
      + assert (Hwa : AC.a_window AC.AK_MALLOC regs a)
          by (unfold AC.a_window, AC.AK_MALLOC; rewrite Haspz; lia).
        split; [exact (Hwinw a Hwa)|]. exact (Hwinp a Hwa).
      + destruct (KST a ltac:(lia) ltac:(lia)) as (Em & Ew).
        split; [exact (proj1 Ew Hwv)|]. exists bb. change (mbyte rsegs mem' a = Some bb). rewrite Em. exact Hbb.
    - intros a Hin. destruct (HAG a Hin) as (Ha0' & Hn0 & Hend & Hb).
      split; [exact Ha0'|]. split; [exact Hn0|]. split; [exact Hend|].
      intros i Hi. destruct (Hb i Hi) as (Hap & bb & Hrd & Hok). split; [exact Hap|].
      exists bb. split; [|exact Hok].
      assert (Hin' : in_globals AF.frame_AG (a + i)) by (replace (a + i) with a by lia; exact Hin).
      change (mbyte rsegs mem' (shadow_addr (a + i)) = Some bb). rewrite (KAG _ Hin'). exact Hrd.
    - intros a Ha Hnf. apply (f1_addr_keep mem mem' a 1 (HWA a Ha Hnf)). intros i Hi.
      assert (Hl : f1_loc mem md (a + i)) by (unfold f1_loc; left; lia).
      assert (Hap : app_mem (a + i)) by (unfold app_mem; right; lia).
      exact (KSH _ Hl Hap).
    - exact HREC.
    - exact F2.
    - exact F3.
    - exact F4.
    - exact F8.
    - exact F9.
    - exact F19.
    - exact F26. }
  split.
  { intros a Ha. destruct Ha as [Hf|[Hb|Hs]].
    - exact (KFR a Hf).
    - exact (proj1 (KBLK a Hb)).
    - rewrite Haspz in Hs. exact (proj1 (KST a ltac:(lia) ltac:(lia))). }
  split.
  { intros a Ha Hw. destruct (FRAME a Ha) as (Hl & _). exact (proj1 (proj2 (KLOC a Hl (Hapart a Ha))) Hw). }
  intros a Ha. destruct Ha as [Hf|[Hb|Hs]].
  - destruct (FRAME a Hf) as (Hl & Hap). exact (KSH a Hl Hap).
  - exact (proj2 (KBLK a Hb)).
  - apply KSH; [left; exact Hs | unfold app_mem; right; lia].
Qed.

(* seg_F1 (S_F1): from the frame-loop head 0x81d40 (turn j) through the allocation call to its return point
   0x81da4. The run f1_evt, 0x81d40 -> 0x5337c (sl_run_lib), reads the code [0x81d40, 0x81da4), [0x82978, 0x82984),
   [0x82990, 0x8299c), the input bytes p + c and p + c + 1 and their shadow bytes, and writes only
   [A + 224, A + 232); FRA and ENT move across that store by f1_fra_spill. The allocation is AC.aa_malloc on
   fra_call_pre; f1_malloc_keep and f1_ent_call_perm move FRA and ENT across it, and the exit body is read off
   the kept bytes: LK (s5 = j is callee-saved, our[] is frame bytes), FC ([A + 224] = left - h was just stored,
   s4 = p + c + h = p + body, s2 = len), FLSH (save-area spills off [A + 224, A + 232), frame shadow and frame
   bytes), f1_IN (a live block of the entry heap and its shadow) and [A + 248] = fr + 176. *)
Lemma f1_run : forall (X : ghost -> Z -> bvmap 5 word -> (word -> option byte) -> Prop) (j : nat),
  (forall g fr regs regs' A m m', X g fr regs m -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END ->
     getr regs' 9 = getr regs 9 ->
     (forall x, fr <= x < fr + FRAME_BYTES \/ A + 40 <= x < A + 216 \/ A + 248 <= x < A + 304 ->
        mbyte rsegs m' x = mbyte rsegs m x) ->
     (forall x, fr <= x < fr + FRAME_BYTES -> mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
     X g fr regs' m') ->
  Hat B APIf ra (fun (g : ghost) (jj : nat) (c : config) =>
    exists phi, CUTST B APIf ra g 0x81da4 (hb1 phi (AC.a_size (flen g jj)))
      (fun fr regs m => (g_n g < 2 ^ 26 /\ (jj <= 255)%nat /\ a0v regs phi /\ HB m phi (flen g jj) /\
         LK g fr jj regs m /\ FC g fr jj regs m /\ FLSH g jj fr regs m /\
         f1_IN g m /\ spill regs m 248 (fr + 176) /\ IFS g fr jj regs m) /\ X g fr regs m) c) j ->
  Hat B APIf ra (fun (g : ghost) (jj : nat) (c : config) =>
    CUTST B APIf ra g 0x81d40 [] (fun fr regs m =>
      (g_n g < 2 ^ 26 /\ LI g fr jj regs m /\ FLSH g jj fr regs m /\ f1_IN g m /\ spill regs m 248 (fr + 176)) /\
      X g fr regs m) c) j.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros X j HXk Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & (Hgn & HLI & HFLSH & HIN & H248) & HX).
  subst c.
  destruct HLI as ((Hj & H21 & HOUR) & (Hc & H22 & H25) & Hleft & HIFS).
  destruct HIN as (HinH0 & HaddrIN & HbytesIN).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & _).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HLE : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (HK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (Hstkhi : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md HAH).
  rewrite Haspz in Hlo.
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2 ^ 64).
  { pose proof Hhdr1 as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (Hfrm8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (EL : t_left (g_in g) j = g_n g - t_c (g_in g) j) by reflexivity.
  assert (Hlen_in : Z.of_nat (length (g_in g)) = g_n g) by reflexivity.
  assert (Hn0 : 0 < g_n g) by lia.
  pose proof (HinH0 Hn0) as HinH.
  (* the input block lies below stklo *)
  destruct (AC.a_laws_blocks _ _ _ _ _ ALAWS _ mem md (g_p g) (g_n g) HAH HinH) as (_ & Hp4096 & Hpn & _ & _).
  (* the two length bytes, their instrumented checks, and the spill slot *)
  pose proof (f1_byte1 mem (g_p g) (t_c (g_in g) j) (g_in g) HbytesIN ltac:(lia) ltac:(rewrite Hlen_in; lia))
    as HB0.
  destruct (f1_shadow1 mem (g_p g + t_c (g_in g) j)
      (addressable_sub mem (g_p g) (g_n g) (t_c (g_in g) j) 1 HaddrIN ltac:(lia) ltac:(lia) ltac:(lia)))
    as (k0 & HK0 & Hk0).
  assert (H2 : exists k1 : byte, 2 <= t_left (g_in g) j ->
     ov_read_bytes rsegs mem (wa (Z.shiftr (g_p g + t_c (g_in g) j + 1) 3 + ASAN_K)) 1 = Some [k1] /\
     (bv_signed k1 = 0 \/ (g_p g + t_c (g_in g) j + 1) mod 8 < bv_signed k1) /\
     ov_read_bytes rsegs mem (wa (g_p g + t_c (g_in g) j + 1)) 1 =
       Some [nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))]).
  { destruct (Z_lt_le_dec (t_left (g_in g) j) 2) as [Hlt|Hge].
    - exists k0. intros Hc2. exfalso. lia.
    - pose proof (addressable_sub mem (g_p g) (g_n g) (t_c (g_in g) j + 1) 1 HaddrIN ltac:(lia) ltac:(lia)
        ltac:(lia)) as Had1.
      rewrite Z.add_assoc in Had1.
      destruct (f1_shadow1 mem _ Had1) as (k1 & HK1 & Hk1).
      exists k1. intros _. split; [exact HK1|]. split; [exact Hk1|].
      rewrite <- Z.add_assoc.
      exact (f1_byte1 mem (g_p g) (t_c (g_in g) j + 1) (g_in g) HbytesIN ltac:(lia)
               ltac:(rewrite Hlen_in; lia)). }
  destruct H2 as (k1 & H2).
  assert (HSOK : store_ok rsegs mem (wa (A + 224)) 8 = true).
  { assert (WR : wr_at rsegs mem (A + 224) 8).
    { pose proof Hwin as (_ & _ & Hw).
      split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hw (A + 224 + i) ltac:(lia))). }
    pose proof (wr_at_store_ok rsegs mem (A + 224) 8 0 8%nat WR ltac:(lia) ltac:(lia)) as HS.
    rewrite Z.add_0_r in HS. exact HS. }
  (* len = min(L, left - h) is a u16 *)
  pose proof (bv_unsigned_in_range 8 (nthb (g_in g) (Z.to_nat (t_c (g_in g) j)))) as Hb0r.
  pose proof (bv_unsigned_in_range 8 (nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1)))) as Hb1r.
  change (bv_modulus 8) with 256 in Hb0r, Hb1r.
  assert (Elen : t_len (g_in g) j =
    Z.min (bv_unsigned (nthb (g_in g) (Z.to_nat (t_c (g_in g) j))) +
           (if 2 <=? t_left (g_in g) j
            then 256 * bv_unsigned (nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))) else 0))
          (t_left (g_in g) j - Z.min 2 (t_left (g_in g) j))) by reflexivity.
  assert (Eh : t_h (g_in g) j = Z.min 2 (t_left (g_in g) j)) by reflexivity.
  assert (Hlen : 0 <= t_len (g_in g) j <= 65535).
  { rewrite Elen. destruct (2 <=? t_left (g_in g) j); lia. }
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x81d40) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x5337c /\ getr R 1 = Z_to_bv 64 0x81da4 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 (t_len (g_in g) j) /\ getr R 18 = Z_to_bv 64 (t_len (g_in g) j) /\
       getr R 20 = Z_to_bv 64 (g_p g + t_c (g_in g) j + t_h (g_in g) j) /\
       mem' = write_to_mem mem (wa (A + 224)) (le8 (Z_to_bv 64 (t_left (g_in g) j - t_h (g_in g) j))))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f1_evt with (A := A) (q := g_p g + t_c (g_in g) j) (left := t_left (g_in g) j)
        (b0 := nthb (g_in g) (Z.to_nat (t_c (g_in g) j)))
        (b1 := nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))) (k0 := k0) (k1 := k1).
      - exact Hr9.
      - exact H22.
      - rewrite <- EL in H25. exact H25.
      - exact Hr26.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact HK0.
      - exact Hk0.
      - exact HB0.
      - exact H2.
      - exact HSOK. }
    intros ms' (a1' & a2' & ->).
    eexists _, _, _. split; [reflexivity|].
    repeat (split; [reflexivity|]). reflexivity. }
  intros R pc' mem1 regs'' md' (Hpc & K1 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K10 & K18 & K20 & Hmem)
    Hreg Hmat.
  subst pc'.
  assert (E1 : getr regs'' 1 = Z_to_bv 64 0x81da4) by (rewrite Hreg; exact K1).
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E10 : getr regs'' 10 = Z_to_bv 64 (t_len (g_in g) j)) by (rewrite Hreg; exact K10).
  assert (E18 : getr regs'' 18 = Z_to_bv 64 (t_len (g_in g) j)) by (rewrite Hreg; exact K18).
  assert (E20 : getr regs'' 20 = Z_to_bv 64 (g_p g + t_c (g_in g) j + t_h (g_in g) j))
    by (rewrite Hreg; exact K20).
  assert (Hrest : 0 <= t_left (g_in g) j - t_h (g_in g) j < 2 ^ 26) by lia.
  set (rest := t_left (g_in g) j - t_h (g_in g) j) in *.
  set (W := f1_Wsp A 224 232 224 232).
  (* ---- the store [s1 + 224] = rest ---- *)
  assert (MU1 : Frame.munch W mem mem1).
  { rewrite Hmem. subst W. unfold f1_Wsp.
    apply (munch_write _ mem mem (A + 224) (le8 (Z_to_bv 64 rest)));
      [apply munch_refl | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; left; lia]. }
  assert (WM1 : Frame.wmono rsegs mem mem1) by (rewrite Hmem; apply wmono_write; apply wmono_refl).
  assert (HAW : all_app W).
  { subst W. unfold f1_Wsp. cbn [all_app].
    split; [apply f1_app_ivl; lia | split; [apply f1_app_ivl; lia | exact I]]. }
  assert (KM1 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 224 <= x < A + 232) ->
                  mbyte rsegs mem1 x = mbyte rsegs mem x).
  { intros x Hx Hn. unfold mbyte. rewrite (MU1 (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. subst W. unfold f1_Wsp. cbn [outside].
    split; [lia|]. split; [lia | exact I]. }
  assert (HWIN1 : stk rsegs mem1 (g_S g - AF.SLOT_STACK) (g_S g)).
  { rewrite Hmem. apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]. }
  destruct (f1_fra_spill g fr [] regs regs'' mem mem1 md md' A 224 232 224 232 HFRA HENT Hr9 HA64
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MU1 WM1 HWIN1 Hmat E2 E3 E4 E8 E9 E19 E26)
    as (HFRA2 & HENT2).
  assert (Hasp'' : AC.aspZ regs'' = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
  (* ---- the allocation call ---- *)
  assert (Hret : YK0s.ret_ok (getr regs'' 1)).
  { rewrite E1. apply YK0s.ret_ok_even. rewrite MState.unsigned_lit by lia. reflexivity. }
  assert (HKm : 0 <= AC.AK_MALLOC <= FN_STACK) by (unfold AC.AK_MALLOC; lia).
  pose proof (fra_call_pre B APIf ra g fr [] regs'' mem1 md' AC.AK_MALLOC HFRA2 HENT2 Hret HKm) as Hpre.
  assert (Hnn : forall p k, In (p, k) (g_H g) -> 0 <= k).
  { intros p0 k0' Hin. pose proof (AC.a_laws_block_size _ _ _ _ _ ALAWS _ mem md p0 k0' HAH Hin). lia. }
  (* the per-class premises of amalloc_at (generation N.1) for the call heap g_H g (the cut's slot heap list is
     empty), with Bc = Bc_of BE for ENT #14's witness BE (Seg/Tac_cls.v) *)
  destruct (Tac_cls.sl_malloc_cls APIf g [] mem1 md' (t_len (g_in g) j) HENT2)
    as (BE & _ & _ & Hfits & Hroom & _).
  eapply SR_bind.
  { apply (AC.aa_malloc AC.ASYMS AsanRTInv.RT API (g_H g) regs'' mem1 md' (t_len (g_in g) j)
             (Tac_cls.Bc_of BE) Hpre E10).
    - unfold AC.ANMAX. lia.
    - unfold AC.ALIVE_MAX, AC.a_size. lia.
    - apply f1_place_room; [exact Hnn | exact Hlive | unfold AC.a_size; lia].
    - exact Hfits.
    - exact Hroom. }
  intros c' (regs' & mem2 & md2 & q & Ec' & Hq & Hnb & Hcp & Herrk & Hownq).
  subst c'. rewrite E1.
  (* the v1.9 contract states the new block's ownership over its bytes, word slack and their shadow (in_blk_ext);
     f1_malloc_keep reads the bytes *)
  assert (Hownq' : forall i, 0 <= i < AC.a_size (t_len (g_in g) j) ->
            AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem1 md' (q + i)).
  { intros i Hi. apply Hownq. left. exists q, (AC.a_size (t_len (g_in g) j)).
    split; [left; reflexivity | lia]. }
  destruct (f1_malloc_keep g fr regs'' mem1 md' (t_len (g_in g) j) regs' mem2 md2 q HFRA2 Hcp Hownq')
    as (HFRAx & KB & KW & KS).
  pose proof Hcp as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof Hcp as Hkept; apply AC.a_call_post_regs in Hkept.
  assert (F2 : getr regs' 2 = getr regs'' 2) by exact (Hkept 2 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F9 : getr regs' 9 = getr regs'' 9) by exact (Hkept 9 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F18 : getr regs' 18 = getr regs'' 18) by exact (Hkept 18 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F20 : getr regs' 20 = getr regs'' 20) by exact (Hkept 20 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F21 : getr regs' 21 = getr regs'' 21) by exact (Hkept 21 ltac:(unfold AC.a_callee_saved; lia)).
  assert (Hasp' : AC.aspZ regs' = sp) by (unfold AC.aspZ; rewrite F2, E2; exact Haspz).
  destruct (AC.a_laws_mat_le _ _ _ _ _ ALAWS ([] ++ g_H g) mem1 md md' Hmat) as (_ & _ & HSTKm & _).
  (* the new block's bytes are app memory below stklo (so below S), off the image and off every entry block *)
  pose proof Hcp as Hsk'; apply AC.a_call_post_stklo in Hsk'.
  assert (Hstk2 : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem1 md' <= g_S g - AF.SLOT_STACK).
  { destruct HFRA2 as (A2 & sp2 & s52 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs2 & _). exact Hs2. }
  assert (HTOUCH : forall a, q <= a < q + AC.a_size (t_len (g_in g) j) ->
            app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a).
  { intros a Ha.
    assert (Hinq : In (q, AC.a_size (t_len (g_in g) j)) (g_H g ++ [(q, AC.a_size (t_len (g_in g) j))]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (AC.a_laws_blocks _ _ _ _ _ ALAWS _ mem2 md2 q (AC.a_size (t_len (g_in g) j)) HAH' Hinq)
      as (_ & _ & Hend & _ & Hall).
    destruct (Hall a Ha) as (Happ & _ & Hnimg & _ & _).
    pose proof Hnb as (_ & _ & _ & _ & _ & Hnew & _).
    destruct (Hnew a Ha) as (Hnib & _).
    split; [exact Happ|]. split; [rewrite Hsk' in Hend; lia|].
    split; [exact Hnimg | exact Hnib]. }
  assert (HENTx : ENT APIf g (hb1 q (AC.a_size (t_len (g_in g) j))) mem2 md2).
  { exact (f1_ent_call_perm g fr [] (hb1 q (AC.a_size (t_len (g_in g) j)))
             (g_H g ++ [(q, AC.a_size (t_len (g_in g) j))]) regs'' mem1 md' regs' mem2 md2
             (fun a => q <= a < q + AC.a_size (t_len (g_in g) j)) AC.AK_MALLOC HENT2 HFRA2 Hcp
             (Permutation_cons_append (g_H g) (q, AC.a_size (t_len (g_in g) j))) HKm HTOUCH Herrk). }
  (* the two-step byte keep: the allocation keeps the stack at or above sp and the frame, the store everything
     off [A + 224, A + 232) *)
  assert (KK : forall x, (fr <= x < fr + FRAME_BYTES \/ sp <= x < APPMEM_END) -> ~ (A + 224 <= x < A + 232) ->
             mbyte rsegs mem2 x = mbyte rsegs mem x).
  { intros x Hx Hn.
    rewrite (KB x ltac:(destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; rewrite Hasp''; exact Hx])).
    apply KM1; [lia | exact Hn]. }
  assert (KSF : forall x, fr <= x < fr + FRAME_BYTES ->
             mbyte rsegs mem2 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
  { intros x Hx. rewrite (KS x ltac:(left; exact Hx)).
    assert (Hsx : shadow_addr x < HIGHMEM_BEG).
    { unfold shadow_addr. rewrite HK, HHB. assert (x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    assert (Hsx0 : 0 <= shadow_addr x) by (unfold shadow_addr; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia).
    apply KM1; lia. }
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite F9, E9; exact Hr9).
  rewrite <- SEGS. apply Hexit. cbv beta.
  exists q, regs', mem2, md2, fr.
  split; [reflexivity|].
  split; [exact HFRAx|].
  split; [exact HENTx|].
  split.
  { (* the cut body *)
  split; [exact Hgn|].
  split; [exact Hj|].
  split; [unfold a0v, rg; exact Hq|].
  split.
  { destruct Hnb as (Hq0 & _ & _ & _ & _ & _ & Haddr & _). split; [exact Hq0 | exact Haddr]. }
  split.
  { (* LK *)
    split; [exact Hj|]. split.
    - unfold rg in *. rewrite F21, E21. exact H21.
    - unfold OURb in *. apply (f1_bkeep mem mem2); [|exact HOUR].
      rewrite OUR_length. intros x Hx. apply KK; lia. }
  split.
  { (* FC *)
    split.
    - exists A. split; [exact H9'|].
      unfold q64. apply (f1_bkeep mem1 mem2).
      + rewrite length_le8. intros x Hx. apply (KB x). right; right. rewrite Hasp''. lia.
      + rewrite Hmem. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
    - split.
      + unfold rg. rewrite F20, E20. f_equal. unfold t_body, f_body, t_h, t_c. lia.
      + unfold rg. rewrite F18, E18. reflexivity. }
  split.
  { (* FLSH *)
    apply (flsh_move g j fr regs regs' A mem mem2 HFLSH Hr9 HA64 ltac:(lia)).
    - rewrite F9, E9. reflexivity.
    - intros x Hx. apply KK; lia.
    - intros x Hx. apply KSF. lia.
    - intros x Hx. split.
      + rewrite (KB x ltac:(right; left; exists (g_p g), (g_n g); split; [exact HinH | lia])).
        apply KM1; lia.
      + rewrite (KS x ltac:(right; left; exists (g_p g), (g_n g); split; [exact HinH | lia])).
        assert (Hsx : 0 <= shadow_addr x < HIGHMEM_BEG).
        { unfold shadow_addr. rewrite HK, HHB.
          assert (0 <= x / 8 < 17592186044416) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
          lia. }
        apply KM1; lia.
    - exact (fra_stk B APIf ra g fr _ regs' mem2 md2 HFRAx). }
  split.
  { (* the input block *)
    split; [intros _; exact HinH|]. split.
    - apply (f1_addr_keep mem1 mem2).
      + exact (sl_addr_keep mem mem1 W (g_p g) (g_n g) HaddrIN MU1 HAW).
      + intros i Hi. apply KS. right; left. exists (g_p g), (g_n g). split; [exact HinH | lia].
    - apply (f1_bkeep mem mem2); [|exact HbytesIN]. intros x Hx. rewrite Hlen_in in Hx.
      rewrite (KB x ltac:(right; left; exists (g_p g), (g_n g); split; [exact HinH | lia])).
      apply KM1; lia. }
  split.
  { (* the spill [s1 + 248] = fr + 176 *)
    apply (f1_spill_move regs regs' A 248 (fr + 176) mem mem2 H248 Hr9 HA64 ltac:(lia) ltac:(lia)).
    - rewrite F9, E9. reflexivity.
    - intros x Hx. apply KK; lia. }
  (* IFS: the two frame records and the first fragment's body are frame bytes, its two spills save-area words *)
  apply (f1_ifs_move g fr j regs regs' A mem mem2 HIFS Hr9 HA64 ltac:(lia)).
  - rewrite F9, E9. reflexivity.
  - intros x Hx. apply KK; lia.
  - intros x Hx. apply KK; lia.
  - intros x Hx. apply KSF. lia. }
  (* the carried predicate: frame and save-area bytes off [A + 216, A + 248), and the frame shadow *)
  apply (HXk g fr regs regs' A mem mem2 HX Hr9 HA64 ltac:(lia)).
  - rewrite F9, E9. reflexivity.
  - intros x Hx. apply KK; lia.
  - exact KSF.
Qed.

(* seg_F1 (S_F1) on the official cuts: f1_run carrying FLC (flc_move across the store and the allocation). *)
Lemma seg_F1 : forall j : nat,
  Hat B APIf ra (Inv_A81da4_at B APIf ra) j -> Hat B APIf ra (Inv_A81d40_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros j Hexit g c (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HLI & HFLSH & HIN & H248 & HC).
  apply (f1_run (fun _ fr regs m => FLC fr regs m) j).
  - intros g' fr' regs1 regs2 A m1 m2 HC' H9 HA HAE E9 KB KS.
    apply (flc_move fr' regs1 regs2 A m1 m2 HC' H9 HA HAE E9).
    + intros x Hx. apply KB. lia.
    + intros x Hx. apply KS. lia.
  - intros g' c' (phi & regs' & mem' & md' & fr' & Ec' & HFRA' & HENT' &
                  (Hgn' & Hj' & Ha0 & HHB & HLK & HFC & HFL & HIN' & H248' & HIFS') & HC').
    apply Hexit. exists phi, regs', mem', md', fr'.
    split; [exact Ec'|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn'|]. split; [exact Hj'|]. split; [exact Ha0|]. split; [exact HHB|].
    split; [exact HLK|]. split; [exact HFC|]. split; [exact HFL|]. split; [exact HIN'|].
    split; [exact H248'|]. split; [exact HIFS' | exact HC'].
  - exists regs, mem, md, fr. split; [exact Ec|]. split; [exact HFRA|]. split; [exact HENT|].
    split; [|exact HC].
    split; [exact Hgn|]. split; [exact HLI|]. split; [exact HFLSH|]. split; [exact HIN | exact H248].
Qed.

End S.
