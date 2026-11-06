(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 1288 of its 1531 lines of code are new or changed and 2314 lines of the source are left out. *)
(* Segment F1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan build of libreac v1.9.0, image B): the frame-loop
   turn j from the loop head 0x81ec4 to the allocation call `jal wrapper_malloc` at 0x81f4c, which returns to
   0x81f50 (the entry of F2).  With q = p + c_j the input cursor and left = n - c_j the bytes left:
     0x81ec4 bnez s9,0x81ecc     s9 = left >= 1 (LI), so the exit jump 0x81ec8 j 0x82eac is not taken
     0x81ecc addi s5,s7,1        s5 = q + 1
     0x81ed0 bltu s6,s5,0x81ed8  s6 = 1 < q + 1 (q >= 4096): the trap 0x81ed4 j 0x82fa0 is not taken
     0x81ed8-0x81ee4             the instrumented check of the byte at q: the shadow byte at (q >> 3) + ASAN_K is
                                 loaded and the branch to 0x82d2c is taken only when it is not 0; at 0x82d2c the
                                 code compares q mod 8 against it and reaches the error path 0x83070 (a call of
                                 __asan_report_load1) only when q mod 8 >= it.  The input bytes are addressable
                                 (f1_IN), so both arms reach 0x81ee8 and the error path is not reached
     0x81ee8 lbu a0,0(s7)        a0 = in[c_j]
     0x81eec bne s9,s6,0x81efc   left = 1: fall through (h = 1, s9 = 0, a1 = 0, j 0x81f28); left >= 2: the second
                                 byte path 0x81efc-0x81f24 (the trap test at 0x81f00, the second instrumented check
                                 at 0x81f08-0x81f14 with its slow arm 0x82d44 and error path 0x8307c,
                                 a1 = in[c_j+1] << 8, s9 = left - 2, s5 = q + 2)
     0x81f28 or s4,a1,a0         s4 = L, the 1- or 2-byte length header
     0x81f2c bltu s4,s9 / 0x81f30 mv s4,s9   s4 = len = min(L, left - h)
     0x81f34 not a0,s5 / 0x81f38 bgeu a0,s4,0x81f40   (q + h) + len <= 2^64 - 1: the trap is not taken
     0x81f40 sd s9,232(s1)       the spill [A+232] = left - h (FC)
     0x81f44 sd a3,240(s1)       the spill [A+240] = j (LK)
     0x81f48 mv a0,s4 / 0x81f4c jal 0x534b8   the allocation request of len bytes
   v1.9.0 against the patched image: left is in s9 (was s8), the record cursor q + h in s5 (was s9), the constant
   1 in s6 (was a2), the two spills move from [A+224, A+240) to [A+232, A+248), the slow arms and traps are at new
   addresses, and the allocator entry is 0x534b8 (was 0x53490).
   The run 0x81ec4 -> 0x534b8 is f1_evt (a Theorem Labs lane's run lemmas of a working branch, without their mem_inv),
   lifted by Tac_slot.sl_run_lib; FRA and ENT move across its two spill stores [A + 232, A + 248) by f1_fra_spill
   (Tac_slot.sl_stk_run / ent_store, after image A's F1.v).  The allocation is taken by the frame's allocator
   contract (FF's APIf: AC.aa_malloc at AC.as_malloc, never the allocator's code) on the a_call_pre that
   SlotInv.fra_call_pre builds from FRA + ENT (K = AK_MALLOC = 4096 <= FN_STACK), with the room premise from FRA's
   live-bytes bound (f1_place_room) and the per-class premises from ENT's 14th conjunct (Seg/Tac_cls.v's
   sl_malloc_cls, Bc := Bc_of BE); f1_malloc_keep moves FRA across it (Tac_slot.sl_mid_perm: the contract
   appends the new block, FRA prepends it) and gives the bytes and shadow bytes the exit reads, f1_ent_call moves
   ENT (lib/B/Prog/Seg/R7.v's r7_ent_call).  Cuts: the official SlotInv.v Inv_B81ec4_at (entry, pc 0x81ec4) and
   Inv_B81f50_at (exit, pc 0x81f50), named by their v1.9 pcs (217aa9d4cd9, a Theorem Labs lane's
   v190-cutnames-B.tsv (a working note, not in this delivery)).  The exit Inv_B82eac (pc 0x82eac) of S_F1 is not reached: LI's 1 <= left_j
   makes `bnez s9` at 0x81ec4 taken.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YI08.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_cls.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcFragLib RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.

(* ---- the branch facts of the run ---- *)

(* `bnez x` with x <> 0 (the loop head 0x81ec4) and `bne x,y` with x <> y (0x81eec). *)
Lemma f1_bne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof.
  intros x y Hx Hy Hn. rewrite (bv_eqb_lit x y Hx Hy).
  apply Bool.negb_true_iff, Z.eqb_neq. exact Hn.
Qed.

Lemma f1_beq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
Proof.
  intros x y Hx Hy Hn. rewrite (bv_eqb_lit x y Hx Hy).
  apply Bool.negb_false_iff, Z.eqb_eq. exact Hn.
Qed.

(* A sign-extended shadow byte against zero (the instrumented checks at 0x81ee4 / 0x81f14). *)
Lemma f1_sxb_nz : forall b : byte, bv_signed b <> 0 -> negb (bv_eqb (sxb b) (Z_to_bv 64 0)) = true.
Proof.
  intros b H. unfold sxb. pose proof (sbyte_range b). unfold bv_eqb.
  rewrite (unsigned_lit 0) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  rewrite (proj2 (Z.eqb_neq _ _)); [reflexivity|].
  intros E. apply H. revert E. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma f1_sxb_z : forall b : byte, bv_signed b = 0 -> negb (bv_eqb (sxb b) (Z_to_bv 64 0)) = false.
Proof. intros b H. unfold sxb. rewrite H. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

(* 0x81f38: `not a0,s5` then `bgeu a0,s4` is taken when (q + h) + len <= 2^64 - 1. *)
Lemma f1_not_ge : forall x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) (Z_to_bv 64 y) = false.
Proof.
  intros x y H1 H2 H3. rewrite (unsigned_lit x) by lia.
  change 18446744073709551615 with (2 ^ 64 - 1). rewrite YI08.lxor_allones by lia.
  unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

(* (in[c+1] << 8) | in[c], the little-endian u16 of the two header bytes (0x81f24 / 0x81f28). *)
Lemma f1_lor_shl8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (Z.shiftl y 8) x = x + 256 * y.
Proof. intros x y Hx Hy. rewrite RcIdentLib.rc_lor_shl8 by lia. lia. Qed.

Lemma f1_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia. Qed.

(* The instrumented check of the byte at address q (srli / add s10 / lb / bnez, and the slow arm andi / bge / j,
   whose taken bge is the error path, a call of __asan_report_load1): both arms of 0x81ee4 / 0x81f14 reach the
   fast path. *)
Ltac f1_shadow q k Hsh :=
  step; rewrite (unsigned_lit q) by lia; step; step; step;
  let E0 := fresh "E0" in let N0 := fresh "N0" in
  destruct (Z.eq_dec (bv_signed k) 0) as [E0|N0];
  [ rewrite (f1_sxb_z k E0); cbv iota
  | rewrite (f1_sxb_nz k N0); cbv iota; step; step;
    rewrite (unsigned_lit q) by lia; rewrite (land7 q ltac:(lia));
    rewrite (lts_sxb (q mod 8) k ltac:(pose proof (Z.mod_pos_bound q 8 ltac:(lia)); lia));
    rewrite (proj2 (Z.ltb_lt (q mod 8) (bv_signed k))) by (unfold shadow_ok in Hsh; lia);
    cbn [negb]; cbv iota; step ].

(* ---- the run 0x81ec4 .. the allocator entry 0x534b8, over explicit registers ---- *)

Section Run.
Context {fx : FPState}.

(* The end state of the run: at the allocator's entry with the return address 0x81f50, the request len in a0 and
   s4, the record cursor q + h in s5, the bytes left after the header in s9, s6 and s8 as they were, and the two
   spills written. *)
Definition f1_post (sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s6 s8 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A q left j h len : Z)
    : machine_state -> Prop :=
  fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x81f50) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 len) a1' a2'
                  (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 (Z_to_bv 64 len) (Z_to_bv 64 (q + h)) s6 (Z_to_bv 64 q)
                  s8 (Z_to_bv 64 (left - h)) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x534b8) fc None m' (seg_rom rsegs) /\
    munch [(A + 232, A + 248)] m m' /\ wmono rsegs m m' /\
    bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 (left - h))) /\
    bytes_at rsegs m' (A + 240) (le8 (Z_to_bv 64 j)).

(* 0x81f28 .. the allocator entry: the length header L is in a1 | a0, the record cursor q + h is in s5 and the
   bytes left after the header in s9; s4 becomes len = min(L, left - h), the two spills are written and the
   request is made. *)
Lemma f1_body :
  forall (ra0 sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len lo hi L : Z),
    0 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    0 <= lo < 2 ^ 64 -> 0 <= hi < 2 ^ 64 -> Z.lor hi lo = L -> 0 <= L < 2 ^ 17 ->
    1 <= h <= 2 -> h <= left -> len = Z.min L (left - h) ->
    wr_at rsegs m (A + 232) 16 ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s6 s8 s11 t3 t4 t5 t6 Fr fc m A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 lo) (Z_to_bv 64 hi) a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + h)) s6 (Z_to_bv 64 q) s8
               (Z_to_bv 64 (left - h)) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f28) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j h len lo hi L Hq Hql Hl Hj HA0 HA1 Hlo Hhi EL HL Hh Hhl Elen HW.
  pose proof (munch_refl [(A + 232, A + 248)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* 0x81f28 or s4,a1,a0 ; 0x81f2c bltu s4,s9 *)
  step. rewrite (unsigned_lit hi) by lia. rewrite (unsigned_lit lo) by lia. rewrite EL.
  step. rewrite (bv_ltu_lit L (left - h)) by lia.
  destruct (Z.ltb_spec L (left - h)) as [Hlt|Hge]; cbv iota;
    [ (* L < left - h: s4 keeps L = len *)
      assert (EE : len = L) by lia; rewrite EE; step; step
    | (* otherwise 0x81f30 mv s4,s9 sets s4 = left - h = len *)
      assert (EE : len = left - h) by lia; rewrite EE; step; step; step ].
  (* both arms: 0x81f34 not a0,s5 ; 0x81f38 bgeu a0,s4 (taken) *)
  all: rewrite (f1_not_ge (q + h)) by lia; cbn [negb]; cbv iota.
  (* 0x81f40 sd s9,232(s1) *)
  all: pose proof (wr_at_store_ok rsegs m (A + 232) 16 0 8 HW ltac:(lia) ltac:(lia)) as HS1.
  all: replace (A + 232 + 0) with (A + 232) in HS1 by lia.
  all: step.
  (* 0x81f44 sd a3,240(s1) *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           pose proof (wr_at_store_ok rsegs mm (A + 232) 16 8 8
                         (wr_at_write rsegs m (A + 232) 16 _ _ HW) ltac:(lia) ltac:(lia)) as HS2
       end.
  all: replace (A + 232 + 8) with (A + 240) in HS2 by lia.
  all: step.
  (* 0x81f48 mv a0,s4 ; 0x81f4c jal 0x534b8 *)
  all: step; step.
  all: apply evt_done; unfold f1_post; do 3 eexists; split; [reflexivity|].
  all: split;
       [ apply munch_write;
         [ apply munch_write; [exact MU | lia | rewrite length_le8; lia
                              | cbn [inside]; rewrite length_le8; lia]
         | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia] |].
  all: split; [apply wmono_write; apply wmono_write; exact WM|].
  all: split;
       [ apply bytes_at_write_other;
         [ apply bytes_at_write_same; [lia | rewrite length_le8; lia]
         | lia | rewrite length_le8; lia | rewrite !length_le8; lia] |].
  all: apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(* 0x81f18 (the second byte's fast path) .. the allocator entry: a1 takes in[c+1], s9 drops to left - 2 and s5
   becomes q + 2. *)
Lemma f1_tail2 :
  forall (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j len : Z) (b0 b1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 2 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1] ->
    wr_at rsegs m (A + 232) 16 ->
    len = Z.min (bv_unsigned b0 + 256 * bv_unsigned b1) (left - 2) ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s6 s8 s11 t3 t4 t5 t6 Fr fc m A q left j 2 len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb b0) a1 a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + 1)) s6 (Z_to_bv 64 q) s8
               (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f18) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j len b0 b1 Hq Hql Hl Hj HA0 HA1 HR1 HW Elen.
  pose proof (f1_byte_rng b0) as Hb0. pose proof (f1_byte_rng b1) as Hb1.
  (* 0x81f18 lbu a1,0(s5) ; 0x81f1c addi s9,s9,-2 ; 0x81f20 addi s5,s7,2 ; 0x81f24 slli a1,a1,8 *)
  step. step. step. step.
  rewrite RcIdentLib.zxb_u.
  replace (left + -2) with (left - 2) by lia.
  unfold zxb at 1.
  apply (f1_body _ sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 Fr fc m
           A q left j 2 len (bv_unsigned b0) (Z.shiftl (bv_unsigned b1) 8)
           (bv_unsigned b0 + 256 * bv_unsigned b1));
    try lia.
  - rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia.
  - apply f1_lor_shl8; lia.
  - exact HW.
Qed.

(* 0x81ee8 (both arms of the first instrumented check) .. the allocator entry. *)
Lemma f1_tail1 :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len : Z) (b0 b1 k1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1]) ->
    (2 <= left -> shadow_ok (q + 1) (bv_signed k1)) ->
    wr_at rsegs m (A + 232) 16 ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
                 A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + 1)) (Z_to_bv 64 1) (Z_to_bv 64 q) s8
               (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ee8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j h len b0 b1 k1 Hq Hql Hl Hj HA0 HA1 HR0 HR1 HK1 HS1 HW Eh Elen.
  pose proof (f1_byte_rng b0) as Hb0. pose proof (f1_byte_rng b1) as Hb1.
  (* 0x81ee8 lbu a0,0(s7) ; 0x81eec bne s9,s6 *)
  step. step.
  destruct (Z.eq_dec left 1) as [E1|N1].
  - (* left = 1: h = 1, the header is the single byte in[c] *)
    subst left. rewrite (f1_beq 1 1 ltac:(lia) ltac:(lia) eq_refl). cbv iota.
    assert (Eh1 : h = 1) by lia. subst h.
    (* 0x81ef0 li s9,0 ; 0x81ef4 li a1,0 ; 0x81ef8 j 0x81f28 *)
    step. step. step.
    unfold zxb at 1.
    apply (f1_body _ sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
             A q 1 j 1 len (bv_unsigned b0) 0 (bv_unsigned b0)); try lia.
    all: try (apply Z.lor_0_l); try exact HW.
    change (2 <=? 1) with false in Elen. rewrite Elen. lia.
  - (* left >= 2: the second header byte *)
    rewrite (f1_bne left 1 ltac:(lia) ltac:(lia) N1). cbv iota.
    assert (Hl2 : 2 <= left) by lia.
    assert (Eh2 : h = 2) by lia. subst h.
    rewrite (proj2 (Z.leb_le 2 left) Hl2) in Elen.
    (* 0x81efc addi a1,s5,1 ; 0x81f00 bltu s6,a1 (taken) *)
    step. step.
    rewrite (bv_ltu_lit 1 (q + 2)) by lia.
    rewrite (proj2 (Z.ltb_lt 1 (q + 2)) ltac:(lia)). cbv iota.
    pose proof (HS1 Hl2) as HSk. pose proof (HK1 Hl2) as HKk. pose proof (HR1 Hl2) as HRk.
    (* 0x81f08-0x81f14: the second instrumented check, on the byte at q + 1 (slow arm 0x82d44) *)
    f1_shadow (q + 1) k1 HSk.
    all: replace (Z.min 2 left) with 2 by lia.
    all: apply (f1_tail2 _ sp gp tp t0 t1 t2 s0 _ _ a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6
                  Fr fc m A q left j len b0 b1); try lia; try assumption.
Qed.

(* The whole run, from the frame-loop head. *)
Lemma f1_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len : Z) (b0 b1 k0 k1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    shadow_ok q (bv_signed k0) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1]) ->
    (2 <= left -> shadow_ok (q + 1) (bv_signed k1)) ->
    wr_at rsegs m (A + 232) 16 ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
                 A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4
               s5 (Z_to_bv 64 1) (Z_to_bv 64 q) s8 (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ec4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j h len b0 b1 k0 k1 Hq Hql Hl Hj HA0 HA1 HR0 HK0 HS0 HR1 HK1 HS1 HW Eh Elen.
  (* 0x81ec4 bnez s9 (taken) ; 0x81ecc addi s5,s7,1 ; 0x81ed0 bltu s6,s5 (taken) *)
  step. if_true_by (f1_bne left 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step.
  rewrite (bv_ltu_lit 1 (q + 1)) by lia.
  rewrite (proj2 (Z.ltb_lt 1 (q + 1)) ltac:(lia)). cbv iota.
  (* 0x81ed8-0x81ee4: the instrumented check of the byte at q (slow arm 0x82d2c) *)
  f1_shadow q k0 HS0.
  all: apply (f1_tail1 _ sp gp tp t0 t1 t2 s0 _ _ a2 a4 a5 a6 a7 s2 s3 s4 s8 s11 t3 t4 t5 t6 Fr fc m
                A q left j h len b0 b1 k1); try lia; try assumption.
Qed.

End Run.

(* ---- byte, register and shadow helpers ---- *)

Lemma f1_mkR_of : forall regs,
  Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

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
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b] /\ shadow_ok X (bv_signed b).
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & _).
  exists b. split.
  - pose proof (ro_cells_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes Z.of_nat] in H. rewrite Z.add_0_r in H. exact H.
  - unfold shadow_ok. destruct OK as [H|H]; [left; exact H | right; lia].
Qed.

(* Bytes whose cells keep their contents. *)
Lemma f1_keep_bytes : forall m m' a bs,
  bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). exact (HK (a + Z.of_nat i) ltac:(lia)).
Qed.

(* A buffer stays addressable when its shadow bytes keep their contents. *)
Lemma f1_addr_keep : forall m m' p n,
  addressable m p n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. rewrite <- Hb. exact (HK i Hi).
Qed.

(* A spill at A + off (A the spill base in register 9) moves to a state with the same register 9 whose bytes at
   [A + off, A + off + 8) are the same. *)
Lemma f1_spill_keep : forall regs regs' m m' A off v,
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  getr regs' 9 = getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v Hr9 HA0 HA1 Hoff E9 HK (A' & HA' & Hq).
  assert (HA'eq : A' = A).
  { pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
    pose proof Hq as Hqb. destruct Hqb as (Hq0 & Hq1 & _).
    rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    rewrite (Z.mod_small A) in Hm by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
  apply (f1_keep_bytes m m' _ _ Hq). rewrite length_le8. change (Z.of_nat 8) with 8.
  intros x Hx. exact (HK x Hx).
Qed.

(* The byte at x is readable in m when it lies inside a bytes_at range. *)
Lemma f1_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma f1_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> Frame.munch W m m' -> Frame.wmono rsegs m m' ->
  (forall x, lo <= x < hi -> Frame.outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* Two names of the spill base register value agree modulo 2^64; an 8-aligned window [A0 + lo, A0 + hi) of the
   448-byte save area misses the spills [A + L, A + H) (F1: [A + 232, A + 248)) unless it overlaps them at
   A0 = A. *)
Lemma f1_spill_out : forall A A0 lo hi L H x, Z_to_bv 64 A0 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
  A0 + lo <= x < A0 + hi -> 0 <= lo -> hi <= 448 -> 0 <= L -> H <= 448 -> (hi <= L \/ H <= lo) ->
  ~ (A + L <= x < A + H).
Proof.
  intros A A0 lo hi L H x E HA Hx Hlo Hhi HL HH Hd.
  apply (f_equal (@bv_unsigned 64)) in E. rewrite !MState.unsigned_lit_wrap in E.
  rewrite (Z.mod_small A) in E by lia.
  assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite HP in *.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- frame-loop record lengths: 38 identity bytes and 72 fragment bytes at every turn ---- *)

Lemma f1_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact Hs].
  assert (Hn : 1 <= RcFrag.fg_n g <= 22).
  { unfold RcFrag.fg_fr in Efr.
    apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr H22]. apply andb_prop in Efr as [_ H1].
    apply Z.leb_le in H22. apply Z.leb_le in H1. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first, RcFrag.fg_body, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb].
    + assert (HT : RcFrag.fg_T st g <= 64).
      { unfold RcFrag.fg_keep in Ek. apply andb_prop in Ek as [_ HT]. apply Z.leb_le in HT. exact HT. }
      destruct (RcFrag.fg_close st g); cbn [negb fg_next];
        apply RcFragLib.rf_clear_length; apply RcFragLib.rf_fg_join_length; assumption.
    + cbn [fg_next]. apply RcFragLib.rf_clear_length. exact Hs.
Qed.

Lemma f1_FG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens _ _); cbn [fs_fg];
    (apply f1_fgst_len; [exact IH | unfold t_g; apply fr50_length]).
Qed.

Lemma f1_ID_len : forall inp j, Z.of_nat (length (t_ID inp j)) = 38.
Proof. intros inp j. rewrite t_ID_length. reflexivity. Qed.

(* The body of the first-fragment state is at most 23 bytes (firstn of the last 23 of the 50 frame bytes), so
   the local `first` (40 bytes at fr + 2880: have, n, the body from fr + 2885) holds it. *)
Lemma f1_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens _ _); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* ---- the KIND_NAME table KNT (FLI's KNT conjunct): 112 bytes inside one RELRO global ---- *)

Lemma f1_kn_len : (length KNC.kind_name_bytes <=? 112)%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* Whether [lo, hi) lies inside one block of frame_RELRO (checked by computation, so the lemmas below follow the
   addresses that FrameAPI.v and reac_ctrl_kind_name_c.v state). *)
Definition f1_relro_cov (lo hi : Z) : bool :=
  existsb (fun p => (fst p <=? lo) && (hi <=? fst p + snd p)) AF.frame_RELRO.

Lemma f1_kn_relro : forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 -> in_globals AF.frame_RELRO x.
Proof.
  intros x Hx.
  assert (Hc : f1_relro_cov KNC.KIND_NAME (KNC.KIND_NAME + 112) = true) by (vm_compute; reflexivity).
  unfold f1_relro_cov in Hc. apply existsb_exists in Hc. destruct Hc as ((lo & len) & Hin & Hb).
  apply andb_true_iff in Hb as (H1 & H2). apply Z.leb_le in H1, H2. cbn [fst snd] in H1, H2.
  exists lo, len. split; [exact Hin | lia].
Qed.

(* ---- bundle moves: a frame-loop bundle survives a change of the memory that keeps the bytes it reads ---- *)

(* FLI: s11, position 2 (`True`), the 22 spills (all off [A + 224, A + 248)), our[]'s six addressable bytes, the
   frame body, RAD (the identity record, the fragment record and the local `first`) and KNT (the KIND_NAME table:
   RELRO bytes and their shadow). *)
Lemma f1_fli_move : forall g fr regs regs' m m' A,
  FLI g fr regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall x, A <= x < A + 224 \/ A + 248 <= x < A + 448 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ fragb fr <= x < fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 ->
     mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  (forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 ->
     mbyte rsegs m' x = mbyte rsegs m x /\ mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  stk rsegs m' fr (fr + FRAME_BYTES) ->
  FLI g fr regs' m'.
Proof.
  intros g fr regs regs' m m' A H H9 HA0 HA1 E9 E27 KA KS KI HSTK.
  destruct H as (H27 & S168a & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HA2624 & _ & HRAD & (HKNb & HKNa) & S168 & S88).
  destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
  assert (K : forall off v, 0 <= off -> off + 8 <= 224 \/ 248 <= off -> off <= 440 ->
            spill regs m off v -> spill regs' m' off v).
  { intros off v H0 H1 H2 Hs. apply (f1_spill_keep regs regs' m m' A off v H9 HA0 HA1 ltac:(lia) E9); [|exact Hs].
    intros x Hx. apply KA. lia. }
  unfold FLI.
  split; [unfold rg in *; rewrite E27; exact H27|].
  do 21 (split; [apply K; [lia | lia | lia | assumption]|]).
  split; [apply (f1_addr_keep m m' _ _ HA2624); intros i Hi; apply KS; lia|].
  split; [exact HSTK|].
  split.
  { split; [apply (f1_addr_keep m m' _ _ HRAD1); intros i Hi; apply KS; lia|].
    split; [apply (f1_addr_keep m m' _ _ HRAD2); intros i Hi; apply KS; unfold fragb in *; lia|].
    apply (f1_addr_keep m m' _ _ HRAD3); intros i Hi; apply KS; lia. }
  split.
  { split.
    - apply (f1_keep_bytes m m' _ _ HKNb). pose proof f1_kn_len as HL. apply Nat.leb_le in HL.
      intros x Hx. apply KI. lia.
    - apply (f1_addr_keep m m' _ _ HKNa). intros i Hi. apply KI. lia. }
  split; (apply K; [lia | lia | lia | assumption]).
Qed.

(* FSj: the frame local `first` (have, a u32 at fr + 2880; n, the byte at fr + 2884; the body from fr + 2885;
   its 40 usable bytes) and the model fact FI. *)
Lemma f1_fsj_move : forall g fr j regs regs' m m',
  FSj g fr j regs m ->
  (forall x, fr + 2880 <= x < fr + 2920 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2880 <= x < fr + 2920 -> mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  FSj g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' (Hhave & Hn & Hbody & Had & HFI) KF KS.
  pose proof (f1_body_len (g_in g) j) as HL.
  unfold FSj, FSb.
  split; [unfold u32 in *; apply (f1_keep_bytes m m' _ _ Hhave); rewrite length_le4; intros x Hx; apply KF; lia|].
  split; [unfold b8 in *; apply (f1_keep_bytes m m' _ _ Hn); cbn [length]; intros x Hx; apply KF; lia|].
  split; [apply (f1_keep_bytes m m' _ _ Hbody); intros x Hx; apply KF; lia|].
  split; [apply (f1_addr_keep m m' _ _ Had); intros i Hi; apply KS; lia|].
  exact HFI.
Qed.

(* REC0: the identity record at fr + 2688 (38 bytes) and the fragment record at fr + 2768 (72 bytes). *)
Lemma f1_rec0_move : forall g fr j m m',
  REC0 g fr j m -> (forall x, fr + 2688 <= x < fr + 2840 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  REC0 g fr j m'.
Proof.
  intros g fr j m m' ((HID & Hok) & (HFG & Hfok)) KF.
  split; split; [| exact Hok | | exact Hfok].
  - unfold IDBe in *. apply (f1_keep_bytes m m' _ _ HID). rewrite f1_ID_len. intros x Hx. apply KF. lia.
  - unfold FGBe in *. apply (f1_keep_bytes m m' _ _ HFG). rewrite f1_FG_len. intros x Hx. apply KF. lia.
Qed.

(* IFS at the loop head gives the records REC0 of the exit cuts. *)
Lemma f1_rec0_of_ifs : forall g fr j regs m, IFS g fr j regs m -> REC0 g fr j m /\ FSj g fr j regs m.
Proof. intros g fr j regs m (HID & HFG & HFS). split; [split; [exact HID | exact HFG] | exact HFS]. Qed.

(* our[]'s six bytes at fr + 2624. *)
Lemma f1_our_move : forall g fr m m', OURb g fr m ->
  (forall x, fr + 2624 <= x < fr + 2630 -> mbyte rsegs m' x = mbyte rsegs m x) -> OURb g fr m'.
Proof.
  intros g fr m m' H KF. unfold OURb in *. apply (f1_keep_bytes m m' _ _ H). rewrite OUR_length.
  intros x Hx. apply KF. cbn in Hx. lia.
Qed.

(* LK: the j spill [A + 240], our[], FLI. *)
Lemma f1_lk_move : forall g fr j regs regs' m m' A,
  LK g fr j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall x, A <= x < A + 224 \/ A + 240 <= x < A + 448 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2624 <= x < fr + 2630 \/ fr + 2688 <= x < fr + 2726 \/ fragb fr <= x < fragb fr + 72 \/
             fr + 2880 <= x < fr + 2920 ->
     mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  (forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 ->
     mbyte rsegs m' x = mbyte rsegs m x /\ mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  stk rsegs m' fr (fr + FRAME_BYTES) ->
  LK g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' A (Hj & S240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 KA KF KS KI HSTK.
  split; [exact Hj|].
  split; [apply (f1_spill_keep regs regs' m m' A 240 _ H9 HA0 HA1 ltac:(lia) E9); [|exact S240];
          intros x Hx; apply KA; lia|].
  split; [exact (f1_our_move g fr m m' HOUR KF)|].
  apply (f1_fli_move g fr regs regs' m m' A HFLI H9 HA0 HA1 E9 E27); [|exact KS | exact KI | exact HSTK].
  intros x Hx. apply KA. lia.
Qed.

(* f1_IN: the input block's membership (a ghost fact), its addressability (its shadow bytes) and its bytes. *)
Lemma f1_in_move : forall g m m', f1_IN g m ->
  (forall x, g_p g <= x < g_p g + g_n g ->
     mbyte rsegs m' x = mbyte rsegs m x /\ mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  f1_IN g m'.
Proof.
  intros g m m' (Hin & Had & Hb) K.
  split; [exact Hin|]. split.
  - apply (f1_addr_keep m m' _ _ Had). intros i Hi. exact (proj2 (K (g_p g + i) ltac:(lia))).
  - apply (f1_keep_bytes m m' _ _ Hb). intros x Hx. exact (proj1 (K x Hx)).
Qed.

(* ---- the allocation room premise: the secondary-map placement bound a_place_room (image A's F1.v) ---- *)

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
   bound of v1.9.0 Contract.v (the band also holds A_PLACE_OTHER = 2^41 bytes of main maps and A_PLACE_OTHER_N
   quarantined chunks) holds with a wide margin, since the live heap is at most 5 * 2^30 bytes (FRA, from
   alib_pre). *)
Lemma f1_place_room : forall H n, (forall p k, In (p, k) H -> 0 <= k) ->
  AC.a_live_bytes H <= 5 * 2 ^ 30 -> 0 <= n <= 65535 -> AC.a_place_room H n.
Proof.
  intros H n Hnn Hlive Hn. right.
  pose proof (f1_sec_count H Hnn) as Hc.
  pose proof (f1_sec_mapped H Hnn) as Hm.
  pose proof (f1_sec_map_le n ltac:(lia)) as Hs.
  set (c := Z.of_nat (length (AC.a_sec_blocks H))) in *.
  assert (Hc0 : 0 <= c) by (unfold c; lia).
  assert (Hcb : c <= 83227) by lia.
  assert (Hprod : (c + AC.A_PLACE_OTHER_N + 1) * (AC.a_sec_map n + 4096) <=
                  (c + AC.A_PLACE_OTHER_N + 1) * 81925).
  { apply Z.mul_le_mono_nonneg_l; [unfold AC.A_PLACE_OTHER_N; lia | lia]. }
  assert (Hprod2 : (c + AC.A_PLACE_OTHER_N + 1) * 81925 <= (83227 + 8354 + 1) * 81925)
    by (apply Z.mul_le_mono_nonneg_r; unfold AC.A_PLACE_OTHER_N; lia).
  unfold AC.A_PLACE_HI, AC.A_PLACE_LO, AC.A_PLACE_OTHER. lia.
Qed.

(* ---- image placement facts (lib/B/Prog/Seg/R7.v) ---- *)

Lemma f1_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f1_img_range : forall x, AC.a_in_img x -> 0 <= x < 6283264.
Proof.
  intros x (s & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f1_img_top s Hin) as Hs. cbv beta in Hs.
  apply Z.leb_le in Hs. pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Definition f1_img_cov (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma f1_img_cov_in : forall lo hi x, f1_img_cov lo hi = true -> lo <= x < hi -> AC.a_in_img x.
Proof.
  intros lo hi x H Hx. unfold f1_img_cov in H. apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (H1 & H2). apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin | lia].
Qed.

Lemma f1_ag_cov : forallb (fun p => f1_img_cov (fst p) (fst p + snd p)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f1_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f1_ag_cov (lo, len) Hin) as H. cbn [fst snd] in H.
  exact (f1_img_cov_in _ _ _ H Hr).
Qed.

(* The client objects of musl's stdio the sink words live in (Contract.v a_client), checked by computation
   (f1_client_in), so the proof follows whatever blocks Contract.v states. *)
Definition f1_client_cov (lo hi : Z) : bool :=
  existsb (fun p => (fst p <=? lo) && (hi <=? fst p + snd p)) AC.a_client.
Lemma f1_client_in : forall lo hi a, f1_client_cov lo hi = true -> lo <= a < hi -> AC.in_blocks AC.a_client a.
Proof.
  intros lo hi a H Ha. unfold f1_client_cov in H. apply existsb_exists in H.
  destruct H as ((b & n) & Hin & Hb). apply andb_true_iff in Hb as (H1 & H2). apply Z.leb_le in H1, H2.
  cbn [fst snd] in H1, H2. exists b, n. split; [exact Hin | lia].
Qed.

(* The image's RELRO globals lie in [0x90000, 0x100000) (checked by computation on FrameAPI.v's list). *)
Lemma f1_relro_ok : forallb (fun p => (0x90000 <=? fst p) && (fst p + snd p <=? 0x100000)) AF.frame_RELRO = true.
Proof. vm_compute. reflexivity. Qed.
Lemma f1_relro_range : forall a, in_globals AF.frame_RELRO a -> 0x90000 <= a < 0x100000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f1_relro_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_true_iff in H as (H1 & H2). apply Z.leb_le in H1, H2. lia.
Qed.

(* ---- local views of the generated allocator laws (v1.9.0 Contract.v, a working branch 48004cf7bfc) ----
   a Theorem Labs lane's rule (15:18Z / 15:32Z): the generator may add conjuncts to a law at any nesting level, so a law's
   conjunct list is taken apart once, here, by a position-free proof (decompose, then match each conjunct by its
   type), and every site of F1-F6 uses these views.  The views state the v1.9.0 laws' content; a later generation
   that adds a conjunct changes no view and no site. *)
Ltac f1_lw_conj := repeat (match goal with |- _ /\ _ => split end).

Section Laws.
Context {fx : YK11.FPState}.
Variable API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Local Notation AH := (AC.aa_AH AC.ASYMS AsanRTInv.RT API).
Local Notation OWN := (AC.aa_owned AC.ASYMS AsanRTInv.RT API).
Local Notation STKLO := (AC.aa_stklo AC.ASYMS AsanRTInv.RT API).
Local Notation STKHI := (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API).
Local Notation LAWS := (AC.aa_laws AC.ASYMS AsanRTInv.RT API).

(* a_laws_blocks: a live block is 16-aligned, at or above 4096, below stklo, ends in app memory, and its bytes are
   writable app memory off the image, the image pages and the side stack. *)
Lemma f1_lw_blocks : forall H mem md p n, AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= STKLO mem md /\ end_in_app p n /\
  forall a, p <= a < p + n ->
    app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\ ~ AC.a_on_img_page a /\ ~ AC.a_in_fs AC.ASYMS mem a.
Proof.
  intros H mem md p n HAH Hin.
  pose proof (AC.a_laws_blocks _ _ _ _ _ LAWS H mem md p n HAH Hin) as P. decompose [and] P.
  f1_lw_conj; try assumption.
  (* the per-byte list, when the law's list has more members than the view's *)
  all: match goal with
       | |- forall x, ?lo <= x < ?hi -> _ =>
           let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
           match goal with Hc : forall y, lo <= y < hi -> _ |- _ => pose proof (Hc a Ha) as Q end;
           decompose [and] Q; f1_lw_conj; assumption
       end.
Qed.

(* a_laws_not_owned *)
Lemma f1_lw_not_owned : forall H mem md a, AH H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/ STKLO mem md <= a < APPMEM_END) ->
  ~ OWN H mem md a /\ ~ OWN H mem md (shadow_addr a).
Proof.
  intros H mem md a HAH Ha.
  pose proof (AC.a_laws_not_owned _ _ _ _ _ LAWS H mem md a HAH Ha) as P. decompose [and] P.
  f1_lw_conj; assumption.
Qed.

(* a_laws_client *)
Lemma f1_lw_client : forall H mem md a, AH H mem md ->
  (AC.in_blocks AC.a_client a -> ~ OWN H mem md a) /\ (AC.a_in_img a -> ~ OWN H mem md (shadow_addr a)) /\
  (AC.as_tp AC.ASYMS <= a < AC.as_tp AC.ASYMS + 8 -> OWN H mem md a).
Proof.
  intros H mem md a HAH.
  pose proof (AC.a_laws_client _ _ _ _ _ LAWS H mem md a HAH) as P. decompose [and] P.
  f1_lw_conj; assumption.
Qed.

(* a_laws_store *)
Lemma f1_lw_store : forall H mem mem' md, AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (STKLO mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AH H mem' md /\ (forall a, OWN H mem' md a <-> OWN H mem md a) /\ STKLO mem' md = STKLO mem md /\
  STKHI mem' md = STKHI mem md.
Proof.
  intros H mem mem' md HAH Hk Hw.
  pose proof (AC.a_laws_store _ _ _ _ _ LAWS H mem mem' md HAH Hk Hw) as P. decompose [and] P.
  f1_lw_conj; assumption.
Qed.

(* a_laws_fs_place *)
Lemma f1_lw_fs_place : forall H mem md b, AH H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= STKLO mem md /\ b mod 4096 = 0 /\
  forall a, b <= a < b + AC.FS_SIZE -> app_mem a.
Proof.
  intros H mem md b HAH Hw Hb.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ LAWS H mem md b HAH Hw Hb) as P. decompose [and] P.
  f1_lw_conj; assumption.
Qed.

(* a_laws_fs_state, its first part: the side stack's state a_fs_ok *)
Lemma f1_lw_fs_state_ok : forall H mem md FS, AH H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw HFS.
  pose proof (AC.a_laws_fs_state _ _ _ _ _ LAWS H mem md FS HAH Hw HFS) as P. decompose [and] P. assumption.
Qed.

(* a_laws_fs_store *)
Lemma f1_lw_fs_store : forall H mem mem' md FS, AH H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (STKLO mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) -> AC.a_fs_ok mem' FS ->
  AH H mem' md /\ (forall a, OWN H mem' md a <-> OWN H mem md a) /\ STKLO mem' md = STKLO mem md /\
  STKHI mem' md = STKHI mem md.
Proof.
  intros H mem mem' md FS HAH Hw HFS Hk Hwr Hok.
  pose proof (AC.a_laws_fs_store _ _ _ _ _ LAWS H mem mem' md FS HAH Hw HFS Hk Hwr Hok) as P. decompose [and] P.
  f1_lw_conj; assumption.
Qed.

(* a_fs_ok's cell part (Contract.v's Definition, taken apart once here): the side stack's bytes are present and
   writable. *)
Lemma f1_lw_fs_ok_cells : forall mem FS, AC.a_fs_ok mem FS ->
  forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b.
Proof.
  intros mem FS Hok a Ha. unfold AC.a_fs_ok in Hok. decompose [and] Hok.
  match goal with Hc : forall x, FS <= x < FS + AC.FS_SIZE -> _ |- _ => exact (Hc a Ha) end.
Qed.

End Laws.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* ---- FRA and ENT across spill stores [A + lo, A + hi) of the 448-byte save area (56 <= lo, hi <= 336) ----
   The store range is app memory above stklo (stklo <= S - SLOT_STACK < sp <= A) and below the entry sp S, so
   a_store_ok for a_laws_store; it misses every FRA cell (the frame below A, the frame shadow below HIGHMEM_BEG,
   the words [A + 40, A + 56) and [A + 336, A + 344), the saved registers [S - 104, S) and the low runtime and
   image cells), lies inside the entry-anchored slot window (ent_store), and the FakeStack frame record is below
   stklo (fsrec_stklo).  Image A's f1_fra_spill (a Theorem Labs lane's f4_fra_spill) re-pinned to image B's save area.
   F1 stores [A + 232, A + 248), F2 [A + 224, A + 232). *)
Lemma f1_fra_spill : forall g fr hb regs regs' mem mem' md md' Asp lo hi,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 Asp -> 0 <= Asp < 2 ^ 64 -> 56 <= lo -> lo <= hi -> hi <= 336 ->
  Frame.munch [(Asp + lo, Asp + hi)] mem mem' ->
  Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' Asp lo hi HFRA HENT H9 HA Hlo Hlh Hhi MU WM HWIN' Hmat
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HAsr : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HA0e : Asp = A0).
  { pose proof (rg_eq64 regs 9 Asp A0 H9 Hr9) as Hm. rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A0.
  assert (HfrL : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (Hbv9 : getr regs 9 = Z_to_bv 64 Asp) by exact H9.
  set (W := [(Asp + lo, Asp + hi)]) in MU.
  assert (HOUT : forall x, x < Asp + lo \/ Asp + hi <= x -> Frame.outside W x).
  { intros x Hx. subst W. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. apply HOUT. unfold AC.GT in Hx. lia. }
  assert (HAW : all_app W).
  { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. lia. }
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
    apply HOUT. destruct (Z_lt_le_dec a (Asp + lo)) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_lt_le_dec a (Asp + hi)) as [Hh|Hh]; [|right; exact Hh].
    exfalso. apply Hns. right. left. lia. }
  destruct (f1_lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH Hmc Hwrit)
    as (HAH' & Hown & HSTKeq & HSTKhi).
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md W
             HFRA MU WM HRO HAW HD HAH' HSTKeq HWIN').
    - intros x Hx. apply HOUT. lia.
    - intros x Hx. apply HOUT. lia.
    - intros A0 HA0 x Hx. apply HOUT. rewrite Hbv9 in HA0.
      pose proof (f1_spill_out Asp A0 336 344 lo hi x (eq_sym HA0) HA Hx ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(lia)). lia.
    - intros A0 HA0 x Hx. apply HOUT. rewrite Hbv9 in HA0.
      pose proof (f1_spill_out Asp A0 40 56 lo hi x (eq_sym HA0) HA Hx ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(lia)). lia.
    - intros x Hx. apply HOUT. lia.
    - intros x Hx. apply HOUT. unfold Sfr, shadow_addr in Hx. Z.div_mod_to_equations. lia.
    - eapply fsrec_stklo; [exact HAH | exact MU |].
      intros x Hx _. apply HOUT. lia.
    - intros x Hx. apply HOUT.
      assert (Hn0 : 0 < g_n g) by lia. destruct (Hinblk Hn0) as (Hin & _).
      destruct (f1_lw_blocks (APIf rc) (hb ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hpe & _). lia.
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
      destruct (Z_lt_le_dec x (Asp + lo)) as [H1|H1];
        [| destruct (Z_lt_le_dec x (Asp + hi)) as [H2|H2]].
      * left. apply HOUT. left. exact H1.
      * right. left. lia.
      * left. apply HOUT. right. exact H2.
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ENT across the allocation, whose post heap H' is a permutation of hb' ++ g_H g (lib/B/Prog/Seg/R7.v's
   r7_ent_call): ENT reads the post heap only through the runtime's ownership of image bytes, which is the same for
   the two orders (ent_owned_img), and through a_laws_not_owned / a_laws_client, which hold for H'.  This is F1's
   one destruct of ENT (v1.9.0: 14 conjuncts; 13 is ENT append #1, ent_shd; 14 the per-class bound, ghost-only). *)
Lemma f1_ent_call : forall g fr hb hb' H' regs mem md regs' mem' md' touched K,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md touched H' regs' mem' md' ->
  Permutation (hb' ++ g_H g) H' ->
  0 <= K <= FN_STACK ->
  (forall a, touched a -> app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a) ->
  AC.a_errno_kept AC.ASYMS mem mem' ->
  ENT APIf g hb' mem' md'.
Proof.
  intros g fr hb hb' H' regs mem md regs' mem' md' touched K HENT HFRA Hcp Hperm HK Hto Hek.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HENT as HE0.
  destruct HE0 as (Hasp & Hgtp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hkshd & Hcls).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & _ & _).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh.
  pose proof Hcp as Hah0; apply AC.a_call_post_ah in Hah0.
  assert (Hah' : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md')
    by exact (AC.a_laws_perm _ _ _ _ _ LAWS H' (hb' ++ g_H g) mem' md' Hah0 (Permutation_sym Hperm)).
  pose proof Hcp as Hsk; apply AC.a_call_post_stklo in Hsk.
  pose proof Hcp as Hskh; apply AC.a_call_post_stkhi in Hskh.
  pose proof Hcp as Hoom; apply AC.a_call_post_oom in Hoom.
  assert (Htp : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (Hfr : forall a, 0 <= a < 2 ^ 64 ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a ->
            ~ AC.a_window K regs a -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
            a <> AC.as_oom AC.ASYMS -> ~ touched a ->
            mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (eapply AC.a_call_post_frame; exact Hcp).
  assert (Hown' : forall a, AC.a_in_img a ->
            (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md' a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a))
    by (intros a Ha; exact (ent_owned_img APIf (hb' ++ g_H g) H' mem' md' mem' md' a Hah' Hah0 eq_refl
                              (fun i _ => eq_refl) Ha)).
  assert (Hwin2 : forall a, AC.a_window K regs a ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < g_S g).
  { intros a Ha. unfold AC.a_window in Ha. unfold FN_STACK in Hwlo.
    rewrite Haspz in Ha. rewrite Haspz in Hwlo. lia. }
  assert (Hoomimg : AC.a_in_img (AC.as_oom AC.ASYMS)) by exact oom_in_img.
  split; [exact Hasp|]. split; [exact Hgtp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|].
  split.
  { destruct Hmdl as (lz & mt & vm0 & fds0 & pins0 & Hmd & Hfd).
    pose proof Hcp as Hmd1'; apply AC.a_call_post_model in Hmd1'. destruct Hmd1' as (lz1 & mt1 & vm1 & Hmd1).
    exists lz1, mt1, vm1, fds0, pins0. split; [|exact Hfd].
    exact (md_shape_step (g_md g) md md' lz mt vm0 fds0 (m_fs (g_md g)) pins0 lz1 mt1 vm1 Hmd Hmd1). }
  split; [rewrite Hsk; exact Hslo|].
  split; [rewrite Hskh; exact Hshi|].
  split.
  { intros q k i Hin Hni Hi.
    destruct (f1_lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
      as (_ & Hq4 & Hend & _ & Hall).
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & Hnimg & _ & _).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hinb : AC.in_blocks (g_H g) (q + i)) by (exists q, k; split; [exact Hin | lia]).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (HinH' : In (q, k) H')
      by (eapply Permutation_in; [exact Hperm | apply in_or_app; right; exact Hin]).
    assert (Hinb2 : AC.in_blocks H' (q + i)) by (exists q, k; split; [exact HinH' | lia]).
    assert (Hn1 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (q + i))
      by exact (proj1 (f1_lw_not_owned (APIf rc) (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hn2 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' (q + i))
      by exact (proj1 (f1_lw_not_owned (APIf rc) H' mem' md' (q + i) Hah0 (or_introl Hinb2))).
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
    assert (Ho2' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a)
      by (intro X; apply Ho2;
          exact (proj1 (ent_owned_img APIf (hb ++ g_H g) (hb' ++ g_H g) mem md mem' md' a HAH Hah' Hsk Htp Hia) X)).
    assert (Ho2'' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a)
      by (intro X; apply Ho2; exact (proj2 (Hown' a Hia) X)).
    destruct (Himg a Hia Ho1 Ho2' Hg He) as (Hm0 & Hw0).
    destruct (Z.eq_dec a (AC.as_oom AC.ASYMS)) as [Eo|Eo].
    - subst a. destruct Hek as (_ & Hoomb).
      split; [rewrite Hoomb; exact Hm0|].
      split; intro X; [exact (proj1 Hoom (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hoom X))].
    - destruct (Hfr a ltac:(lia) Ho2' Ho2'' ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia) He Eo
                  ltac:(intro Ht; exact (proj1 (proj2 (proj2 (Hto a Ht))) Hia))) as (Hm & Hw).
      split; [rewrite Hm; exact Hm0|].
      split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Ha.
    assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) by lia.
    assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' <= a < APPMEM_END)
      by (rewrite Hsk; lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a)
      by exact (proj1 (f1_lw_not_owned (APIf rc) (hb ++ g_H g) mem md a HAH
                  (or_intror (or_intror (or_intror Hst))))).
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a)
      by exact (proj1 (f1_lw_not_owned (APIf rc) H' mem' md' a Hah0
                  (or_intror (or_intror (or_intror Hst'))))).
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
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (proj1 (proj2 (f1_lw_client (APIf rc) (hb ++ g_H g) mem md a HAH)) Hi).
      - assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) by lia.
        exact (proj2 (f1_lw_not_owned (APIf rc) (hb ++ g_H g) mem md a HAH
                  (or_intror (or_intror (or_intror Hst))))). }
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (proj1 (proj2 (f1_lw_client (APIf rc) H' mem' md' a Hah0)) Hi).
      - assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' <= a < APPMEM_END)
          by (rewrite Hsk; lia).
        exact (proj2 (f1_lw_not_owned (APIf rc) H' mem' md' a Hah0
                  (or_intror (or_intror (or_intror Hst'))))). }
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
  (* ENT append #1: the shadow bytes of the entry blocks the target does not keep (Tac_slot's ent_shadow_call,
     over the permuted post heap H') *)
  { intros q k i Hin Hni Hi.
    destruct (f1_lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
      as (_ & Hq4 & Hend & _ & Hall).
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & _).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (HinH' : In (q, k) H')
      by (eapply Permutation_in; [exact Hperm | apply in_or_app; right; exact Hin]).
    assert (Hinb2 : AC.in_blocks H' (q + i)) by (exists q, k; split; [exact HinH' | lia]).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (shadow_addr (q + i)))
      by exact (proj2 (f1_lw_not_owned (APIf rc) (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' (shadow_addr (q + i)))
      by exact (proj2 (f1_lw_not_owned (APIf rc) H' mem' md' (q + i) Hah0 (or_introl Hinb2))).
    pose proof (shadow_of_app (q + i) Happq) as Hsh1.
    destruct (in_shadow_range (shadow_addr (q + i)) Hsh1) as (R1 & R2).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1.
    destruct (Hfr (shadow_addr (q + i)) ltac:(lia) Hno Hno'
                ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                      rewrite <- He in X; lia)
                ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
    rewrite Hm. exact (Hkshd q k i Hin Hni Hi). }
  (* ENT #14, the per-class bound: it names the ghost only *)
  exact Hcls.
Qed.

(* ---- across the allocation call (amalloc_ret, a_call_post at AK_MALLOC with the new block (q, N)) ----
   FRA moves to the post state with hb = [(q, N)] (Tac_slot.sl_mid_perm), and the bytes the exit cut reads are
   kept: the frame, the live blocks and their shadow, the stack at or above sp, the RELRO globals and the shadow of
   every image byte.  A kept byte is not the allocator's before or after (a_laws_not_owned for blocks, FS and the
   real stack; a_laws_client for the sink cells and the shadow of image bytes; frame_facts for RELRO), so not in
   the new block either (whose bytes were the allocator's), and lies off errno, the OOM flag and the allocator's
   window [sp - 4096, sp) (the frame by sl_frame_apart_win, the rest by position).  Image A's f1_malloc_keep with
   image B's addresses (lib/B/Prog/Seg/R7.v). *)
Definition f1_loc (mem : word -> option byte) (md : Model) (a : Z) : Prop :=
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END \/
  (AC.a_in_fs AC.ASYMS mem a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).

Lemma f1_malloc_keep : forall g fr regs mem md N regs' mem' md' q,
  FRA B APIf ra g fr [] regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API)
    (AC.aa_owned AC.ASYMS AsanRTInv.RT API)
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API)
    AC.AK_MALLOC (g_H g) regs mem md (fun a => q <= a < q + N) (g_H g ++ [(q, N)]) regs' mem' md' ->
  (forall a, AC.in_blk_ext [(q, N)] a -> AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md a) ->
  FRA B APIf ra g fr (hb1 q N) regs' mem' md' /\
  (forall a, (fr <= a < fr + FRAME_BYTES \/ AC.in_blocks (g_H g) a \/ AC.aspZ regs <= a < APPMEM_END \/
              in_globals AF.frame_RELRO a) -> mbyte rsegs mem' a = mbyte rsegs mem a) /\
  (forall a, (fr <= a < fr + FRAME_BYTES \/ AC.in_blocks (g_H g) a \/
              AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END \/ AC.a_in_img a) ->
     mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
Proof.
  intros g fr regs mem md N regs' mem' md' q HFRA Hcp Hownq.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & HRimg & Hown & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  pose proof (sl_frame_apart_win B APIf ra g fr [] regs mem md HFRA) as Hapart0.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & _).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (HFS : AC.FS_SIZE = 11571200) by reflexivity.
  (* errno and the OOM flag by name (v1.9.0 Contract.v, a working branch); their values only for lia *)
  assert (Eerr : AC.a_errno AC.ASYMS = 6145452) by reflexivity.
  assert (Eoom : AC.as_oom AC.ASYMS = 1227040) by reflexivity.
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
    destruct (f1_lw_fs_place (APIf rc) _ mem md bb HAH Hwm Hbr) as (Hg & Hfsk & _ & Hfa').
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
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, N)]) mem' md' a ->
      ~ (sp - 4096 <= a < sp) -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
      a <> AC.as_oom AC.ASYMS ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Ho1 Ho2 Hw He Hoo. apply (Hfk a Ha Ho1 Ho2); [| exact He | exact Hoo |].
    - unfold AC.a_window, AC.AK_MALLOC. rewrite Haspz. exact Hw.
    - cbv beta. intros Ht. apply Ho1. apply Hownq. left. exists q, N. split; [left; reflexivity | lia]. }
  assert (FSPOST : forall a, AC.a_in_fs AC.ASYMS mem a -> AC.a_in_fs AC.ASYMS mem' a).
  { intros a (bb & Hbr & Hwm & Hb). exists bb. split; [exact Hbr|]. split; [|exact Hb].
    intros k Hk. rewrite (Htp16 (Z.of_nat k) ltac:(lia)). exact (Hwm k Hk). }
  (* a located byte and its shadow are not the allocator's, before or after *)
  assert (LOC : forall a, f1_loc mem md a ->
      0 <= a < 2 ^ 64 /\ AC.GT <= a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md (shadow_addr a) /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, N)]) mem' md' a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, N)]) mem' md' (shadow_addr a)).
  { intros a Hl.
    assert (Hpl : AC.in_blocks ([] ++ g_H g) a \/ AC.in_slack ([] ++ g_H g) a \/ AC.a_in_fs AC.ASYMS mem a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END).
    { destruct Hl as [Hs|[Hfs _]]; [right; right; right; exact Hs | right; right; left; exact Hfs]. }
    assert (Hql : AC.in_blocks (g_H g ++ [(q, N)]) a \/
                  AC.in_slack (g_H g ++ [(q, N)]) a \/ AC.a_in_fs AC.ASYMS mem' a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md' <= a < APPMEM_END).
    { rewrite Hsk'. destruct Hl as [Hs|[Hfs _]];
        [right; right; right; exact Hs | right; right; left; exact (FSPOST a Hfs)]. }
    destruct (f1_lw_not_owned (APIf rc) _ mem md a HAH Hpl) as (N1 & N2).
    destruct (f1_lw_not_owned (APIf rc) _ mem' md' a HAH' Hql) as (N3 & N4).
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
  assert (KCL : forall a, AC.a_errno AC.ASYMS + 4 <= a < AC.GT -> AC.in_blocks AC.a_client a ->
      mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ha Hcl. refine (proj1 (KEEP a _ _ _ _ _ _)); [lia | | | lia | lia | lia].
    - exact (proj1 (f1_lw_client (APIf rc) _ mem md a HAH) Hcl).
    - exact (proj1 (f1_lw_client (APIf rc) _ mem' md' a HAH') Hcl). }
  (* the shadow byte of an image byte is not the allocator's, before or after *)
  assert (KIMG : forall a, AC.a_in_img a ->
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Himg. pose proof (f1_img_range a Himg) as Hr.
    assert (Hsa : ASAN_K <= shadow_addr a < ASAN_K + 785408).
    { unfold shadow_addr. Z.div_mod_to_equations. lia. }
    refine (proj1 (KEEP _ _ _ _ _ _ _)); [lia | | | lia | lia | lia].
    - exact (proj1 (proj2 (f1_lw_client (APIf rc) _ mem md a HAH)) Himg).
    - exact (proj1 (proj2 (f1_lw_client (APIf rc) _ mem' md' a HAH')) Himg). }
  (* a RELRO byte: frame_facts says the runtime owns none *)
  assert (KREL : forall a, in_globals AF.frame_RELRO a -> mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Hin. pose proof (f1_relro_range a Hin) as Har.
    refine (proj1 (KEEP a _ _ _ _ _ _)); [lia | | | lia | lia | lia].
    + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
    + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin). }
  (* a byte of a live block and its shadow are kept *)
  assert (KBLK : forall a, AC.in_blocks (g_H g) a ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hb.
    pose proof Hb as (p0 & k0 & Hin0 & Hr0).
    destruct (f1_lw_blocks (APIf rc) _ mem md p0 k0 HAH Hin0) as (_ & Hp0 & Hpk & _ & Hbb).
    destruct (Hbb a Hr0) as (Hap & _ & Hnimg & _ & _).
    assert (Hb' : AC.in_blocks (g_H g ++ [(q, N)]) a).
    { exists p0, k0. split; [apply in_or_app; left; exact Hin0 | exact Hr0]. }
    destruct (f1_lw_not_owned (APIf rc) _ mem md a HAH (or_introl Hb)) as (N1 & N2).
    destruct (f1_lw_not_owned (APIf rc) _ mem' md' a HAH' (or_introl Hb')) as (N3 & N4).
    assert (Hne : ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4)).
    { intros He. apply Hnimg. exact (errno_in_img a He). }
    assert (Hno : a <> AC.as_oom AC.ASYMS).
    { intros ->. apply Hnimg. exact oom_in_img. }
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
    - apply (f1_keep_bytes mem mem'); [exact Hflag|]. cbn [length]. intros x Hx. apply KFS1. lia.
    - apply (f1_keep_bytes mem mem'); [exact Htail|]. rewrite length_le8. intros x Hx. apply KFS1. lia. }
  (* the input block (for n > 0 a block of g_H g) *)
  assert (Hlen_in : Z.of_nat (length (g_in g)) = g_n g) by reflexivity.
  assert (KIN : forall x, g_p g <= x < g_p g + g_n g ->
      mbyte rsegs mem' x = mbyte rsegs mem x /\
      mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
  { intros x Hx. assert (Hn0 : 0 < g_n g) by lia. destruct (Hinblk Hn0) as (Hin & _).
    apply KBLK. exists (g_p g), (g_n g). split; [exact Hin | lia]. }
  split.
  { apply (sl_mid_perm B APIf ra g fr [] (hb1 q N) (g_H g ++ [(q, N)]) regs mem md
      regs' mem' md' (fun a => q <= a < q + N) AC.AK_MALLOC HFRA Hcp).
    - exact (Permutation_cons_append (g_H g) (q, N)).
    - cbn. lia.
    - destruct Hsn as ((Hthm & Hlkm) & Hhdm & Hfd).
      split; [split|split].
      + eapply YI14.val_mem_frame; [|exact Hthm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx. try rewrite SEGS.
        apply KCL; [lia | eapply f1_client_in; [| exact Hx]; vm_compute; reflexivity].
      + eapply YI14.val_mem_frame; [|exact Hlkm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx. try rewrite SEGS.
        apply KCL; [lia | eapply f1_client_in; [| exact Hx]; vm_compute; reflexivity].
      + intros k Hk. pose proof (Hhdm k Hk) as Hk'. try rewrite SEGS in Hk'. try rewrite SEGS.
        rewrite KCL; [exact Hk' | rewrite Hhead; lia |
          apply (f1_client_in (@sk_ofl_head SH) (@sk_ofl_head SH + 8));
          [rewrite Hhead; vm_compute; reflexivity | lia]].
      + destruct Hmod as (lz & mt & vm' & Emd). rewrite Emd. exact Hfd.
    - intros a Hin. pose proof (Hgimg a Hin) as E. rewrite SEGS in E |- *. rewrite <- E. exact (KREL a Hin).
    - unfold q64 in *. apply (f1_keep_bytes mem mem'); [exact Hhdr1|].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - unfold q64 in *. apply (f1_keep_bytes mem mem'); [exact Hhdr2|].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - intros A0 HA0 HA0r.
      assert (EA0 : A0 = A).
      { unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (f1_keep_bytes mem mem'); [exact Hspill|].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - intros A0 HA0 HA0r v Hv.
      assert (EA0 : A0 = A).
      { unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (f1_keep_bytes mem mem'); [exact Hv|].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - intros A0 HA0 HA0r.
      assert (EA0 : A0 = A).
      { unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (f1_keep_bytes mem mem'); [exact Hfr56|].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - destruct Hsh as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
      apply (f1_keep_bytes mem mem'); [exact Hshb|]. rewrite Hshl. intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Ex : x = shadow_addr (fr + 8 * (x - Sfr fr))).
      { unfold shadow_addr at 1. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
      destruct (FRAME _ Hin) as (Hl & Hap).
      rewrite Ex. exact (KSH _ Hl Hap).
    - apply (f1_keep_bytes mem mem'); [exact Hsaved|]. intros x Hx.
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
    - intros a Hin. apply (f1_addr_keep mem mem' a 1 (HAG a Hin)). intros i Hi.
      replace (a + i) with a by lia. exact (KIMG a (f1_ag_img a Hin)).
    - intros a Ha Hnf. apply (f1_addr_keep mem mem' a 1 (HWA a Ha Hnf)). intros i Hi.
      assert (Hl : f1_loc mem md (a + i)) by (unfold f1_loc; left; lia).
      assert (Hap : app_mem (a + i)) by (unfold app_mem; right; lia).
      exact (KSH _ Hl Hap).
    - exact HREC.
    - apply (f1_keep_bytes mem mem' _ _ Hinb). intros x Hx. rewrite Hlen_in in Hx. exact (proj1 (KIN x Hx)).
    - intros Hn0. destruct (Hinblk Hn0) as (_ & Had).
      apply (f1_addr_keep mem mem' _ _ Had). intros i Hi. exact (proj2 (KIN (g_p g + i) ltac:(lia))).
    - exact F2.
    - exact F3.
    - exact F4.
    - exact F8.
    - exact F9.
    - exact F19.
    - exact F26. }
  split.
  { intros a Ha. destruct Ha as [Hf|[Hb|[Hs|Hr]]].
    - exact (KFR a Hf).
    - exact (proj1 (KBLK a Hb)).
    - rewrite Haspz in Hs. exact (proj1 (KST a ltac:(lia) ltac:(lia))).
    - exact (KREL a Hr). }
  intros a Ha. destruct Ha as [Hf|[Hb|[Hs|Hi]]].
  - destruct (FRAME a Hf) as (Hl & Hap). exact (KSH a Hl Hap).
  - exact (proj2 (KBLK a Hb)).
  - apply KSH; [left; exact Hs | unfold app_mem; right; lia].
  - exact (KIMG a Hi).
Qed.

(* ---- the allocation call 0x81f4c `jal 0x534b8`: F1's one use of the allocator contract ----
   AC.aa_malloc (Contract.v amalloc_at) at the v1.9.0 allocator entry 0x534b8, its per-class premises from ENT's
   14th conjunct (Tac_cls.sl_malloc_cls, Bc := Bc_of BE), its room premise from FRA's live-bytes bound
   (f1_place_room).  A later generation's contract change breaks this lemma only. *)
Lemma f1_malloc_sr : forall g regs mem md n,
  ENT APIf g [] mem md ->
  AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API)
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API) AC.AK_MALLOC (g_H g) regs mem md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n <= 65535 ->
  (forall p k, In (p, k) (g_H g) -> 0 <= k) -> AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30 ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x534b8) mem (seg_rom rsegs)) md)
    (AC.amalloc_ret AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API)
       (AC.aa_owned AC.ASYMS AsanRTInv.RT API) (AC.aa_stklo AC.ASYMS AsanRTInv.RT API)
       (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API) AC.AK_MALLOC (g_H g) regs mem md n).
Proof.
  intros g regs mem md n HENT Hpre E10 Hn Hnn Hlive.
  pose proof (AC.aa_malloc AC.ASYMS AsanRTInv.RT API) as HMAL.
  unfold AC.amalloc_contract, AC.amalloc_at in HMAL.
  destruct (Tac_cls.sl_malloc_cls APIf g [] mem md n HENT) as (BE & _ & _ & Hfits & Hroom & _).
  (* the allocator entry of the v1.9.0 image; Contract.v's as_malloc names it *)
  assert (EM : AC.as_malloc AC.ASYMS = 0x534b8) by reflexivity.
  rewrite <- EM.
  apply (HMAL (g_H g) regs mem md n (Tac_cls.Bc_of BE) Hpre E10).
  - unfold AC.ANMAX. lia.
  - unfold AC.ALIVE_MAX, AC.a_size. lia.
  - apply f1_place_room; [exact Hnn | exact Hlive | unfold AC.a_size; lia].
  - exact Hfits.
  - exact Hroom.
Qed.

(* ---- the segment ---- *)

(* seg_F1 (S_F1): from the frame-loop head 0x81ec4 (turn j) through the allocation call to its return point
   0x81f50.  The run f1_evt, 0x81ec4 -> 0x534b8 (sl_run_lib), reads the code, the input bytes p + c and p + c + 1
   and their shadow bytes, and writes only [A + 232, A + 248); FRA and ENT move across that store by f1_fra_spill.
   The allocation is AC.aa_malloc on fra_call_pre with Bc := Bc_of BE for ENT's per-class witness BE
   (Tac_cls.sl_malloc_cls); f1_malloc_keep and f1_ent_call move FRA and ENT across it, and the exit body is read off
   the kept bytes: LK ([A + 240] = j was just stored, our[] and FLI are frame bytes / save-area spills / frame
   shadow), FC ([A + 232] = left - h was just stored, s5 = p + c + h = p + body, s4 = len), f1_IN (a live block of the
   entry heap and its shadow), FSj (the frame local `first` and its shadow), REC0 (frame bytes) and s6 = 1 (a
   callee-saved register no instruction of the run writes).  The exit 0x82eac is not reached: LI's 1 <= left_j
   makes `bnez s9` at 0x81ec4 taken. *)
Lemma seg_F1 : forall j : nat,
  Hat B APIf ra (Inv_B81f50_at B APIf ra) j -> Hcut B APIf ra (Inv_B82eac B APIf ra) ->
  Hat B APIf ra (Inv_B81ec4_at B APIf ra) j.
Proof.
  intros j Hexit _ g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HLI & HIN & _ & Hs6).
  subst c.
  destruct HLI as (Hj & H13 & HOUR & (Hc & H23 & H25) & Hleft & HIFS & HFLI).
  destruct (f1_rec0_of_ifs g fr j regs mem HIFS) as (HREC & HFSj).
  pose proof HIN as HIN0. destruct HIN0 as (HinH0 & HaddrIN & HbytesIN).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (Hstkhi : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md HAH).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (EL : t_left (g_in g) j = g_n g - t_c (g_in g) j) by reflexivity.
  assert (Hlen_in : Z.of_nat (length (g_in g)) = g_n g) by reflexivity.
  assert (Hn0 : 0 < g_n g) by lia.
  pose proof (HinH0 Hn0) as HinH.
  (* the input block lies below stklo *)
  destruct (f1_lw_blocks (APIf rc) _ mem md (g_p g) (g_n g) HAH HinH) as (_ & Hp4096 & Hpn & _ & _).
  (* the two length bytes, their instrumented checks, and the spill slots *)
  pose proof (f1_byte1 mem (g_p g) (t_c (g_in g) j) (g_in g) HbytesIN ltac:(lia) ltac:(rewrite Hlen_in; lia))
    as HB0.
  destruct (f1_shadow1 mem (g_p g + t_c (g_in g) j)
      (addressable_sub mem (g_p g) (g_n g) (t_c (g_in g) j) 1 HaddrIN ltac:(lia) ltac:(lia) ltac:(lia)))
    as (k0 & HK0 & Hk0).
  assert (H2 : exists k1 : byte, 2 <= t_left (g_in g) j ->
     ov_read_bytes rsegs mem (wa (Z.shiftr (g_p g + t_c (g_in g) j + 1) 3 + ASAN_K)) 1 = Some [k1] /\
     shadow_ok (g_p g + t_c (g_in g) j + 1) (bv_signed k1) /\
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
  assert (HWR : wr_at rsegs mem (A + 232) 16).
  { pose proof Hwin as (_ & _ & Hw).
    split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hw (A + 232 + i) ltac:(lia))). }
  pose proof (bv_unsigned_in_range 8 (nthb (g_in g) (Z.to_nat (t_c (g_in g) j)))) as Hb0r.
  pose proof (bv_unsigned_in_range 8 (nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1)))) as Hb1r.
  change (bv_modulus 8) with 256 in Hb0r, Hb1r.
  assert (Elen : t_len (g_in g) j =
    Z.min (bv_unsigned (nthb (g_in g) (Z.to_nat (t_c (g_in g) j))) +
           (if 2 <=? (g_n g - t_c (g_in g) j)
            then 256 * bv_unsigned (nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))) else 0))
          ((g_n g - t_c (g_in g) j) - t_h (g_in g) j)) by reflexivity.
  assert (Eh : t_h (g_in g) j = Z.min 2 (g_n g - t_c (g_in g) j)) by reflexivity.
  assert (Hlen : 0 <= t_len (g_in g) j <= 65535).
  { rewrite Elen, Eh. destruct (2 <=? g_n g - t_c (g_in g) j); lia. }
  assert (Hh12 : 1 <= t_h (g_in g) j <= 2) by (rewrite Eh; lia).
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x81ec4) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x534b8 /\ getr R 1 = Z_to_bv 64 0x81f50 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 22 = getr regs 22 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       getr R 10 = Z_to_bv 64 (t_len (g_in g) j) /\ getr R 20 = Z_to_bv 64 (t_len (g_in g) j) /\
       getr R 21 = Z_to_bv 64 (g_p g + t_c (g_in g) j + t_h (g_in g) j) /\
       Frame.munch [(A + 232, A + 248)] mem mem' /\ Frame.wmono rsegs mem mem' /\
       bytes_at rsegs mem' (A + 232) (le8 (Z_to_bv 64 (g_n g - t_c (g_in g) j - t_h (g_in g) j))) /\
       bytes_at rsegs mem' (A + 240) (le8 (Z_to_bv 64 (Z.of_nat j))))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { rewrite f1_mkR_of.
    pose proof Hr9 as R9. pose proof Hs6 as R22. pose proof H13 as R13. pose proof H23 as R23.
    pose proof H25 as R25. pose proof Hr26 as R26.
    unfold rg in R9, R22, R13, R23, R25, R26.
    rewrite R9, R22, R13, R23, R25, R26.
    eapply LE.evt_mono.
    {
      apply (f1_evt (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 14)
               (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
               (getr regs 21) (getr regs 24) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr mem
               A (g_p g + t_c (g_in g) j) (g_n g - t_c (g_in g) j) (Z.of_nat j) (t_h (g_in g) j)
               (t_len (g_in g) j)
               (nthb (g_in g) (Z.to_nat (t_c (g_in g) j))) (nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1)))
               k0 k1).
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact HB0.
      - exact HK0.
      - exact Hk0.
      - intros H2l. exact (proj2 (proj2 (H2 ltac:(lia)))).
      - intros H2l. exact (proj1 (H2 ltac:(lia))).
      - intros H2l. exact (proj1 (proj2 (H2 ltac:(lia)))).
      - exact HWR.
      - exact Eh.
      - exact Elen. }
    intros ms' (a1' & a2' & m' & -> & MU & WM & HB232 & HB240).
    eexists _, _, m'. split; [reflexivity|].
    repeat (split; [reflexivity|]).
    split; [exact MU|]. split; [exact WM|]. split; [exact HB232 | exact HB240]. }
  intros R pc' mem1 regs'' md'
    (Hpc & K1 & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K26 & K27 & K10 & K20 & K21 & MU1 & WM1 & HB232 & HB240)
    Hreg Hmat.
  subst pc'.
  assert (E1 : getr regs'' 1 = Z_to_bv 64 0x81f50) by (rewrite Hreg; exact K1).
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
  assert (E10 : getr regs'' 10 = Z_to_bv 64 (t_len (g_in g) j)) by (rewrite Hreg; exact K10).
  assert (E20 : getr regs'' 20 = Z_to_bv 64 (t_len (g_in g) j)) by (rewrite Hreg; exact K20).
  assert (E21 : getr regs'' 21 = Z_to_bv 64 (g_p g + t_c (g_in g) j + t_h (g_in g) j))
    by (rewrite Hreg; exact K21).
  (* ---- the two spill stores [A + 232, A + 248) ---- *)
  assert (KM1 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 232 <= x < A + 248) -> mbyte rsegs mem1 x = mbyte rsegs mem x).
  { intros x Hx Hn. unfold mbyte. rewrite (MU1 (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HWIN1 : stk rsegs mem1 (g_S g - AF.SLOT_STACK) (g_S g)).
  { apply (f1_stk_tr _ mem mem1 _ _ Hwin MU1 WM1). intros x Hx.
    destruct (Z_lt_le_dec x (A + 232)) as [Hl|Hl]; [left; cbn [Frame.outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec x (A + 240)) as [Hh|Hh].
    - right. apply (f1_ba_rd mem1 (A + 232) _ x HB232). rewrite length_le8. cbn. lia.
    - destruct (Z_lt_le_dec x (A + 248)) as [Hh2|Hh2].
      + right. apply (f1_ba_rd mem1 (A + 240) _ x HB240). rewrite length_le8. cbn. lia.
      + left. cbn [Frame.outside]. split; [lia | exact I]. }
  destruct (f1_fra_spill g fr [] regs regs'' mem mem1 md md' A 232 248 HFRA HENT Hr9 HA64 ltac:(lia) ltac:(lia)
              ltac:(lia) MU1 WM1 HWIN1 Hmat E2 E3 E4 E8 E9 E19 E26) as (HFRA2 & HENT2).
  assert (Hasp'' : AC.aspZ regs'' = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
  (* ---- the allocation call ---- *)
  assert (Hret : YK0s.ret_ok (getr regs'' 1)) by (unfold YK0s.ret_ok; rewrite E1; vm_compute; reflexivity).
  assert (HKm : 0 <= AC.AK_MALLOC <= FN_STACK) by (unfold AC.AK_MALLOC; lia).
  pose proof (fra_call_pre B APIf ra g fr [] regs'' mem1 md' AC.AK_MALLOC HFRA2 HENT2 Hret HKm) as Hpre.
  assert (Hnn : forall p k, In (p, k) (g_H g) -> 0 <= k).
  { intros p0 k0' Hin. pose proof (AC.a_laws_block_size _ _ _ _ _ ALAWS _ mem md p0 k0' HAH Hin). lia. }
  eapply SR_bind.
  { apply (f1_malloc_sr g regs'' mem1 md' (t_len (g_in g) j) HENT2 Hpre E10); [lia | exact Hnn | exact Hlive]. }
  intros c' (regs' & mem2 & md2 & q & Ec' & Hq & Hnb & Hcp & Herrk & Hownq).
  subst c'. rewrite E1.
  destruct (f1_malloc_keep g fr regs'' mem1 md' (AC.a_size (t_len (g_in g) j)) regs' mem2 md2 q
              HFRA2 Hcp Hownq) as (HFRAx & KB & KS).
  (* the callee-saved registers the exit reads *)
  pose proof Hcp as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof Hcp as Hkept; apply AC.a_call_post_regs in Hkept.
  assert (F9 : getr regs' 9 = getr regs'' 9) by exact (Hkept 9 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F20 : getr regs' 20 = getr regs'' 20) by exact (Hkept 20 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F22 : getr regs' 22 = getr regs'' 22) by exact (Hkept 22 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F21 : getr regs' 21 = getr regs'' 21) by exact (Hkept 21 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F27 : getr regs' 27 = getr regs'' 27) by exact (Hkept 27 ltac:(unfold AC.a_callee_saved; lia)).
  (* the new block's bytes are app memory below stklo (so below S), off the image and off every entry block *)
  pose proof Hcp as Hsk'; apply AC.a_call_post_stklo in Hsk'.
  assert (HTOUCH : forall a, q <= a < q + AC.a_size (t_len (g_in g) j) ->
            app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a).
  { intros a Ha.
    assert (Hinq : In (q, AC.a_size (t_len (g_in g) j)) (g_H g ++ [(q, AC.a_size (t_len (g_in g) j))]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (f1_lw_blocks (APIf rc) _ mem2 md2 q (AC.a_size (t_len (g_in g) j)) HAH' Hinq)
      as (_ & _ & Hend & _ & Hall).
    destruct (Hall a Ha) as (Happ & _ & Hnimg & _ & _).
    pose proof Hnb as (_ & _ & _ & _ & _ & Hnew & _).
    destruct (Hnew a Ha) as (Hnib & _).
    assert (Hstk2 : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem1 md' <= g_S g - AF.SLOT_STACK).
    { destruct HFRA2 as (A2 & sp2 & s52 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs2 & _). exact Hs2. }
    split; [exact Happ|]. split; [rewrite Hsk' in Hend; lia|].
    split; [exact Hnimg | exact Hnib]. }
  assert (HENTx : ENT APIf g (hb1 q (AC.a_size (t_len (g_in g) j))) mem2 md2).
  { exact (f1_ent_call g fr [] (hb1 q (AC.a_size (t_len (g_in g) j)))
             (g_H g ++ [(q, AC.a_size (t_len (g_in g) j))]) regs'' mem1 md' regs' mem2 md2
             (fun a => q <= a < q + AC.a_size (t_len (g_in g) j)) AC.AK_MALLOC HENT2 HFRA2 Hcp
             (Permutation_cons_append (g_H g) (q, AC.a_size (t_len (g_in g) j))) HKm HTOUCH Herrk). }
  (* the two-step byte keep: the allocation keeps the stack at or above sp and the frame, the store everything
     off [A + 232, A + 248) *)
  assert (Hfrb : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (KK : forall x, (fr <= x < fr + FRAME_BYTES \/ sp <= x < APPMEM_END) -> ~ (A + 232 <= x < A + 248) ->
             mbyte rsegs mem2 x = mbyte rsegs mem x).
  { intros x Hx Hn.
    rewrite (KB x ltac:(destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; left; rewrite Hasp''; exact Hx])).
    exact (KM1 x ltac:(destruct Hx as [Hx|Hx]; lia) Hn). }
  assert (KSF : forall x, fr <= x < fr + FRAME_BYTES ->
             mbyte rsegs mem2 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
  { intros x Hx. rewrite (KS x ltac:(left; exact Hx)).
    assert (x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= x / 8) by (apply Z.div_pos; lia).
    apply KM1; unfold shadow_addr; rewrite HK; lia. }
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite F9, E9; exact Hr9).
  assert (E9' : getr regs' 9 = getr regs 9) by (rewrite F9; exact E9).
  assert (E27' : getr regs' 27 = getr regs 27) by (rewrite F27; exact E27).
  rewrite <- SEGS. apply Hexit. cbv beta.
  exists q, regs', mem2, md2, fr.
  split; [reflexivity|].
  split; [exact HFRAx|].
  split; [exact HENTx|].
  split; [exact Hgn|].
  split; [exact Hj|].
  split; [unfold a0v, rg; exact Hq|].
  split.
  { destruct Hnb as (Hq0 & _ & _ & _ & _ & _ & Haddr & _). split; [exact Hq0 | exact Haddr]. }
  split.
  { (* LK *)
    split; [exact Hj|].
    split.
    { exists A. split; [exact H9'|].
      unfold q64. apply (f1_keep_bytes mem1 mem2); [exact HB240|].
      rewrite length_le8. intros x Hx. apply (KB x). right; right; left. rewrite Hasp''. lia. }
    split; [apply (f1_our_move g fr mem mem2 HOUR); intros x Hx; apply KK; lia|].
    apply (f1_fli_move g fr regs regs' mem mem2 A HFLI Hr9 ltac:(lia) ltac:(lia) E9' E27').
    - intros x Hx. apply KK; lia.
    - intros x Hx. apply KSF. unfold fragb in Hx. lia.
    - intros x Hx. pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRimg & _).
      pose proof (f1_kn_relro x Hx) as Hrel. unfold KNC.KIND_NAME in Hx. split.
      + rewrite (KB x (or_intror (or_intror (or_intror Hrel)))). apply KM1; lia.
      + rewrite (KS x (or_intror (or_intror (or_intror (HRimg x Hrel))))).
        assert (Hsx : ASAN_K <= shadow_addr x < ASAN_K + 785408).
        { unfold shadow_addr. Z.div_mod_to_equations. lia. }
        apply KM1; rewrite HK in Hsx; lia.
    - exact (fra_stk B APIf ra g fr _ regs' mem2 md2 HFRAx). }
  split.
  { (* FC *)
    split.
    - exists A. split; [exact H9'|].
      unfold q64. apply (f1_keep_bytes mem1 mem2); [exact HB232|].
      rewrite length_le8. intros x Hx. apply (KB x). right; right; left. rewrite Hasp''. lia.
    - split.
      + unfold rg. rewrite F21, E21. f_equal. unfold t_body, f_body, t_h, t_c. lia.
      + unfold rg. rewrite F20, E20. reflexivity. }
  split.
  { (* the input block *)
    apply (f1_in_move g mem mem2 HIN). intros x Hx.
    assert (Hb : AC.in_blocks (g_H g) x) by (exists (g_p g), (g_n g); split; [exact HinH | lia]).
    split.
    - rewrite (KB x ltac:(right; left; exact Hb)). apply KM1; lia.
    - rewrite (KS x ltac:(right; left; exact Hb)).
      assert (0 <= x / 8 < 17592186044416) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      apply KM1; unfold shadow_addr; rewrite HK; lia. }
  split.
  { (* FSj: the frame local `first` and its shadow are frame bytes / frame shadow *)
    apply (f1_fsj_move g fr j regs regs' mem mem2 HFSj); intros x Hx; [apply KK; lia | apply KSF; lia]. }
  split.
  { (* REC0: the two frame records are frame bytes *)
    apply (f1_rec0_move g fr j mem mem2 HREC). intros x Hx. apply KK; lia. }
  (* s6 = 1 *)
  unfold rg in *. rewrite F22, E22. exact Hs6.
Qed.

End S.
