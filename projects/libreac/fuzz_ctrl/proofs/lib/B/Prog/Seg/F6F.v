(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1665 of its 1776 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F5.v, with its addresses and numbers changed; 477 of its 613 lines of code are new or changed and 1640 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F6.v, with its module paths and module names changed; 118 of its 390 lines of code are new or changed and 341 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F6.v f6_loop (:210), f6_run_evt (:301) at a working branch
     3803efccea0 (blob df03c7420aaf751c6e429c1eaa11283e23ef41a3);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f6_loop_of_F, f6_run_evt_of_F (evtF_evt + rng_all) re-derive the source statements. *)
(* rule 24: no function proved. *)
(* Neither run calls: f6_run_evt ends at 0x8214c, the entry of the parse call block (F5.c_evt / c_pre_F).
   Regions: the record bytes [phi + 16, phi + 50) (byte 16, byte 17 and the 32 summed bytes), the shadow byte of
   each of those addresses (the instrumented checks at 0x820a8, 0x820f0 and 0x8211c; their slow paths read no
   further memory), and the four save-area words [A+184], [A+248], [A+272] (read) and [A+312]. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib RcLib RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F5 F6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF ExecF_all StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* F6.f6_nt / F6.f6_tk over the evtF goal (four arguments); the condition tactic F6.f6_cond is unchanged. *)
Ltac f6_ntF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; f6_cond]
  end.

Ltac f6_tkF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; f6_cond]
  end.

(* ================= the block-sum loop 0x82098 -> 0x820d8 ================= *)
Lemma f6_loop_F : forall (RNG : footprint)
  (ra0 sp gp tp t1 t2 s0 s1v s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  rng RNG (phi + 18) 32 ->
  (forall x, phi + 18 <= x < phi + 50 -> rng RNG (Z.shiftr x 3 + ASAN_K) 1) ->
  (forall y0 y2 y4 y5 y6 : word,
     evtF rsegs RNG Q (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
         y0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x820d8) fc None m (seg_rom rsegs))) ->
  forall (n i : nat) (y0 y1 y2 y4 y5 y6 : word), (i + n = 32)%nat -> (0 < n)%nat ->
    y0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> y1 = Z_to_bv 64 (psum (skipn 18 bs) i) ->
    y2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> y4 = Z_to_bv 64 (32 - Z.of_nat i) ->
  evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
         y0 y1 y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x82098) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t1 t2 s0 s1v s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 Fr fc m phi bs Q
    Hphi0 Hphi50 Hlen HB HA Rbody Rsh Hjoin n.
  induction n as [|n IH]; intros i y0 y1 y2 y4 y5 y6 Hin Hn E0 E1 E2 E4; [lia|].
  subst y0 y1 y2 y4.
  assert (Hiz : 0 <= Z.of_nat i < 32) by lia.
  assert (Haddr1 : addressable m (phi + 18 + Z.of_nat i) 1).
  { replace (phi + 18 + Z.of_nat i) with (phi + (18 + Z.of_nat i)) by lia.
    apply (addressable_sub m phi 50 (18 + Z.of_nat i) 1 HA); lia. }
  pose proof (Rsh (phi + 18 + Z.of_nat i) ltac:(lia)) as Rshi.
  destruct (f6_shadow1 m (phi + 18 + Z.of_nat i) Haddr1) as (sb & RDsb & OKsb & ISsb).
  pose proof (rd_byte rsegs m phi bs (18 + i)%nat HB ltac:(lia)) as RDb.
  replace (Z.of_nat (18 + i)) with (18 + Z.of_nat i) in RDb by lia.
  replace (phi + (18 + Z.of_nat i)) with (phi + 18 + Z.of_nat i) in RDb by lia.
  pose proof (psum_range (skipn 18 bs) i) as PR.
  (* the join at 0x820b0 (the shadow check passed), with the slow path's a5 / a6 generalized *)
  assert (G40 : forall z5 z6 : word,
    evtF rsegs RNG Q (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
       (Z_to_bv 64 (phi + 18 + Z.of_nat i)) (Z_to_bv 64 (psum (skipn 18 bs) i))
       (Z_to_bv 64 (phi + 18 + Z.of_nat i)) (Z_to_bv 64 (- (phi + 18)))
       (Z_to_bv 64 (32 - Z.of_nat i)) z5 z6 (Z_to_bv 64 32)
       s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820b0) fc None m (seg_rom rsegs))).
  { intros z5 z6.
    step. (* 820b0 lbu a5,0(a2) *)
    step. (* 820b4 addi a4,a4,-1 *)
    step. (* 820b8 addi a0,a0,1 *)
    step. (* 820bc add a1,a1,a5 *)
    rewrite <- (f6_nth_skipn byte (Z_to_bv 8 0) 18 bs i).
    rewrite psum_S_zxb.
    step. (* 820c0 addi a2,a2,1 *)
    step. (* 820c4 bnez a4,82098 *)
    destruct n as [|n'].
    - (* the last turn: a4 = 0, not taken; 0x820c8 j 820d8 *)
      replace i with 31%nat in * by lia.
      f6_ntF.
      step. (* 820c8 j 820d8 *)
      apply Hjoin.
    - (* more turns: back to 0x82098 at i + 1 *)
      f6_tkF.
      apply (IH (S i)); try lia; try reflexivity; try (f_equal; lia). }
  (* the ubsan end test and the shadow check 0x82098-0x820ac *)
  step. (* 82098 add a5,a3,a4 *)
  step. (* 8209c beq a5,a7,82fa0 *)
  f6_ntF.
  step. (* 820a0 srli a5,a0,3 *)
  step. (* 820a4 add a5,a5,s10 *)
  rewrite (MState.unsigned_lit (phi + 18 + Z.of_nat i)) by lia.
  step. (* 820a8 lb a5,0(a5) *)
  step. (* 820ac bnez a5,820cc *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb)) by (pose proof (rc_byte_signed sb); lia).
  destruct (Z.eqb_spec (bv_signed sb) 0) as [Z0|Z0].
  - (* shadow 0: not taken, fall to 0x820b0 *)
    cbn [negb]. cbv iota. apply (G40 (Z_to_bv 64 (bv_signed sb)) y6).
  - (* shadow <> 0: the slow path 0x820cc-0x820d0, whose report 0x83048 is not reached *)
    cbn [negb]. cbv iota.
    step. (* 820cc andi a6,a0,7 *)
    rewrite (MState.unsigned_lit (phi + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
    step. (* 820d0 blt a6,a5,820b0 *)
    rewrite (rc_lts_signed ((phi + 18 + Z.of_nat i) mod 8) (bv_signed sb))
      by (pose proof (rc_byte_signed sb); pose proof (Z.mod_pos_bound (phi + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
    replace ((phi + 18 + Z.of_nat i) mod 8 <? bv_signed sb) with true
      by (symmetry; apply Z.ltb_lt; destruct OKsb as [H|H]; lia).
    cbv iota.
    apply (G40 (Z_to_bv 64 (bv_signed sb)) (Z_to_bv 64 ((phi + 18 + Z.of_nat i) mod 8))).
Qed.

(* ================= the run 0x82098 -> 0x8214c over explicit registers ================= *)
Lemma f6_run_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t1 t2 s0 a5i a6i s3 s4v s5i s6 s7 s9i s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi A v8 e272 : Z) (bs : list byte),
    0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
    bytes_at rsegs m phi bs -> addressable m phi 50 ->
    0 <= A -> A + 448 <= 2 ^ 64 -> stk rsegs m (A + 184) (A + 320) ->
    0 <= v8 < 2 ^ 64 -> q64 m (A + 272) e272 -> e272 = (if v8 =? 0 then 0 else 1) ->
    phi + 50 <= A -> (forall x, phi <= x < phi + 50 -> shadow_addr x < A) ->
    rng RNG (phi + 16) 34 ->
    (forall x, phi + 16 <= x < phi + 50 -> rng RNG (Z.shiftr x 3 + ASAN_K) 1) ->
    rng RNG (A + 184) 8 -> rng RNG (A + 248) 8 -> rng RNG (A + 272) 8 -> rng RNG (A + 312) 8 ->
    evtF rsegs RNG
      (fun ms' => exists b0 b1 b2 b3 b4 b5 b6 : word,
         ms' = MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
                       b0 b1 b2 b3 b4 b5 b6 (Z_to_bv 64 32)
                       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8)
                       (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 1 else 0))
                       (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x8214c) fc None
                  (write_to_mem
                     (write_to_mem (write_to_mem m (wa (A + 312)) (le8 (Z_to_bv 64 (phi + 18))))
                        (wa (A + 184)) (le8 (Z_to_bv 64 (f6_tf bs))))
                     (wa (A + 248))
                     (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1))))
                  (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
               (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 18))
               (Z_to_bv 64 (- (phi + 18))) (Z_to_bv 64 32) a5i a6i (Z_to_bv 64 32)
               (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82098) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t1 t2 s0 a5i a6i s3 s4v s5i s6 s7 s9i s11 t3 t4 t5 t6 Fr fc m phi A v8 e272 bs
    Hphi0 Hphi50 Hlen HB HA HA0 HA448 Hstk Hv8 Hq272 He272 Hsep Hshadow
    Rrec Rsh R184 R248 R272 R312.
  match goal with |- evtF _ _ ?Q _ => set (QE := Q) end.
  set (m1 := write_to_mem m (wa (A + 312)) (le8 (Z_to_bv 64 (phi + 18)))).
  set (m2 := write_to_mem m1 (wa (A + 184)) (le8 (Z_to_bv 64 (f6_tf bs)))).
  set (m3 := write_to_mem m2 (wa (A + 248))
               (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1)))).
  (* the three save-area words are byte-backed and writable *)
  assert (HSO : forall m' off, wmono rsegs m m' -> 184 <= off -> off + 8 <= 320 ->
            store_ok rsegs m' (wa (A + off)) 8 = true).
  { intros m' off HW Ho1 Ho2. apply (c_store_ok m m' (A + off) 8); [| exact HW | lia | lia].
    intros k Hk. destruct Hstk as (_ & _ & Hs). change (Z.of_nat 8) with 8 in Hk.
    exact (proj1 (Hs (A + off + k) ltac:(lia))). }
  (* the record and the [A+272] word across the first two stores *)
  assert (MU1 : munch [(A + 312, A + 320)] m m1).
  { subst m1. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia
      | rewrite length_le8; cbn [inside]; left; lia]. }
  assert (WM1 : wmono rsegs m m1) by (subst m1; apply wmono_write; apply wmono_refl).
  assert (WM2 : wmono rsegs m m2) by (subst m2 m1; apply wmono_write; apply wmono_write; apply wmono_refl).
  assert (HB1 : bytes_at rsegs m1 phi bs).
  { subst m1. apply c_ba_write; [exact HB | lia | rewrite length_le8; lia |].
    rewrite length_le8, Hlen. intros x Hx. left. cbn [Z.of_nat] in Hx. lia. }
  assert (HA1 : addressable m1 phi 50).
  { apply (c_addr_keep [(A + 312, A + 320)] m m1 phi 50 HA MU1).
    intros k Hk. pose proof (Hshadow (phi + k) ltac:(lia)) as Hsk. cbn [outside]. repeat split. lia. }
  assert (HQ272 : q64 m2 (A + 272) e272).
  { subst m2 m1. unfold q64. apply c_ba_write; [| lia | rewrite length_le8; lia |].
    - apply c_ba_write; [exact Hq272 | lia | rewrite length_le8; lia |].
      rewrite !length_le8. intros x Hx. left. cbn [Z.of_nat] in Hx. lia.
    - rewrite !length_le8. intros x Hx. right. cbn [Z.of_nat] in Hx. lia. }
  pose proof (bytes_at_ov_read rsegs m2 (A + 272) (le8 (Z_to_bv 64 e272)) 0 8 HQ272
                ltac:(rewrite length_le8; lia)) as RD272.
  cbn [Z.of_nat] in RD272. rewrite Z.add_0_r, skipn_O, firstn_all2 in RD272 by (rewrite length_le8; lia).
  pose proof (rd_byte rsegs m1 phi bs 16 HB1 ltac:(lia)) as RD16. change (Z.of_nat 16) with 16 in RD16.
  pose proof (rd_byte rsegs m1 phi bs 17 HB1 ltac:(lia)) as RD17. change (Z.of_nat 17) with 17 in RD17.
  assert (Ha16 : addressable m1 (phi + 16) 1) by (apply (addressable_sub m1 phi 50 16 1 HA1); lia).
  destruct (f6_shadow1 m1 (phi + 16) Ha16) as (sb16 & RDs16 & OK16 & IS16).
  assert (Ha17 : addressable m1 (phi + 17) 1) by (apply (addressable_sub m1 phi 50 17 1 HA1); lia).
  destruct (f6_shadow1 m1 (phi + 17) Ha17) as (sb17 & RDs17 & OK17 & IS17).
  pose proof (Rsh (phi + 16) ltac:(lia)) as Rsh16.
  pose proof (Rsh (phi + 17) ltac:(lia)) as Rsh17.
  assert (HS184 : store_ok rsegs m1 (wa (A + 184)) 8 = true) by (apply (HSO m1 184 WM1); lia).
  assert (HS248 : store_ok rsegs m2 (wa (A + 248)) 8 = true) by (apply (HSO m2 248 WM2); lia).
  pose proof (psum_range (skipn 18 bs) 32) as PRs. change (Z.of_nat 32) with 32 in PRs.
  pose proof (Z.mod_pos_bound (psum (skipn 18 bs) 32) 256 ltac:(lia)) as PRm.
  (* the join at 0x82130: both arms of the byte-16 / byte-17 test, [A+184] = the tfill flag *)
  assert (GA0 : forall d c0 c2 c3 c4 c5 c6 : word, d = Z_to_bv 64 (f6_tf bs) ->
    evtF rsegs RNG QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       c0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) c2 c3 c4 c5 c6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x82130) fc None (write_to_mem m1 (wa (A + 184)) (le8 d)) (seg_rom rsegs))).
  { intros d c0 c2 c3 c4 c5 c6 Ed. subst d. change (write_to_mem m1 _ _) with m2.
    step. (* 82130 snez a0,s8 *)
    rewrite f6_snez, (MState.unsigned_lit v8) by lia.
    step. (* 82134 ld a2,272(s1) *)
    step. (* 82138 bne a0,a2,82fa4 : not taken *)
    rewrite He272, bv_eqb_refl. cbn [negb]. cbv iota.
    step. (* 8213c andi a0,a1,0xff *)
    rewrite (MState.unsigned_lit (psum (skipn 18 bs) 32)) by lia. rewrite f6_land255.
    step. (* 82140 seqz s9,a0 *)
    rewrite f6_seqz, (MState.unsigned_lit (psum (skipn 18 bs) 32 mod 256)) by lia.
    step. (* 82144 snez a0,a0 *)
    rewrite f6_snez, (MState.unsigned_lit (psum (skipn 18 bs) 32 mod 256)) by lia.
    step. (* 82148 sd a0,248(s1) *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => change mm with m3 end.
    unfold QE. apply evtF_done. do 7 eexists. reflexivity. }
  (* the join at 0x820f8 (the byte-16 shadow check passed) *)
  assert (G88 : forall c2 c3 c4 c5 c6 : word,
    evtF rsegs RNG QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       (Z_to_bv 64 (phi + 16)) (Z_to_bv 64 (psum (skipn 18 bs) 32)) c2 c3 c4 c5 c6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820f8) fc None m1 (seg_rom rsegs))).
  { intros c2 c3 c4 c5 c6.
    step. (* 820f8 lbu a0,0(a0) : byte 16 *)
    step. (* 820fc beqz a0,82108 *)
    unfold zxb. rewrite (rc_eqb0_signed (bv_unsigned (nth 16 bs (Z_to_bv 8 0))))
      by (pose proof (f6_byte_range (nth 16 bs (Z_to_bv 8 0))); lia).
    destruct (Z.eqb_spec (bv_unsigned (nth 16 bs (Z_to_bv 8 0))) 0) as [B16|B16].
    - (* byte 16 = 0: the byte-17 check, [A+184] = seqz byte17 *)
      cbv iota.
      assert (GB4 : forall e3 e4 e5 e6 : word,
        evtF rsegs RNG QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
           (Z_to_bv 64 (phi + 17)) (Z_to_bv 64 (psum (skipn 18 bs) 32)) (sxb sb17) e3 e4 e5 e6 (Z_to_bv 64 32)
           (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82124) fc None m1 (seg_rom rsegs))).
      { intros e3 e4 e5 e6.
        step. (* 82124 lbu a0,0(a0) : byte 17 *)
        step. (* 82128 seqz a0,a0 *)
        rewrite f6_seqz.
        step. (* 8212c sd a0,184(s1) *)
        apply GA0.
        unfold f6_tf. rewrite B16, Z.eqb_refl. rewrite ?f6_zxb_u.
        rewrite ?(MState.unsigned_lit (bv_unsigned (nth 17 bs (Z_to_bv 8 0))))
          by (pose proof (f6_byte_range (nth 17 bs (Z_to_bv 8 0))); lia).
        reflexivity. }
      step. (* 82108 li a0,-18 *)
      step. (* 8210c bltu a0,s2,82fa0 : not taken *)
      f6_ntF.
      step. (* 82110 addi a0,s2,17 *)
      step. (* 82114 srli a2,a0,3 *)
      step. (* 82118 add a2,a2,s10 *)
      rewrite (MState.unsigned_lit (phi + 17)) by lia.
      step. (* 8211c lb a2,0(a2) *)
      step. (* 82120 bnez a2,82e4c *)
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb17)) by (pose proof (rc_byte_signed sb17); lia).
      destruct (Z.eqb_spec (bv_signed sb17) 0) as [Z17|Z17].
      + cbn [negb]. cbv iota. apply (GB4 c3 c4 c5 c6).
      + cbn [negb]. cbv iota.
        step. (* 82e4c andi a3,a0,7 *)
        rewrite (MState.unsigned_lit (phi + 17)) by lia. rewrite rc_land7.
        step. (* 82e50 bge a3,a2,830d4 : not taken *)
        rewrite (rc_lts_signed ((phi + 17) mod 8) (bv_signed sb17))
          by (pose proof (rc_byte_signed sb17); pose proof (Z.mod_pos_bound (phi + 17) 8 ltac:(lia)); lia).
        replace ((phi + 17) mod 8 <? bv_signed sb17) with true
          by (symmetry; apply Z.ltb_lt; destruct OK17 as [H|H]; lia).
        cbn [negb]. cbv iota.
        step. (* 82e54 j 82124 *)
        apply (GB4 (Z_to_bv 64 ((phi + 17) mod 8)) c4 c5 c6).
    - (* byte 16 <> 0: 0x82100 sd zero,184(s1) ; 0x82104 j 82130 *)
      cbv iota.
      step. (* 82100 sd zero,184(s1) *)
      step. (* 82104 j 82130 *)
      apply GA0. unfold f6_tf. rewrite (proj2 (Z.eqb_neq _ 0) B16).
      first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
  (* the tail 0x820d8 -> 0x820f8, the loop's join *)
  assert (Htail : forall c0 c2 c3 c4 c5 c6 : word,
    evtF rsegs RNG QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       c0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) c2 c3 c4 c5 c6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820d8) fc None m (seg_rom rsegs))).
  { intros c0 c2 c3 c4 c5 c6.
    pose proof (HSO m 312 (wmono_refl rsegs m) ltac:(lia) ltac:(lia)) as HS312.
    step. (* 820d8 sd t0,312(s1) *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => change mm with m1 end.
    step. (* 820dc li a0,-17 *)
    step. (* 820e0 bltu a0,s2,82fa0 : not taken *)
    f6_ntF.
    step. (* 820e4 addi a0,s2,16 *)
    step. (* 820e8 srli a2,a0,3 *)
    step. (* 820ec add a2,a2,s10 *)
    rewrite (MState.unsigned_lit (phi + 16)) by lia.
    step. (* 820f0 lb a2,0(a2) *)
    step. (* 820f4 bnez a2,82dd4 *)
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb16)) by (pose proof (rc_byte_signed sb16); lia).
    destruct (Z.eqb_spec (bv_signed sb16) 0) as [Z16|Z16].
    - cbn [negb]. cbv iota. apply (G88 (Z_to_bv 64 (bv_signed sb16)) c3 c4 c5 c6).
    - cbn [negb]. cbv iota.
      step. (* 82dd4 andi a3,a0,7 *)
      rewrite (MState.unsigned_lit (phi + 16)) by lia. rewrite rc_land7.
      step. (* 82dd8 bge a3,a2,830b4 : not taken *)
      rewrite (rc_lts_signed ((phi + 16) mod 8) (bv_signed sb16))
        by (pose proof (rc_byte_signed sb16); pose proof (Z.mod_pos_bound (phi + 16) 8 ltac:(lia)); lia).
      replace ((phi + 16) mod 8 <? bv_signed sb16) with true
        by (symmetry; apply Z.ltb_lt; destruct OK16 as [H|H]; lia).
      cbn [negb]. cbv iota.
      step. (* 82ddc j 820f8 *)
      apply (G88 (Z_to_bv 64 (bv_signed sb16)) (Z_to_bv 64 ((phi + 16) mod 8)) c4 c5 c6). }
  assert (Hjoin : forall y0 y2 y4 y5 y6 : word,
    evtF rsegs RNG QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       y0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820d8) fc None m (seg_rom rsegs)))
    by (intros y0 y2 y4 y5 y6; apply Htail).
  assert (Rloop : rng RNG (phi + 18) 32) by (eapply rng_sub; [exact Rrec | lia | lia]).
  assert (Rshloop : forall x, phi + 18 <= x < phi + 50 -> rng RNG (Z.shiftr x 3 + ASAN_K) 1)
    by (intros x Hx; apply Rsh; lia).
  apply (f6_loop_F RNG ra0 sp gp tp t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) s3 s4v s5i s6 s7
           (Z_to_bv 64 v8) s9i s11 t3 t4 t5 t6 Fr fc m phi bs QE
           Hphi0 Hphi50 Hlen HB HA Rloop Rshloop Hjoin 32%nat 0%nat
           (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 32) a5i a6i);
    try reflexivity; try lia; try (f_equal; lia).
Qed.

(* ---- the compare lemmas: the source statements, re-derived from the _F forms ---- *)

Lemma f6_shad_rng_all : forall x, 0 <= x -> x + 1 <= 2 ^ 64 -> rng RNG_all (Z.shiftr x 3 + ASAN_K) 1.
Proof.
  intros x H0 H1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (HP : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (HD : x / 8 <= x) by (apply Z.div_le_upper_bound; lia).
  apply rng_all; unfold ASAN_K; lia.
Qed.

Lemma f6_loop_of_F : forall
  (ra0 sp gp tp t1 t2 s0 s1v s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall y0 y2 y4 y5 y6 : word,
     LE.evt rsegs Q (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
         y0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x820d8) fc None m (seg_rom rsegs))) ->
  forall (n i : nat) (y0 y1 y2 y4 y5 y6 : word), (i + n = 32)%nat -> (0 < n)%nat ->
    y0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> y1 = Z_to_bv 64 (psum (skipn 18 bs) i) ->
    y2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> y4 = Z_to_bv 64 (32 - Z.of_nat i) ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
         y0 y1 y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x82098) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t1 t2 s0 s1v s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 Fr fc m phi bs Q
    Hphi0 Hphi50 Hlen HB HA Hjoin n i y0 y1 y2 y4 y5 y6 Hin Hn E0 E1 E2 E4.
  apply (evtF_evt rsegs RNG_all).
  apply (f6_loop_F RNG_all ra0 sp gp tp t1 t2 s0 s1v s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 Fr fc m phi bs Q
           Hphi0 Hphi50 Hlen HB HA
           ltac:(apply rng_all; lia)
           ltac:(intros x Hx; apply f6_shad_rng_all; lia)
           ltac:(intros z0 z2 z4 z5 z6; apply (evt_evtF_all rsegs); apply Hjoin)
           n i y0 y1 y2 y4 y5 y6 Hin Hn E0 E1 E2 E4).
Qed.
Definition f6_loop_src_check : ltac:(let T := type of F6.f6_loop in exact T) := f6_loop_of_F.

Lemma f6_run_evt_of_F :
  forall (ra0 sp gp tp t1 t2 s0 a5i a6i s3 s4v s5i s6 s7 s9i s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi A v8 e272 : Z) (bs : list byte),
    0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
    bytes_at rsegs m phi bs -> addressable m phi 50 ->
    0 <= A -> A + 448 <= 2 ^ 64 -> stk rsegs m (A + 184) (A + 320) ->
    0 <= v8 < 2 ^ 64 -> q64 m (A + 272) e272 -> e272 = (if v8 =? 0 then 0 else 1) ->
    phi + 50 <= A -> (forall x, phi <= x < phi + 50 -> shadow_addr x < A) ->
    LE.evt rsegs
      (fun ms' => exists b0 b1 b2 b3 b4 b5 b6 : word,
         ms' = MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
                       b0 b1 b2 b3 b4 b5 b6 (Z_to_bv 64 32)
                       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8)
                       (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 1 else 0))
                       (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x8214c) fc None
                  (write_to_mem
                     (write_to_mem (write_to_mem m (wa (A + 312)) (le8 (Z_to_bv 64 (phi + 18))))
                        (wa (A + 184)) (le8 (Z_to_bv 64 (f6_tf bs))))
                     (wa (A + 248))
                     (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1))))
                  (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
               (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 18))
               (Z_to_bv 64 (- (phi + 18))) (Z_to_bv 64 32) a5i a6i (Z_to_bv 64 32)
               (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82098) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all).
  apply f6_run_evt_F with (e272 := e272); try assumption.
  - apply rng_all; lia.
  - intros x Hx. apply f6_shad_rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
Qed.
Definition f6_run_evt_src_check : ltac:(let T := type of F6.f6_run_evt in exact T) := f6_run_evt_of_F.
