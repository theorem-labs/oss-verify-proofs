(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1080 of its 1151 lines of code are new or changed and 940 lines of the source are left out. *)
(* Segment R16 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): cut Inv_B8194c_at b (v1.9
   pc 0x8194c) -> cut Inv_B81aa0_at b (v1.9 pc 0x81aa0) (S_R16 (forms-asan-ubsan-v190.md (a working note, not in this delivery));
   row S_R16 (a Theorem Labs lane's v190-segment-table.md (a working note, not in this delivery)): CHANGED, register renaming s2 -> s11; FREE = wrapper_free at 0x534b4).
   rule 24: no function proved (a slot segment).
   0x8194c heads the 32-byte block-sum loop of the turns b = 1, 2 (the cut carries b = 1 \/ b = 2). It is entered at
   loop index i < 32 with a0 = a2 = Phi_r + 18 + i, a4 = 32 - i, a1 = rsum g b i (the sum of the first i of the 32
   bytes Phi_r[18 ..]). One turn:
     0x8194c add a5,a3,a4 ; 0x81950 bne a5,s11,0x81958 - the UBSan trap test: a3 = room = 2^64 - 18 - Phi_r
       (0x8192c-0x81940), s11 = 32, so a5 = s11 only when Phi_r + 18 + i wraps; it does not (0 < Phi_r and
       Phi_r + n_b <= 2^47 from HB), so 0x81954 `j 0x82fa0` (the trap) is not taken;
     0x81958 srli a5,a0,3 ; 0x8195c add a5,a5,s10 ; 0x81960 lb a5,0(a5) ; 0x81964 bnez a5,0x81984 - the instrumented
       check (shadow byte of a0); with the 32 bytes at Phi_r + 18 addressable (HB) the shadow byte k is 0, or k > 0
       and 0x81984 andi a6,a0,7 ; 0x81988 blt a6,a5,0x81968 is taken: the error path 0x8198c `j 0x83060` (a report
       entry) is not reached;
     0x81968 lbu a5,0(a2) ; addi a4,a4,-1 ; addi a0,a0,1 ; add a1,a1,a5 ; addi a2,a2,1 ; 0x8197c bnez a4,0x8194c.
   The loop is proved by induction on the down-counter a4 = 32 - i (r16_loop_ind). At a4 = 0 it leaves by
   0x81980 `j 0x81a8c`; 0x81a8c zext.b a0,a1 is 0 because the block sum of X(b) closes for b = 1, 2 (r16_rtm_sum, by
   computation on the 11 catalogue rows; the harness's `block_sum_closes(frame)`), so 0x81a90 beqz a0,0x81a98 is
   taken and the abort edge 0x81a94 `j 0x82fa4` is not. Then 0x81a98 mv a0,s4 ; 0x81a9c jal wrapper_free frees
   Phi_r and returns to 0x81aa0, the exit cut.
   The free call is R15's (the same instructions and the same transport: aa_free from the a_call_pre of
   fra_call_pre, FRA by sl_mid, ENT by ent_call, every exit byte kept by a_call_post's frame clause). RBE's image
   bytes (the row table at BA_FR + 72 and the catalogue row at mrow in RELRO, frame_facts; the box bytes at BOXA in
   the read-only segment) and FRA's input facts (the input block is a live entry block, apart from the freed one:
   a_laws_not_owned in both heaps) are kept by that clause too.
   The exit cut names the turn-(S b) records: RID / RFG (S b) = RID / RFG b for b <= 2 (r16_RS_012).
   The official Inv_B8194c_at carries the two registers the trap test reads: a3 = rg regs 13 (- (phi + 18)) and
   s11 = rg regs 27 32; the exit's s11 = 32 is kept by the loop and by the free call (s11 is callee-saved).
   The free's per-class premises (v1.9 afree_at): the class bytes of the call heap (Phi_r, n_b) :: g_H g under
   Bc = Bc_of BE and the room row, from ENT's 14th conjunct (the entry heap's per-class bound) through
   Seg/Tac_cls.v's sl_free_cls.  No local cut: seg_R16 is forms-asan-ubsan-v190.md's S_R16. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require SlotModel.
Import ListNotations.
Open Scope Z_scope.

(* ---- the run 0x8194c .. 0x81a9c in the Lib engine ---- *)

(* The trap test 0x81950: a5 = room + (32 - i) is s11 = 32 only when (a5 - 32) mod 2^64 = 0. *)
Lemma r16_eqb32 : forall x, (x - 32) mod 2 ^ 64 <> 0 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 32) = false.
Proof.
  intros x H. unfold bv_eqb. apply Z.eqb_neq. intros E. apply H.
  rewrite !unsigned_lit_wrap in E. rewrite Zminus_mod, E, Z.sub_diag. reflexivity.
Qed.

(* room = - q: a5 - 32 = - (q + i), which is not 0 mod 2^64 for 0 < q + i < 2^64 (Phi_r + 18 + i does not wrap). *)
Lemma r16_room_ne : forall x q j, x = - (q + j) + 32 -> 0 < q + j < 2 ^ 64 -> (x - 32) mod 2 ^ 64 <> 0.
Proof.
  intros x q j -> H E. assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
  rewrite HP in *. Z.div_mod_to_equations. lia.
Qed.

Lemma r16_land255 : forall S, S mod 256 = 0 -> Z.land S 255 = 0.
Proof. intros S H. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. exact H. Qed.

(* The loop: head 0x8194c (trap test 0x81950), shadow check 0x81958-0x81964 (slow arm 0x81984-0x81988), body
   0x81968, latch 0x8197c, exit 0x81980. a3 = - q and s11 = 32 are fixed. *)
Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hq : 0 < q.
  Hypothesis Hq32 : q + 32 <= 2 ^ 64.
  Hypothesis Hlen : length xs = 32%nat.
  Hypothesis HB : bytes_at rsegs m q xs.
  Hypothesis HSR : asan_shadow_rd rsegs m off q 32 W.
  Hypothesis HAD : asan_addressable rsegs m off q 32.

  Abbreviation ST pc x10 x11 x12 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 (- q)) x14 x15 x16 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x15 x16,
    evt rsegs Q (ST 0x81980 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32)) (Z_to_bv 64 (q + 32))
                    (Z_to_bv 64 0) x15 x16).

  Lemma r16_loop_ind : forall n i x15 x16, (i + n = 32)%nat -> (0 < n)%nat ->
    evt rsegs Q (ST 0x8194c (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                    (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x15 x16).
  Proof using Hq Hq32 Hlen HB HSR HAD EXIT.
    induction n as [|n IH]; intros i x15 x16 Hin Hn; [lia|].
    assert (BODY : forall y15 y16,
      evt rsegs Q (ST 0x81968 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                      (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y15 y16)).
    { intros y15 y16.
      pose proof (rd_byte rsegs m q xs i HB ltac:(lia)) as RD.
      pose proof (psum_range xs i) as PR.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rc_eqb0_signed (32 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb].
        replace i with 31%nat in * by lia.
        replace (q + Z.of_nat 31 + 1) with (q + 32) by lia.
        replace (32 - Z.of_nat 31 + -1) with 0 by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (q + Z.of_nat i + 1) with (q + Z.of_nat (S i)) by lia.
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    (* 0x8194c / 0x81950: the trap test is not taken *)
    step. step.
    lazymatch goal with
    | |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 32)] =>
        rewrite (r16_eqb32 x) by (apply (r16_room_ne x q (Z.of_nat i)); lia)
    end.
    cbn [negb]. cbv iota.
    (* 0x81958 .. 0x81964: the shadow check of a0 = q + i *)
    destruct (asan_shadow_read rsegs m off q 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((q + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (q + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((q + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End Loop.

(* An `addi rd,rs,0` result. *)
Lemma r16_mv : forall x : word, Z_to_bv 64 (bv_unsigned x + 0) = x.
Proof. intros x. rewrite Z.add_0_r. apply Z_to_bv_lit_self. Qed.

(* The run from the loop head at index i (i < 32) to the allocator's free entry 0x534b4: the loop, 0x81980
   `j 0x81a8c`, 0x81a8c zext.b a0,a1 = 0 (the block sum closes), 0x81a90 beqz a0,0x81a98 (taken), 0x81a98 mv a0,s4,
   0x81a9c jal wrapper_free. Memory is unchanged; ra = 0x81aa0, a0 = s4. *)
Lemma r16_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (- q) -> a4 = Z_to_bv 64 (32 - Z.of_nat i) -> s11 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat -> 0 < q ->
    length xs = 32%nat -> bytes_at rsegs m q xs -> addressable m q 32 -> psum xs 32 mod 256 = 0 ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) (m' : word -> option byte),
         ms' = MS R F pc' fc None m' (seg_rom rsegs) /\ pc' = Z_to_bv 64 0x534b4 /\ m' = m /\
         getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8194c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i -> -> -> -> -> -> -> Hi Hq Hlen HB AD HS.
  destruct (rt_addressable_bound m q 32 AD) as (_ & _ & Hq32).
  pose proof (rt_shadow_rd m q 32 [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable m q 32 AD) as HAD.
  pose proof (psum_range xs 32) as PR. change (Z.of_nat 32) with 32 in PR.
  refine (r16_loop_ind ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m q ASAN_K xs []
            _ Hq ltac:(lia) Hlen HB HSR HAD _ (32 - i)%nat i a5 a6 ltac:(lia) ltac:(lia)).
  intros x15 x16.
  step. step.
  rewrite (unsigned_lit (psum xs 32)) by lia. rewrite (r16_land255 (psum xs 32) HS).
  step. try if_true.
  step. step.
  rewrite ?r16_mv.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [first [reflexivity | vm_compute; reflexivity]|].
  split; [reflexivity|].
  split; [first [reflexivity | vm_compute; reflexivity]|].
  repeat split.
Qed.

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma r16_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* The 32 block bytes Phi_r[18 .. 50) of the frame Phi_r holds (RFb: bytes_at Phi_r F_b, rt_g = fr50 F_b). *)
Lemma r16_fr50_eq : forall bs, (50 <= length bs)%nat -> SlotModel.fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold SlotModel.fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma r16_blk_at : forall m phi Fb, bytes_at rsegs m phi Fb -> (50 <= length Fb)%nat ->
  bytes_at rsegs m (phi + 18) (skipn 18 (SlotModel.fr50 Fb)) /\ length (skipn 18 (SlotModel.fr50 Fb)) = 32%nat.
Proof.
  intros m phi Fb H L. rewrite (r16_fr50_eq Fb L).
  split; [| rewrite length_skipn, length_firstn; lia].
  rewrite <- (firstn_skipn 50 Fb) in H.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H. destruct H as [H _].
  rewrite <- (firstn_skipn 18 (firstn 50 Fb)) in H.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H. destruct H as [_ H].
  replace (phi + 18) with (phi + Z.of_nat (length (firstn 18 (firstn 50 Fb)))) by (rewrite !length_firstn; lia).
  exact H.
Qed.

(* ---- the cuts, the model and the free call ---- *)
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcIdentModel RcFrag RcFragLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynthLib RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_cls.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LImg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module REm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.
Module REmL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmitLib.
Module RSyL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynthLib.
Module RFinL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFinLib.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.

(* ---- the round-trip model at turn b = 1, 2 ---- *)

(* The cut's names, by reflexivity over variables (never a conversion at the concrete round-trip values). *)
Lemma r16_rsum : forall g (b i : nat), rsum g b i = RcModel.psum (skipn 18 (rt_g (g_in g) (Z.of_nat b))) i.
Proof. reflexivity. Qed.

Lemma r16_rt_g : forall inp b, rt_g inp b = fr50 (rt_F inp b).
Proof. reflexivity. Qed.

(* Lengths: a catalogue row is 296 bytes, X(b) 32, and F_b has n_b >= 124 bytes when n_b <> 0. *)
Lemma r16_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (LImg.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (LImg.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma r16_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, BAP.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RS6.rc (rt_mb inp) b =? 1 then RS6.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RS6.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RSyL.rs_synth_len. apply r16_row_len. }
  destruct (b <=? 1); [apply RFinL.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

Lemma r16_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, BAP.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (REmL.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, REm.em_fr, REm.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, r16_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* Every round-trip value depends on the input only through OUR and i*. *)
Lemma r16_istar_range : forall inp, 0 <= istar inp < 11.
Proof. intros inp. unfold istar, CAT_N. apply Z.mod_pos_bound. lia. Qed.

Section R16Cong.
Variables inp inp' : list byte.
Hypothesis HO : OUR inp = OUR inp'.
Hypothesis HI : istar inp = istar inp'.

Lemma r16_ac_mrow : mrow inp = mrow inp'.
Proof using HO HI. unfold mrow. rewrite HI. reflexivity. Qed.

Lemma r16_ac_mb : rt_mb inp = rt_mb inp'.
Proof using HO HI. unfold rt_mb. rewrite HI. reflexivity. Qed.

Lemma r16_ac_nb : rt_nb inp = rt_nb inp'.
Proof using HO HI. unfold rt_nb. rewrite r16_ac_mb. reflexivity. Qed.

Lemma r16_ac_n : forall b, rt_n inp b = rt_n inp' b.
Proof using HO HI. intros b. unfold rt_n, rt_E, rt_uw. rewrite r16_ac_mrow, r16_ac_mb. reflexivity. Qed.

Lemma r16_ac_X : forall b, rt_X inp b = rt_X inp' b.
Proof using HO HI. intros b. unfold rt_X. rewrite r16_ac_mrow, r16_ac_mb, r16_ac_nb. reflexivity. Qed.

Lemma r16_ac_g : forall b, rt_g inp b = rt_g inp' b.
Proof using HO HI. intros b. unfold rt_g, rt_F. rewrite HO, r16_ac_X, r16_ac_n. reflexivity. Qed.
End R16Cong.

(* The canonical input of OUR and istar: OUR, then the mode byte 2 i. *)
Definition r16_cn (our : list byte) (i : Z) : list byte := our ++ [RcIdentModel.zb (2 * i)].

Lemma r16_cn_OUR : forall our i, length our = 6%nat -> OUR (r16_cn our i) = our.
Proof.
  intros our i H. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  reflexivity.
Qed.

Lemma r16_cn_istar : forall our i, length our = 6%nat -> 0 <= i < 11 -> istar (r16_cn our i) = i.
Proof.
  intros our i H Hi. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* The block sums of X(1) and X(2) close (blocksum, stated unfolded: psum .. 32 mod 256 = 0) for b = 1, 2, by
   computation on the 11 catalogue rows (the 6 OUR bytes stay variables; they are frame bytes 0 .. 5, outside the
   block). Stated over psum directly: a conversion between blocksum and its body at a variable list is not
   needed anywhere. *)
Lemma r16_rtm_sum : forall inp b, 1 <= b <= 2 -> RcModel.psum (skipn 18 (rt_g inp b)) 32 mod 256 = 0.
Proof.
  intros inp b Hb.
  assert (HO : OUR inp = OUR (r16_cn (OUR inp) (istar inp))) by (symmetry; apply r16_cn_OUR, OUR_length).
  assert (HI : istar inp = istar (r16_cn (OUR inp) (istar inp)))
    by (symmetry; apply r16_cn_istar; [apply OUR_length | apply r16_istar_range]).
  rewrite (r16_ac_g _ _ HO HI).
  clear HO HI.
  generalize (OUR_length inp) (r16_istar_range inp).
  generalize (OUR inp) (istar inp).
  intros our i HL Hi.
  destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate HL; clear HL.
  assert (Eb : b = 1 \/ b = 2) by lia.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  clear Hb Hi.
  destruct Eb as [->| ->];
    destruct Ei as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* The round-trip state does not move across the turns b <= 2. *)
Lemma r16_st_S : forall inp (b : nat), rt_st inp (S b) =
  let s := rt_st inp b in let x := Z.of_nat b in
  if rt_n inp x =? 0 then s
  else if (x =? 3) || (x =? 4) then (rp_id (fst s) (rt_n inp x) (rt_g inp x), snd s)
  else if (x =? 5) || (x =? 6) then (fg_id (fst s) (rt_n inp x) (snd s) (rt_g inp x), fg_st (rt_n inp x) (snd s) (rt_g inp x))
  else s.
Proof. intros inp b. reflexivity. Qed.

Lemma r16_RS_012 : forall inp (b : nat), (b <= 2)%nat -> RID inp (S b) = RID inp b /\ RFG inp (S b) = RFG inp b.
Proof.
  intros inp b Hb. unfold RID, RFG. rewrite r16_st_S. cbv zeta.
  destruct (rt_n inp (Z.of_nat b) =? 0); [split; reflexivity|].
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  replace ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  split; reflexivity.
Qed.

(* ---- register, cell and byte helpers, image placement, turn records, spills (R15's, renamed) ---- *)


(* Bytes whose cells keep their contents. *)
Lemma r16_keep_bytes : forall m m' a bs,
  bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). exact (HK (a + Z.of_nat i) ltac:(lia)).
Qed.

(* A buffer stays addressable when its shadow bytes keep their contents (ADDR-KEEP). *)
Lemma r16_addr_keep : forall m m' p n,
  addressable m p n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. rewrite <- Hb. exact (HK i Hi).
Qed.

(* A register value read twice in [0, 2^64). *)
Lemma r16_rg_eq : forall regs r x y, rg regs r x -> rg regs r y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
  intros regs r x y Hx Hy Hxr Hyr. pose proof (rg_eq64 regs r x y Hx Hy) as Hm.
  rewrite !Z.mod_small in Hm by lia. exact Hm.
Qed.

(* A callee-saved register of an allocator entry, at a register named by a numeral. *)
Lemma r16_regs_kept_at : forall regs regs' (r : reg) (z : Z),
  AC.a_regs_kept regs regs' -> AC.a_callee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HK Hc <-. exact (HK z Hc). Qed.

(* The shadow byte of the frame's 8 k-th byte. *)
Lemma r16_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* ---- image placement, on the image's segment table ---- *)

(* The image's loaded segments all end below GT = 0x5fe000. *)
Lemma r16_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r16_img_range : forall x, AC.a_in_img x -> 0 <= x < 6283264.
Proof.
  intros x (s & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r16_img_top s Hin) as Hs. cbv beta in Hs.
  apply Z.leb_le in Hs. pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Definition r16_img_cov (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma r16_img_cov_in : forall lo hi x, r16_img_cov lo hi = true -> lo <= x < hi -> AC.a_in_img x.
Proof.
  intros lo hi x H Hx. unfold r16_img_cov in H. apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (H1 & H2). apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin | lia].
Qed.

(* The registered globals are image bytes; so are the musl sink cells. *)
Lemma r16_ag_cov : forallb (fun p => r16_img_cov (fst p) (fst p + snd p)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r16_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r16_ag_cov (lo, len) Hin) as H. cbn [fst snd] in H.
  exact (r16_img_cov_in _ _ _ H Hr).
Qed.

Lemma r16_sink_cov_a : r16_img_cov 0x5fc8e1 0x5fc8e2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r16_sink_cov_b : r16_img_cov 0x5fcd40 0x5fcd50 = true.
Proof. vm_compute. reflexivity. Qed.

(* The client objects of musl's stdio the sink words live in (Contract.v a_client). *)
Lemma r16_client_a : forall a, 0x5dc680 <= a < 0x5dc680 + 131728 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5dc680, 131728. split; [cbn; tauto | exact Ha]. Qed.
Lemma r16_client_b : forall a, 0x5fc918 <= a < 0x5fc918 + 4320 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5fc918, 4320. split; [cbn; tauto | exact Ha]. Qed.

(* The image's RELRO range (AF.frame_RELRO, one entry) is [0x9f168, 0xa15e8). *)
Lemma r16_relro_range : forall a, in_globals AF.frame_RELRO a -> 0x9f168 <= a < 0xa15e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AF.frame_RELRO in Hin. cbn [In] in Hin.
  destruct Hin as [E|[]]; inversion E; subst; lia.
Qed.

(* The image's first loaded segment [0x10000, 0x30104) is read-only; it holds round_trip.box (BOXA = 0x21140) and the
   catalogue's row-name strings. *)
Definition r16_ro_cov (lo hi : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma r16_ro_cov_ok : r16_ro_cov 0x21140 0x218f0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r16_ro_in : forall x, 0x21140 <= x < 0x218f0 -> AC.a_in_ro x.
Proof.
  intros x Hx. pose proof r16_ro_cov_ok as H. unfold r16_ro_cov in H.
  apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (Hb & H2). apply andb_true_iff in Hb as (Hw & H1).
  apply negb_true_iff in Hw. apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin|]. split; [exact Hw | lia].
Qed.

Lemma r16_ro_img : forall x, AC.a_in_ro x -> AC.a_in_img x.
Proof. intros x (s & Hin & _ & Hr). exists s. split; [exact Hin | exact Hr]. Qed.

(* The row name of every catalogue row that has one lies in [0x214a0, 0x218e0] (by computation on the 11 rows of
   BOX_CATALOGUE; rt_mb inp is row istar inp, istar inp < 11). *)
Lemma r16_rows_b :
  forallb (fun i => (RS6.has (rowb i) =? 0) || (RS6.rname (rowb i) =? 0) ||
                    ((0x214a0 <=? RS6.rname (rowb i)) && (RS6.rname (rowb i) <=? 0x218e0)))
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r16_rname : forall inp, RS6.has (rt_mb inp) <> 0 -> RS6.rname (rt_mb inp) <> 0 ->
  0x214a0 <= RS6.rname (rt_mb inp) <= 0x218e0.
Proof.
  intros inp H1 H2. unfold rt_mb in *.
  assert (Hi : 0 <= istar inp < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hin : In (istar inp) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) by (cbn [In]; lia).
  pose proof (proj1 (forallb_forall _ _) r16_rows_b _ Hin) as Hb. cbv beta in Hb.
  apply orb_true_iff in Hb as [Hb|Hb]; [apply orb_true_iff in Hb as [Hb|Hb]|].
  - apply Z.eqb_eq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
  - apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1, Hb2. lia.
Qed.

(* The row-name string is at most 16 bytes. *)
Lemma r16_cstr_len : forall k a, (length (img_cstr a k) <= k)%nat.
Proof.
  induction k as [|k IH]; intros a; cbn [img_cstr]; [cbn [length]; lia|].
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length];
    [lia | specialize (IH (a + 1)); lia].
Qed.

Lemma r16_nb_len : forall inp, (length (rt_nb inp) <= 16)%nat.
Proof. intros inp. unfold rt_nb. apply r16_cstr_len. Qed.

(* ---- the turn records: the identity record RID is 38 bytes and the fragment record RFG 72 bytes at every turn
   (R6's r6_rid_len / r6_rfg_len), so both lie inside the frame ---- *)

Lemma r16_rid_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst];
    first [exact IH | apply RcIdentModel.ING_length; exact IH].
Qed.

Lemma r16_rtg_len : forall inp x, length (rt_g inp x) = 50%nat.
Proof. intros inp x. unfold rt_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma r16_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
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

Lemma r16_rfg_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd];
    first [exact IH | apply r16_fgst_len; [exact IH | apply r16_rtg_len]].
Qed.

(* ---- spills and the side-arm frame record ---- *)

(* A spill at A + off (A the spill base in register 9) moves to a later state whose register 9 is the same and whose
   bytes at [A + off, A + off + 8) are the same. *)
Lemma r16_spill_keep : forall regs regs' m m' A off v,
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
  apply (r16_keep_bytes m m' _ _ Hq). rewrite length_le8. change (Z.of_nat 8) with 8.
  intros x Hx. exact (HK x Hx).
Qed.

(* FSREC moves to a state that keeps the 16 bytes at tp and every FakeStack byte outside the frame body. *)
Lemma r16_fsrec_keep : forall mem mem' fr,
  FSREC fr mem ->
  (forall i, 0 <= i < 16 -> mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i)) ->
  (forall x, AC.a_in_fs AC.ASYMS mem x -> ~ (fr + 24 <= x < fr + 3136) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) Htp' HK.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (Hin : forall x, FS <= x < FS + AC.FS_SIZE -> AC.a_in_fs AC.ASYMS mem x)
    by (intros x Hx; exists FS; split; [exact HFSr | split; [exact Htp | exact Hx]]).
  exists FS, j.
  split.
  { intros k Hk. rewrite (Htp' (Z.of_nat k) ltac:(lia)). exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { apply (r16_keep_bytes mem mem' _ _ Hflag). cbn [length]. change (Z.of_nat 1) with 1.
    intros x Hx. apply HK; [apply Hin|]; lia. }
  { apply (r16_keep_bytes mem mem' _ _ Htail). rewrite length_le8. change (Z.of_nat 8) with 8.
    intros x Hx. rewrite HB6 in Hx. apply HK; [apply Hin|]; lia. }
Qed.

(* ---- interval apartness ---- *)

Lemma r16_dj_gt : forall fr hi c d, AC.GT <= fr -> d <= AC.GT -> RcLay.ly_dj (fr + 544) hi c d.
Proof. intros fr hi c d H1 H2. unfold RcLay.ly_dj. right. lia. Qed.

Lemma r16_dj_hit : forall lo hi c d (P : Z -> Prop), lo < hi -> c < d ->
  (forall x, c <= x < d -> P x) -> (forall x, lo <= x < hi -> ~ P x) -> RcLay.ly_dj lo hi c d.
Proof.
  intros lo hi c d P Hlh Hcd HP HN. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec hi c) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec d lo) as [H2|H2]; [right; exact H2|].
  exfalso. destruct (Z_le_gt_dec lo c) as [H3|H3].
  - apply (HN c); [lia | apply HP; lia].
  - apply (HN lo); [lia | apply HP; lia].
Qed.

(* The RELRO range [0x9f168, 0xa15e8) holds the catalogue (CAT = 0x9f620, 11 rows of 296 bytes) and CTRL_FRAMES
   (the row table at BA_FR + 72 = 0xa0648, 168 bytes). *)
Lemma r16_relro_in : forall x, 0x9f168 <= x < 0x9f168 + 9344 -> in_globals AF.frame_RELRO x.
Proof.
  intros x Hx. exists 0x9f168, 9344. split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity | exact Hx].
Qed.

Lemma r16_tbl_len : Z.of_nat (length BAP.ba_tbl) = 168.
Proof. vm_compute. reflexivity. Qed.

Lemma r16_box_len : Z.of_nat (length box6) = 6.
Proof. reflexivity. Qed.

(* ---- The Contract.v laws whose conclusion lists this file takes apart: each one ONCE, here (a Theorem Labs lane via a Theorem Labs lane
   15:32Z: the next generation then breaks one line per law, not every site). ---- *)

(* a_laws_fs_place: the side stack FS is above GT, ends at or below stklo, and is application memory. *)
Lemma r16_fs_place : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros API H mem md FS HAH Hw HFS.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md FS HAH Hw HFS)
    as (HGT & Hend & _ & Happ).
  split; [exact HGT|]. split; [exact Hend | exact Happ].
Qed.

(* a_laws_blocks: a live block (p, n) ends at or below stklo, and each of its bytes is application memory, off the
   image and off the side stack. *)
Lemma r16_blocks : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_img a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros API H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md p n HAH Hin)
    as (_ & _ & Hstk & _ & Hb).
  split; [exact Hstk|].
  intros a Ha. destruct (Hb a Ha) as (Happ & _ & Himg & _ & Hfs). exact (conj Happ (conj Himg Hfs)).
Qed.

(* a_laws_not_owned, for the real stack / side stack bytes and for the bytes of a live block. *)
Lemma r16_no_own_cls : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END \/ AC.a_in_fs AC.ASYMS mem a ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md a /\
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md (shadow_addr a).
Proof.
  intros API H mem md a HAH Hx.
  apply (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md a HAH).
  destruct Hx as [Hx|Hx]; [right; right; right; exact Hx | right; right; left; exact Hx].
Qed.

Lemma r16_no_own_blk : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md -> AC.in_blocks H a ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md a /\
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md (shadow_addr a).
Proof.
  intros API H mem md a HAH Hx.
  exact (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md a HAH (or_introl Hx)).
Qed.

(* a_laws_client: the client cells are not the runtime's, nor the shadow bytes of image bytes. *)
Lemma r16_client : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md ->
  (AC.in_blocks AC.a_client a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md a) /\
  (AC.a_in_img a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H mem md (shadow_addr a)).
Proof.
  intros API H mem md a HAH.
  destruct (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md a HAH) as (H1 & H2 & _).
  exact (conj H1 H2).
Qed.

(* a_laws_mat_le: AH and stklo across lazy-page materialization. *)
Lemma r16_mat_le : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md') /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md.
Proof.
  intros API H mem md md' Hm.
  destruct (AC.a_laws_mat_le _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md md' Hm)
    as (HAH & _ & Hlo & _).
  exact (conj HAH Hlo).
Qed.

Section R16.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ---- the segment lemma ---- *)

Lemma seg_R16 : forall b : nat, Hat B APIf ra (Inv_B81aa0_at B APIf ra) b -> Hat B APIf ra (Inv_B8194c_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct HInv as (phi & i & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR &
    HRBE & Hr21 & Hile & Hr10 & Hr12 & Hr14 & Hb12 & Hilt & Hr11 & HRFb & Hr13 & Hr27).
  subst c. rewrite SEGS.
  destruct HRFb as ((_ & _ & _ & _ & HIDB & HFGB) & Hnz & Hr20 & HFb).
  assert (Hble2 : (b <= 2)%nat) by (destruct Hb12 as [E|E]; rewrite E; lia).
  destruct (r16_RS_012 (g_in g) b Hble2) as (EID & EFG).
  (* the frame Phi_r: n_b >= 124 bytes, addressable; its 32 block bytes at Phi_r + 18 and their sum *)
  destruct (r16_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hnb, HLF.
  pose proof HHB as (Hphinz & HAphi0).
  assert (Hsz : AC.a_size (rnb g b) = rnb g b) by (clear - Hnb; unfold AC.a_size; lia).
  rewrite Hsz in HAphi0.
  pose proof (rt_addressable_bound mem phi (rnb g b) HAphi0) as (Hphi0 & _ & Hphihi).
  assert (HA18 : addressable mem (phi + 18) 32)
    by (apply (addressable_sub mem phi (rnb g b) 18 32 HAphi0); clear - Hnb; lia).
  assert (HLb : (50 <= length (rt_F (g_in g) (Z.of_nat b)))%nat) by (rewrite HLF; clear - Hnb; lia).
  destruct (r16_blk_at mem phi _ HFb HLb) as (HBxs & Hlenxs).
  rewrite <- (r16_rt_g (g_in g) (Z.of_nat b)) in HBxs, Hlenxs.
  assert (HSum : RcModel.psum (skipn 18 (rt_g (g_in g) (Z.of_nat b))) 32 mod 256 = 0)
    by (apply r16_rtm_sum; clear - Hb12; lia).
  rewrite r16_rsum in Hr11.
  unfold rg in Hr10, Hr11, Hr12, Hr13, Hr14, Hr27.
    pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HSbnd : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as HAPART.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HERRv : AC.a_errno AC.ASYMS = 6145452) by reflexivity.
  assert (HOOMv : AC.as_oom AC.ASYMS = 1227040) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  rewrite Haspz in HAPART.
  (* the run: the loop from index i, the low-byte test, mv a0,s4 and the jal to the allocator's free entry *)
  apply (sl_run_lib regs (Z_to_bv 64 0x8194c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x534b4 /\ mem' = mem /\
       getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = getr regs 20 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite r16_mkR_of.
    eapply LE.evt_mono.
    + eapply (r16_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr mem (phi + 18)
               (skipn 18 (rt_g (g_in g) (Z.of_nat b))) i);
        [ exact Hr10 | exact Hr11 | exact Hr12 | exact Hr13 | exact Hr14 | exact Hr27 | exact Hr26 | exact Hilt
        | clear - Hphi0; lia | exact Hlenxs | exact HBxs | exact HA18 | exact HSum ].
    + intros ms' (R & pc' & m' & Hms & P0 & Pm & P1 & P10 & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P21 & P22 & P23 &
        P24 & P25 & P26 & P27).
      exists R, pc', m'. split; [exact Hms|].
      exact (conj P0 (conj Pm (conj P1 (conj P10 (conj P2 (conj P3 (conj P4 (conj P8 (conj P9 (conj P18 (conj P19
               (conj P21 (conj P22 (conj P23 (conj P24 (conj P25 (conj P26 P27))))))))))))))))).
  - intros R pc' mem' regs'' md'
      (Hpc & Hmem & K1 & K10 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K27)
      Hreg Hmat.
    subst pc' mem'.
    (* the loop facts and the frame-model facts are not read below; dropping them keeps lia's context small *)
    clear Hile Hr10 Hr11 Hr12 Hr13 Hr14 Hilt i Hb12 Hble2 Hnb HLF HHB Hphinz HAphi0 Hsz Hphi0 Hphihi HA18 HLb
      HBxs Hlenxs HSum Hnz HFb.
    assert (E1 : getr regs'' 1 = Z_to_bv 64 0x81aa0) by (rewrite Hreg; exact K1).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 phi) by (rewrite Hreg, K10; exact Hr20).
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (HFRAc : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs regs'' mem md md' HFRA);
          [exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 | exact Hmat]).
    assert (HENTc : ENT APIf g (hb1 phi (rnb g b)) mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
    destruct (r16_mat_le (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md md' Hmat) as (HAHm & Hlom).
    assert (HAH' : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md')
      by exact (HAHm HAH).
    assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md')
      by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md' HAH').
    assert (Hstklo' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= g_S g - AF.SLOT_STACK)
      by (rewrite Hlom; exact Hstklo).
    rewrite HHMv in Hhigh.
    (* the free pre at the call, from FRA + ENT *)
    assert (HPREc : AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                      AC.AK_FREE (hb1 phi (rnb g b) ++ g_H g) regs'' mem md').
    { apply (fra_call_pre B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md' AC.AK_FREE HFRAc HENTc).
      - unfold YK0s.ret_ok. rewrite E1. vm_compute. reflexivity.
      - unfold AC.AK_FREE. rewrite HFN. lia. }
    (* the allocator's free, on the frame's law: the live list is [] ++ (Phi, n) :: g_H g, and the per-class
       premises for Bc = Bc_of BE from ENT's per-class conjunct (Tac_cls.sl_free_cls) *)
    pose proof (AC.aa_free AC.ASYMS AsanRTInv.RT (APIf rc)) as HFREE.
    unfold AC.afree_contract, AC.afree_at in HFREE.
    assert (EF : AC.as_free AC.ASYMS = 0x534b4) by reflexivity.
    destruct (sl_free_cls APIf g (hb1 phi (rnb g b)) mem md' phi (rnb g b) HENTc) as (BE & _ & _ & HCB & HROOM).
    eapply (SR_bind rsegs).
    + rewrite <- EF.
      exact (HFREE [] (g_H g) regs'' mem md' phi (rnb g b) (Bc_of BE) HPREc E10 HCB HROOM).
    + intros c' (regs3 & mem3 & md3 & Ec' & HPOST & HKERR).
      rewrite E1 in Ec'. subst c'.
      change ([] ++ (phi, rnb g b) :: g_H g) with (hb1 phi (rnb g b) ++ g_H g) in HPOST.
      (* the post's projections *)
      pose proof HPOST as HAH3; apply AC.a_call_post_ah in HAH3.
      pose proof HPOST as HKR; apply AC.a_call_post_regs in HKR.
      pose proof HPOST as HMOD; apply AC.a_call_post_model in HMOD.
      pose proof HPOST as HSTK3; apply AC.a_call_post_stklo in HSTK3.
      assert (HTP3 : forall i, 0 <= i < 16 ->
                mbyte rsegs mem3 (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
        by (eapply AC.a_call_post_tp; exact HPOST).
      assert (HWIN3 : forall a, AC.a_window AC.AK_FREE regs'' a -> writable_at rsegs mem3 a)
        by (eapply AC.a_call_post_win_writable; exact HPOST).
      assert (HWP : forall a, AC.a_window AC.AK_FREE regs'' a -> exists bb, mbyte rsegs mem3 a = Some bb)
        by (eapply AC.a_call_post_win_present; exact HPOST).
      assert (HFRM : forall a, 0 <= a < 2 ^ 64 ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' a ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 a ->
                ~ AC.a_window AC.AK_FREE regs'' a ->
                ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) -> a <> AC.as_oom AC.ASYMS ->
                ~ (phi <= a < phi + rnb g b) ->
                mbyte rsegs mem3 a = mbyte rsegs mem a /\
                (writable_at rsegs mem a <-> writable_at rsegs mem3 a))
        by (eapply AC.a_call_post_frame; exact HPOST).
      (* the freed block: app memory below stklo, off the image and off the side stack *)
      assert (Hpin : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)) by (left; reflexivity).
      destruct (r16_blocks (APIf rc) _ mem md' phi (rnb g b) HAH' Hpin) as (Hplo & Hpall).
      (* callee-saved registers *)
      assert (G2 : getr regs3 2 = getr regs'' 2)
        by (apply (r16_regs_kept_at regs'' regs3 2 2 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G3 : getr regs3 3 = getr regs'' 3)
        by (apply (r16_regs_kept_at regs'' regs3 3 3 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G4 : getr regs3 4 = getr regs'' 4)
        by (apply (r16_regs_kept_at regs'' regs3 4 4 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G8 : getr regs3 8 = getr regs'' 8)
        by (apply (r16_regs_kept_at regs'' regs3 8 8 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G9 : getr regs3 9 = getr regs'' 9)
        by (apply (r16_regs_kept_at regs'' regs3 9 9 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G18 : getr regs3 18 = getr regs'' 18)
        by (apply (r16_regs_kept_at regs'' regs3 18 18 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G19 : getr regs3 19 = getr regs'' 19)
        by (apply (r16_regs_kept_at regs'' regs3 19 19 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G21 : getr regs3 21 = getr regs'' 21)
        by (apply (r16_regs_kept_at regs'' regs3 21 21 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G22 : getr regs3 22 = getr regs'' 22)
        by (apply (r16_regs_kept_at regs'' regs3 22 22 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G23 : getr regs3 23 = getr regs'' 23)
        by (apply (r16_regs_kept_at regs'' regs3 23 23 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G24 : getr regs3 24 = getr regs'' 24)
        by (apply (r16_regs_kept_at regs'' regs3 24 24 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G26 : getr regs3 26 = getr regs'' 26)
        by (apply (r16_regs_kept_at regs'' regs3 26 26 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G25 : getr regs3 25 = getr regs'' 25)
        by (apply (r16_regs_kept_at regs'' regs3 25 25 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G27 : getr regs3 27 = getr regs'' 27)
        by (apply (r16_regs_kept_at regs'' regs3 27 27 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      (* the window of the allocator entry, in the caller's terms *)
      assert (Haspc : AC.aspZ regs'' = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
      assert (HWv : forall x, AC.a_window AC.AK_FREE regs'' x <-> sp - 4096 <= x < sp)
        by (intros x; unfold AC.a_window, AC.AK_FREE; rewrite Haspc; tauto).
      (* ownership classes: the real stack, the side stack, their shadow bytes, the client cells, the shadow bytes
         of image bytes and the read-only image bytes are never the allocator's, in either state *)
      assert (NO1 : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                      AC.a_in_fs AC.ASYMS mem x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' x /\
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md'
                          (shadow_addr x)).
      { intros x Hx. exact (r16_no_own_cls (APIf rc) _ mem md' x HAH' Hx). }
      assert (Hfsmem : forall x, AC.a_in_fs AC.ASYMS mem x -> AC.a_in_fs AC.ASYMS mem3 x).
      { intros x (FSb & HFSr & Hw & Hr). exists FSb. split; [exact HFSr|]. split; [|exact Hr].
        intros k Hk. rewrite (HTP3 (Z.of_nat k) ltac:(lia)). exact (Hw k Hk). }
      assert (NO2 : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                      AC.a_in_fs AC.ASYMS mem x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 x /\
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 (shadow_addr x)).
      { intros x Hx.
        apply (r16_no_own_cls (APIf rc) ([] ++ g_H g) mem3 md3 x HAH3).
        destruct Hx as [Hx|Hx]; [left; rewrite HSTK3; exact Hx | right; exact (Hfsmem x Hx)]. }
      assert (NOc1 : forall x, AC.in_blocks AC.a_client x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' x)
        by (intros x Hx; exact (proj1 (r16_client (APIf rc) _ mem md' x HAH') Hx)).
      assert (NOc2 : forall x, AC.in_blocks AC.a_client x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 x)
        by (intros x Hx; exact (proj1 (r16_client (APIf rc) ([] ++ g_H g) mem3 md3 x HAH3) Hx)).
      assert (NOi1 : forall x, AC.a_in_img x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md'
                          (shadow_addr x))
        by (intros x Hx; exact (proj2 (r16_client (APIf rc) _ mem md' x HAH') Hx)).
      assert (NOi2 : forall x, AC.a_in_img x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 (shadow_addr x))
        by (intros x Hx; exact (proj2 (r16_client (APIf rc) ([] ++ g_H g) mem3 md3 x HAH3) Hx)).
      (* THE TRANSPORT: a byte the allocator entry may not touch keeps its value and its writability *)
      assert (KEEP : forall x, 0 <= x < 2 ^ 64 ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' x ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 x ->
                ~ (sp - 4096 <= x < sp) ->
                ~ (AC.a_errno AC.ASYMS <= x < AC.a_errno AC.ASYMS + 4) -> x <> AC.as_oom AC.ASYMS ->
                ~ (phi <= x < phi + rnb g b) ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx No1 No2 Nw Ne Noo Nt.
        apply (HFRM x Hx No1 No2); [ intro Hc; apply Nw; exact (proj1 (HWv x) Hc)
                                   | exact Ne | exact Noo | exact Nt]. }
      (* class A: the real stack at or above sp *)
      assert (KST : forall x, sp <= x <= g_S g ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. apply KEEP; try lia.
        - apply NO1. left. lia.
        - apply NO2. left. lia. }
      (* class F: the side stack's bytes *)
      assert (KFS : forall x, AC.a_in_fs AC.ASYMS mem x ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. pose proof Hx as Hx'. destruct Hx' as (FSb & HFSr & Hw & Hr).
        destruct (r16_fs_place (APIf rc) _ mem md' FSb HAH' Hw HFSr) as (HGT & Hend & Happ).
        pose proof (Happ x Hr) as Happx.
        unfold app_mem in Happx.
        apply KEEP.
        - lia.
        - exact (proj1 (NO1 x (or_intror Hx))).
        - exact (proj1 (NO2 x (or_intror Hx))).
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj2 (proj2 (Hpall x Hc)) Hx). }
      (* the frame bytes are on the real stack or in the side stack *)
      assert (HFRC : forall x, fr <= x < fr + 3136 ->
                AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                AC.a_in_fs AC.ASYMS mem x).
      { intros x Hx. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
        - left. rewrite Hlom. exact (Hreal x Hx).
        - right. exact (Hfs x Hx). }
      (* class B: the frame, on either arm *)
      assert (KFR : forall x, fr <= x < fr + 3136 ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. destruct (HFRC x Hx) as [Hc|Hc]; [|exact (KFS x Hc)].
        apply KEEP.
        - lia.
        - exact (proj1 (NO1 x (or_introl Hc))).
        - exact (proj1 (NO2 x (or_introl Hc))).
        - intro Hc2. exact (HAPART x Hx Hc2).
        - lia.
        - lia.
        - lia. }
      (* class C: the shadow bytes of real-stack and side-stack bytes *)
      assert (KSHX : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                       AC.a_in_fs AC.ASYMS mem x ->
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hcls.
        assert (Happx : app_mem x).
        { destruct Hcls as [Hc|Hc].
          - unfold app_mem. lia.
          - destruct Hc as (FSb & HFSr & Hw & Hr).
            destruct (r16_fs_place (APIf rc) _ mem md' FSb HAH' Hw HFSr) as (_ & _ & Happ). exact (Happ x Hr). }
        assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; exact Happx).
        pose proof (in_shadow_range _ Hshd) as Hrr.
        pose proof Hshd as Hshd'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ _)).
        - lia.
        - exact (proj2 (NO1 _ Hcls)).
        - exact (proj2 (NO2 _ Hcls)).
        - lia.
        - lia.
        - lia.
        - intro Hc. destruct (Hpall _ Hc) as (Happq & _).
          exact (app_not_shadow _ Happq Hshd). }
      assert (KSH : forall x, 0 <= x < 392 ->
                mbyte rsegs mem3 (Sfr fr + x) = mbyte rsegs mem (Sfr fr + x)).
      { intros x Hx. rewrite <- r16_sh8. apply KSHX. apply HFRC. lia. }
      (* class D: the shadow bytes of image bytes *)
      assert (KAG : forall x, AC.a_in_img x ->
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hx.
        pose proof (r16_img_range x Hx) as Himgb.
        assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; unfold app_mem; lia).
        pose proof (in_shadow_range _ Hshd) as Hrr.
        pose proof Hshd as Hshd'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ _)).
        - lia.
        - exact (NOi1 x Hx).
        - exact (NOi2 x Hx).
        - lia.
        - lia.
        - lia.
        - intro Hc. destruct (Hpall _ Hc) as (Happx & _).
          exact (app_not_shadow _ Happx Hshd). }
      (* class E: the musl client cells the sink words live in *)
      assert (KCL : forall x, AC.in_blocks AC.a_client x -> AC.a_in_img x ->
                ~ (AC.a_errno AC.ASYMS <= x < AC.a_errno AC.ASYMS + 4) -> x <> AC.as_oom AC.ASYMS ->
                mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hcl Himg Ne Noo.
        pose proof (r16_img_range x Himg) as Hr.
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (NOc1 x Hcl).
        - exact (NOc2 x Hcl).
        - lia.
        - exact Ne.
        - exact Noo.
        - intro Hc. exact (proj1 (proj2 (Hpall x Hc)) Himg). }
      (* class G: the image's read-only bytes holding the catalogue's row-name strings *)
      assert (KRO : forall x, 0x21140 <= x < 0x218f0 -> mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hx. pose proof (r16_ro_in x Hx) as Hro'. pose proof (r16_ro_img x Hro') as Himg.
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (AC.a_laws_ro_not_owned _ _ _ _ _ ALAWS _ mem md' x HAH' Hro').
        - exact (AC.a_laws_ro_not_owned _ _ _ _ _ ALAWS _ mem3 md3 x HAH3 Hro').
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj1 (proj2 (Hpall x Hc)) Himg). }
      (* the image's RELRO bytes (the row table at BA_FR + 72, the catalogue row at mrow): frame_facts says the
         runtime owns none of them, in any state *)
      assert (KREL : forall a, in_globals AF.frame_RELRO a -> mbyte rsegs mem3 a = mbyte rsegs mem a).
      { pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRimg & HOWNG & _).
        intros a Ha. pose proof (r16_relro_range a Ha) as Hra.
        exact (proj1 (KEEP a ltac:(lia)
                        (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha) (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha)
                        ltac:(lia) ltac:(lia) ltac:(lia)
                        (fun Hc => proj1 (proj2 (Hpall a Hc)) (HRimg a Ha)))). }
      (* the image's RELRO bytes: frame_facts says the runtime owns none of them, in any state *)
      assert (Hgimg3 : G_img_c B AF.frame_RELRO mem3).
      { pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRimg & HOWNG & _).
        intros a Ha. pose proof (Hgimg a Ha) as Hg0. pose proof (r16_relro_range a Ha) as Hra.
        rewrite SEGS in Hg0 |- *.
        destruct (KEEP a ltac:(lia)
                    (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha) (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha)
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    (fun Hc => proj1 (proj2 (Hpall a Hc)) (HRimg a Ha))) as (Hmb & _).
        rewrite Hmb. exact Hg0. }
      assert (Hsn3 : sink_none B mem3 md3).
      { pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _).
        pose proof HFRAc as (A2 & sp2 & s52 & _ & _ & _ & Hsnc & _).
        destruct Hsnc as ((Hthrm & Hlockm) & Hohd & Hfd).
        destruct HMOD as (lz & mt & vm' & Emd3).
        split; [split|split].
        - eapply YI14.val_mem_frame; [|exact Hthrm].
          intros x Hx. rewrite Hthr in Hx. cbn in Hx. try rewrite SEGS.
          apply KCL.
          + apply r16_client_a. lia.
          + exact (r16_img_cov_in 0x5fc8e1 0x5fc8e2 x r16_sink_cov_a ltac:(lia)).
          + lia.
          + lia.
        - eapply YI14.val_mem_frame; [|exact Hlockm].
          intros x Hx. rewrite Hlock in Hx. cbn in Hx. try rewrite SEGS.
          apply KCL.
          + apply r16_client_b. lia.
          + exact (r16_img_cov_in 0x5fcd40 0x5fcd50 x r16_sink_cov_b ltac:(lia)).
          + lia.
          + lia.
        - intros k Hk. pose proof (Hohd k Hk) as Hk'.
          try rewrite SEGS in Hk'. try rewrite SEGS.
          rewrite KCL.
          + exact Hk'.
          + apply r16_client_b. rewrite Hhead. lia.
          + eapply r16_img_cov_in; [exact r16_sink_cov_b | rewrite Hhead; lia].
          + rewrite Hhead. lia.
          + rewrite Hhead. lia.
        - rewrite Emd3. exact Hfd. }
      assert (Hwin3 : stk rsegs mem3 (g_S g - AF.SLOT_STACK) (g_S g)).
      { pose proof Hwin as HwinD. destruct HwinD as (W0 & W1 & W).
        split; [exact W0|]. split; [exact W1|].
        intros x Hx.
        destruct (Z_lt_le_dec x sp) as [Hbelow|Habove].
        - destruct (Z_lt_le_dec x (sp - 4096)) as [Hlow|Hupw].
          + assert (Hcls : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END) by lia.
            destruct (W x Hx) as (Hw & bb & Hb).
            destruct (KEEP x ltac:(lia) (proj1 (NO1 x (or_introl Hcls)))
                        (proj1 (NO2 x (or_introl Hcls))) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as (Hmb & Hwr).
            split; [exact (proj1 Hwr Hw)|]. exists bb. rewrite <- Hb. exact Hmb.
          + assert (Hwx : AC.a_window AC.AK_FREE regs'' x) by (apply (HWv x); lia).
            split; [exact (HWIN3 x Hwx) | exact (HWP x Hwx)].
        - destruct (W x Hx) as (Hw & bb & Hb).
          destruct (KST x ltac:(lia)) as (Hmb & Hwr).
          split; [exact (proj1 Hwr Hw)|]. exists bb. rewrite <- Hb. exact Hmb. }
      assert (HAG3 : forall a, in_globals AF.frame_AG a -> addressable mem3 a 1).
      { intros a Hin. apply (r16_addr_keep mem mem3 a 1 (HAG a Hin)).
        intros i Hi. replace (a + i) with a by lia. apply KAG. exact (r16_ag_img a Hin). }
      (* the slot window outside the frame stays addressable: its shadow bytes are real-stack shadow *)
      assert (HWA3 : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
                addressable mem3 a 1).
      { intros a H1 H2. apply (r16_addr_keep mem mem3 a 1 (HWA a H1 H2)).
        intros i Hi. replace (a + i) with a by lia. apply KSHX. left. lia. }
      (* the frame record of the side arm *)
      assert (HREC3 : FSREC fr mem -> FSREC fr mem3).
      { intros HR. apply (r16_fsrec_keep mem mem3 fr HR HTP3).
        intros x Hx _. exact (proj1 (KFS x Hx)). }
      (* the spills and the frame words at mem3 *)
      assert (Q336 : q64 mem3 (A + 336) fr).
      { apply (r16_keep_bytes mem mem3 _ _ Hspill). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Q40 : q64 mem3 (A + 40) fr).
      { apply (r16_keep_bytes mem mem3 _ _ Hfr40). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Qsaved : bytes_at rsegs mem3 (g_S g - 104) (saved_bytes ra g)).
      { apply (r16_keep_bytes mem mem3 _ _ Hsaved).
        unfold saved_bytes. rewrite !length_app, !length_le8. cbn [Nat.add].
        change (Z.of_nat 104) with 104. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Qhdr1 : q64 mem3 fr 0x41b58ab3).
      { apply (r16_keep_bytes mem mem3 _ _ Hhdr1). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (Qhdr2 : q64 mem3 (fr + 16) AF.ENTRY).
      { apply (r16_keep_bytes mem mem3 _ _ Hhdr2). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QOUR : OURb g fr mem3).
      { unfold OURb in *. apply (r16_keep_bytes mem mem3 _ _ HOUR). rewrite OUR_length.
        change (Z.of_nat 6) with 6. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (Qsh : exists sh, bytes_at rsegs mem3 (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
      { destruct Hsh as (sh & Hb & Hl). exists sh. split; [|exact Hl].
        apply (r16_keep_bytes mem mem3 _ _ Hb). rewrite Hl. intros x Hx.
        rewrite FRAME_SHADOW_val in Hx. change (Z.of_nat (Z.to_nat 392)) with 392 in Hx.
        replace x with (Sfr fr + (x - Sfr fr)) by lia. apply KSH. lia. }
      (* the turn-(S b) records, in the frame *)
      assert (QIDB : IDBr g fr (RID (g_in g) (S b)) mem3).
      { rewrite EID. unfold IDBr in *. apply (r16_keep_bytes mem mem3 _ _ HIDB). rewrite r16_rid_len.
        change (Z.of_nat 38) with 38. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QFGB : FGBr g fr (RFG (g_in g) (S b)) mem3).
      { rewrite EFG. unfold FGBr in *. apply (r16_keep_bytes mem mem3 _ _ HFGB). rewrite r16_rfg_len.
        change (Z.of_nat 72) with 72. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QCUR : CUR g 7 regs3).
      { destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|].
        unfold rg in Hc23, Hc25 |- *.
        split; [rewrite G23, E23; exact Hc23 | rewrite G25, E25; exact Hc25]. }
      (* FRA's input facts after the call: the input block (p, n) is a live entry block (in both heaps), apart from
         the freed block, below stklo and off the image, so its bytes and shadow bytes are kept *)
      destruct (fra_in B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md' HFRAc) as (Hinb0 & Hinblk0).
      assert (KIN : forall x, g_p g <= x < g_p g + g_n g ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hx.
        destruct (Hinblk0 ltac:(clear - Hx; lia)) as (HinH & _).
        assert (Hib : AC.in_blocks (hb1 phi (rnb g b) ++ g_H g) x)
          by (exists (g_p g), (g_n g); split; [apply in_or_app; right; exact HinH | exact Hx]).
        assert (Hib3 : AC.in_blocks ([] ++ g_H g) x)
          by (exists (g_p g), (g_n g); split; [exact HinH | exact Hx]).
        destruct (r16_no_own_blk (APIf rc) _ mem md' x HAH' Hib) as (No1 & No1s).
        destruct (r16_no_own_blk (APIf rc) _ mem3 md3 x HAH3 Hib3) as (No2 & No2s).
        destruct (r16_blocks (APIf rc) _ mem md' (g_p g) (g_n g) HAH'
                    (in_or_app _ _ _ (or_intror HinH))) as (Hpend & Hball).
        destruct (Hball x Hx) as (Happx & Himgx & _).
        destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md' phi (rnb g b) (g_p g) (g_n g) HAH' HinH)
          as [D|D].
        all: assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; exact Happx).
        all: pose proof (in_shadow_range _ Hshd) as Hrr.
        all: pose proof Hshd as Hshd'.
        all: unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        all: pose proof Happx as Happx'; unfold app_mem in Happx'.
        all: split;
          [ refine (proj1 (KEEP x _ No1 No2 _ _ _ _));
            [ clear - Happx' HP64 HLMv HHMv HAPPv; lia
            | clear - Hx Hpend Hstklo' HSS HS4; lia
            | intro Hc; exact (Himgx (errno_in_img x Hc))
            | intro Hc; rewrite Hc in Himgx; exact (Himgx oom_in_img)
            | clear - Hx D; lia ]
          | refine (proj1 (KEEP (shadow_addr x) _ No1s No2s _ _ _ _));
            [ clear - Hshd' HP64; lia
            | clear - Hshd' Hhigh Hstklo' HSS HS4; lia
            | clear - Hshd' HERRv; lia
            | clear - Hshd' HOOMv; lia
            | intro Hc; destruct (Hpall _ Hc) as (Happq & _); exact (app_not_shadow _ Happq Hshd) ] ]. }
      assert (QINB : bytes_at rsegs mem3 (g_p g) (g_in g)).
      { apply (r16_keep_bytes mem mem3 _ _ Hinb0). intros x Hx.
        exact (proj1 (KIN x ltac:(clear - Hx; unfold g_n, nlen; lia))). }
      assert (QINAD : 0 < g_n g -> addressable mem3 (g_p g) (g_n g)).
      { intros Hn. destruct (Hinblk0 Hn) as (_ & Had). apply (r16_addr_keep mem mem3 _ _ Had).
        intros i Hi. exact (proj2 (KIN (g_p g + i) ltac:(clear - Hi; lia))). }
      (* FRA at the exit: the live list is g_H g, hb = [] *)
      assert (HFRAx : FRA B APIf ra g fr [] regs3 mem3 md3).
      { apply (sl_mid B APIf ra g fr (hb1 phi (rnb g b)) [] regs'' mem md' regs3 mem3 md3
                 (fun a => phi <= a < phi + rnb g b) AC.AK_FREE HFRAc HPOST).
        - cbn [length]. lia.
        - exact Hsn3.
        - exact Hgimg3.
        - exact Qhdr1.
        - exact Qhdr2.
        - intros A2 HA2 HA2r. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r16_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2. exact Q336.
        - intros A2 HA2 HA2r v Hv. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r16_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2.
          apply (r16_keep_bytes mem mem3 _ _ Hv). rewrite length_le8.
          change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))).
        - intros A2 HA2 HA2r. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r16_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2. exact Q40.
        - exact Qsh.
        - exact Qsaved.
        - exact Hwin3.
        - exact HAG3.
        - exact HWA3.
        - exact HREC3.
        - exact QINB.
        - exact QINAD.
        - rewrite G2; reflexivity.
        - rewrite G3; reflexivity.
        - rewrite G4; reflexivity.
        - rewrite G8; reflexivity.
        - rewrite G9; reflexivity.
        - rewrite G19; reflexivity.
        - rewrite G26; reflexivity. }
      (* ENT at the exit: the touched bytes are the freed block *)
      assert (HENTx : ENT APIf g [] mem3 md3).
      { apply (ent_call B APIf ra g fr (hb1 phi (rnb g b)) [] regs'' mem md' regs3 mem3 md3
                 (fun a => phi <= a < phi + rnb g b) AC.AK_FREE HENTc HFRAc HPOST).
        - unfold AC.AK_FREE. rewrite HFN. lia.
        - intros a Ha. cbv beta in Ha. destruct (Hpall a Ha) as (Happ & Himg & _).
          split; [exact Happ|]. split; [lia|]. split; [exact Himg|].
          intros (q & k & Hin & Hr).
          destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md' phi (rnb g b) q k HAH' Hin)
            as [D|D]; lia.
        - exact HKERR. }
      (* RBE at the exit *)
      assert (HRBE3 : RBE g fr regs3 mem3).
      { destruct HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
                          S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA & HID38 & HNM & HOUR6 & HTBL &
                          HBOX & HMROW & HPRA & S152 & S112 & HFG72 & S160).
        unfold PRA in HPRA.
        destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
        assert (E9' : getr regs3 9 = getr regs 9) by (rewrite G9; exact E9).
        assert (HA0 : 0 <= A) by lia.
        assert (HA1 : A + 448 <= 2 ^ 64) by lia.
        assert (HKA : forall off, 0 <= off <= 440 -> forall x, A + off <= x < A + off + 8 ->
                  mbyte rsegs mem3 x = mbyte rsegs mem x)
          by (intros off Hoff x Hx; exact (proj1 (KST x ltac:(lia)))).
        assert (K : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs3 mem3 off v)
          by (intros off v Hoff Hs; exact (r16_spill_keep regs regs3 mem mem3 A off v Hr9 HA0 HA1 Hoff E9'
                                             (HKA off Hoff) Hs)).
        unfold RBE.
        do 21 (split; [apply K; [lia | assumption]|]).
        split.
        { unfold OUTA in *. apply (r16_addr_keep mem mem3 (fr + 544) 1492 HOUTA).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { apply (r16_addr_keep mem mem3 (fr + 2176) 38 HID38).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { intros Hnm. destruct (HNM Hnm) as (Hok & Hbs & Had & Hpos & Hhi).
          destruct Hnm as (Hh & Hrn).
          pose proof (r16_rname (g_in g) Hh Hrn) as Hrng.
          pose proof (r16_nb_len (g_in g)) as Hlen.
          split; [exact Hok|]. split.
          - apply (r16_keep_bytes mem mem3 _ _ Hbs). intros x Hx. apply KRO. lia.
          - split; [|split; [exact Hpos | exact Hhi]].
            apply (r16_addr_keep mem mem3 _ _ Had). intros i Hi. apply KAG. apply r16_ro_img. apply r16_ro_in.
            lia. }
        split.
        { apply (r16_addr_keep mem mem3 (fr + 2624) 6 HOUR6).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { apply (r16_keep_bytes mem mem3 _ _ HTBL). rewrite r16_tbl_len.
          intros x Hx. apply KREL. apply r16_relro_in. clear - Hx. unfold BAC.BA_FR in Hx. lia. }
        split.
        { apply (r16_keep_bytes mem mem3 _ _ HBOX). rewrite r16_box_len.
          intros x Hx. apply KRO. clear - Hx. unfold BOXA in Hx. lia. }
        split.
        { apply (r16_keep_bytes mem mem3 _ _ HMROW). unfold rt_mb. rewrite r16_row_len. change (Z.of_nat 296) with 296.
          pose proof (r16_istar_range (g_in g)) as Hist.
          intros x Hx. apply KREL. apply r16_relro_in. clear - Hx Hist. unfold mrow, CAT, CAT_ROW in Hx. lia. }
        split; [unfold PRA; do 10 (split; [apply K; [lia | assumption]|]); apply K; [lia | assumption]|].
        split; [apply K; [lia | assumption]|].
        split; [apply K; [lia | assumption]|].
        split.
        { apply (r16_addr_keep mem mem3 (fr + 2256) 72 HFG72).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        apply K; [lia | assumption]. }
      (* the exit cut *)
      rewrite <- SEGS. apply Hexit.
      exists regs3, mem3, md3, fr.
      split; [reflexivity|].
      split; [exact HFRAx|].
      split; [exact HENTx|].
      split; [exact Hgn|].
      split; [exact Hb6|].
      split; [unfold rg in Hr22 |- *; rewrite G22, E22; exact Hr22|].
      split; [exact QOUR|].
      split; [exact HRBE3|].
      split; [unfold rg in Hr21 |- *; rewrite G21, E21; exact Hr21|].
      split.
      { split; [exact Hb6|].
        split; [exact QCUR|].
        split; [exact QOUR|].
        split; [unfold rg in Hr22 |- *; rewrite G22, E22; exact Hr22|].
        split; [exact QIDB | exact QFGB]. }
      unfold rg. rewrite G27, E27. exact Hr27.
Qed.

End R16.
