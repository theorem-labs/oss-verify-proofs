(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 3942 of its 4075 lines of code are new or changed and 878 lines of the source are left out. *)
(* Segment R10 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the round-trip kind
   dispatch of turn b, from the cut 0x817a4 (after reac_ctrl_parse) to the five cuts the five arms reach
   (plan-asan-ubsan.md section 2 row R10 and forms-asan-ubsan-v190.md S_R10).  rule 24: no function proved (a slot
   segment).  v1.9 against v1.8: every pc +0x64, the count n_b in s2 (v1.8 s9), the reply slots' spills
   [A + 240] / [A + 232] / [A + 224] (v1.8 [A + 232] / [A + 224] / [A + 216]), the constant 32 in s11 (v1.8 s2).

   The block 0x817a4-0x817b4 writes the three metadata bytes of the reply slots: [S(fr) + 306] = 2 (the 2 bytes at
   fr + 2448), [S(fr) + 308] = 0 and [S(fr) + 312] = 0 (the 8 bytes at fr + 2464 and at fr + 2496).  Then the
   dispatch on the turn index b (s6) and on the parse kind (a0):
     0x817b8 `blt s5,s6,817f8`   leaves for b = 5, 6 (s5 = 4 at the entry cut);
     0x817c4 `bgeu a1,a3,8186c`  leaves for b = 0, 1, 2 (a1 = b - 3 unsigned, a3 = 2);
     b = 3, 4: 0x817cc `beq a0,a1` with a1 = 5 to 0x817d4, then REPLY@0x817e8 -> 0x817ec;
     b = 6:    0x81800 / 0x81808 / 0x81810 `beq a0,11` to 0x81818, FRAG@0x81830 -> 0x81834 (Inv_B81834_at);
     b = 5:    0x81800 to 0x818ec, 0x818f0 `beq a0,11`, FRAG@0x81910 -> 0x81914 (Inv_B81914_at);
     b = 0:    0x8186c `bnez s6` not taken, the two ports metadata bytes [S(fr) + 316] = 0 / [S(fr) + 317] = 4
               (the 12 bytes at fr + 2528), 0x8187c `beq a0,9`, the block-sum prologue -> 0x818a8 (Inv_B818a8_at);
     b = 1, 2: 0x8186c taken, 0x81920 `beq a0,5`, the block-sum prologue -> 0x8194c (Inv_B8194c_at).
   0x817d0 (and 0x817f4 / 0x81814 / 0x81880 / 0x818f4 / 0x81924 on the other arms) is the abort edge `j 82fa4`,
   NOT an instrumented shadow check: each is the fall-through of the kind compare just above it, shown not taken
   from the arm's kind, rt_k (g_in g) b (9 for b = 0, 5 for b = 1 .. 4, 11 for b = 5, 6; r10_rtk, a model fact
   computed over the 11 catalogue rows).  The segment owns no UBSan trap branch of section 1.7.

   The two FRAG calls (0x81830, 0x81910) are taken on reac_ctrl_identity_fragment_c.v and the REPLY call
   (0x817e8) on reac_ctrl_identity_reply_c.v, never on their code; both are Section hypotheses.  mem_inv comes
   through MemNorm.evt_normalize from ro_agree, never from a cut.  The REPLY call's class-1 side-stack package is
   rebuilt at the call from FRA (Tac_fsfree fra_fp), with the three metadata stores of 0x817a8-0x817b0 in its
   write list, and carried across those stores (r10_fp_head / r10_tls_head).

   Cuts: seg_R10 is S_R10 on the official cuts, entry Inv_B817a4_at (the fragment record pointer [A + 112] =
   fr + 2256 the fragment arms reload at 0x81818 / 0x818f8 is RBE's).  Every exit carries s11 = 32 (rg regs 27 32:
   no s11 write in the segment, the callees keep it).  The b = 0 and b = 1, 2 exits Inv_B818a8_at / Inv_B8194c_at
   carry the room word
   a3 = -(Phi + 18) of the block-sum prologue (0x81888-0x8189c / 0x8192c-0x81940, r10_room).  The b = 6 exit
   Inv_B81834_at is prover a Theorem Labs lane's R12X: b = 6, n_b <> 0, s4 = Phi, the identity record RID 6, the fragment call's
   new record RFG 7 at fr + 2256 and its 72 addressable bytes, a0 = fg_rf, and on the closing class (turn 6 is
   FgClose, RtmB rb_rtm_close) the three out cells of the fragment contract's FgClose post.  RBE's adopt-10
   conjunct, the fragment record's 72 addressable bytes, is carried because no arm writes its shadow bytes
   S(fr) + 282 .. 290 (the arms' shadow stores are 306 / 308 / 312 / 316 / 317). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_identity_reply_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP asan_stack_malloc_c bcmp_wrap_c memcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply RcFrag.
Import ListNotations.
Open Scope Z_scope.

Module RPC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_reply_c.
Module FGC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.
Module RFP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memcmp_c.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Module RRp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.
Module RFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.

(* A byte store of a register whose value is not a literal (0x817a8 `sb a3,306(s3)`, 0x81874 `sb a2,317(s3)`): the
   engine's cell_of_bytes knows le8 / le4 / le2 / a singleton / le1 (zxb b), not le1 of a register.  le1 v is
   [Z_to_bv 8 (bv_unsigned v)] by conversion, so one extra branch serves it (as lib/B/Prog/Seg/A4.v, R9.v). *)
Local Ltac fix_lit_store ::=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) => idtac
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | _ => idtac
  end.

(* The branch conditions of the dispatch are closed terms once the turn index and the kind are literals, so the
   engine's solve_cond or a plain computation decides them. *)
Local Ltac brT :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota | symmetry; first [solve_cond | vm_compute; reflexivity]]
  end.
Local Ltac brF :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota | symmetry; first [solve_cond | vm_compute; reflexivity]]
  end.

(* A register equation of the final state: the engine normalizes literal sums while it steps. *)
Local Ltac r10_req := first [reflexivity | rewrite lit_add_lit; reflexivity].

(* One byte of a byte-list fact, by its index. *)
Lemma r10_bat_idx : forall m a l (i : nat) (x : byte) (b : Z),
  bytes_at rsegs m a l -> nth_error l i = Some x -> b = a + Z.of_nat i -> bytes_at rsegs m b [x].
Proof.
  intros m a l i x b (H0 & H1 & H) Hx ->.
  assert (Hi : (i < length l)%nat) by (apply nth_error_Some; rewrite Hx; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros j Hj. cbn [length] in Hj. assert (Ej : j = 0%nat) by lia. subst j.
  rewrite Z.add_0_r. rewrite (H i Hi). cbn [nth_error]. exact Hx.
Qed.
Local Ltac r10_bi Hb i := eapply (r10_bat_idx _ _ _ i); [exact Hb | reflexivity | cbn [Z.of_nat]; lia].

Lemma r10_cb_len : forall m a n bs, rw_cells rsegs m a [CB n bs] -> length bs = n.
Proof. intros m a n bs ((Hwf & _) & _). cbn [cells_wf cell_wf] in Hwf. exact (proj1 Hwf). Qed.

(* The room word of the block-sum prologue (li a0,-18; sub a0,a0,s4; sltiu a3,a0,-17; neg a3,a3; and a3,a3,a0):
   with s4 = Phi and Phi + 18 below 2^64, sltiu gives 1, neg the all-ones mask, so a3 = a0 = -(Phi + 18). *)
Lemma r10_room : forall phi, 0 <= phi -> phi + 18 < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltiu (Z_to_bv 64
      (18446744073709551598 - bv_unsigned (Z_to_bv 64 phi))) (-17)))))
    (bv_unsigned (Z_to_bv 64 (18446744073709551598 - bv_unsigned (Z_to_bv 64 phi)))))
  = Z_to_bv 64 (- (phi + 18)).
Proof.
  intros phi H0 H1.
  assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold v_sltiu.
  rewrite (MState.unsigned_lit phi) by lia.
  rewrite (MState.unsigned_lit (18446744073709551598 - phi)) by lia.
  replace (bv_wrap 64 (-17)) with 18446744073709551599 by (vm_compute; reflexivity).
  rewrite (proj2 (Z.ltb_lt (18446744073709551598 - phi) 18446744073709551599)) by lia.
  rewrite (MState.unsigned_lit 1) by lia.
  replace (bv_unsigned (Z_to_bv 64 (0 - 1))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  apply bv_eq. rewrite !MState.unsigned_lit_wrap. rewrite HP. Z.div_mod_to_equations. lia.
Qed.

(* ---- the run of the b = 0 arm: 0x817a4 -> 0x818a8 ---- *)
(* 0x817a4 li a3,2; sb a3,306(s3); sb zero,308(s3); sb zero,312(s3); li a2,4; blt s5,s6 (not taken: b = 0);
   addi a1,s6,-3; li s5,36; bgeu a1,a3 (taken); bnez s6 (not taken); sb zero,316(s3); sb a2,317(s3); li a1,9;
   beq a0,a1 (taken: a0 = 9); then the block-sum prologue `li a1,0; li a0,-18; sub a0,a0,s4; addi a2,s4,18;
   sltiu a3,a0,-17; neg a3,a3; and a3,a3,a0; li a4,32; mv a0,a2`, so at the loop head a0 = a2 = Phi_r + 18,
   a1 = 0 (the running sum at i = 0) and a4 = 32. *)
Lemma r10_cfg0 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (junk : list byte),
    s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 9 ->
    0 <= phi -> phi + 18 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 12 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte) (l12 : list byte) (c3 c4 : byte),
         ms' = MS R F (Z_to_bv 64 0x818a8) fc None m1 (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
         getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l12 /\ length l12 = 12%nat /\
         bytes_at rsegs m1 (bv_unsigned s3 + 316) [c3] /\ bv_signed c3 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 317) [c4] /\ bv_signed c4 = 4)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi junk -> -> -> -> Hphi0 Hphi1 HC HMI.
  pose proof (r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 [|j8 [|j9 [|j10 [|j11 [|? ?]]]]]]]]]]]]];
    cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 5 step.
  step. brF.
  do 2 step.
  step. brT.
  step. brF.
  do 3 step.
  step. brT.
  do 9 step.
  apply evt_done. do 2 eexists. eexists. do 2 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [r10_req|]. split; [r10_req|]. split; [r10_req|]. split; [r10_req|].
  split; [rewrite <- (r10_room phi) by lia; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
  split; [exact Hb|].
  split; [cbn [length]; reflexivity|].
  split; [r10_bi Hb 10%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10_bi Hb 11%nat|].
  vm_compute; reflexivity.
Qed.

(* ---- the run of the b = 1, 2 arm: 0x817a4 -> 0x8194c ---- *)
(* 0x817a4 .. 0x817c4 as above (bgeu taken: b - 3 >= 2 unsigned), 0x8186c bnez s6 (taken), 0x8191c li a1,5;
   0x81920 beq a0,a1 (taken: a0 = 5), and the prologue twin 0x81928-0x81948. *)
Lemma r10_sum12 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi bz : Z) (junk : list byte),
    s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 bz -> a0 = Z_to_bv 64 5 ->
    (bz = 1 \/ bz = 2) ->
    0 <= phi -> phi + 18 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 12 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte) (l12 : list byte),
         ms' = MS R F (Z_to_bv 64 0x8194c) fc None m1 (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
         getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l12 /\ length l12 = 12%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi bz junk -> -> -> -> Hbz Hphi0 Hphi1 HC HMI.
  pose proof (r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 [|j8 [|j9 [|j10 [|j11 [|? ?]]]]]]]]]]]]];
    cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct Hbz as [-> | ->].
  all: do 5 step.
  all: step; brF.
  all: do 2 step.
  all: step; brT.
  all: step; brT.
  all: do 1 step.
  all: step; brT.
  all: do 9 step.
  all: apply evt_done; do 2 eexists; eexists.
  all: split; [reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [reflexivity|].
  all: split; [r10_req|]; split; [r10_req|]; split; [r10_req|]; split; [r10_req|].
  all: split; [rewrite <- (r10_room phi) by lia; reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [exact HMI|].
  all: destruct HC as ((_ & Hb) & _); cbn [cells_bytes cbytes app] in Hb.
  all: split; [exact Hb | cbn [length]; reflexivity].
Qed.

(* ---- the head of the three call arms: 0x817a4 and the kind dispatch ---- *)
(* b = 3, 4: 0x817a4 .. 0x817cc `beq a0,a1` taken, so the abort edge 0x817d0 is not reached. *)
Lemma r10_head_reply :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 bz -> a0 = Z_to_bv 64 5 -> (bz = 3 \/ bz = 4) ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 5) (Z_to_bv 64 5) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x817d4) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz junk -> -> -> Hbz HC HMI.
  pose proof (r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|? ?]]]]]]]]; cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct Hbz as [-> | ->].
  all: do 5 step.
  all: step; brF.
  all: do 2 step.
  all: step; brF.
  all: do 1 step.
  all: step; brT.
  all: apply evt_done; do 5 eexists.
  all: split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [exact HMI|].
  all: destruct HC as ((_ & Hb) & _); cbn [cells_bytes cbytes app] in Hb.
  all: split; [r10_bi Hb 0%nat|].
  all: split; [vm_compute; reflexivity|].
  all: split; [r10_bi Hb 2%nat|].
  all: split; [vm_compute; reflexivity|].
  all: split; [r10_bi Hb 6%nat|].
  all: split; [vm_compute; reflexivity|].
  all: split; [exact Hb | cbn [length]; reflexivity].
Qed.

(* b = 6: 0x817b8 taken to 0x817f8, 0x81800 not taken, 0x81808 not taken, 0x81810 `beq a0,11` taken to
   0x81818 (the abort edge 0x81814 not reached). *)
Lemma r10_head_frag6 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 6 -> a0 = Z_to_bv 64 11 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) (Z_to_bv 64 11) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81818) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk -> -> -> HC HMI.
  pose proof (r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|? ?]]]]]]]]; cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 5 step.
  step; brT.
  do 2 step.
  step; brF.
  step.
  step; brF.
  step.
  step; brT.
  apply evt_done. do 5 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
  split; [r10_bi Hb 0%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10_bi Hb 2%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10_bi Hb 6%nat|].
  split; [vm_compute; reflexivity|].
  split; [exact Hb | cbn [length]; reflexivity].
Qed.

(* b = 5: 0x817b8 taken to 0x817f8, 0x81800 `beq s6,5` taken to 0x818ec, 0x818f0 `beq a0,11` taken to 0x818f8
   (the abort edge 0x818f4 not reached). *)
Lemma r10_head_frag5 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 5 -> a0 = Z_to_bv 64 11 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) (Z_to_bv 64 11) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x818f8) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk -> -> -> HC HMI.
  pose proof (r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|? ?]]]]]]]]; cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 5 step.
  step; brT.
  do 2 step.
  step; brT.
  step.
  step; brT.
  apply evt_done. do 5 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
  split; [r10_bi Hb 0%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10_bi Hb 2%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10_bi Hb 6%nat|].
  split; [vm_compute; reflexivity|].
  split; [exact Hb | cbn [length]; reflexivity].
Qed.

(* ---- the REPLY call 0x817d4-0x817e8, on reac_ctrl_identity_reply_c.v ----
   a0 = Phi_r (0x817d4 mv a0,s4), a1 = n_b (0x817d8 mv a1,s2; v1.8 had s9) and the three out slots of the frame
   from the spills [A + 240] = fr + 2448, [A + 232] = fr + 2464, [A + 224] = fr + 2496 (0x817dc / 0x817e0 /
   0x817e4; v1.8 had [A + 232] / [A + 224] / [A + 216]). *)
Lemma r10_reply_call : RPC.reac_ctrl_identity_reply_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi N fr FS : Z) (g50 ja jp jn : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s4 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= N < 2 ^ 64 ->
    0 <= fr -> fr + 3136 <= 2 ^ 64 -> fr mod 32 = 0 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 -> RPC.REAC_CTRL_IDENTITY_REPLY_K <= spv ->
    HIGHMEM_BEG <= spv - RPC.REAC_CTRL_IDENTITY_REPLY_K -> spv <= APPMEM_END ->
    ro_cells rsegs m (bv_unsigned s1 + 240) [C8 (Z_to_bv 64 (fr + 2448))] ->
    ro_cells rsegs m (bv_unsigned s1 + 232) [C8 (Z_to_bv 64 (fr + 2464))] ->
    ro_cells rsegs m (bv_unsigned s1 + 224) [C8 (Z_to_bv 64 (fr + 2496))] ->
    stk rsegs m (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv ->
    mem_inv rsegs m ->
    length g50 = 50%nat -> (50 <= N -> bytes_at rsegs m phi g50) ->
    (phi + 50 <= spv - RPC.REAC_CTRL_IDENTITY_REPLY_K \/ spv <= phi) ->
    (fr + 3136 <= phi \/ phi + 50 <= fr) ->
    (fr + 3136 <= spv - RPC.REAC_CTRL_IDENTITY_REPLY_K \/ spv <= fr) ->
    rw_cells rsegs m (fr + 2448) [CB 2 ja] -> rw_cells rsegs m (fr + 2464) [CB 8 jp] ->
    rw_cells rsegs m (fr + 2496) [CB 8 jn] ->
    asan_cells m -> shadow_rw m ->
    addressable m (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) RPC.REAC_CTRL_IDENTITY_REPLY_K ->
    (50 <= N -> addressable m phi 50) ->
    addressable m (fr + 2448) 2 -> addressable m (fr + 2464) 8 -> addressable m (fr + 2496) 8 ->
    (fr + 3136 <= RT_LO \/ RT_HI <= fr) ->
    addressable m PC.REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m BW.REAL_BCMP (le8 (wa BW.BCMP)) ->
    bytes_at rsegs m BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) ->
    bytes_at rsegs m BW.GOT_CF (le8 (wa BW.CF)) ->
    bytes_at rsegs m (BW.CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (BW.CF + 255) [Z_to_bv 8 1] ->
    RFP.fp [1%nat] m (bv_unsigned tp) FS (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv
      (RPC.reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) spv)
      (RPC.reac_ctrl_identity_reply_D phi N (fr + 2448) (fr + 2464) (fr + 2496)) ->
    RPC.reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS
      (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x817ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (RRp.reply_ret phi N (fr + 2448) (fr + 2464) (fr + 2496) g50) /\
         munch (RPC.reac_ctrl_identity_reply_fp phi N (fr + 2448) (fr + 2464) (fr + 2496) spv g50 ++
                RFP.fp_w [1%nat] FS ++
                [(shadow_addr (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv /\
         (RRp.reply_ok phi N (fr + 2448) (fr + 2464) (fr + 2496) g50 = true ->
            rw_cells rsegs m' (fr + 2448) [CB 2 (RRp.reply_addr g50)] /\
            rw_cells rsegs m' (fr + 2464) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
            rw_cells rsegs m' (fr + 2496) [CB 8 (le8 (Z_to_bv 64 (RRp.ir_s g50 - 13)))]) /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) RPC.REAC_CTRL_IDENTITY_REPLY_K /\
         RFP.fp [1%nat] m' (bv_unsigned tp) FS (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv
           (RPC.reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) spv)
           (RPC.reac_ctrl_identity_reply_D phi N (fr + 2448) (fr + 2464) (fr + 2496)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817d4) fc None m (seg_rom rsegs)).
Proof.
  intros REPLY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi N fr FS g50 ja jp jn -> -> -> -> HA0 HA248 Hphi0 Hphi50 HN Hfr0 Hfr64 Hfr32
    Hsp64 Hsp16 HspK HHM HAE RO1 RO2 RO3 ST HMI Hg50l Hg50b HphiW HphiF HfrW RWa RWp RWn HAC HSW
    ADw ADphi ADa ADp ADn HRT ADbc HB1 HB2 HB3 HB4 HB5 FPp TLS.
  unfold RPC.reac_ctrl_identity_reply_contract in REPLY. cbv zeta in REPLY.
  assert (HK : RPC.REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite EA in RO1, RO2, RO3.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply REPLY with (fr := phi) (len := N) (pa := fr + 2448) (pp := fr + 2464) (pn := fr + 2496)
      (S := spv) (FS := FS) (g := g50) (ja := ja) (jp := jp) (jn := jn).
    all: rewrite ?Esp.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hsp16.
    - exact HspK.
    - exact ST.
    - exact HMI.
    - exact Hg50l.
    - intros _ H50. split; [lia|]. split; [exact (Hg50b H50) | rewrite HK; exact HphiW].
    - intros _. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact RWa|]. split; [exact RWp|]. split; [exact RWn|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. split; [lia|]. split; [lia|].
      rewrite HK. split; [lia|]. split; [lia | lia].
    - exact HAC.
    - exact HSW.
    - exact HHM.
    - exact HAE.
    - exact ADw.
    - intros _ H50. exact (ADphi H50).
    - intros _. split; [exact ADa|]. split; [exact ADp|]. split; [exact ADn|].
      split; [lia|]. split; [lia | lia].
    - exact ADbc.
    - exact HB1.
    - exact HB2.
    - exact HB3.
    - exact HB4.
    - exact HB5.
    - exact FPp.
    - exact TLS. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & RWc & ACc & SWc & ADc & FPc & TLc).
  subst ms'.
  rewrite ?Esp in MU, STc, ADc, FPc.
  replace (ret_pc (Z_to_bv 64 0x817ec)) with (Z_to_bv 64 0x817ec)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STc|].
  split; [exact RWc|].
  split; [exact ACc|]. split; [exact SWc|]. split; [exact ADc | exact FPc].
Qed.

(* ---- the FRAG call of the b = 6 arm, 0x81818-0x81830, on reac_ctrl_identity_fragment_c.v ----
   a0 = the fragment record fr + 2256 ([A + 112]), a1 = Phi_r, a2 = n_b, and the three out slots as in the
   reply arm. *)
Lemma r10_frag6_call : FGC.reac_ctrl_identity_fragment_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi N fr : Z) (g50 st72 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s4 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= N < 2 ^ 64 ->
    0 <= fr -> fr + 3136 <= 2 ^ 64 -> fr mod 32 = 0 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 -> FGC.REAC_CTRL_IDENTITY_FRAGMENT_K <= spv ->
    HIGHMEM_BEG <= spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K -> spv <= APPMEM_END ->
    ro_cells rsegs m (bv_unsigned s1 + 112) [C8 (Z_to_bv 64 (fr + 2256))] ->
    ro_cells rsegs m (bv_unsigned s1 + 240) [C8 (Z_to_bv 64 (fr + 2448))] ->
    ro_cells rsegs m (bv_unsigned s1 + 232) [C8 (Z_to_bv 64 (fr + 2464))] ->
    ro_cells rsegs m (bv_unsigned s1 + 224) [C8 (Z_to_bv 64 (fr + 2496))] ->
    stk rsegs m (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv ->
    mem_inv rsegs m ->
    length g50 = 50%nat -> (50 <= N -> bytes_at rsegs m phi g50) -> length st72 = 72%nat ->
    rw_cells rsegs m (fr + 2256) [CB 72 st72] ->
    wr_at rsegs m (fr + 2448) 2 -> wr_at rsegs m (fr + 2464) 8 -> wr_at rsegs m (fr + 2496) 8 ->
    (phi + 50 <= spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= phi) ->
    (fr + 3136 <= phi \/ phi + 50 <= fr) ->
    (fr + 3136 <= spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr) ->
    asan_cells m -> shadow_rw m ->
    (50 <= N -> addressable m phi 50) ->
    addressable m (fr + 2256) 72 ->
    addressable m (fr + 2448) 2 -> addressable m (fr + 2464) 8 -> addressable m (fr + 2496) 8 ->
    app_mem (fr + 2256 + 78) ->
    (fr + 3136 <= RT_LO \/ RT_HI <= fr) ->
    bytes_at rsegs m BW.REAL_BCMP (le8 (wa BW.BCMP)) ->
    bytes_at rsegs m BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) ->
    bytes_at rsegs m BW.GOT_CF (le8 (wa BW.CF)) ->
    bytes_at rsegs m (BW.CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (BW.CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81834) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (RFr.fg_ret (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                                               (fr + 2496) N st72 g50)) /\
         munch (RFr.fg_fp FGC.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
                  spv (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50)) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv /\
         FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50
           (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50) m' /\
         asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81818) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi N fr g50 st72 -> -> -> -> HA0 HA248 Hphi0 Hphi50 HN Hfr0 Hfr64 Hfr32
    Hsp64 Hsp16 HspK HHM HAE RO0 RO1 RO2 RO3 ST HMI Hg50l Hg50b Hst72l RWf WRa WRp WRn
    HphiW HphiF HfrW HAC HSW ADphi ADf ADa ADp ADn HappF HRT HB1 HB2 HB3 HB4 HB5.
  unfold FGC.reac_ctrl_identity_fragment_contract in FRAG. cbv zeta in FRAG.
  assert (HK : FGC.REAC_CTRL_IDENTITY_FRAGMENT_K = 4672) by reflexivity.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite EA in RO0, RO1, RO2, RO3.
  do 7 step.
  eapply evt_cut.
  { eapply FRAG with (f := fr + 2256) (fr := phi) (len := N) (pa := fr + 2448) (pp := fr + 2464)
      (pn := fr + 2496) (g := g50) (st := st72).
    all: rewrite ?Esp.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hsp16.
    - rewrite HK in ST |- *. exact ST.
    - exact Hg50l.
    - exact Hst72l.
    - intros _ _ _ _ _ H50. exact (Hg50b H50).
    - intros _ _ _ _ _. split; [exact RWf|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact WRa|]. split; [exact WRp|]. split; [exact WRn|].
      cbn [RFr.all_dj RFr.dj_from]. rewrite HK.
      repeat split; try exact I; lia.
    - exact HMI.
    - exact HAC.
    - exact HSW.
    - rewrite HK in HHM |- *. exact HHM.
    - exact HAE.
    - intros _ _ _ _ _ H50. exact (ADphi H50).
    - intros _ _ _ _ _. split; [exact ADf|]. split; [exact ADa|]. split; [exact ADp|]. split; [exact ADn|].
      split; [exact HappF|]. cbn [RFr.dj_from]. repeat split; try exact I; unfold RT_LO, RT_HI in *; lia.
    - exact HB1.
    - exact HB2.
    - exact HB3.
    - exact HB4.
    - exact HB5. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & MEMc & ACc & SWc).
  subst ms'.
  rewrite ?Esp in MU, STc.
  replace (ret_pc (Z_to_bv 64 0x81834)) with (Z_to_bv 64 0x81834)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STc|].
  split; [exact MEMc|]. split; [exact ACc | exact SWc].
Qed.

(* ---- the FRAG call of the b = 5 arm, 0x818f8-0x81910: the same six argument instructions at the other
   placement of the arm (0x818f8 .. 0x81910), returning to 0x81914. *)
Lemma r10_frag5_call : FGC.reac_ctrl_identity_fragment_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi N fr : Z) (g50 st72 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s4 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= N < 2 ^ 64 ->
    0 <= fr -> fr + 3136 <= 2 ^ 64 -> fr mod 32 = 0 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 -> FGC.REAC_CTRL_IDENTITY_FRAGMENT_K <= spv ->
    HIGHMEM_BEG <= spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K -> spv <= APPMEM_END ->
    ro_cells rsegs m (bv_unsigned s1 + 112) [C8 (Z_to_bv 64 (fr + 2256))] ->
    ro_cells rsegs m (bv_unsigned s1 + 240) [C8 (Z_to_bv 64 (fr + 2448))] ->
    ro_cells rsegs m (bv_unsigned s1 + 232) [C8 (Z_to_bv 64 (fr + 2464))] ->
    ro_cells rsegs m (bv_unsigned s1 + 224) [C8 (Z_to_bv 64 (fr + 2496))] ->
    stk rsegs m (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv ->
    mem_inv rsegs m ->
    length g50 = 50%nat -> (50 <= N -> bytes_at rsegs m phi g50) -> length st72 = 72%nat ->
    rw_cells rsegs m (fr + 2256) [CB 72 st72] ->
    wr_at rsegs m (fr + 2448) 2 -> wr_at rsegs m (fr + 2464) 8 -> wr_at rsegs m (fr + 2496) 8 ->
    (phi + 50 <= spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= phi) ->
    (fr + 3136 <= phi \/ phi + 50 <= fr) ->
    (fr + 3136 <= spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr) ->
    asan_cells m -> shadow_rw m ->
    (50 <= N -> addressable m phi 50) ->
    addressable m (fr + 2256) 72 ->
    addressable m (fr + 2448) 2 -> addressable m (fr + 2464) 8 -> addressable m (fr + 2496) 8 ->
    app_mem (fr + 2256 + 78) ->
    (fr + 3136 <= RT_LO \/ RT_HI <= fr) ->
    bytes_at rsegs m BW.REAL_BCMP (le8 (wa BW.BCMP)) ->
    bytes_at rsegs m BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) ->
    bytes_at rsegs m BW.GOT_CF (le8 (wa BW.CF)) ->
    bytes_at rsegs m (BW.CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (BW.CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81914) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (RFr.fg_ret (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                                               (fr + 2496) N st72 g50)) /\
         munch (RFr.fg_fp FGC.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
                  spv (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50)) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv /\
         FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50
           (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50) m' /\
         asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818f8) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi N fr g50 st72 -> -> -> -> HA0 HA248 Hphi0 Hphi50 HN Hfr0 Hfr64 Hfr32
    Hsp64 Hsp16 HspK HHM HAE RO0 RO1 RO2 RO3 ST HMI Hg50l Hg50b Hst72l RWf WRa WRp WRn
    HphiW HphiF HfrW HAC HSW ADphi ADf ADa ADp ADn HappF HRT HB1 HB2 HB3 HB4 HB5.
  unfold FGC.reac_ctrl_identity_fragment_contract in FRAG. cbv zeta in FRAG.
  assert (HK : FGC.REAC_CTRL_IDENTITY_FRAGMENT_K = 4672) by reflexivity.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite EA in RO0, RO1, RO2, RO3.
  do 7 step.
  eapply evt_cut.
  { eapply FRAG with (f := fr + 2256) (fr := phi) (len := N) (pa := fr + 2448) (pp := fr + 2464)
      (pn := fr + 2496) (g := g50) (st := st72).
    all: rewrite ?Esp.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hsp16.
    - rewrite HK in ST |- *. exact ST.
    - exact Hg50l.
    - exact Hst72l.
    - intros _ _ _ _ _ H50. exact (Hg50b H50).
    - intros _ _ _ _ _. split; [exact RWf|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact WRa|]. split; [exact WRp|]. split; [exact WRn|].
      cbn [RFr.all_dj RFr.dj_from]. rewrite HK.
      repeat split; try exact I; lia.
    - exact HMI.
    - exact HAC.
    - exact HSW.
    - rewrite HK in HHM |- *. exact HHM.
    - exact HAE.
    - intros _ _ _ _ _ H50. exact (ADphi H50).
    - intros _ _ _ _ _. split; [exact ADf|]. split; [exact ADa|]. split; [exact ADp|]. split; [exact ADn|].
      split; [exact HappF|]. cbn [RFr.dj_from]. repeat split; try exact I; unfold RT_LO, RT_HI in *; lia.
    - exact HB1.
    - exact HB2.
    - exact HB3.
    - exact HB4.
    - exact HB5. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & MEMc & ACc & SWc).
  subst ms'.
  rewrite ?Esp in MU, STc.
  replace (ret_pc (Z_to_bv 64 0x81914)) with (Z_to_bv 64 0x81914)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STc|].
  split; [exact MEMc|]. split; [exact ACc | exact SWc].
Qed.

(* ==== the segment on the cuts ==== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require RtmB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcIdentModel RcFragLib RcLay RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RLy := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
Module LImg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.
Open Scope Z_scope.

(* ---- byte, cell and interval helpers (as lib/B/Prog/Seg/R6.v) ---- *)

Lemma r10_ba_rd : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma r10_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma r10_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r10_cells_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma r10_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

(* A frame range [lo, hi) as one writable cell of its current bytes. *)
Lemma r10_rw_stk : forall m lo hi, stk rsegs m lo hi -> lo <= hi ->
  exists bs, length bs = Z.to_nat (hi - lo) /\ rw_cells rsegs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
  intros m lo hi Hs Hle. destruct (stk_bytes rsegs m lo hi Hs Hle) as (bs & Hl & Hb).
  exists bs. split; [exact Hl|]. rewrite <- Hl. apply r10_rw_CB; [exact Hb|].
  rewrite Hl. replace (Z.of_nat (Z.to_nat (hi - lo))) with (hi - lo) by lia. exact (r10_wr_stk m lo hi Hs).
Qed.

Lemma r10_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma r10_mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof.
  intros m a. unfold mbyte, mrd, wa. destruct (m (Z_to_bv 64 a)); [reflexivity|].
  unfold YK11.seg_rom, PropExec.seg_rom. reflexivity.
Qed.

Lemma r10_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof. intros W x. destruct (KindBGlue.kb_outside_dec W x); [left | right]; assumption. Qed.

Lemma r10_out_app : forall A C x, outside A x -> outside C x -> outside (A ++ C) x.
Proof.
  induction A as [|[lo hi] A IH]; intros C x HA HB; cbn [app outside] in *; [exact HB|].
  destruct HA as [H1 H2]. split; [exact H1 | exact (IH C x H2 HB)].
Qed.

Lemma r10_nout_app : forall A C x, ~ outside (A ++ C) x -> ~ outside A x \/ ~ outside C x.
Proof.
  intros A C x H. destruct (r10_out_dec A x) as [HA|HA]; [|left; exact HA].
  destruct (r10_out_dec C x) as [HC|HC]; [|right; exact HC].
  exfalso. exact (H (r10_out_app A C x HA HC)).
Qed.

Lemma r10_nout_cons : forall lo hi W x, ~ outside ((lo, hi) :: W) x -> (lo <= x < hi) \/ ~ outside W x.
Proof.
  intros lo hi W x H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - left. lia.
  - right. intros Ho. apply H. split; [lia | exact Ho].
  - right. intros Ho. apply H. split; [lia | exact Ho].
Qed.

Lemma r10_nout_nil : forall x, ~ outside [] x -> False.
Proof. intros x H. apply H. exact I. Qed.

Lemma r10_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) Hm Hw HX. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  destruct (HX a Ha) as [Ho | Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r10_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

Lemma r10_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma r10_addr_of1 : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn He H. split; [exact Hp|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & HA). pose proof (HA 0 ltac:(lia)) as Hb.
  rewrite Z.add_0_r in Hb. exact Hb.
Qed.

Lemma r10_addr_cat : forall m p n1 n2, addressable m p n1 -> addressable m (p + n1) n2 -> addressable m p (n1 + n2).
Proof.
  intros m p n1 n2 (A0 & A1 & A2 & HA) (B0 & B1 & B2 & HB). split; [exact A0|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_ge_dec i n1) as [Hl|Hl]; [apply HA; lia|].
  replace (p + i) with (p + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

(* Addressability of the bytes of one granule from the value its shadow byte was just given: 0 makes all eight
   bytes addressable, k in 1 .. 7 the first k. *)
Lemma r10_addr_sh : forall m p k (c : byte),
  bytes_at rsegs m (shadow_addr p) [c] -> p mod 8 = 0 -> 0 <= k <= 8 ->
  (bv_signed c = 0 \/ k <= bv_signed c <= 7) ->
  (forall i, 0 <= i < k -> app_mem (p + i)) -> 0 <= p -> p + k <= APPMEM_END ->
  addressable m p k.
Proof.
  intros m p k c (_ & _ & Hc) Hp8 Hk Hv Happ Hp0 Hpe.
  split; [exact Hp0|]. split; [lia|]. split; [exact Hpe|].
  intros i Hi. split; [exact (Happ i Hi)|].
  exists c. split.
  - assert (E : shadow_addr (p + i) = shadow_addr p) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
    rewrite E. specialize (Hc 0%nat ltac:(cbn [length]; lia)). cbn [Z.of_nat nth_error] in Hc.
    rewrite Z.add_0_r in Hc. exact Hc.
  - unfold shadow_ok. destruct Hv as [Hv|Hv]; [left; exact Hv|]. right.
    assert (E : (p + i) mod 8 = i) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* ---- the normalized memory (MemNorm) and back (as R6) ---- *)

Lemma r10_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r10_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r10_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) r10_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma r10_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply r10_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma r10_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma r10_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r10_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r10_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r10_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r10_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r10_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r10_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r10_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r10_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r10_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r10_cells_tr : forall m m0, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_cells m -> asan_cells m0.
Proof.
  intros m m0 TB H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

Lemma r10_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma r10_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma r10_tls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k TB
    (T1 & T2 & T3 & T4 & T5 & Hk & T6 & T7 & T8 & T9 & (tb & te & T10) & T11 & T12 & T13 & T14 & T15 & T16 &
     HDB & T17).
  unfold asan_tls_cells.
  repeat match goal with |- _ /\ _ => split end.
  all: try (apply TB; assumption).
  all: try lia.
  all: try assumption.
  exists tb, te. apply TB. exact T10.
Qed.

Lemma r10_cls_tr : forall m m0 FS c, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  fp_cls m FS c -> fp_cls m0 FS c.
Proof.
  intros m m0 FS c TB (Hc & h & flags & HH & HF & HFl & HFb).
  split; [exact Hc|]. exists h, flags. split; [apply TB; exact HH|]. split; [apply TB; exact HF|].
  split; [exact HFl | exact HFb].
Qed.

Lemma r10_fp_tr : forall m m0 cs TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (forall l h, 0x5fe000 <= l -> stk rsegs m l h -> stk rsegs m0 l h) ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros m m0 cs TP FS lo hi W D TB TSk
    (DT & TSv & C & T & DB & k & Htls & Htp & (P1 & P2 & P3 & P4 & P5) & H88 & H96 & Hcls & Hlo & Happ &
     Hd1 & Hd2).
  exists DT, TSv, C, T, DB, k.
  split; [exact (r10_tls_tr m m0 TP DT TSv C T DB k TB Htls)|].
  split; [apply TB; exact Htp|].
  split.
  { split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    apply TSk; [unfold ASAN_GT in P3; lia | exact P5]. }
  split; [apply TB; exact H88|]. split; [apply TB; exact H96|].
  split; [eapply Forall_impl; [|exact Hcls]; intros c Hc; exact (r10_cls_tr m m0 FS c TB Hc)|].
  split; [exact Hlo|]. split; [exact Happ|]. split; [exact Hd1 | exact Hd2].
Qed.

(* ---- the side-stack package across the three metadata stores of 0x817a8-0x817b0 (fl_fp / fl_tls of
   RcAsanFPLib, for writes inside the HEAD range of fp's write list instead of its window) ---- *)
Lemma r10_fp_head : forall cs m m' TP FS lo hi a b W0 D W',
  fp cs m TP FS lo hi ((a, b) :: W0) D -> munch W' m m' -> wmono rsegs m m' -> sub_fp W' [(a, b)] ->
  (forall x, FS <= x < FS + FS_SIZE -> outside W' x) ->
  fp cs m' TP FS lo hi ((a, b) :: W0) D.
Proof.
  intros cs m m' TP FS lo hi a b W0 D W' (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA &
    HWd & HDd) Hm Hw Hs BEL.
  exists DT, TS, C, T, DB, k.
  pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  unfold asan_tls_cells in HT.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  split.
  { unfold asan_tls_cells.
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [exact T6|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [destruct T11 as (tb & te & T11); exists tb, te; fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [exact T18|]. fl_cell Hm Hs. }
  split; [fl_cell Hm Hs|].
  split.
  { unfold fs_place in *. destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|].
    split; [exact P3|]. split; [exact P4|]. eapply stk_transport; [exact P5 | exact Hm | exact Hw |].
    intros x Hx. left. apply BEL. exact Hx. }
  split; [eapply fl_bytes; [exact H88 | exact Hm | intros x Hx; apply BEL; rewrite ?length_le8 in Hx;
                             unfold FS_SIZE; lia]|].
  split; [eapply fl_bytes; [exact H96 | exact Hm | intros x Hx; apply BEL; cbn [length] in Hx;
                             unfold FS_SIZE; lia]|].
  split; [exact (Forall_impl _ (fun c => fl_cls W' m m' FS c BEL Hm) HCL)|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma r10_tls_head : forall cs m m' TP FS lo hi a b W0 D W' X,
  fp cs m TP FS lo hi ((a, b) :: W0) D -> munch W' m m' -> sub_fp W' [(a, b)] ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X.
Proof.
  intros cs m m' TP FS lo hi a b W0 D W' X (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Hm Hs Htls DT TS C T DB k HT.
  pose proof HT0 as HT0c.
  pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  assert (OUT : forall c d, RLy.ly_dj a b c d -> forall x, c <= x < d -> outside W' x)
    by (intros c d Hab x Hx; apply (fl_out_lo W' a b x Hs); unfold RLy.ly_dj in Hab; lia).
  destruct HT0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
    & A18 & A19).
  destruct HT as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17
    & B18 & B19).
  assert (EDT : DT0 = DT) by (apply (fl_le8_eq W' m m' (TP - 8) DT0 DT A3 B3 Hm); fl_tls_out OUT).
  assert (Ek : k0 = k) by (apply (fl_le4_eq W' m m' TSD_KEY k0 k A6 B6 A7 B7 Hm); fl_tls_out OUT).
  assert (ETS : TS0 = TS) by (apply (fl_le8_eq W' m m' (TP - 88) TS0 TS A8 B8 Hm); fl_tls_out OUT).
  subst DT0 k0 TS0.
  assert (EC : C0 = C) by (apply (fl_le8_eq W' m m' (bv_unsigned TS + 8 * k) C0 C A9 B9 Hm); fl_tls_out OUT).
  subst C0.
  assert (ET : T0 = T) by (apply (fl_le8_eq W' m m' (bv_unsigned C + 152) T0 T A10 B10 Hm); fl_tls_out OUT).
  assert (EDB : DB0 = DB) by (apply (fl_le8_eq W' m m' (TP + 8) DB0 DB A17 B17 Hm); fl_tls_out OUT).
  subst T0 DB0.
  exact (Htls DT TS C T DB k HT0c).
Qed.

(* ---- the cells the bcmp wrapper reads (the callees' last five premises), from RT ---- *)
Lemma r10_bw_cells : forall sp m md, AsanRTInv.RT sp m md ->
  bytes_at rsegs m BW.REAL_BCMP (le8 (wa BW.BCMP)) /\ bytes_at rsegs m BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) /\
  bytes_at rsegs m BW.GOT_CF (le8 (wa BW.CF)) /\
  bytes_at rsegs m (BW.CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (BW.CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HR. pose proof (AsanRTInv.RT_cf_cells _ _ _ HRT) as HCF.
  unfold asan_real_cells in HR. rewrite Forall_forall in HR.
  destruct HCF as (CF1 & _ & _ & _ & _ & _ & CF7 & _).
  split; [exact (HR (0xa2610, 0x98930) ltac:(unfold RT_REALS; repeat (first [left; reflexivity | right])))|].
  split; [exact (HR (0xa2608, 0x98a00) ltac:(unfold RT_REALS; repeat (first [left; reflexivity | right])))|].
  split; [exact CF1|].
  split.
  - eapply (r10_bat_idx _ _ _ 14%nat);
      [exact CF7 | vm_compute; reflexivity | unfold BW.CF, RT_CF; cbn [Z.of_nat]; lia].
  - eapply (r10_bat_idx _ _ _ 15%nat);
      [exact CF7 | vm_compute; reflexivity | unfold BW.CF, RT_CF; cbn [Z.of_nat]; lia].
Qed.

(* ---- shadow arithmetic ---- *)
Lemma r10_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r10_rt_disjoint : forall W, Forall (fun r => AC.GT <= fst r) W -> rt_disjoint W.
Proof.
  assert (L : forall W a n, Forall (fun r => a + n <= fst r) W -> disjoint_from W a n).
  { induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
    apply Forall_cons_iff in H as [H1 H2]. cbn [fst] in H1.
    split; [left; exact H1 | exact (IH a n H2)]. }
  intros W H. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
    RT_AGLOB_LEN.
  repeat split; apply L; (eapply Forall_impl; [|exact H]);
    intros [lo hi] Hl; cbn [fst] in *; unfold AC.GT in Hl; lia.
Qed.

(* ==== the round-trip model of the turn (every value is a function of OUR and i* only; the facts are computed
   over the 11 catalogue rows with OUR's 6 bytes left as variables, as Seg/R11.v's r11_rtm) ==== *)

Lemma r10_istar_range : forall inp, 0 <= istar inp < 11.
Proof. intros inp. unfold istar, CAT_N. apply Z.mod_pos_bound. lia. Qed.

Section Cong.
Variables inp inp' : list byte.
Hypothesis HO : OUR inp = OUR inp'.
Hypothesis HI : istar inp = istar inp'.

Lemma r10c_mrow : mrow inp = mrow inp'.
Proof using HO HI. unfold mrow. rewrite HI. reflexivity. Qed.

Lemma r10c_mb : rt_mb inp = rt_mb inp'.
Proof using HO HI. unfold rt_mb. rewrite HI. reflexivity. Qed.

Lemma r10c_nb : rt_nb inp = rt_nb inp'.
Proof using HO HI. unfold rt_nb. rewrite r10c_mb. reflexivity. Qed.

Lemma r10c_n : forall b, rt_n inp b = rt_n inp' b.
Proof using HO HI. intros b. unfold rt_n, rt_E, rt_uw. rewrite r10c_mrow, r10c_mb. reflexivity. Qed.

Lemma r10c_X : forall b, rt_X inp b = rt_X inp' b.
Proof using HO HI. intros b. unfold rt_X. rewrite r10c_mrow, r10c_mb, r10c_nb. reflexivity. Qed.

Lemma r10c_F : forall b, rt_F inp b = rt_F inp' b.
Proof using HO HI. intros b. unfold rt_F. rewrite HO, r10c_X, r10c_n. reflexivity. Qed.

Lemma r10c_g : forall b, rt_g inp b = rt_g inp' b.
Proof using HO HI. intros b. unfold rt_g. rewrite r10c_F. reflexivity. Qed.

End Cong.

Definition r10_cn (our : list byte) (i : Z) : list byte := our ++ [RIM.zb (2 * i)].

Lemma r10_cn_OUR : forall our i, length our = 6%nat -> OUR (r10_cn our i) = our.
Proof.
  intros our i H. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  reflexivity.
Qed.

Lemma r10_cn_istar : forall our i, length our = 6%nat -> 0 <= i < 11 -> istar (r10_cn our i) = i.
Proof.
  intros our i H Hi. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Ltac r10_rows inp :=
  let HO := fresh "HO" in let HI := fresh "HI" in
  assert (HO : OUR inp = OUR (r10_cn (OUR inp) (istar inp)))
    by (symmetry; apply r10_cn_OUR, OUR_length);
  assert (HI : istar inp = istar (r10_cn (OUR inp) (istar inp)))
    by (symmetry; apply r10_cn_istar; [apply OUR_length | apply r10_istar_range]);
  rewrite ?(r10c_n _ _ HO HI), ?(r10c_g _ _ HO HI), ?(r10c_F _ _ HO HI);
  clear HO HI;
  generalize (OUR_length inp) (r10_istar_range inp);
  generalize (OUR inp) (istar inp);
  let our := fresh "our" in let i := fresh "i" in let HL := fresh "HL" in let Hi := fresh "Hi" in
  intros our i HL Hi;
  destruct our as [|?x0 [|?x1 [|?x2 [|?x3 [|?x4 [|?x5 [|? ?]]]]]]]; try discriminate HL; clear HL;
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10)
    by lia;
  clear Hi;
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].

(* The parse kind of turn b that the dispatch tests: 0x8187c `beq a0,9` (b = 0), 0x817cc / 0x81920 `beq a0,5`
   (b = 1, 2, 3, 4) and 0x81810 / 0x818f0 `beq a0,11` (b = 5, 6). *)
Definition r10_kind (b : nat) : Z :=
  match b with 0%nat => 9 | 5%nat => 11 | 6%nat => 11 | _ => 5 end.

(* Every turn b <= 6 whose frame is sent (n_b <> 0): the parse kind is r10_kind b, the frame has n_b >= 52 bytes. *)
Lemma r10_rtk : forall inp (b : nat), (b <= 6)%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  rt_k inp (Z.of_nat b) = r10_kind b /\ 52 <= rt_n inp (Z.of_nat b) /\
  Z.of_nat (length (rt_F inp (Z.of_nat b))) = rt_n inp (Z.of_nat b).
Proof.
  intros inp b Hb. unfold rt_k.
  destruct b as [|[|[|[|[|[|[|b]]]]]]]; [..|lia]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ r10_kind];
    r10_rows inp; intros Hn; vm_compute in Hn |- *;
    first [split; [reflexivity | split; [congruence | reflexivity]] | exfalso; exact (Hn eq_refl)].
Qed.

(* The catalogue row of the input: one of the 11 rows of BOX_CATALOGUE, 8-byte aligned, 296 bytes (R6). *)
Lemma r10_mb_len : forall inp, length (rt_mb inp) = 296%nat.
Proof.
  intros inp. unfold rt_mb, rowb, img.
  destruct (LImg.image_bytes rsegs (CAT + CAT_ROW * istar inp) 296) eqn:Ei;
    [exact (LImg.image_bytes_length rsegs 296 _ _ Ei) | apply repeat_length].
Qed.

Lemma r10_mrow_rng : forall inp, CAT <= mrow inp <= CAT + 296 * 10 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. unfold mrow, istar, CAT_N, CAT, CAT_ROW.
  pose proof (Z.mod_pos_bound (mode inp / 2) 11 ltac:(lia)) as Hb.
  set (k := (mode inp / 2) mod 11) in *. split; [lia|].
  replace (652832 + 296 * k) with ((81604 + 37 * k) * 8) by lia.
  apply Z.mod_mul. lia.
Qed.

(* The turn records: RID 38 bytes, RFG 72 bytes at every turn (Seg/R13.v's r13_rid_len / r13_rfg_len). *)
Lemma r10_rid_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst];
    first [exact IH | apply RcIdentModel.ING_length; exact IH].
Qed.

Lemma r10_rtg_len : forall inp x, length (rt_g inp x) = 50%nat.
Proof. intros inp x. unfold rt_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma r10_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
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

Lemma r10_rfg_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd];
    first [exact IH | apply r10_fgst_len; [exact IH | apply r10_rtg_len]].
Qed.

(* The fragment turn b = 5 when its frame is not a closing fragment (fg_rf = 0, the official cut's conjunct): the
   identity record is kept and the fragment record is the fragment step's. *)
Lemma r10_st5 : forall inp (b : nat), b = 5%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  fg_rf (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)) = 0 ->
  RID inp (S b) = RID inp b /\
  RFG inp (S b) = fg_st (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)).
Proof.
  intros inp b Hb Hn Hrf. unfold RID, RFG in Hrf |- *. cbn [rt_st].
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  assert (E1 : ((Z.of_nat b =? 3) || (Z.of_nat b =? 4))%bool = false) by (subst b; reflexivity).
  assert (E2 : ((Z.of_nat b =? 5) || (Z.of_nat b =? 6))%bool = true) by (subst b; reflexivity).
  rewrite E1, E2. cbn [fst snd]. unfold fg_id. rewrite Hrf. split; reflexivity.
Qed.

(* The fragment turn b = 6 with its frame sent: the fragment record of turn S b is the fragment step's (the
   identity record is fg_id's; the exit Inv_B81834_at names only the fragment record of turn S b). *)
Lemma r10_st6 : forall inp (b : nat), b = 6%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  RFG inp (S b) = fg_st (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)).
Proof.
  intros inp b Hb Hn. unfold RFG. cbn [rt_st].
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  assert (E1 : ((Z.of_nat b =? 3) || (Z.of_nat b =? 4))%bool = false) by (subst b; reflexivity).
  assert (E2 : ((Z.of_nat b =? 5) || (Z.of_nat b =? 6))%bool = true) by (subst b; reflexivity).
  rewrite E1, E2. cbn [snd]. reflexivity.
Qed.

(* The fragment call's class with five nonzero pointers is the model's class fcls. *)
Lemma r10_fgc : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  RcFrag.fg_class f fr pa pp pn len st g = fcls len st g.
Proof.
  intros f fr pa pp pn len st g H1 H2 H3 H4 H5. unfold fcls, RcFrag.fg_class.
  rewrite (proj2 (Z.eqb_neq f 0) H1), (proj2 (Z.eqb_neq fr 0) H2), (proj2 (Z.eqb_neq pa 0) H3),
    (proj2 (Z.eqb_neq pp 0) H4), (proj2 (Z.eqb_neq pn 0) H5).
  reflexivity.
Qed.

(* The first 50 bytes of a frame of at least 50 bytes are its leading bytes. *)
Lemma r10_fr50 : forall m a F, bytes_at rsegs m a F -> (50 <= length F)%nat -> bytes_at rsegs m a (fr50 F).
Proof.
  intros m a F H HL. unfold fr50. rewrite firstn_app.
  replace (50 - length F)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  rewrite <- (firstn_skipn 50 F) in H. apply bytes_at_app in H as (H1 & _). exact H1.
Qed.

(* ---- the run on the normalized memory, lifted to SR on the real configuration (R6's r6_run) ---- *)
Section Run.
Context {fx : FPState}.

Lemma r10_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) r10_wx Hro HE)
    as HE'.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE' | exact Hh |].
  intros ms' md' (can & (s0 & (R & pc' & m0' & Es0 & HKR) & Hrel & Hsame) & Heq) Hmat.
  subst s0.
  destruct can as [cr cf cp cs cv cc cm co].
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
  subst.
  apply (HK _ _ _ regs' _ md' HKR); [apply KindBGlue.kb_getr_eqv; exact HR | exact E8 | exact Hsame | exact Hmat].
Qed.

End Run.

(* ==== the write set of an arm, and the addresses it misses ==== *)

(* Every address an arm of this segment may write: the frame's 392 metadata bytes; the reply slots
   [fr + 2448, fr + 2504) and, on the two fragment arms (frg = true), the fragment record
   [fr + 2256, fr + 2328); the callee's own window [sp - K, sp) and its metadata; and, on the reply arm
   (rpl = true), the class-1 side stack (the hint words, the class-0 / class-1 flag bytes, the class-1 frames)
   and those frames' metadata. *)
Definition r10_in (frg rpl : bool) (fr sp K FS x : Z) : Prop :=
  (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
  (fr + 2448 <= x < fr + 2504) \/
  (frg = true /\ fr + 2256 <= x < fr + 2328) \/
  (sp - K <= x < sp) \/
  (shadow_addr (sp - K) <= x < shadow_addr sp) \/
  (rpl = true /\ FS <= x < FS + 16) \/ (rpl = true /\ FS + 4096 <= x < FS + 28672) \/
  (rpl = true /\ FS + 1085440 <= x < FS + 2134016) \/
  (rpl = true /\ shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)).

(* An address outside [lo, lo + 8 n) has its shadow byte outside [shadow_addr lo, shadow_addr (lo + 8 n)). *)
(* mod-8 arithmetic, spelled out (lia does not do divisibility with a symbolic quotient). *)
Lemma r10_mod8_of16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
  intros x H. rewrite (Z.mod_divide x 8 ltac:(lia)).
  apply (Z.divide_trans 8 16 x); [exists 2; reflexivity | apply (Z.mod_divide x 16 ltac:(lia)); exact H].
Qed.

Lemma r10_sub_mod8 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a - b) mod 8 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.

Lemma r10_add_mod8 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof. intros a b Ha Hb. rewrite Zplus_mod, Ha, Hb. reflexivity. Qed.

Lemma r10_div8_exact : forall a, a mod 8 = 0 -> 8 * (a / 8) = a.
Proof. intros a H. symmetry. apply Z.div_exact; [lia | exact H]. Qed.

Lemma r10_shq : forall lo n y, lo mod 8 = 0 -> 0 <= lo -> 0 <= n ->
  (y < lo \/ lo + 8 * n <= y) -> ~ (shadow_addr lo <= shadow_addr y < shadow_addr (lo + 8 * n)).
Proof.
  intros lo n y Hm Hlo Hn Hy. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* (o1) no address below the image top is written. *)
Lemma r10_o1 : forall frg rpl fr sp K FS x,
  AC.GT <= fr -> AC.GT <= sp - K -> AC.GT <= FS -> 0 <= x < AC.GT ->
  ~ r10_in frg rpl fr sp K FS x.
Proof.
  intros frg rpl fr sp K FS x Hfr Hsp HFS Hx.
  assert (HG : AC.GT = 6283264) by reflexivity.
  assert (HK : ASAN_K = 2147450880) by reflexivity.
  assert (HSfr : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia).
  assert (HshW : ASAN_K <= shadow_addr (sp - K))
    by (unfold shadow_addr; pose proof (Z.div_pos (sp - K) 8 ltac:(lia) ltac:(lia)); lia).
  assert (HshF : ASAN_K <= shadow_addr (FS + 1085440))
    by (unfold shadow_addr; pose proof (Z.div_pos (FS + 1085440) 8 ltac:(lia) ltac:(lia)); lia).
  unfold r10_in. intros [H|[H|[(_ & H)|[H|[H|[(_ & H)|[(_ & H)|[(_ & H)|(_ & H)]]]]]]]]; lia.
Qed.

(* (o2) an application byte outside the ranges r10_in names is not written. *)
Lemma r10_o2 : forall frg rpl fr sp K FS x,
  0 <= fr -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  0 <= sp - K -> (forall a, sp - K <= a < sp -> app_mem a) ->
  0 <= FS -> (forall a, FS <= a < FS + 2134016 -> app_mem a) ->
  app_mem x -> ~ (fr + 2448 <= x < fr + 2504) -> ~ (fr + 2256 <= x < fr + 2328) ->
  ~ (sp - K <= x < sp) ->
  (rpl = true -> ~ (FS <= x < FS + 16) /\ ~ (FS + 4096 <= x < FS + 28672) /\
                 ~ (FS + 1085440 <= x < FS + 2134016)) ->
  ~ r10_in frg rpl fr sp K FS x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros frg rpl fr sp K FS x Hfr0 Hfrapp Hsp0 Hwapp HFS0 HFSapp Happ Hn1 Hn2 Hnw Hfs.
  assert (HSfr : in_shadow x -> False) by (intros Hs; exact (app_not_shadow x Happ Hs)).
  assert (Hdv : shadow_addr fr + FRAME_SHADOW <= shadow_addr (fr + FRAME_BYTES)).
  { unfold shadow_addr. replace (fr + FRAME_BYTES) with (fr + FRAME_SHADOW * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  unfold r10_in, Sfr. intros [H|[H|[(_ & H)|[H|[H|[(Hr & H)|[(Hr & H)|[(Hr & H)|(Hr & H)]]]]]]]].
  - apply HSfr. apply (fsf_sh_in_win fr (fr + FRAME_BYTES) x); [lia | exact Hfrapp | lia].
  - lia.
  - lia.
  - lia.
  - apply HSfr. apply (fsf_sh_in_win (sp - K) sp x); [lia | exact Hwapp | exact H].
  - destruct (Hfs Hr) as (H1 & _ & _). lia.
  - destruct (Hfs Hr) as (_ & H2 & _). lia.
  - destruct (Hfs Hr) as (_ & _ & H3). lia.
  - apply HSfr. apply (fsf_sh_in_win (FS + 1085440) (FS + 2134016) x);
      [lia | intros a Ha; apply HFSapp; lia | exact H].
Qed.

(* (o3) the shadow byte of an application byte outside the frame, the callee window and the class-1 frames is
   not written either. *)
Lemma r10_o3 : forall frg rpl fr sp K FS y,
  fr mod 8 = 0 -> 0 <= fr -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  K mod 8 = 0 -> 0 <= K -> sp mod 8 = 0 -> 0 <= sp - K -> (forall a, sp - K <= a < sp -> app_mem a) ->
  0 <= FS -> FS mod 8 = 0 -> (forall a, FS <= a < FS + 2134016 -> app_mem a) ->
  app_mem y -> ~ (fr <= y < fr + FRAME_BYTES) -> ~ (sp - K <= y < sp) ->
  (rpl = true -> ~ (FS + 1085440 <= y < FS + 2134016)) ->
  ~ r10_in frg rpl fr sp K FS (shadow_addr y).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros frg rpl fr sp K FS y Hfr8 Hfr0 Hfrapp HK8 HK0 Hsp8 Hsp0 Hwapp HFS0 HFS8 HFSapp Happ Hnf Hnw Hnfs.
  assert (Hsh : in_shadow (shadow_addr y)) by (apply shadow_of_app; exact Happ).
  assert (Hnapp : app_mem (shadow_addr y) -> False) by (intros Ha; exact (app_not_shadow _ Ha Hsh)).
  unfold r10_in. intros [H|[H|[(_ & H)|[H|[H|[(Hr & H)|[(Hr & H)|[(Hr & H)|(Hr & H)]]]]]]]].
  - apply (r10_shq fr FRAME_SHADOW y Hfr8 Hfr0 ltac:(lia) ltac:(lia)).
    assert (E : shadow_addr (fr + 8 * FRAME_SHADOW) = Sfr fr + FRAME_SHADOW)
      by (unfold Sfr, shadow_addr; replace (fr + 8 * FRAME_SHADOW) with (fr + FRAME_SHADOW * 8) by lia;
          rewrite Z.div_add by lia; lia).
    rewrite E. unfold Sfr in H |- *. lia.
  - apply Hnapp. apply Hfrapp. lia.
  - apply Hnapp. apply Hfrapp. lia.
  - apply Hnapp. apply Hwapp. lia.
  - assert (E : sp - K + 8 * (K / 8) = sp) by (rewrite (r10_div8_exact K HK8); lia).
    pose proof (r10_shq (sp - K) (K / 8) y (r10_sub_mod8 sp K Hsp8 HK8) Hsp0
                  ltac:(apply Z.div_pos; lia) ltac:(lia)) as Hq.
    rewrite E in Hq. exact (Hq H).
  - apply Hnapp. apply HFSapp. lia.
  - apply Hnapp. apply HFSapp. lia.
  - apply Hnapp. apply HFSapp. lia.
  - pose proof (Hnfs Hr) as Hy.
    assert (E : FS + 1085440 + 8 * 131072 = FS + 2134016) by lia.
    pose proof (r10_shq (FS + 1085440) 131072 y (r10_add_mod8 FS 1085440 HFS8 ltac:(reflexivity))
                  ltac:(lia) ltac:(lia) ltac:(lia)) as Hq.
    rewrite E in Hq. exact (Hq H).
Qed.

(* The frame's 392 metadata bytes are shadow bytes. *)
Lemma r10_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW ->
  in_shadow (Sfr fr + k).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr k Happ Hk. rewrite <- (r10_sh8 fr k). apply shadow_of_app. apply Happ. lia.
Qed.

(* shadow_rw across a run whose written shadow bytes read back. *)
Lemma r10_srw_keep : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall x, in_shadow x -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' H MU WM HR a Ha. destruct (H a Ha) as (Hv & b & Hb). split; [apply WM, Hv|].
  destruct (r10_out_dec W a) as [Ho|Hno].
  - exists b. pose proof (in_shadow_range a Ha) as Hbd.
    unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exact (HR a Ha Hno).
Qed.

(* A frame range as one writable cell of n bytes. *)
Lemma r10_rw_stkn : forall m lo n, stk rsegs m lo (lo + Z.of_nat n) ->
  exists bs, length bs = n /\ rw_cells rsegs m lo [CB n bs].
Proof.
  intros m lo n Hs.
  destruct (stk_bytes rsegs m lo (lo + Z.of_nat n) Hs ltac:(lia)) as (bs & Hl & Hb).
  replace (lo + Z.of_nat n - lo) with (Z.of_nat n) in Hl by lia. rewrite Nat2Z.id in Hl.
  exists bs. split; [exact Hl|]. rewrite <- Hl.
  apply r10_rw_CB; [exact Hb|]. rewrite Hl.
  replace (Z.of_nat n) with (lo + Z.of_nat n - lo) by lia. exact (r10_wr_stk m lo _ Hs).
Qed.

(* a_fs_ok across a run that writes no byte of the side stack's metadata region. *)
Lemma r10_fsok_keep : forall mem mem' W FS,
  AC.a_fs_ok mem FS -> munch W mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q) ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
     exists b, mbyte rsegs mem' q = Some b) ->
  (forall q, FS <= q < FS + 36864 -> outside W q) ->
  0 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 -> AC.a_fs_ok mem' FS.
Proof.
  intros mem mem' W FS Hok MU HW HP HK HFS0 HFSe.
  apply (Tac_fs.a_fs_ok_pres W mem mem' FS Hok MU HW HP); [|exact HFS0 | exact HFSe].
  intros q Hq. apply HK. split; [|exact (Tac_fs.fs_meta_below FS q Hq)].
  destruct Hq as [H'|[H'|[(c & Hc & Hr)|(c & j & Hc & Hj & ->)]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. assert (0 <= Z.of_nat c) by lia. lia.
  - pose proof (Tac_fs.a_fs_flag_range FS c j Hc Hj). lia.
Qed.

(* ==== the segment ==== *)
Section R10.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The two ending callees, taken on their lib/B contracts, never on their code. *)
Hypothesis REPLY : RPC.reac_ctrl_identity_reply_contract.
Hypothesis FRAG : FGC.reac_ctrl_identity_fragment_contract.

(* The allocator-law fields this file reads, in the shape its use sites take, read through SlotInv's LawFields
   (lw_*: each generated law is taken apart once there).  a_laws_fs_store has no LawFields lemma; r10_fs_store
   takes it apart here, once, by decompose (so an appended conjunct changes no line). *)
Lemma r10_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ end_in_app p n /\
  (forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\
     ~ AC.a_on_img_page a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [H1 H2 H3 H4 H5].
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

Lemma r10_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS mod 4096 = 0 /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw HFS.
  destruct (lw_fs_place (APIf rc) H mem md FS HAH Hw HFS) as [H1 H2 H3 H4].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma r10_fs_state : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw HFS. exact (lw_fs_ok (APIf rc) H mem md FS HAH Hw HFS).
Qed.

(* a_fs_ok's first conjunct: every side-stack byte is writable and present. *)
Lemma r10_fs_ok_cells : forall mem FS, AC.a_fs_ok mem FS ->
  forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b.
Proof. intros mem FS H. exact (lw_fs_bytes mem FS H). Qed.

Lemma r10_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Hw HFS Hag Hwr Hok.
  decompose [and] (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS HAH
                     Hw HFS Hag Hwr Hok).
  refine (conj _ (conj _ (conj _ _))); assumption.
Qed.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame (the low image, the frame
   header, the spills [A + 40, A + 56) / [A + 336, A + 344), the saved registers and the input block) and keeps
   every shadow byte readable, given the new frame-shadow list, the run's heap invariant / stklo, the
   S-anchored window still backed, the frame_AG globals and the window outside the frame still addressable, and
   the side-arm frame record (R4's r4_fra, with the input facts of push 5d). W may hold frame bytes, the
   callee's window, side-stack bytes and shadow bytes. *)
Lemma r10_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HWin HAG' HWA' HFSR E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA448|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hfsrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HFSR Hfsrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (r10_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|].
  split; [exact Hlive|].
  exact (fra_in_keep_sh g mem mem' W Hinb Hinblk MU HWin).
Qed.

(* The numbers of the frame, the callee window and the side stack, and the three "outside W" facts, from FRA
   and the arm's write set. *)
Lemma r10_outs : forall g fr hb regs mem md FS frg rpl K W,
  FRA B APIf ra g fr hb regs mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  0 <= K <= FN_STACK -> K mod 8 = 0 ->
  (forall x, ~ outside W x -> r10_in frg rpl fr (AC.aspZ regs) K FS x) ->
  AC.GT <= FS /\ FS mod 8 = 0 /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
  FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS + 6328320 <= fr /\
  AC.GT <= fr /\ fr mod 8 = 0 /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\ fr + FRAME_BYTES <= APPMEM_END /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AF.SLOT_STACK /\
  HIGHMEM_BEG <= g_S g - AF.SLOT_STACK /\
  g_S g - AF.SLOT_STACK <= AC.aspZ regs - K /\ AC.aspZ regs <= g_S g /\ g_S g < APPMEM_END /\
  (forall a, AC.aspZ regs - K <= a < AC.aspZ regs -> app_mem a) /\
  Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG /\
  (forall x, 0 <= x < 6283264 -> outside W x) /\
  (forall x, app_mem x -> ~ (fr + 2448 <= x < fr + 2504) -> ~ (fr + 2256 <= x < fr + 2328) ->
     ~ (AC.aspZ regs - K <= x < AC.aspZ regs) ->
     (rpl = true -> ~ (FS <= x < FS + 16) /\ ~ (FS + 4096 <= x < FS + 28672) /\
                    ~ (FS + 1085440 <= x < FS + 2134016)) -> outside W x) /\
  (forall y, app_mem y -> ~ (fr <= y < fr + FRAME_BYTES) -> ~ (AC.aspZ regs - K <= y < AC.aspZ regs) ->
     (rpl = true -> ~ (FS + 1085440 <= y < FS + 2134016)) -> outside W (shadow_addr y)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md FS frg rpl K W HFRA HFSw HFSr HK HK8 Hsub.
  destruct (fra_fsfree B APIf ra g fr hb regs mem md HFRA)
    as (FS0 & Hw0 & Hr0 & Hok0 & HGT0 & Hal0 & Happ0 & Hend0 & Hfrb & _).
  assert (EFS : FS0 = FS)
    by (apply (fsf_wm_uniq mem (AC.as_tp AC.ASYMS) FS0 FS Hw0 HFSw Hr0 HFSr);
        unfold AC.as_tp, AC.ASYMS; cbn; lia).
  subst FS0.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & _ & _ & _ & _ & _ & Hspm & Haspz & Hstklo & _ & _ & _ & _ &
    _ & _ & Hfrm & _ & _ & HAS & Hspa & Hfa & HA448 & HS4 & HAPP & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  destruct (r10_fs_place (hb ++ g_H g) mem md FS HAH HFSw HFSr)
    as (_ & HFSstk & _ & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGv : AC.GT = 6283264) by reflexivity.
  assert (HfrE : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - Hal0; Z.div_mod_to_equations; lia).
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HFS0 : 0 <= FS) by lia.
  assert (HShm : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr, shadow_addr, ASAN_K, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia. }
  assert (Hwapp : forall a, sp - K <= a < sp -> app_mem a).
  { intros a Ha. unfold app_mem. right. lia. }
  assert (HFSapp2 : forall a, FS <= a < FS + 2134016 -> app_mem a) by (intros a Ha; apply Happ0; lia).
  rewrite Haspz in Hsub |- *.
  split; [lia|]. split; [exact HFS8|]. split; [exact Happ0|]. split; [lia|]. split; [exact Hfrb|].
  split; [lia|]. split; [exact Hfr8|]. split; [exact Hfrapp|]. split; [exact HfrE|].
  split; [exact Hstklo|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HAPP|].
  split; [exact Hwapp|]. split; [exact HShm|].
  split.
  { intros x Hx. destruct (r10_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso.
    exact (r10_o1 frg rpl fr sp K FS x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Hsub x Hno)). }
  split.
  { intros x Happ H1 H2 H3 H4. destruct (r10_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso.
    exact (r10_o2 frg rpl fr sp K FS x Hfr0 Hfrapp ltac:(lia) Hwapp HFS0 HFSapp2 Happ H1 H2 H3 H4
             (Hsub x Hno)). }
  { intros y Happ H1 H2 H3. destruct (r10_out_dec W (shadow_addr y)) as [Ho|Hno]; [exact Ho|].
    exfalso.
    exact (r10_o3 frg rpl fr sp K FS y Hfr8 Hfr0 Hfrapp HK8 ltac:(lia) (r10_mod8_of16 sp Hspm)
             ltac:(lia) Hwapp HFS0 HFS8 HFSapp2 Happ H1 H2 H3 (Hsub (shadow_addr y) Hno)). }
Qed.

(* FSREC across an arm: the tp word is an image byte, the class-6 flag byte lies in [FS + 36352, FS + 36608)
   and the slot's last word at fr + 4088 is a FakeStack byte above the class-1 area. *)
Lemma r10_fsrec : forall mem mem' W fr FS,
  FSREC fr mem -> munch W mem mem' ->
  (forall FS', word_mem rsegs mem (AC.as_tp AC.ASYMS) FS' -> 0 <= FS' < 2 ^ 64 -> FS' = FS) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall j x, 0 <= j < 256 -> fr = FS + 6328320 + j * 4096 ->
     (FS + 36352 <= x < FS + 36608 \/ fr + 4088 <= x < fr + 4096) -> outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr FS (FS0 & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU HU HLO HW.
  pose proof (HU FS0 Htp HFSr) as EFS. subst FS0.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j)
    by (unfold SMC.fs_flag; cbn [Z.of_nat]; lia).
  rewrite HM6 in Hj.
  assert (Hfrv : fr = FS + 6328320 + j * 4096)
    by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn [Z.of_nat]; lia).
  exists FS, j.
  split.
  { intros k Hk. unfold mbyte. rewrite (MU (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    - exact (Htp k Hk).
    - rewrite MState.unsigned_lit by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
      apply HLO. unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split; [exact HFSr|]. split; [rewrite HM6; exact Hj|]. split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
    apply (HW j x Hj Hfrv). left. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx.
    apply (HW j x Hj Hfrv). right. rewrite HB6 in Hx. lia. }
Qed.

(* FRA and ENT across one arm of the segment: the write set lies in r10_in, every written byte reads back, the
   side stack's own state is the one the arm leaves (a_fs_ok mem'), and the callee's window is addressable
   afterwards. *)
Lemma r10_land : forall g fr hb regs regs' mem mem' md FS frg rpl K W,
  FRA B APIf ra g fr hb regs mem md ->
  ENT APIf g hb mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.a_fs_ok mem' FS ->
  0 <= K <= FN_STACK -> K mod 8 = 0 ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall x, ~ outside W x -> r10_in frg rpl fr (AC.aspZ regs) K FS x) ->
  (forall x, ~ outside W x -> exists bb, mrd rsegs mem' (wa x) = Some bb) ->
  shadow_rw mem' ->
  addressable mem' (AC.aspZ regs - K) K ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md FS frg rpl K W HFRA HENT HFSw HFSr HFSOK' HK HK8 MU WM HRO HDJ Hsub Hrd
    HSW' HADw' E2 E3 E4 E8 E9 E19 E26.
  destruct (r10_outs g fr hb regs mem md FS frg rpl K W HFRA HFSw HFSr HK HK8 Hsub)
    as (HGTFS & HFS8 & HFSapp & HFSstk & HFSfr & HGTfr & Hfr8 & Hfrapp & HfrE & Hstklo & Hhm & Hwlo & Hwhi &
        HSapp & Hwapp & HShm & OUTLO & OUTAPP & OUTSH).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo2 & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (proj1 (fra_frame B APIf ra g fr hb regs mem md HFRA) K HK) as Hsep.
  rewrite Haspz in HADw', Hsub, Hwlo, Hwapp, OUTAPP, OUTSH, Hsep.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGv : AC.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (Hwrit : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
  assert (HU : forall FS', word_mem rsegs mem (AC.as_tp AC.ASYMS) FS' -> 0 <= FS' < 2 ^ 64 -> FS' = FS)
    by (intros FS' Hw' Hr'; apply (fsf_wm_uniq mem (AC.as_tp AC.ASYMS) FS' FS Hw' HFSw Hr' HFSr);
        unfold AC.as_tp, AC.ASYMS; cbn; lia).
  assert (Ebb : forall y, shadow_addr (8 * (y - ASAN_K)) = y)
    by (intros y; unfold shadow_addr, ASAN_K; rewrite Z.mul_comm, Z.div_mul by lia; lia).
  (* the heap invariant, ownership and the stack bounds across the arm *)
  assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
            ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
            ~ (FS <= q < FS + AC.FS_SIZE) ->
            ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ q = shadow_addr bb) ->
            mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
  { intros q Hq Hnok Hnfs Hnsh.
    destruct (r10_out_dec W q) as [Ho|Hno].
    - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
    - exfalso.
      assert (Hfrst : forall x, fr <= x < fr + FRAME_BYTES ->
                AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x \/
                (FS <= x < FS + AC.FS_SIZE)).
      { intros x Hx. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        - left. right; left. exact (Hreal x Hx).
        - right. destruct (Hfs x Hx) as (FSb & HFSbr & Hwb & Hlob & Hhib).
          pose proof (HU FSb Hwb HFSbr) as ->. lia. }
      destruct (Hsub q Hno) as [Hx|[Hx|[(_ & Hx)|[Hx|[Hx|[(_ & Hx)|[(_ & Hx)|[(_ & Hx)|(_ & Hx)]]]]]]]].
      + assert (Hin : fr <= 8 * (q - ASAN_K) < fr + FRAME_BYTES)
          by (clear - Hx Hfr8 HFBv HFSv; unfold Sfr, shadow_addr, ASAN_K in Hx |- *;
              Z.div_mod_to_equations; lia).
        destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        * apply Hnok. right. right. right. exists (8 * (q - ASAN_K)).
          split; [symmetry; apply Ebb|]. right. left. exact (Hreal _ Hin).
        * apply Hnsh. exists (8 * (q - ASAN_K)). split; [|symmetry; apply Ebb].
          destruct (Hfs _ Hin) as (FSb & HFSbr & Hwb & Hlob & Hhib).
          pose proof (HU FSb Hwb HFSbr) as ->. lia.
      + destruct (Hfrst q ltac:(lia)) as [Hc|Hc]; [exact (Hnok Hc) | exact (Hnfs Hc)].
      + destruct (Hfrst q ltac:(lia)) as [Hc|Hc]; [exact (Hnok Hc) | exact (Hnfs Hc)].
      + apply Hnok. right; left. split; [lia|]. unfold APPMEM_END in *. lia.
      + apply Hnok. right. right. right. exists (8 * (q - ASAN_K)).
        split; [symmetry; apply Ebb|]. right. left.
        assert (Hin : sp - K <= 8 * (q - ASAN_K) < sp)
          by (clear - Hx HK8 Hspm; unfold shadow_addr, ASAN_K in Hx |- *;
              pose proof (r10_mod8_of16 sp Hspm); Z.div_mod_to_equations; lia).
        split; [lia|]. unfold APPMEM_END in *. lia.
      + apply Hnfs. lia.
      + apply Hnfs. lia.
      + apply Hnfs. lia.
      + apply Hnsh. exists (8 * (q - ASAN_K)). split; [|symmetry; apply Ebb].
        clear - Hx HFS8. unfold shadow_addr, ASAN_K in Hx |- *. unfold AC.FS_SIZE.
        Z.div_mod_to_equations. lia. }
  destruct (r10_fs_store (hb ++ g_H g) mem mem' md FS HAH HFSw HFSr Hagree Hwrit HFSOK')
    as (HAH' & HOWN' & HSTK' & HHI').
  (* the frame's 392 metadata bytes after the arm *)
  assert (Hshnew : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
    { split; [unfold Sfr, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
      split; [unfold HIGHMEM_BEG in HShm; lia|].
      intros a Ha. apply HSW'.
      replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
    destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
    exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
  (* the input block is apart from everything the arm writes *)
  assert (Hinap : forall x, g_p g <= x < g_p g + g_n g ->
            app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            ~ (fr <= x < fr + FRAME_BYTES) /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx.
    destruct (fra_in_apart B APIf ra g fr hb regs mem md HFRA x Hx) as (Hax & Hlx & Hfx & _).
    split; [exact Hax|]. split; [exact Hlx|]. split; [exact Hfx|].
    intros Hfs. destruct (Hinblk ltac:(lia)) as (Hin & _).
    destruct (r10_blocks (hb ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & _ & _ & Hall).
    destruct (Hall x Hx) as (_ & _ & _ & _ & Hnfs).
    exact (Hnfs (Tac_fs.a_fs_in AC.ASYMS mem FS x HFSw HFSr Hfs)). }
  assert (HWinb : forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)).
  { intros x Hx. destruct (Hinap x Hx) as (Hax & Hlx & Hfx & Hnfs).
    split.
    - apply OUTAPP; [exact Hax | lia | lia | lia | intros _; repeat split; lia].
    - apply OUTSH; [exact Hax | exact Hfx | lia | intros _; lia]. }
  (* the registered globals and the slot window stay addressable *)
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Hin.
    assert (Hlo : 0 <= a < AC.GT).
    { destruct Hin as (lo & len & Hil & Hr).
      assert (HBl : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? AC.GT)) AF.frame_AG = true)
        by (vm_compute; reflexivity).
      rewrite forallb_forall in HBl. pose proof (HBl _ Hil) as Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
      cbn [fst snd] in *. lia. }
    apply (r10_addr_keep W mem mem' a 1 (HAG a Hin) MU).
    intros i Hi. replace (a + i) with a by lia.
    apply OUTSH; [unfold app_mem, LOWMEM_END; left; lia | lia | lia | intros _; lia]. }
  assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
            addressable mem' a 1).
  { intros a Ha1 Ha2.
    destruct (Z_le_gt_dec (sp - K) a) as [Hb1|Hb1]; [destruct (Z_lt_ge_dec a sp) as [Hb2|Hb2]|].
    - apply (r10_addr_sub mem' (sp - K) K); [exact HADw' | lia | lia | lia].
    - apply (r10_addr_keep W mem mem' a 1 (HWA a Ha1 Ha2) MU).
      intros i Hi. replace (a + i) with a by lia.
      apply OUTSH; [unfold app_mem; right; lia | exact Ha2 | lia | intros _; lia].
    - apply (r10_addr_keep W mem mem' a 1 (HWA a Ha1 Ha2) MU).
      intros i Hi. replace (a + i) with a by lia.
      apply OUTSH; [unfold app_mem; right; lia | exact Ha2 | lia | intros _; lia]. }
  split.
  { apply (r10_fra g fr hb regs regs' mem mem' md W HFRA MU WM HRO HDJ HAH' HSTK');
      try assumption.
    - intros a Ha. exact (proj2 (HSW' a Ha)).
    - intros x Hx.
      apply OUTAPP; [apply Hfrapp; lia | lia | lia | lia | intros _; repeat split; lia].
    - rewrite HbvA. intros x Hx.
      apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros _; repeat split; lia].
    - rewrite HbvA. intros x Hx.
      apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros _; repeat split; lia].
    - intros x Hx.
      apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros _; repeat split; lia].
    - intros x Hx. destruct (r10_out_dec W x) as [Ho|Hno]; [left; exact Ho | right; exact (Hrd x Hno)].
    - intros Hrec. apply (r10_fsrec mem mem' W fr FS Hrec MU HU OUTLO).
      intros j x Hj Hfrv Hcase.
      apply OUTAPP.
      + apply HFSapp. destruct Hcase as [Hc|Hc]; lia.
      + destruct Hcase as [Hc|Hc]; lia.
      + destruct Hcase as [Hc|Hc]; lia.
      + destruct Hcase as [Hc|Hc]; lia.
      + intros _. destruct Hcase as [Hc|Hc]; repeat split; lia. }
  { eapply ent_munch with (W := W) (mem := mem);
      [exact HENT | exact HAH | exact MU | | exact HSTK' | exact HHI' |
       intros a _ Ho; exact (proj2 (HOWN' a) Ho)].
    intros x Hk.
    destruct Hk as [Hblk | [Himg | [Habv | [(b0 & Hor & ->) | (q & kk & i & Hin & Hni & Hi & ->)]]]].
    - destruct Hblk as (q & kk & i & Hin & Hni & Hi & ->).
      destruct (r10_blocks (hb ++ g_H g) mem md q kk HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hend & _ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      assert (Hnfs' : ~ (FS <= q + i < FS + AC.FS_SIZE))
        by (intros Hc; exact (Hnfs (Tac_fs.a_fs_in AC.ASYMS mem FS (q + i) HFSw HFSr Hc))).
      assert (Hnfr : ~ (fr <= q + i < fr + FRAME_BYTES)).
      { intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        - destruct (Hreal _ Hc) as (Hlo & _). lia.
        - apply Hnfs'. destruct (Hfs _ Hc) as (FSb & HFSbr & Hwb & Hlob & Hhib).
          pose proof (HU FSb Hwb HFSbr) as ->. lia. }
      apply OUTAPP; [exact Happq | lia | lia | lia | intros _; repeat split; lia].
    - apply OUTLO. pose proof (img_below_GT _ Himg) as Hb. unfold AC.GT in Hb. lia.
    - apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros _; repeat split; lia].
    - assert (Hb0 : (0 <= b0 < AC.GT) \/ (g_S g <= b0 < APPMEM_END))
        by (destruct Hor as [Hi|Hr]; [left; exact (img_below_GT b0 Hi) | right; exact Hr]).
      apply OUTSH.
      + unfold app_mem, LOWMEM_END. destruct Hb0 as [Hc|Hc]; [left; lia | right; lia].
      + destruct Hb0 as [Hc|Hc]; lia.
      + destruct Hb0 as [Hc|Hc]; lia.
      + intros _. destruct Hb0 as [Hc|Hc]; lia.
    - (* ent_kept's fifth case: the shadow of an entry block's byte (app memory below stklo, off the side stack
         and the frame) *)
      destruct (r10_blocks (hb ++ g_H g) mem md q kk HAH (in_or_app _ _ _ (or_intror Hin)))
        as (_ & _ & Hend & _ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      assert (Hnfs' : ~ (FS <= q + i < FS + AC.FS_SIZE))
        by (intros Hc; exact (Hnfs (Tac_fs.a_fs_in AC.ASYMS mem FS (q + i) HFSw HFSr Hc))).
      assert (Hnfr : ~ (fr <= q + i < fr + FRAME_BYTES)).
      { intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        - destruct (Hreal _ Hc) as (Hlo & _). lia.
        - apply Hnfs'. destruct (Hfs _ Hc) as (FSb & HFSbr & Hwb & Hlob & Hhib).
          pose proof (HU FSb Hwb HFSbr) as ->. lia. }
      apply OUTSH; [exact Happq | exact Hnfr | lia | intros _; lia]. }
Qed.

(* ---- the two fragment arms ---- *)

(* The fragment call's write list: the record, the three out slots and its own window. *)
Lemma r10_fgfp_in : forall K f pa pp pn S cls x, ~ outside (RFr.fg_fp K f pa pp pn S cls) x ->
  (f <= x < f + 72) \/ (pa <= x < pa + 2) \/ (pp <= x < pp + 8) \/ (pn <= x < pn + 8) \/ (S - K <= x < S).
Proof.
  intros K f pa pp pn S cls x H. destruct cls; cbn [RFr.fg_fp] in H;
    repeat (apply r10_nout_cons in H; destruct H as [H|H]; [tauto|]);
    exfalso; exact (r10_nout_nil x H).
Qed.

(* Writability moves with wmono. *)
Lemma r10_wr_mono : forall m m' a n, wr_at rsegs m a n -> wmono rsegs m m' -> wr_at rsegs m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) WM. split; [exact H0|]. split; [exact H1|].
  intros i Hi. exact (WM (Z_to_bv 64 (a + i)) (H i Hi)).
Qed.

(* Every byte the fragment call writes reads back: the record (its post names its bytes, 72 of them), the three
   out slots on the closing class, and its own window (its post's stk). *)
Lemma r10_fg_rd : forall f pa pp pn st g len m' K S x,
  FGC.fg_mem f pa pp pn st g (fcls len st g) m' -> length st = 72%nat -> length g = 50%nat ->
  stk rsegs m' (S - K) S ->
  ~ outside (RFr.fg_fp K f pa pp pn S (fcls len st g)) x -> exists bb, mrd rsegs m' (wa x) = Some bb.
Proof.
  intros f pa pp pn st g len m' K S x HM Hst Hg HS Hx.
  assert (HL : length (fg_next st g (fcls len st g)) = 72%nat)
    by (change (fg_next st g (fcls len st g)) with (fg_st len st g); apply r10_fgst_len; assumption).
  assert (HW : S - K <= x < S -> exists bb, mrd rsegs m' (wa x) = Some bb)
    by (intros Hxw; destruct HS as (_ & _ & Hs); exact (proj2 (Hs x Hxw))).
  destruct (fcls len st g) eqn:Ec; cbn [RFr.fg_fp] in Hx; cbn [FGC.fg_mem] in HM; cbn [fg_next] in HL.
  - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx]; [exact (HW Hin)|].
    exfalso. exact (r10_nout_nil x Hx).
  - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx]; [exact (HW Hin)|].
    exfalso. exact (r10_nout_nil x Hx).
  - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
    + replace x with (f + (x - f)) by lia. apply (r10_ba_rd m' f _ _ HM). rewrite HL. lia.
    + apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx]; [exact (HW Hin)|].
      exfalso. exact (r10_nout_nil x Hx).
  - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
    + replace x with (f + (x - f)) by lia. apply (r10_ba_rd m' f _ _ HM). rewrite HL. lia.
    + apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx]; [exact (HW Hin)|].
      exfalso. exact (r10_nout_nil x Hx).
  - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
    + replace x with (f + (x - f)) by lia. apply (r10_ba_rd m' f _ _ HM). rewrite HL. lia.
    + apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx]; [exact (HW Hin)|].
      exfalso. exact (r10_nout_nil x Hx).
  - destruct HM as (HMf & HMa & HMp & HMn).
    apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
    + replace x with (f + (x - f)) by lia. apply (r10_ba_rd m' f _ _ HMf). rewrite HL. lia.
    + apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
      * replace x with (pa + (x - pa)) by lia. apply (r10_ba_rd m' pa _ _ HMa).
        rewrite length_le2. lia.
      * apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
        -- replace x with (pp + (x - pp)) by lia. apply (r10_ba_rd m' pp _ _ HMp).
           rewrite length_le8. lia.
        -- apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
           ++ replace x with (pn + (x - pn)) by lia. apply (r10_ba_rd m' pn _ _ HMn).
              rewrite length_le8. lia.
           ++ apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx]; [exact (HW Hin)|].
              exfalso. exact (r10_nout_nil x Hx).
Qed.

(* The fragment call's post moves with the bytes. *)
Lemma r10_fgmem_tr : forall f pa pp pn st g cls m m',
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m' a bs) ->
  FGC.fg_mem f pa pp pn st g cls m -> FGC.fg_mem f pa pp pn st g cls m'.
Proof.
  intros f pa pp pn st g cls m m' TB H. destruct cls; cbn [FGC.fg_mem] in H |- *;
    try exact I; try (apply TB; exact H).
  destruct H as (H1 & H2 & H3 & H4).
  split; [exact (TB _ _ H1)|]. split; [exact (TB _ _ H2)|]. split; [exact (TB _ _ H3) | exact (TB _ _ H4)].
Qed.

(* An application byte is outside a range of the frame's metadata. *)
Lemma r10_out1_app : forall fr lo hi x, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  Sfr fr <= lo -> hi <= Sfr fr + FRAME_SHADOW -> app_mem x -> outside [(lo, hi)] x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr lo hi x Hfa Hlo Hhi Hx. apply KindBGlue.outside_one.
  destruct (Z_lt_ge_dec x lo) as [H|H]; [left; exact H|].
  destruct (Z_lt_ge_dec x hi) as [H2|H2]; [|right; lia].
  exfalso. apply (app_not_shadow x Hx). replace x with (Sfr fr + (x - Sfr fr)) by lia.
  apply r10_fsh; [exact Hfa | lia].
Qed.

(* The body facts every exit cut of this segment shares (the turn's heap block, the loop registers, out[],
   the catalogue bundle RBE), across a run whose write set misses the image, the save area, the frame outside
   [fr + 2256, fr + 2544), the shadow of everything outside that frame range and (adopt 10) the shadow bytes
   S(fr) + 282 .. 290 of the fragment record [fr + 2256, fr + 2328). *)
Lemma r10_base : forall g fr b phi A regs regs' mem mem' W,
  rg regs 9 A -> 0 <= A /\ A + 448 <= 2 ^ 64 ->
  HB mem phi (rnb g b) -> rg regs 22 (Z.of_nat b) -> OURb g fr mem -> CUR g 7 regs -> RBE g fr regs mem ->
  munch W mem mem' ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall y, 0 <= y < 6283264 -> outside W (shadow_addr y)) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> ~ (2256 <= x - fr < 2544) -> outside W x) ->
  (forall i, 0 <= i < FRAME_BYTES -> ~ (2256 <= i < 2544) -> outside W (shadow_addr (fr + i))) ->
  (forall i, 0 <= i < 72 -> outside W (shadow_addr (fr + 2256 + i))) ->
  (forall x, phi <= x < phi + AC.a_size (rnb g b) -> outside W (shadow_addr x)) ->
  (forall x, A <= x < A + 448 -> outside W x) ->
  getr regs' 9 = getr regs 9 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  HB mem' phi (rnb g b) /\ rg regs' 22 (Z.of_nat b) /\ OURb g fr mem' /\ CUR g 7 regs' /\
  RBE g fr regs' mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr b phi A regs regs' mem mem' W Hr9 HA64 HHB Hr22 HOUR HCUR HRBE MU OUTLO OUTIMSH OUTFRB OUTFRSH
    OUTREC OUTPHI OUTA448 E9 E22 E23 E25.
  assert (Hspl : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs' mem' off v).
  { intros off v Hoff (A' & HA' & Hq).
    assert (EA : A' = A).
    { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
      pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
      change (2 ^ 64) with 18446744073709551616 in *. cbn [Z.of_nat] in Hq.
      Z.div_mod_to_equations. lia. }
    subst A'. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
    unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
    rewrite length_le8. intros x Hx. apply OUTA448. cbn [Z.of_nat] in Hx. lia. }
  split.
  { split; [exact (proj1 HHB)|].
    apply (r10_addr_keep W mem mem' phi (AC.a_size (rnb g b)) (proj2 HHB) MU).
    intros i Hi. apply OUTPHI. lia. }
  split; [unfold rg in *; rewrite E22; exact Hr22|].
  split.
  { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
    rewrite OUR_length. intros x Hx. apply OUTFRB; lia. }
  split.
  { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
    split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
  destruct HRBE as (B128 & B312 & B272 & B264 & B256 & B248 & B56 & B184 & B144 & B8 & B32 & B24 & B16 &
                    B96 & B120 & B240 & B232 & B224 & B176 & B208 & B64 &
                    BOUT & BID & BNAME & BOUR & BTBL & BBOX & BMROW &
                    (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b) &
                    B152 & B112 & BFG & B160).
  split; [exact (Hspl 128 _ ltac:(lia) B128)|].
  split; [exact (Hspl 312 _ ltac:(lia) B312)|].
  split; [exact (Hspl 272 _ ltac:(lia) B272)|].
  split; [exact (Hspl 264 _ ltac:(lia) B264)|].
  split; [exact (Hspl 256 _ ltac:(lia) B256)|].
  split; [exact (Hspl 248 _ ltac:(lia) B248)|].
  split; [exact (Hspl 56 _ ltac:(lia) B56)|].
  split; [exact (Hspl 184 _ ltac:(lia) B184)|].
  split; [exact (Hspl 144 _ ltac:(lia) B144)|].
  split; [exact (Hspl 8 _ ltac:(lia) B8)|].
  split; [exact (Hspl 32 _ ltac:(lia) B32)|].
  split; [exact (Hspl 24 _ ltac:(lia) B24)|].
  split; [exact (Hspl 16 _ ltac:(lia) B16)|].
  split; [exact (Hspl 96 _ ltac:(lia) B96)|].
  split; [exact (Hspl 120 _ ltac:(lia) B120)|].
  split; [exact (Hspl 240 _ ltac:(lia) B240)|].
  split; [exact (Hspl 232 _ ltac:(lia) B232)|].
  split; [exact (Hspl 224 _ ltac:(lia) B224)|].
  split; [exact (Hspl 176 _ ltac:(lia) B176)|].
  split; [exact (Hspl 208 _ ltac:(lia) B208)|].
  split; [exact (Hspl 64 _ ltac:(lia) B64)|].
  split.
  { unfold OUTA in *. apply (r10_addr_keep W mem mem' (fr + 544) 1492 BOUT MU).
    intros i Hi. replace (fr + 544 + i) with (fr + (544 + i)) by lia. apply OUTFRSH; lia. }
  split.
  { apply (r10_addr_keep W mem mem' (fr + 2176) 38 BID MU).
    intros i Hi. replace (fr + 2176 + i) with (fr + (2176 + i)) by lia. apply OUTFRSH; lia. }
  split.
  { intros Hnm. destruct (BNAME Hnm) as (Hn1 & Hn2 & Hn3 & Hn4 & Hn5).
    split; [exact Hn1|].
    split.
    { eapply fl_bytes; [exact Hn2 | exact MU |]. intros x Hx. apply OUTLO. unfold AC.GT in Hn5. lia. }
    split.
    { apply (r10_addr_keep W mem mem' _ _ Hn3 MU). intros i Hi.
      apply OUTIMSH. unfold AC.GT in Hn5. lia. }
    split; [exact Hn4 | exact Hn5]. }
  split.
  { apply (r10_addr_keep W mem mem' (fr + 2624) 6 BOUR MU).
    intros i Hi. replace (fr + 2624 + i) with (fr + (2624 + i)) by lia. apply OUTFRSH; lia. }
  split.
  { eapply fl_bytes; [exact BTBL | exact MU |]. intros x Hx. apply OUTLO.
    assert (HT : Z.of_nat (length BAP.ba_tbl) = 168) by (vm_compute; reflexivity).
    rewrite HT in Hx. unfold BAC.BA_FR in *. lia. }
  split.
  { eapply fl_bytes; [exact BBOX | exact MU |]. intros x Hx. apply OUTLO.
    assert (HT : Z.of_nat (length box6) = 6) by (vm_compute; reflexivity).
    rewrite HT in Hx. unfold BOXA in *. lia. }
  split.
  { eapply fl_bytes; [exact BMROW | exact MU |]. intros x Hx. apply OUTLO.
    pose proof (r10_mrow_rng (g_in g)) as (Hm1 & _).
    assert (HT : Z.of_nat (length (rt_mb (g_in g))) = 296) by (rewrite r10_mb_len; reflexivity).
    unfold CAT in *. lia. }
  split.
  { unfold PRA.
    split; [exact (Hspl 136 _ ltac:(lia) P136)|].
    split; [exact (Hspl 280 _ ltac:(lia) P280)|].
    split; [exact (Hspl 168 _ ltac:(lia) P168)|].
    split; [exact (Hspl 192 _ ltac:(lia) P192)|].
    split; [exact (Hspl 200 _ ltac:(lia) P200)|].
    split; [exact (Hspl 216 _ ltac:(lia) P216)|].
    split; [exact (Hspl 104 _ ltac:(lia) P104)|].
    split; [exact (Hspl 288 _ ltac:(lia) P288)|].
    split; [exact (Hspl 296 _ ltac:(lia) P296)|].
    split; [exact (Hspl 304 _ ltac:(lia) P304)|].
    exact (Hspl 168 _ ltac:(lia) P168b). }
  split; [exact (Hspl 152 _ ltac:(lia) B152)|].
  split; [exact (Hspl 112 _ ltac:(lia) B112)|].
  split; [exact (r10_addr_keep W mem mem' (fr + 2256) 72 BFG MU OUTREC)|].
  exact (Hspl 160 _ ltac:(lia) B160).
Qed.

(* ==== the arms, on the official entry Inv_B817a4_at ==== *)

(* ---- the b = 0 arm: 0x817a4 -> 0x818a8 (Inv_B818a8_at at i = 0) ---- *)
Lemma r10_arm0 : forall (b : nat), b = 0%nat ->
  Hat B APIf ra (Inv_B818a8_at B APIf ra) b -> Hat B APIf ra (Inv_B817a4_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hb0 Hexit g c HInv. subst b.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR &
                    HRBE & Hr21 & Ha0 & HRF & H24 & H16 & H96 & H120 & HAD2256 & H5rf & Hr27).
  subst c. rewrite SEGS.
  pose proof HRF as ((HRB & Hnz & Hr20 & HFb) & HrN).
  destruct (r10_rtk (g_in g) 0%nat ltac:(lia) Hnz) as (Hk & Hn52 & Hlen).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0%nat) in Hn52, Hlen.
  rewrite Hk in Ha0.
  destruct (fra_fsfree B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA)
    as (FS & HFSw & HFSr & HFSok & HFSGT & HFSal & HFSappA & HFSend & HFSfr & _).
  set (W := [(Sfr fr + 306, Sfr fr + 318)]) in *.
  assert (Hsub : forall x, ~ outside W x -> r10_in false false fr (AC.aspZ regs) 0 FS x).
  { intros x Hx. apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil].
    - left. lia.
    - exfalso. exact (r10_nout_nil x Hnil). }
  destruct (r10_outs g fr (hb1 phi (rnb g 0)) regs mem md FS false false 0 W HFRA HFSw HFSr
              ltac:(unfold FN_STACK, AF.SLOT_STACK; lia) ltac:(reflexivity) Hsub)
    as (HGTFS & HFS8 & HFSapp & HFSstk & HFSfr2 & HGTfr & Hfr8 & Hfrapp & HfrE & Hstklo & Hhm & Hwlo & Hwhi &
        HSapp & Hwapp & HShm & OUTLO & OUTAPP & OUTSH).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo2 & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  rewrite Haspz in Hwlo, Hwhi, Hwapp, OUTAPP, OUTSH.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAb : 0 <= A /\ A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(unfold AC.GT in HGTfr; lia) ltac:(lia)); lia).
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HbvS3 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit;
        unfold HIGHMEM_BEG in HShm; lia).
  (* the granule map of the frame, and the one written granule range *)
  assert (HshFr : forall i, 0 <= i -> shadow_addr (fr + i) = Sfr fr + i / 8).
  { intros i Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  assert (OUTFRSH : forall i, 0 <= i -> ~ (2448 <= i < 2544) -> outside W (shadow_addr (fr + i))).
  { intros i Hi Hni. rewrite (HshFr i Hi). apply KindBGlue.outside_one.
    Z.div_mod_to_equations. lia. }
  assert (OUTFRB : forall x, fr <= x < fr + FRAME_BYTES -> outside W x).
  { intros x Hx. apply (r10_out1_app fr); [exact Hfrapp | lia | lia | exact (Hfrapp x Hx)]. }
  (* the heap block of the turn *)
  assert (Hsz : AC.a_size (rnb g 0) = rnb g 0) by (unfold AC.a_size; lia).
  assert (HInb : In (phi, rnb g 0) (hb1 phi (rnb g 0) ++ g_H g)) by (left; reflexivity).
  destruct (r10_blocks (hb1 phi (rnb g 0) ++ g_H g) mem md phi (rnb g 0) HAH HInb)
    as (_ & _ & Hpstklo & _ & Hblkb).
  assert (Hphifr : forall x, phi <= x < phi + rnb g 0 -> app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros x Hx. destruct (Hblkb x Hx) as (Happx & _ & _ & _ & Hnfs).
    split; [exact Happx|]. intros Hc.
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - destruct (Hreal x Hc) as (Hlo & _). lia.
    - exact (Hnfs (Hfs x Hc)). }
  assert (OUTPHI : forall x, phi <= x < phi + rnb g 0 -> outside W x /\ outside W (shadow_addr x)).
  { intros x Hx. destruct (Hphifr x Hx) as (Happx & Hnfr).
    split.
    - apply OUTAPP; [exact Happx | | | | intros Hc; discriminate Hc];
        (intros Hc; apply Hnfr; lia).
    - apply OUTSH; [exact Happx | exact Hnfr | lia | intros Hc; discriminate Hc]. }
  (* the run, on the normalized memory *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (Hst12 : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 12)).
  { split; [lia|]. split; [cbn [Z.of_nat]; unfold HIGHMEM_BEG, APPMEM_END in *; lia|].
    intros a Ha. cbn [Z.of_nat] in Ha. apply HSWm.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (Sfr fr + 306) _ HR0 ltac:(lia) Hst12) as Hst12n.
  destruct (r10_rw_stkn (normalize rsegs mem) (Sfr fr + 306) 12%nat Hst12n) as (junk & Hjl & HRW).
  assert (Hphi0 : 0 <= phi /\ phi + 18 < 2 ^ 64).
  { pose proof HFb as HFb'. apply bytes_at_bound in HFb'. rewrite Hlen in HFb'. lia. }
  apply (r10_run regs (Z_to_bv 64 0x817a4) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x818a8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
       getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27 /\
       munch W (normalize rsegs mem) m0' /\ wmono rsegs (normalize rsegs mem) m0' /\
       (exists l12, bytes_at rsegs m0' (Sfr fr + 306) l12 /\ length l12 = 12%nat) /\
       (exists c3, bytes_at rsegs m0' (Sfr fr + 316) [c3] /\ bv_signed c3 = 0) /\
       (exists c4, bytes_at rsegs m0' (Sfr fr + 317) [c4] /\ bv_signed c4 = 4))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r10_mkR_of.
    eapply evt_mono.
    + apply (r10_cfg0 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr (normalize rsegs mem) phi junk).
      * exact Hr20.
      * exact Hr21.
      * exact Hr22.
      * exact Ha0.
      * lia.
      * lia.
      * rewrite HbvS3. exact HRW.
      * exact HMI0.
    + intros ms' (R & m1 & l12 & c3 & c4 & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P20 & P22 & P23 & P24 & P25 &
                  P26 & P21 & P10 & P11 & P12 & P14 & P13 & P18 & P27 & MUq & WMq & MIq & Hb12 & Hl12 & Hb3 & Hs3v &
                  Hb4 & Hs4v).
      rewrite HbvS3 in MUq, Hb12, Hb3, Hb4.
      exists R, (Z_to_bv 64 0x818a8), m1. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P20|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P25|]. split; [exact P26|]. split; [exact P21|].
      split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P14|].
      split; [exact P13|]. split; [exact P18|]. split; [exact P27|].
      split; [exact MUq|]. split; [exact WMq|].
      split; [exists l12; split; [exact Hb12 | exact Hl12]|].
      split; [exists c3; split; [exact Hb3 | exact Hs3v] | exists c4; split; [exact Hb4 | exact Hs4v]].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K22 & K23 & K24 & K25 & K26 & K21 & K10 & K11 & K12 & K14 &
       K13 & K18 & K27 &
       MU0 & WM0 & (l12 & Hb12 & Hl12) & (c3 & Hb3 & Hs3v) & (c4 & Hb4 & Hs4v)) Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E21 : getr regs'' 21 = Z_to_bv 64 36) by (rewrite Hreg; exact K21).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (phi + 18)) by (rewrite Hreg; exact K10).
    assert (E11 : getr regs'' 11 = Z_to_bv 64 0) by (rewrite Hreg; exact K11).
    assert (E12 : getr regs'' 12 = Z_to_bv 64 (phi + 18)) by (rewrite Hreg; exact K12).
    assert (E14 : getr regs'' 14 = Z_to_bv 64 32) by (rewrite Hreg; exact K14).
    assert (E13 : getr regs'' 13 = Z_to_bv 64 (- (phi + 18))) by (rewrite Hreg; exact K13).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    (* back from the normalized memory *)
    assert (TB' : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (TB' _ _ Hb12) as Hb12'. pose proof (TB' _ _ Hb3) as Hb3'. pose proof (TB' _ _ Hb4) as Hb4'.
    (* every written byte reads back *)
    assert (Hrd : forall x, ~ outside W x -> exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exfalso; exact (r10_nout_nil x Hnil)].
      replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
      apply (r10_ba_rd mem' (Sfr fr + 306) l12); [exact Hb12' | rewrite Hl12; lia]. }
    assert (HSW' : shadow_rw mem').
    { apply (r10_srw_keep W mem mem' HSWm MU WM). intros x _ Hno. exact (Hrd x Hno). }
    assert (HDJ : rt_disjoint W).
    { apply r10_rt_disjoint. repeat constructor. cbn [fst]. unfold AC.GT. lia. }
    assert (HPres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
              exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq (bb & Hb). destruct (r10_out_dec W q) as [Ho|Hno].
      - exists bb. rewrite (KindBGlue.mbyte_munch rsegs W mem mem' q MU Hq Ho). exact Hb.
      - rewrite r10_mbyte_mrd. exact (Hrd q Hno). }
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (r10_fsok_keep mem mem' W FS HFSok MU
               ltac:(intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)) HPres);
        [| unfold AC.GT in HGTFS; lia | unfold AC.FS_SIZE, APPMEM_END in *; lia].
      intros q Hq. apply OUTAPP; [apply HFSapp; unfold AC.FS_SIZE; lia | lia | lia | lia |
                                 intros Hc; discriminate Hc]. }
    assert (HADw : addressable mem' (AC.aspZ regs - 0) 0).
    { rewrite Haspz. split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|]. intros i Hi. lia. }
    destruct (r10_land g fr (hb1 phi (rnb g 0)) regs regs'' mem mem' md FS false false 0 W
                HFRA HENT HFSw HFSr HFSOK' ltac:(unfold FN_STACK, AF.SLOT_STACK; lia) ltac:(reflexivity)
                MU WM HRO' HDJ Hsub Hrd HSW' HADw E2 E3 E4 E8 E9 E19 E26) as (HFRAm & HENTm).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g 0)) regs'' regs'' mem' md md' HFRAm);
          try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g 0)) mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
    (* the spills and byte facts the exit cut reads *)
    assert (HAout : forall off, 0 <= off <= 440 -> forall x, A + off <= x < A + off + 8 -> outside W x).
    { intros off Hoff x Hx.
      apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
    assert (Hspl : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A' & HA' & Hq).
      assert (EA : A' = A).
      { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
        pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
        change (2 ^ 64) with 18446744073709551616 in *. cbn [Z.of_nat] in Hq.
        Z.div_mod_to_equations. lia. }
      subst A'. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply (HAout off Hoff). cbn [Z.of_nat] in Hx. lia. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, 0%nat, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [lia|].
    split.
    { split; [exact (proj1 HHB)|].
      apply (r10_addr_keep W mem mem' phi (AC.a_size (rnb g 0)) (proj2 HHB) MU).
      intros i Hi. rewrite Hsz in Hi. exact (proj2 (OUTPHI (phi + i) ltac:(lia))). }
    split; [unfold rg in *; rewrite E22; exact Hr22|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      rewrite OUR_length. intros x Hx. apply OUTFRB. lia. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    split.
    { refine (proj2 (proj2 (proj2 (proj2 (r10_base g fr 0%nat phi A regs regs'' mem mem' W Hr9 HAb HHB Hr22 HOUR
                HCUR HRBE MU OUTLO _ _ _ _ _ _ E9 E22 E23 E25))))).
      - intros y Hy. apply OUTSH; [unfold app_mem, LOWMEM_END; left; lia | unfold AC.GT in HGTfr; lia | lia |
                                   intros Hc; discriminate Hc].
      - intros x Hx _. apply OUTFRB. exact Hx.
      - intros i Hi Hn. apply OUTFRSH; lia.
      - intros i Hi. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia. apply OUTFRSH; lia.
      - intros x Hx. rewrite Hsz in Hx. exact (proj2 (OUTPHI x Hx)).
      - intros x Hx. apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
    split; [unfold rg; rewrite E21; reflexivity|].
    split; [lia|].
    split; [unfold rg; rewrite E10; f_equal; cbn [Z.of_nat]; lia|].
    split; [unfold rg; rewrite E12; f_equal; cbn [Z.of_nat]; lia|].
    split; [unfold rg; rewrite E14; f_equal; cbn [Z.of_nat]; lia|].
    split; [reflexivity|].
    split; [lia|].
    split; [unfold rg; rewrite E11; f_equal; reflexivity|].
    split.
    { split; [|unfold rg in *; rewrite E18; exact HrN].
      split.
      { destruct HRB as (Hb6' & HCUR' & HOUR' & Hr22' & HIDB & HFGB).
        split; [exact Hb6'|].
        split.
        { destruct HCUR' as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
          split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
        split.
        { unfold OURb in *. eapply fl_bytes; [exact HOUR' | exact MU |].
          rewrite OUR_length. intros x Hx. apply OUTFRB. lia. }
        split; [unfold rg in *; rewrite E22; exact Hr22'|].
        split.
        { unfold IDBr in *. eapply fl_bytes; [exact HIDB | exact MU |].
          rewrite r10_rid_len. intros x Hx. apply OUTFRB. lia. }
        { unfold FGBr in *. eapply fl_bytes; [exact HFGB | exact MU |].
          rewrite r10_rfg_len. intros x Hx. apply OUTFRB. lia. } }
      split; [exact Hnz|].
      split; [unfold rg in *; rewrite E20; exact Hr20|].
      eapply fl_bytes; [exact HFb | exact MU |]. rewrite Hlen. intros x Hx.
      exact (proj1 (OUTPHI x ltac:(lia))). }
    split; [exact (Hspl 24 _ ltac:(lia) H24)|].
    split; [exact (Hspl 16 _ ltac:(lia) H16)|].
    split; [exact (Hspl 96 _ ltac:(lia) H96)|].
    split; [exact (Hspl 120 _ ltac:(lia) H120)|].
    (* the 12 ports bytes: the two metadata bytes the arm wrote *)
    split.
    { replace 12 with (8 + 4) by lia.
      apply r10_addr_cat.
      + apply (r10_addr_sh mem' (fr + 2528) 8 c3).
        * rewrite (HshFr 2528 ltac:(lia)). replace (2528 / 8) with 316 by reflexivity. exact Hb3'.
        * clear - Hfr8. Z.div_mod_to_equations. lia.
        * lia.
        * left. exact Hs3v.
        * intros i Hi. apply Hfrapp. lia.
        * unfold AC.GT in HGTfr. lia.
        * lia.
      + replace (fr + 2528 + 8) with (fr + 2536) by lia.
        apply (r10_addr_sh mem' (fr + 2536) 4 c4).
        * rewrite (HshFr 2536 ltac:(lia)). replace (2536 / 8) with 317 by reflexivity. exact Hb4'.
        * clear - Hfr8. Z.div_mod_to_equations. lia.
        * lia.
        * right. lia.
        * intros i Hi. apply Hfrapp. lia.
        * unfold AC.GT in HGTfr. lia.
        * lia. }
    (* the room word of the prologue and s2 = 32 (not written by the arm) *)
    split; [unfold rg; exact E13|].
    unfold rg in *. rewrite E27. exact Hr27.
Qed.

(* ---- the b = 1, 2 arm: 0x817a4 -> 0x8194c (Inv_B8194c_at at i = 0) ---- *)
Lemma r10_arm12 : forall (b : nat), (b = 1 \/ b = 2)%nat ->
  Hat B APIf ra (Inv_B8194c_at B APIf ra) b -> Hat B APIf ra (Inv_B817a4_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hb12 Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR &
                    HRBE & Hr21 & Ha0 & HRF & H24 & H16 & H96 & H120 & HAD2256 & H5rf & Hr27).
  subst c. rewrite SEGS.
  pose proof HRF as ((HRB & Hnz & Hr20 & HFb) & HrN).
  destruct (r10_rtk (g_in g) b ltac:(lia) Hnz) as (Hk & Hn52 & Hlen).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hn52, Hlen.
  rewrite Hk in Ha0.
  assert (Hkv : r10_kind b = 5) by (destruct Hb12 as [-> | ->]; reflexivity).
  rewrite Hkv in Ha0.
  destruct (fra_fsfree B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA)
    as (FS & HFSw & HFSr & HFSok & HFSGT & HFSal & HFSappA & HFSend & HFSfr & _).
  set (W := [(Sfr fr + 306, Sfr fr + 318)]) in *.
  assert (Hsub : forall x, ~ outside W x -> r10_in false false fr (AC.aspZ regs) 0 FS x).
  { intros x Hx. apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil].
    - left. lia.
    - exfalso. exact (r10_nout_nil x Hnil). }
  destruct (r10_outs g fr (hb1 phi (rnb g b)) regs mem md FS false false 0 W HFRA HFSw HFSr
              ltac:(unfold FN_STACK, AF.SLOT_STACK; lia) ltac:(reflexivity) Hsub)
    as (HGTFS & HFS8 & HFSapp & HFSstk & HFSfr2 & HGTfr & Hfr8 & Hfrapp & HfrE & Hstklo & Hhm & Hwlo & Hwhi &
        HSapp & Hwapp & HShm & OUTLO & OUTAPP & OUTSH).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo2 & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  rewrite Haspz in Hwlo, Hwhi, Hwapp, OUTAPP, OUTSH.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAb : 0 <= A /\ A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(unfold AC.GT in HGTfr; lia) ltac:(lia)); lia).
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HbvS3 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit;
        unfold HIGHMEM_BEG in HShm; lia).
  assert (HshFr : forall i, 0 <= i -> shadow_addr (fr + i) = Sfr fr + i / 8).
  { intros i Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  assert (OUTFRSH : forall i, 0 <= i -> ~ (2448 <= i < 2544) -> outside W (shadow_addr (fr + i))).
  { intros i Hi Hni. rewrite (HshFr i Hi). apply KindBGlue.outside_one.
    Z.div_mod_to_equations. lia. }
  assert (OUTFRB : forall x, fr <= x < fr + FRAME_BYTES -> outside W x).
  { intros x Hx. apply (r10_out1_app fr); [exact Hfrapp | lia | lia | exact (Hfrapp x Hx)]. }
  assert (Hsz : AC.a_size (rnb g b) = rnb g b) by (unfold AC.a_size; lia).
  assert (HInb : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)) by (left; reflexivity).
  destruct (r10_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInb)
    as (_ & _ & Hpstklo & _ & Hblkb).
  assert (Hphifr : forall x, phi <= x < phi + rnb g b -> app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros x Hx. destruct (Hblkb x Hx) as (Happx & _ & _ & _ & Hnfs).
    split; [exact Happx|]. intros Hc.
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - destruct (Hreal x Hc) as (Hlo & _). lia.
    - exact (Hnfs (Hfs x Hc)). }
  assert (OUTPHI : forall x, phi <= x < phi + rnb g b -> outside W x /\ outside W (shadow_addr x)).
  { intros x Hx. destruct (Hphifr x Hx) as (Happx & Hnfr).
    split.
    - apply OUTAPP; [exact Happx | | | | intros Hc; discriminate Hc];
        (intros Hc; apply Hnfr; lia).
    - apply OUTSH; [exact Happx | exact Hnfr | lia | intros Hc; discriminate Hc]. }
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (Hst12 : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 12)).
  { split; [lia|]. split; [cbn [Z.of_nat]; unfold HIGHMEM_BEG, APPMEM_END in *; lia|].
    intros a Ha. cbn [Z.of_nat] in Ha. apply HSWm.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (Sfr fr + 306) _ HR0 ltac:(lia) Hst12) as Hst12n.
  destruct (r10_rw_stkn (normalize rsegs mem) (Sfr fr + 306) 12%nat Hst12n) as (junk & Hjl & HRW).
  assert (Hphi0 : 0 <= phi /\ phi + 18 < 2 ^ 64).
  { pose proof HFb as HFb'. apply bytes_at_bound in HFb'. rewrite Hlen in HFb'. lia. }
  apply (r10_run regs (Z_to_bv 64 0x817a4) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x8194c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
       getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27 /\
       munch W (normalize rsegs mem) m0' /\ wmono rsegs (normalize rsegs mem) m0' /\
       (exists l12, bytes_at rsegs m0' (Sfr fr + 306) l12 /\ length l12 = 12%nat))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r10_mkR_of.
    eapply evt_mono.
    + apply (r10_sum12 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr (normalize rsegs mem) phi (Z.of_nat b) junk).
      * exact Hr20.
      * exact Hr21.
      * exact Hr22.
      * exact Ha0.
      * destruct Hb12 as [-> | ->]; [left | right]; reflexivity.
      * lia.
      * lia.
      * rewrite HbvS3. exact HRW.
      * exact HMI0.
    + intros ms' (R & m1 & l12 & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P20 & P22 & P23 & P24 & P25 &
                  P26 & P21 & P10 & P11 & P12 & P14 & P13 & P18 & P27 & MUq & WMq & MIq & Hb12b & Hl12).
      rewrite HbvS3 in MUq, Hb12b.
      exists R, (Z_to_bv 64 0x8194c), m1. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P20|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P25|]. split; [exact P26|]. split; [exact P21|].
      split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P14|].
      split; [exact P13|]. split; [exact P18|]. split; [exact P27|].
      split; [exact MUq|]. split; [exact WMq|].
      exists l12. split; [exact Hb12b | exact Hl12].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K22 & K23 & K24 & K25 & K26 & K21 & K10 & K11 & K12 & K14 &
       K13 & K18 & K27 & MU0 & WM0 & (l12 & Hb12b & Hl12)) Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E21 : getr regs'' 21 = Z_to_bv 64 36) by (rewrite Hreg; exact K21).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (phi + 18)) by (rewrite Hreg; exact K10).
    assert (E11 : getr regs'' 11 = Z_to_bv 64 0) by (rewrite Hreg; exact K11).
    assert (E12 : getr regs'' 12 = Z_to_bv 64 (phi + 18)) by (rewrite Hreg; exact K12).
    assert (E14 : getr regs'' 14 = Z_to_bv 64 32) by (rewrite Hreg; exact K14).
    assert (E13 : getr regs'' 13 = Z_to_bv 64 (- (phi + 18))) by (rewrite Hreg; exact K13).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (TB' : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (TB' _ _ Hb12b) as Hb12'.
    assert (Hrd : forall x, ~ outside W x -> exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exfalso; exact (r10_nout_nil x Hnil)].
      replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
      apply (r10_ba_rd mem' (Sfr fr + 306) l12); [exact Hb12' | rewrite Hl12; lia]. }
    assert (HSW' : shadow_rw mem').
    { apply (r10_srw_keep W mem mem' HSWm MU WM). intros x _ Hno. exact (Hrd x Hno). }
    assert (HDJ : rt_disjoint W).
    { apply r10_rt_disjoint. repeat constructor. cbn [fst]. unfold AC.GT. lia. }
    assert (HPres : forall q, 0 <= q < 2 ^ 64 -> (exists bb, mbyte rsegs mem q = Some bb) ->
              exists bb, mbyte rsegs mem' q = Some bb).
    { intros q Hq (bb & Hb). destruct (r10_out_dec W q) as [Ho|Hno].
      - exists bb. rewrite (KindBGlue.mbyte_munch rsegs W mem mem' q MU Hq Ho). exact Hb.
      - rewrite r10_mbyte_mrd. exact (Hrd q Hno). }
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (r10_fsok_keep mem mem' W FS HFSok MU
               ltac:(intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)) HPres);
        [| unfold AC.GT in HGTFS; lia | unfold AC.FS_SIZE, APPMEM_END in *; lia].
      intros q Hq. apply OUTAPP; [apply HFSapp; unfold AC.FS_SIZE; lia | lia | lia | lia |
                                 intros Hc; discriminate Hc]. }
    assert (HADw : addressable mem' (AC.aspZ regs - 0) 0).
    { rewrite Haspz. split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|]. intros i Hi. lia. }
    destruct (r10_land g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md FS false false 0 W
                HFRA HENT HFSw HFSr HFSOK' ltac:(unfold FN_STACK, AF.SLOT_STACK; lia) ltac:(reflexivity)
                MU WM HRO' HDJ Hsub Hrd HSW' HADw E2 E3 E4 E8 E9 E19 E26) as (HFRAm & HENTm).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAm);
          try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
    assert (HAout : forall off, 0 <= off <= 440 -> forall x, A + off <= x < A + off + 8 -> outside W x).
    { intros off Hoff x Hx.
      apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
    assert (Hspl : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A' & HA' & Hq).
      assert (EA : A' = A).
      { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
        pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
        change (2 ^ 64) with 18446744073709551616 in *. cbn [Z.of_nat] in Hq.
        Z.div_mod_to_equations. lia. }
      subst A'. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply (HAout off Hoff). cbn [Z.of_nat] in Hx. lia. }
    rewrite <- SEGS. apply Hexit. exists phi, 0%nat, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [lia|].
    split.
    { split; [exact (proj1 HHB)|].
      apply (r10_addr_keep W mem mem' phi (AC.a_size (rnb g b)) (proj2 HHB) MU).
      intros i Hi. rewrite Hsz in Hi. exact (proj2 (OUTPHI (phi + i) ltac:(lia))). }
    split; [unfold rg in *; rewrite E22; exact Hr22|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      rewrite OUR_length. intros x Hx. apply OUTFRB. lia. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    split.
    { refine (proj2 (proj2 (proj2 (proj2 (r10_base g fr b phi A regs regs'' mem mem' W Hr9 HAb HHB Hr22 HOUR
                HCUR HRBE MU OUTLO _ _ _ _ _ _ E9 E22 E23 E25))))).
      - intros y Hy. apply OUTSH; [unfold app_mem, LOWMEM_END; left; lia | unfold AC.GT in HGTfr; lia | lia |
                                   intros Hc; discriminate Hc].
      - intros x Hx _. apply OUTFRB. exact Hx.
      - intros i Hi Hn. apply OUTFRSH; lia.
      - intros i Hi. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia. apply OUTFRSH; lia.
      - intros x Hx. rewrite Hsz in Hx. exact (proj2 (OUTPHI x Hx)).
      - intros x Hx. apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
    split; [unfold rg; rewrite E21; reflexivity|].
    split; [lia|].
    split; [unfold rg; rewrite E10; f_equal; cbn [Z.of_nat]; lia|].
    split; [unfold rg; rewrite E12; f_equal; cbn [Z.of_nat]; lia|].
    split; [unfold rg; rewrite E14; f_equal; cbn [Z.of_nat]; lia|].
    split; [exact Hb12|].
    split; [lia|].
    split; [unfold rg; rewrite E11; f_equal; reflexivity|].
    split.
    { split.
      { destruct HRB as (Hb6' & HCUR' & HOUR' & Hr22' & HIDB & HFGB).
        split; [exact Hb6'|].
        split.
        { destruct HCUR' as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
          split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
        split.
        { unfold OURb in *. eapply fl_bytes; [exact HOUR' | exact MU |].
          rewrite OUR_length. intros x Hx. apply OUTFRB. lia. }
        split; [unfold rg in *; rewrite E22; exact Hr22'|].
        split.
        { unfold IDBr in *. eapply fl_bytes; [exact HIDB | exact MU |].
          rewrite r10_rid_len. intros x Hx. apply OUTFRB. lia. }
        { unfold FGBr in *. eapply fl_bytes; [exact HFGB | exact MU |].
          rewrite r10_rfg_len. intros x Hx. apply OUTFRB. lia. } }
      split; [exact Hnz|].
      split; [unfold rg in *; rewrite E20; exact Hr20|].
      eapply fl_bytes; [exact HFb | exact MU |]. rewrite Hlen. intros x Hx.
      exact (proj1 (OUTPHI x ltac:(lia))). }
    (* the room word of the prologue and s2 = 32 (not written by the arm) *)
    split; [unfold rg; exact E13|].
    unfold rg in *. rewrite E27. exact Hr27.
Qed.

(* ---- b = 6: 0x817a4 -> FRAG@0x81830 -> 0x81834 (Inv_B81834_at) ---- *)
Lemma r10_arm6 : forall (b : nat), b = 6%nat ->
  Hat B APIf ra (Inv_B81834_at B APIf ra) b -> Hat B APIf ra (Inv_B817a4_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hb6v Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR &
                    HRBE & Hr21 & Ha0 & HRF & H24 & H16 & H96 & H120 & HAD2256 & H5rf & Hr27).
  subst c. rewrite SEGS.
  pose proof HRF as ((HRB & Hnz & Hr20 & HFb) & HrN).
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H240 & H232 & H224 & _).
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & _ & _ & _ & _ & _ & _ & _ & _ & H112 & _).
  destruct (r10_rtk (g_in g) b ltac:(lia) Hnz) as (Hk & Hn52 & Hlen).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hn52, Hlen.
  assert (Hkv : r10_kind b = 11) by (subst b; reflexivity).
  rewrite Hk, Hkv in Ha0.
  destruct (fra_fsfree B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA)
    as (FS & HFSw & HFSr & HFSok & HFSGT & HFSal & HFSappA & HFSend & HFSfrb & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo2 & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (proj2 HHB) as (HpA0 & HnA0 & HpAe & _).
  set (KF := FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) in *.
  assert (HKF : KF = 4672) by reflexivity.
  set (g50 := rt_g (g_in g) (Z.of_nat b)) in *.
  set (st72 := RFG (g_in g) b) in *.
  set (N := rnb g b) in *.
  assert (Hsz : AC.a_size N = N) by (unfold AC.a_size; lia).
  assert (Hg50l : length g50 = 50%nat) by (unfold g50; apply r10_rtg_len).
  assert (Hst72l : length st72 = 72%nat) by (unfold st72; apply r10_rfg_len).
  assert (Hphib : 0 < phi /\ phi + N <= 2 ^ 64 /\ phi + 50 <= 2 ^ 64).
  { pose proof (proj1 HHB) as Hphinz.
    pose proof HFb as HFb'. apply bytes_at_bound in HFb'. rewrite Hlen in HFb'. lia. }
  set (W2 := RFr.fg_fp KF (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) sp (fcls N st72 g50)) in *.
  set (W := [(Sfr fr + 306, Sfr fr + 313)] ++ W2) in *.
  assert (Hsub : forall x, ~ outside W x -> r10_in true false fr (AC.aspZ regs) KF FS x).
  { intros x Hx. apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
    - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [left; lia|].
      exfalso. exact (r10_nout_nil x Hnil).
    - destruct (r10_fgfp_in _ _ _ _ _ _ _ x Hx) as [H|[H|[H|[H|H]]]].
      + right. right. left. split; [reflexivity | lia].
      + right. left. lia.
      + right. left. lia.
      + right. left. lia.
      + right. right. right. left. rewrite Haspz. lia. }
  destruct (r10_outs g fr (hb1 phi (rnb g b)) regs mem md FS true false KF W HFRA HFSw HFSr
              ltac:(rewrite HKF; unfold FN_STACK, AF.SLOT_STACK; lia) ltac:(rewrite HKF; reflexivity) Hsub)
    as (HGTFS & HFS8 & HFSapp & HFSstk & HFSfr2 & HGTfr & Hfr8 & Hfrapp & HfrE & Hstklo & Hhm & Hwlo & Hwhi &
        HSapp & Hwapp & HShm & OUTLO & OUTAPP & OUTSH).
  rewrite Haspz in Hwlo, Hwhi, Hwapp, OUTAPP, OUTSH, Hplace, Hlo, Hstkw.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAb : 0 <= A /\ A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(unfold AC.GT in HGTfr; lia) ltac:(lia)); lia).
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HGv : AC.GT = 6283264) by reflexivity.
  assert (HbvS3 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit; unfold HIGHMEM_BEG in HShm; lia).
  assert (Hbvsp : bv_unsigned (getr regs 2) = sp)
    by (rewrite Hr2; apply MState.unsigned_lit; unfold APPMEM_END in *; lia).
  assert (Ecls : RcFrag.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50
                 = fcls N st72 g50)
    by (apply r10_fgc; unfold AC.GT in HGTfr; lia).
  (* turn 6 of the round-trip model is a closing fragment (RtmB, computed over the 11 catalogue rows) *)
  assert (Hcls : fcls N st72 g50 = RFr.FgClose).
  { assert (Hn6 : rt_n (g_in g) 6 <> 0) by (unfold N, rnb in Hnz; rewrite Hb6v in Hnz; exact Hnz).
    pose proof (RtmB.rb_rtm_close (g_in g) Hn6) as Hc.
    unfold N, st72, g50, rnb. rewrite Hb6v. exact Hc. }
  assert (HshFr : forall i, 0 <= i -> shadow_addr (fr + i) = Sfr fr + i / 8).
  { intros i Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  pose proof (Hplace KF ltac:(rewrite HKF; unfold FN_STACK, AF.SLOT_STACK in *; lia)) as Hsep.
  assert (NSH1 : forall x, app_mem x -> ~ (Sfr fr + 306 <= x < Sfr fr + 313)).
  { intros x Hax Hc. apply (app_not_shadow x Hax).
    replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  assert (OUTSH1 : forall y, ~ (fr <= y < fr + FRAME_BYTES) -> outside [(Sfr fr + 306, Sfr fr + 313)] (shadow_addr y)).
  { intros y Hy. apply KindBGlue.outside_one.
    assert (E : shadow_addr (fr + 8 * FRAME_SHADOW) = Sfr fr + FRAME_SHADOW)
      by (rewrite (HshFr (8 * FRAME_SHADOW) ltac:(lia)); f_equal; reflexivity).
    pose proof (r10_shq fr FRAME_SHADOW y Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hq.
    rewrite E in Hq. unfold Sfr in Hq |- *. lia. }
  assert (OUTW2SH : forall x, in_shadow x -> outside W2 x).
  { intros x Hx. destruct (r10_out_dec W2 x) as [Ho|Hno]; [exact Ho|]. exfalso.
    destruct (r10_fgfp_in _ _ _ _ _ _ _ x Hno) as [H|[H|[H|[H|H]]]].
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hwapp x ltac:(lia)) Hx). }
  assert (OUTWSH : forall y, ~ (fr <= y < fr + FRAME_BYTES) -> app_mem y -> outside W (shadow_addr y)).
  { intros y Hy Hay. apply r10_out_app; [exact (OUTSH1 y Hy) | apply OUTW2SH; apply shadow_of_app; exact Hay]. }
  assert (OUTFRB : forall x, fr <= x < fr + FRAME_BYTES -> ~ (2256 <= x - fr < 2544) -> outside W x).
  { intros x Hx H1. apply OUTAPP; [apply Hfrapp; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
  assert (OUTFRSH : forall i, 0 <= i < FRAME_BYTES -> ~ (2256 <= i < 2544) -> outside W (shadow_addr (fr + i))).
  { intros i Hi H1. apply r10_out_app.
    - apply KindBGlue.outside_one. rewrite (HshFr i ltac:(lia)). Z.div_mod_to_equations. lia.
    - apply OUTW2SH. apply shadow_of_app. apply Hfrapp. lia. }
  assert (OUTREC : forall i, 0 <= i < 72 -> outside W (shadow_addr (fr + 2256 + i))).
  { intros i Hi. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia. apply r10_out_app.
    - apply KindBGlue.outside_one. rewrite (HshFr (2256 + i) ltac:(lia)). Z.div_mod_to_equations. lia.
    - apply OUTW2SH. apply shadow_of_app. apply Hfrapp. lia. }
  assert (OUTIMSH : forall y, 0 <= y < 6283264 -> outside W (shadow_addr y)).
  { intros y Hy. apply OUTWSH; [lia | unfold app_mem, LOWMEM_END; left; lia]. }
  assert (HInb : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)) by (left; reflexivity).
  destruct (r10_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInb)
    as (_ & Hp4096 & Hpstklo & _ & Hblkb).
  try change (rnb g b) with N in Hpstklo.
  assert (Hphifr : forall x, phi <= x < phi + N -> app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros x Hx. destruct (Hblkb x Hx) as (Happx & _ & _ & _ & Hnfs).
    split; [exact Happx|]. intros Hc.
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - destruct (Hreal x Hc) as (Hlo' & _). lia.
    - exact (Hnfs (Hfs x Hc)). }
  assert (Hphidj : fr + FRAME_BYTES <= phi \/ phi + 50 <= fr).
  { destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (phi + 50) fr) as [H2|H2]; [right; exact H2|].
    exfalso. apply (proj2 (Hphifr (Z.max phi fr) ltac:(lia))). lia. }
  assert (OUTPHISH : forall x, phi <= x < phi + AC.a_size N -> outside W (shadow_addr x)).
  { intros x Hx. rewrite Hsz in Hx. destruct (Hphifr x Hx) as (Happx & Hnfr).
    exact (OUTWSH x Hnfr Happx). }
  assert (OUTA448 : forall x, A <= x < A + 448 -> outside W x).
  { intros x Hx. apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [unfold AC.GT in HGTfr; lia|]. split; [unfold APPMEM_END in *; lia|].
    intros a Ha. split; [exact (Hfrw a Ha)|].
    destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSbr & Hwb & Hlob & Hhib).
      destruct (r10_fs_ok_cells mem FSb (r10_fs_state (hb1 phi (rnb g b) ++ g_H g) mem md FSb HAH Hwb HFSbr) a
                  ltac:(lia)) as (_ & bb & Hb).
      exists bb. rewrite <- r10_mbyte_mrd. exact Hb. }
  assert (Hwr : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 <= n -> wr_at rsegs mem a n).
  { intros a n Ha Hn Hn0. split; [unfold AC.GT in HGTfr; lia|]. split; [unfold APPMEM_END in *; lia|].
    intros i Hi. destruct Hfstk as (_ & _ & Hs). exact (proj1 (Hs (a + i) ltac:(lia))). }
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TA0 : forall p n, addressable mem p n -> addressable (normalize rsegs mem) p n)
    by (intros p n Ha; exact (r10_addr_rel mem (normalize rsegs mem) p n HR0 Ha)).
  assert (TW0 : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 <= n ->
            wr_at rsegs (normalize rsegs mem) a n).
  { intros a n Ha Hn Hn0. apply (wr_at_norm rsegs mem (normalize rsegs mem) a n HR0); [apply Hwr; lia|].
    intros i Hi. apply r10_ro_wa. unfold AC.GT in HGTfr. unfold APPMEM_END in *. lia. }
  assert (Hst7 : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 7)).
  { split; [lia|]. split; [cbn [Z.of_nat]; unfold HIGHMEM_BEG, APPMEM_END in *; lia|].
    intros a Ha. cbn [Z.of_nat] in Ha. apply HSWm.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (Sfr fr + 306) _ HR0 ltac:(lia) Hst7) as Hst7n.
  destruct (r10_rw_stkn (normalize rsegs mem) (Sfr fr + 306) 7%nat Hst7n) as (junk7 & Hj7l & HRW7).
  assert (Hstw : stk rsegs mem (sp - KF) sp).
  { destruct (stk_split rsegs mem (sp - FN_STACK) (sp - KF) sp Hstkw
                ltac:(rewrite HKF in *; unfold FN_STACK, AF.SLOT_STACK in *; lia)) as (_ & Hw). exact Hw. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (sp - KF) sp HR0 ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia) Hstw)
    as Hstwn.
  assert (HADwin : addressable mem (sp - KF) KF).
  { apply r10_addr_of1; [unfold HIGHMEM_BEG in *; lia | rewrite HKF; lia | unfold APPMEM_END in *; lia|].
    intros i Hi. apply HWA; [lia|]. lia. }
  destruct (r10_bw_cells sp mem md HRT) as (HB1 & HB2 & HB3 & HB4 & HB5).
  assert (Hqof : forall off v, 0 <= off <= 440 -> spill regs mem off v ->
            q64 (normalize rsegs mem) (A + off) v).
  { intros off v Hoff (A' & HA' & Hq).
    assert (EA : A' = A).
    { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
      pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
      change (2 ^ 64) with 18446744073709551616 in *. cbn [Z.of_nat] in Hq.
      Z.div_mod_to_equations. lia. }
    subst A'. apply TB0. exact Hq. }
  apply (r10_run regs (Z_to_bv 64 0x817a4) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81834 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 20 = getr regs 20 /\ getr R 21 = Z_to_bv 64 36 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27 /\
       getr R 10 = Z_to_bv 64 (RFr.fg_ret (fcls N st72 g50)) /\
       munch W (normalize rsegs mem) m0' /\ wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (sp - KF) sp /\ asan_cells m0' /\ shadow_rw m0' /\
       FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50 (fcls N st72 g50) m0' /\
       (exists l7, bytes_at rsegs m0' (Sfr fr + 306) l7 /\ length l7 = 7%nat))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r10_mkR_of.
    eapply evt_cut.
    { apply (r10_head_frag6 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr (normalize rsegs mem) junk7).
      - exact Hr21.
      - unfold rg in Hr22. rewrite Hr22, Hb6v. reflexivity.
      - exact Ha0.
      - rewrite HbvS3. exact HRW7.
      - exact HMI0. }
    intros ms1 (m1 & l7 & c0 & c1 & c2 & Hms1 & MU1 & WM1 & MI1 & Hc0 & Hs0 & Hc1 & Hs1v & Hc2 & Hs2v & Hb7 & Hl7).
    subst ms1. rewrite HbvS3 in MU1, Hc0, Hc1, Hc2, Hb7.
    assert (OUT1 : forall x, ~ (Sfr fr + 306 <= x < Sfr fr + 313) ->
              outside [(Sfr fr + 306, Sfr fr + 313)] x)
      by (intros x Hx; apply KindBGlue.outside_one; lia).
    assert (TB1 : forall a bs, bytes_at rsegs (normalize rsegs mem) a bs ->
              (forall x, a <= x < a + Z.of_nat (length bs) -> ~ (Sfr fr + 306 <= x < Sfr fr + 313)) ->
              bytes_at rsegs m1 a bs).
    { intros a bs Hb Hx. eapply fl_bytes; [exact Hb | exact MU1 |]. intros x Hxr. apply OUT1. exact (Hx x Hxr). }
    assert (Hro1 : forall off v, 0 <= off <= 440 -> spill regs mem off v ->
              ro_cells rsegs m1 (A + off) [C8 (Z_to_bv 64 v)]).
    { intros off v Hoff Hs. apply r10_ro8. apply TB1; [exact (Hqof off v Hoff Hs)|].
      rewrite length_le8. intros x Hx. apply NSH1. unfold app_mem. right. lia. }
    assert (Hstw1 : stk rsegs m1 (sp - KF) sp).
    { apply (r10_stk_tr _ (normalize rsegs mem) m1 _ _ Hstwn MU1 WM1).
      intros x Hx. left. apply OUT1. apply NSH1. apply Hwapp. lia. }
    assert (HAC1 : asan_cells m1).
    { apply (fl_asan_cells [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1
               (r10_cells_tr mem (normalize rsegs mem) TB0 HACm) MU1).
      intros x Hx. apply OUT1. unfold RT_LO, RT_HI in Hx. lia. }
    assert (Hrd1 : forall x, Sfr fr + 306 <= x < Sfr fr + 313 -> exists bb, mrd rsegs m1 (wa x) = Some bb).
    { intros x Hx. replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
      apply (r10_ba_rd m1 (Sfr fr + 306) l7); [exact Hb7 | rewrite Hl7; lia]. }
    assert (HSW1 : shadow_rw m1).
    { apply (r10_srw_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1
               (r10_srw_rel mem (normalize rsegs mem) HR0 HSWm) MU1 WM1).
      intros x _ Hno. apply r10_nout_cons in Hno. destruct Hno as [Hin|Hnil];
        [exact (Hrd1 x Hin) | exfalso; exact (r10_nout_nil x Hnil)]. }
    assert (HADph1 : addressable m1 phi 50).
    { apply (r10_addr_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1 phi 50).
      - apply (r10_addr_sub (normalize rsegs mem) phi (AC.a_size N));
          [apply TA0; exact (proj2 HHB) | lia | lia | lia].
      - exact MU1.
      - intros i Hi. apply OUTSH1. exact (proj2 (Hphifr (phi + i) ltac:(lia))). }
    assert (HADf1 : addressable m1 (fr + 2256) 72).
    { apply (r10_addr_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1 (fr + 2256) 72
               (TA0 _ _ HAD2256) MU1).
      intros i Hi. apply OUT1. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia.
      rewrite (HshFr (2256 + i) ltac:(lia)). Z.div_mod_to_equations. lia. }
    assert (HADa1 : addressable m1 (fr + 2448) 2).
    { apply (r10_addr_sh m1 (fr + 2448) 2 c0).
      - rewrite (HshFr 2448 ltac:(lia)). replace (2448 / 8) with 306 by reflexivity. exact Hc0.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - right. lia.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (HADp1 : addressable m1 (fr + 2464) 8).
    { apply (r10_addr_sh m1 (fr + 2464) 8 c1).
      - rewrite (HshFr 2464 ltac:(lia)). replace (2464 / 8) with 308 by reflexivity. exact Hc1.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - left. exact Hs1v.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (HADn1 : addressable m1 (fr + 2496) 8).
    { apply (r10_addr_sh m1 (fr + 2496) 8 c2).
      - rewrite (HshFr 2496 ltac:(lia)). replace (2496 / 8) with 312 by reflexivity. exact Hc2.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - left. exact Hs2v.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (Hwrat1 : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 <= n -> wr_at rsegs m1 a n)
      by (intros a n Ha Hn Hn0; apply (r10_wr_mono (normalize rsegs mem) m1); [apply TW0; lia | exact WM1]).
    assert (HRWf1 : rw_cells rsegs m1 (fr + 2256) [CB 72 st72]).
    { rewrite <- Hst72l. apply r10_rw_CB.
      - apply TB1; [apply TB0; exact (proj2 (proj2 (proj2 (proj2 (proj2 HRB)))))|].
        rewrite Hst72l. intros x Hx. apply NSH1. apply Hfrapp. cbn [Z.of_nat] in Hx. lia.
      - rewrite Hst72l. cbn [Z.of_nat]. apply Hwrat1; lia. }
    eapply evt_mono.
    + eapply (r10_frag6_call FRAG) with (spv := sp) (A := A) (phi := phi) (N := N) (fr := fr)
        (g50 := g50) (st72 := st72).
      * exact Hr2.
      * unfold rg in Hr9. exact Hr9.
      * unfold rg in Hr20. exact Hr20.
      * unfold rg in HrN. exact HrN.
      * unfold APPMEM_END in *. lia.
      * unfold APPMEM_END in *. lia.
      * lia.
      * lia.
      * lia.
      * unfold AC.GT in HGTfr. lia.
      * unfold APPMEM_END in *. lia.
      * exact Hfrm.
      * unfold APPMEM_END in *. lia.
      * exact Hspm.
      * unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia.
      * unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia.
      * unfold APPMEM_END in *. lia.
      * rewrite HbvA. exact (Hro1 112 _ ltac:(lia) H112).
      * rewrite HbvA. exact (Hro1 240 _ ltac:(lia) H240).
      * rewrite HbvA. exact (Hro1 232 _ ltac:(lia) H232).
      * rewrite HbvA. exact (Hro1 224 _ ltac:(lia) H224).
      * exact Hstw1.
      * exact MI1.
      * exact Hg50l.
      * intros _. apply TB1; [apply TB0; unfold g50, rt_g; apply r10_fr50; [exact HFb | lia]|].
        rewrite Hg50l. intros x Hx. apply NSH1.
        exact (proj1 (Hphifr x ltac:(cbn [Z.of_nat] in Hx; lia))).
      * exact Hst72l.
      * exact HRWf1.
      * apply Hwrat1; lia.
      * apply Hwrat1; lia.
      * apply Hwrat1; lia.
      * left. unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
      * exact Hphidj.
      * unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
      * exact HAC1.
      * exact HSW1.
      * intros _. exact HADph1.
      * exact HADf1.
      * exact HADa1.
      * exact HADp1.
      * exact HADn1.
      * apply Hfrapp. lia.
      * right. unfold RT_HI. unfold AC.GT in HGTfr. lia.
      * apply TB1; [apply TB0; exact HB1|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.REAL_BCMP in Hx. lia.
      * apply TB1; [apply TB0; exact HB2|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.REAL_MEMCMP in Hx. lia.
      * apply TB1; [apply TB0; exact HB3|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.GOT_CF in Hx. lia.
      * apply TB1; [apply TB0; exact HB4|]. intros x Hx. cbn [length Z.of_nat] in Hx.
        unfold BW.CF in Hx. lia.
      * apply TB1; [apply TB0; exact HB5|]. intros x Hx. cbn [length Z.of_nat] in Hx.
        unfold BW.CF in Hx. lia.
    + intros ms2 (R & m2 & Hms2 & Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 &
                  Q18 & Q27 & Q10 & MU2 & WM2 & MI2 & ST2 & MEM2 & AC2 & SW2).
      rewrite Ecls in MU2, Q10, MEM2.
      exists R, (Z_to_bv 64 0x81834), m2. split; [exact Hms2|].
      split; [reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q8|].
      split; [exact Q9|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|].
      split; [exact Q23|]. split; [exact Q24|]. split; [exact Q25|]. split; [exact Q26|]. split; [exact Q18|]. split; [exact Q27|].
      split; [exact Q10|].
      split; [exact (KindBGlue.munch_cat _ _ _ m1 _ MU1 MU2)|].
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|].
      split; [exact ST2|]. split; [exact AC2|]. split; [exact SW2|]. split; [exact MEM2|].
      exists l7. split; [|exact Hl7].
      eapply fl_bytes; [exact Hb7 | exact MU2 |].
      intros x Hx. apply OUTW2SH. rewrite Hl7 in Hx. cbn [Z.of_nat] in Hx.
      replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K18 & K27 & K10 &
       MU0 & WM0 & ST0 & AC0 & SW0 & MEM0 & (l7 & Hb7' & Hl7')) Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E21 : getr regs'' 21 = Z_to_bv 64 36) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (RFr.fg_ret (fcls N st72 g50))) by (rewrite Hreg; exact K10).
    assert (TB' : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (r10_stk_back mem' m0' (sp - KF) sp HRel ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia) ST0) as ST.
    pose proof (r10_srw_back mem' m0' HRel SW0) as HSW'.
    pose proof (TB' _ _ Hb7') as Hb7''.
    pose proof (r10_fgmem_tr _ _ _ _ _ _ _ m0' mem' TB' MEM0) as MEM'.
    assert (Hrd : forall x, ~ outside W x -> exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
      - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exfalso; exact (r10_nout_nil x Hnil)].
        replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
        apply (r10_ba_rd mem' (Sfr fr + 306) l7); [exact Hb7'' | rewrite Hl7'; lia].
      - exact (r10_fg_rd (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50 N mem' KF sp x
                 MEM' Hst72l Hg50l ST Hx). }
    assert (HDJ : rt_disjoint W).
    { apply r10_rt_disjoint. apply Forall_app. split.
      - repeat constructor. cbn [fst]. unfold AC.GT. lia.
      - unfold W2. destruct (fcls N st72 g50); cbn [RFr.fg_fp]; repeat constructor; cbn [fst];
          unfold AC.GT, HIGHMEM_BEG in *; lia. }
    assert (HPres : forall q, 0 <= q < 2 ^ 64 -> (exists bb, mbyte rsegs mem q = Some bb) ->
              exists bb, mbyte rsegs mem' q = Some bb).
    { intros q Hq (bb & Hb). destruct (r10_out_dec W q) as [Ho|Hno].
      - exists bb. rewrite (KindBGlue.mbyte_munch rsegs W mem mem' q MU Hq Ho). exact Hb.
      - rewrite r10_mbyte_mrd. exact (Hrd q Hno). }
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (r10_fsok_keep mem mem' W FS HFSok MU
               ltac:(intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)) HPres);
        [| unfold AC.GT in HGTFS; lia | unfold AC.FS_SIZE, APPMEM_END in *; lia].
      intros q Hq. apply OUTAPP; [apply HFSapp; unfold AC.FS_SIZE; lia | lia | lia | lia |
                                 intros Hc; discriminate Hc]. }
    assert (HADw : addressable mem' (AC.aspZ regs - KF) KF).
    { rewrite Haspz. apply (r10_addr_keep W mem mem' (sp - KF) KF HADwin MU).
      intros i Hi. apply OUTWSH; [lia | apply Hwapp; lia]. }
    destruct (r10_land g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md FS true false KF W
                HFRA HENT HFSw HFSr HFSOK' ltac:(rewrite HKF; unfold FN_STACK, AF.SLOT_STACK; lia)
                ltac:(rewrite HKF; reflexivity)
                MU WM HRO' HDJ Hsub Hrd HSW' HADw E2 E3 E4 E8 E9 E19 E26) as (HFRAm & HENTm).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAm);
          try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
    destruct (r10_base g fr b phi A regs regs'' mem mem' W Hr9 HAb HHB Hr22 HOUR HCUR HRBE MU
                OUTLO OUTIMSH OUTFRB OUTFRSH OUTREC OUTPHISH OUTA448 E9 E22 E23 E25)
      as (HHB' & Hr22' & HOUR' & HCUR' & HRBE').
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [lia|]. split; [exact HHB'|]. split; [exact Hr22'|].
    split; [exact HOUR'|]. split; [exact HCUR'|]. split; [exact HRBE'|].
    split; [unfold rg; rewrite E21; reflexivity|].
    (* R12X: turn 6, its frame sent, s4 = Phi, the identity record RID 6 (kept), the fragment call's new record
       RFG 7 (the FgClose post), its 72 addressable bytes, a0 = fg_rf and the three out cells of the post *)
    rewrite Hcls in MEM'. cbn [FGC.fg_mem] in MEM'.
    destruct MEM' as (HfgN & Hpa & Hpp & Hpn).
    split; [exact Hb6v|].
    split; [exact Hnz|].
    split; [unfold rg in *; rewrite E20; exact Hr20|].
    split.
    { pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HRB))))) as HIDB.
      unfold IDBr in *. eapply fl_bytes; [exact HIDB | exact MU |].
      rewrite r10_rid_len. intros x Hx. apply OUTFRB; lia. }
    split.
    { unfold FGBr. rewrite (r10_st6 (g_in g) b Hb6v Hnz).
      change (bytes_at rsegs mem' (fr + 2256) (fg_st N st72 g50)).
      unfold fg_st. rewrite Hcls. cbn [fg_next]. exact HfgN. }
    split; [exact (r10_addr_keep W mem mem' (fr + 2256) 72 HAD2256 MU OUTREC)|].
    split; [unfold a0v, rg, fg_rf; exact E10|].
    split.
    { intros _. split; [exact Hpa|]. split; [exact Hpp | exact Hpn]. }
    unfold rg in *. rewrite E27. exact Hr27.
Qed.

(* The b = 5 arm's record after a non-closing fragment call: the call's post names it on the classes that write
   it, and on FgNone the call writes only its own window. *)
Lemma r10_fgb : forall K f pa pp pn S st g len m m',
  RFr.fg_ret (fcls len st g) = 0 -> bytes_at rsegs m f st ->
  munch (RFr.fg_fp K f pa pp pn S (fcls len st g)) m m' ->
  (forall x, f <= x < f + Z.of_nat (length st) -> ~ (S - K <= x < S)) ->
  FGC.fg_mem f pa pp pn st g (fcls len st g) m' ->
  bytes_at rsegs m' f (fg_st len st g).
Proof.
  intros K f pa pp pn S st g len m m' Hret Hb MU Hw HM. unfold fg_st.
  revert Hret MU HM. destruct (fcls len st g); intros Hret MU HM;
    cbn [fg_next FGC.fg_mem RFr.fg_ret RFr.fg_fp] in *; try discriminate Hret; try exact HM.
  eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply KindBGlue.outside_one.
  pose proof (Hw x Hx). lia.
Qed.

(* ---- b = 5: 0x817a4 -> FRAG@0x81910 -> 0x81914 (Inv_B81914_at); the fragment is not a closing one
   (fg_rf = 0, the official cut's conjunct), so a0 = 0 and the turn's records are RID b and fg_st ---- *)
Lemma r10_arm5 : forall (b : nat), b = 5%nat ->
  Hat B APIf ra (Inv_B81914_at B APIf ra) b -> Hat B APIf ra (Inv_B817a4_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hb6v Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR &
                    HRBE & Hr21 & Ha0 & HRF & H24 & H16 & H96 & H120 & HAD2256 & H5rf & Hr27).
  subst c. rewrite SEGS.
  pose proof HRF as ((HRB & Hnz & Hr20 & HFb) & HrN).
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H240 & H232 & H224 & _).
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & _ & _ & _ & _ & _ & _ & _ & _ & H112 & _).
  destruct (r10_rtk (g_in g) b ltac:(lia) Hnz) as (Hk & Hn52 & Hlen).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hn52, Hlen.
  assert (Hkv : r10_kind b = 11) by (subst b; reflexivity).
  rewrite Hk, Hkv in Ha0.
  destruct (fra_fsfree B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA)
    as (FS & HFSw & HFSr & HFSok & HFSGT & HFSal & HFSappA & HFSend & HFSfrb & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo2 & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (proj2 HHB) as (HpA0 & HnA0 & HpAe & _).
  set (KF := FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) in *.
  assert (HKF : KF = 4672) by reflexivity.
  assert (Hrf' : fg_rf (rnb g b) (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b)) = 0)
    by (subst b; exact (H5rf eq_refl)).
  destruct (r10_st5 (g_in g) b Hb6v Hnz Hrf') as (EID & EFG).
  set (g50 := rt_g (g_in g) (Z.of_nat b)) in *.
  set (st72 := RFG (g_in g) b) in *.
  set (N := rnb g b) in *.
  assert (Hsz : AC.a_size N = N) by (unfold AC.a_size; lia).
  assert (Hg50l : length g50 = 50%nat) by (unfold g50; apply r10_rtg_len).
  assert (Hst72l : length st72 = 72%nat) by (unfold st72; apply r10_rfg_len).
  assert (Hphib : 0 < phi /\ phi + N <= 2 ^ 64 /\ phi + 50 <= 2 ^ 64).
  { pose proof (proj1 HHB) as Hphinz.
    pose proof HFb as HFb'. apply bytes_at_bound in HFb'. rewrite Hlen in HFb'. lia. }
  set (W2 := RFr.fg_fp KF (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) sp (fcls N st72 g50)) in *.
  set (W := [(Sfr fr + 306, Sfr fr + 313)] ++ W2) in *.
  assert (Hsub : forall x, ~ outside W x -> r10_in true false fr (AC.aspZ regs) KF FS x).
  { intros x Hx. apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
    - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [left; lia|].
      exfalso. exact (r10_nout_nil x Hnil).
    - destruct (r10_fgfp_in _ _ _ _ _ _ _ x Hx) as [H|[H|[H|[H|H]]]].
      + right. right. left. split; [reflexivity | lia].
      + right. left. lia.
      + right. left. lia.
      + right. left. lia.
      + right. right. right. left. rewrite Haspz. lia. }
  destruct (r10_outs g fr (hb1 phi (rnb g b)) regs mem md FS true false KF W HFRA HFSw HFSr
              ltac:(rewrite HKF; unfold FN_STACK, AF.SLOT_STACK; lia) ltac:(rewrite HKF; reflexivity) Hsub)
    as (HGTFS & HFS8 & HFSapp & HFSstk & HFSfr2 & HGTfr & Hfr8 & Hfrapp & HfrE & Hstklo & Hhm & Hwlo & Hwhi &
        HSapp & Hwapp & HShm & OUTLO & OUTAPP & OUTSH).
  rewrite Haspz in Hwlo, Hwhi, Hwapp, OUTAPP, OUTSH, Hplace, Hlo, Hstkw.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAb : 0 <= A /\ A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(unfold AC.GT in HGTfr; lia) ltac:(lia)); lia).
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HGv : AC.GT = 6283264) by reflexivity.
  assert (HbvS3 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit; unfold HIGHMEM_BEG in HShm; lia).
  assert (Hbvsp : bv_unsigned (getr regs 2) = sp)
    by (rewrite Hr2; apply MState.unsigned_lit; unfold APPMEM_END in *; lia).
  assert (Ecls : RcFrag.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50
                 = fcls N st72 g50)
    by (apply r10_fgc; unfold AC.GT in HGTfr; lia).
  assert (HshFr : forall i, 0 <= i -> shadow_addr (fr + i) = Sfr fr + i / 8).
  { intros i Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  pose proof (Hplace KF ltac:(rewrite HKF; unfold FN_STACK, AF.SLOT_STACK in *; lia)) as Hsep.
  assert (NSH1 : forall x, app_mem x -> ~ (Sfr fr + 306 <= x < Sfr fr + 313)).
  { intros x Hax Hc. apply (app_not_shadow x Hax).
    replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  assert (OUTSH1 : forall y, ~ (fr <= y < fr + FRAME_BYTES) -> outside [(Sfr fr + 306, Sfr fr + 313)] (shadow_addr y)).
  { intros y Hy. apply KindBGlue.outside_one.
    assert (E : shadow_addr (fr + 8 * FRAME_SHADOW) = Sfr fr + FRAME_SHADOW)
      by (rewrite (HshFr (8 * FRAME_SHADOW) ltac:(lia)); f_equal; reflexivity).
    pose proof (r10_shq fr FRAME_SHADOW y Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hq.
    rewrite E in Hq. unfold Sfr in Hq |- *. lia. }
  assert (OUTW2SH : forall x, in_shadow x -> outside W2 x).
  { intros x Hx. destruct (r10_out_dec W2 x) as [Ho|Hno]; [exact Ho|]. exfalso.
    destruct (r10_fgfp_in _ _ _ _ _ _ _ x Hno) as [H|[H|[H|[H|H]]]].
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx).
    - exact (app_not_shadow x (Hwapp x ltac:(lia)) Hx). }
  assert (OUTWSH : forall y, ~ (fr <= y < fr + FRAME_BYTES) -> app_mem y -> outside W (shadow_addr y)).
  { intros y Hy Hay. apply r10_out_app; [exact (OUTSH1 y Hy) | apply OUTW2SH; apply shadow_of_app; exact Hay]. }
  assert (OUTFRB : forall x, fr <= x < fr + FRAME_BYTES -> ~ (2256 <= x - fr < 2544) -> outside W x).
  { intros x Hx H1. apply OUTAPP; [apply Hfrapp; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
  assert (OUTFRSH : forall i, 0 <= i < FRAME_BYTES -> ~ (2256 <= i < 2544) -> outside W (shadow_addr (fr + i))).
  { intros i Hi H1. apply r10_out_app.
    - apply KindBGlue.outside_one. rewrite (HshFr i ltac:(lia)). Z.div_mod_to_equations. lia.
    - apply OUTW2SH. apply shadow_of_app. apply Hfrapp. lia. }
  assert (OUTREC : forall i, 0 <= i < 72 -> outside W (shadow_addr (fr + 2256 + i))).
  { intros i Hi. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia. apply r10_out_app.
    - apply KindBGlue.outside_one. rewrite (HshFr (2256 + i) ltac:(lia)). Z.div_mod_to_equations. lia.
    - apply OUTW2SH. apply shadow_of_app. apply Hfrapp. lia. }
  assert (OUTIMSH : forall y, 0 <= y < 6283264 -> outside W (shadow_addr y)).
  { intros y Hy. apply OUTWSH; [lia | unfold app_mem, LOWMEM_END; left; lia]. }
  assert (HInb : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)) by (left; reflexivity).
  destruct (r10_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInb)
    as (_ & Hp4096 & Hpstklo & _ & Hblkb).
  try change (rnb g b) with N in Hpstklo.
  assert (Hphifr : forall x, phi <= x < phi + N -> app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros x Hx. destruct (Hblkb x Hx) as (Happx & _ & _ & _ & Hnfs).
    split; [exact Happx|]. intros Hc.
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - destruct (Hreal x Hc) as (Hlo' & _). lia.
    - exact (Hnfs (Hfs x Hc)). }
  assert (Hphidj : fr + FRAME_BYTES <= phi \/ phi + 50 <= fr).
  { destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (phi + 50) fr) as [H2|H2]; [right; exact H2|].
    exfalso. apply (proj2 (Hphifr (Z.max phi fr) ltac:(lia))). lia. }
  assert (OUTPHISH : forall x, phi <= x < phi + AC.a_size N -> outside W (shadow_addr x)).
  { intros x Hx. rewrite Hsz in Hx. destruct (Hphifr x Hx) as (Happx & Hnfr).
    exact (OUTWSH x Hnfr Happx). }
  assert (OUTA448 : forall x, A <= x < A + 448 -> outside W x).
  { intros x Hx. apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros Hc; discriminate Hc]. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [unfold AC.GT in HGTfr; lia|]. split; [unfold APPMEM_END in *; lia|].
    intros a Ha. split; [exact (Hfrw a Ha)|].
    destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSbr & Hwb & Hlob & Hhib).
      destruct (r10_fs_ok_cells mem FSb (r10_fs_state (hb1 phi (rnb g b) ++ g_H g) mem md FSb HAH Hwb HFSbr) a
                  ltac:(lia)) as (_ & bb & Hb).
      exists bb. rewrite <- r10_mbyte_mrd. exact Hb. }
  assert (Hwr : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 <= n -> wr_at rsegs mem a n).
  { intros a n Ha Hn Hn0. split; [unfold AC.GT in HGTfr; lia|]. split; [unfold APPMEM_END in *; lia|].
    intros i Hi. destruct Hfstk as (_ & _ & Hs). exact (proj1 (Hs (a + i) ltac:(lia))). }
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TA0 : forall p n, addressable mem p n -> addressable (normalize rsegs mem) p n)
    by (intros p n Ha; exact (r10_addr_rel mem (normalize rsegs mem) p n HR0 Ha)).
  assert (TW0 : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 <= n ->
            wr_at rsegs (normalize rsegs mem) a n).
  { intros a n Ha Hn Hn0. apply (wr_at_norm rsegs mem (normalize rsegs mem) a n HR0); [apply Hwr; lia|].
    intros i Hi. apply r10_ro_wa. unfold AC.GT in HGTfr. unfold APPMEM_END in *. lia. }
  assert (Hst7 : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 7)).
  { split; [lia|]. split; [cbn [Z.of_nat]; unfold HIGHMEM_BEG, APPMEM_END in *; lia|].
    intros a Ha. cbn [Z.of_nat] in Ha. apply HSWm.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (Sfr fr + 306) _ HR0 ltac:(lia) Hst7) as Hst7n.
  destruct (r10_rw_stkn (normalize rsegs mem) (Sfr fr + 306) 7%nat Hst7n) as (junk7 & Hj7l & HRW7).
  assert (Hstw : stk rsegs mem (sp - KF) sp).
  { destruct (stk_split rsegs mem (sp - FN_STACK) (sp - KF) sp Hstkw
                ltac:(rewrite HKF in *; unfold FN_STACK, AF.SLOT_STACK in *; lia)) as (_ & Hw). exact Hw. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (sp - KF) sp HR0 ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia) Hstw)
    as Hstwn.
  assert (HADwin : addressable mem (sp - KF) KF).
  { apply r10_addr_of1; [unfold HIGHMEM_BEG in *; lia | rewrite HKF; lia | unfold APPMEM_END in *; lia|].
    intros i Hi. apply HWA; [lia|]. lia. }
  destruct (r10_bw_cells sp mem md HRT) as (HB1 & HB2 & HB3 & HB4 & HB5).
  assert (Hqof : forall off v, 0 <= off <= 440 -> spill regs mem off v ->
            q64 (normalize rsegs mem) (A + off) v).
  { intros off v Hoff (A' & HA' & Hq).
    assert (EA : A' = A).
    { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
      pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
      change (2 ^ 64) with 18446744073709551616 in *. cbn [Z.of_nat] in Hq.
      Z.div_mod_to_equations. lia. }
    subst A'. apply TB0. exact Hq. }
  apply (r10_run regs (Z_to_bv 64 0x817a4) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81914 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 20 = getr regs 20 /\ getr R 21 = Z_to_bv 64 36 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27 /\
       getr R 10 = Z_to_bv 64 (RFr.fg_ret (fcls N st72 g50)) /\
       munch W (normalize rsegs mem) m0' /\ wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (sp - KF) sp /\ asan_cells m0' /\ shadow_rw m0' /\
       FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50 (fcls N st72 g50) m0' /\
       (exists l7, bytes_at rsegs m0' (Sfr fr + 306) l7 /\ length l7 = 7%nat) /\
       bytes_at rsegs m0' (fr + 2256) (fg_st N st72 g50))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r10_mkR_of.
    eapply evt_cut.
    { apply (r10_head_frag5 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr (normalize rsegs mem) junk7).
      - exact Hr21.
      - unfold rg in Hr22. rewrite Hr22, Hb6v. reflexivity.
      - exact Ha0.
      - rewrite HbvS3. exact HRW7.
      - exact HMI0. }
    intros ms1 (m1 & l7 & c0 & c1 & c2 & Hms1 & MU1 & WM1 & MI1 & Hc0 & Hs0 & Hc1 & Hs1v & Hc2 & Hs2v & Hb7 & Hl7).
    subst ms1. rewrite HbvS3 in MU1, Hc0, Hc1, Hc2, Hb7.
    assert (OUT1 : forall x, ~ (Sfr fr + 306 <= x < Sfr fr + 313) ->
              outside [(Sfr fr + 306, Sfr fr + 313)] x)
      by (intros x Hx; apply KindBGlue.outside_one; lia).
    assert (TB1 : forall a bs, bytes_at rsegs (normalize rsegs mem) a bs ->
              (forall x, a <= x < a + Z.of_nat (length bs) -> ~ (Sfr fr + 306 <= x < Sfr fr + 313)) ->
              bytes_at rsegs m1 a bs).
    { intros a bs Hb Hx. eapply fl_bytes; [exact Hb | exact MU1 |]. intros x Hxr. apply OUT1. exact (Hx x Hxr). }
    assert (Hro1 : forall off v, 0 <= off <= 440 -> spill regs mem off v ->
              ro_cells rsegs m1 (A + off) [C8 (Z_to_bv 64 v)]).
    { intros off v Hoff Hs. apply r10_ro8. apply TB1; [exact (Hqof off v Hoff Hs)|].
      rewrite length_le8. intros x Hx. apply NSH1. unfold app_mem. right. lia. }
    assert (Hstw1 : stk rsegs m1 (sp - KF) sp).
    { apply (r10_stk_tr _ (normalize rsegs mem) m1 _ _ Hstwn MU1 WM1).
      intros x Hx. left. apply OUT1. apply NSH1. apply Hwapp. lia. }
    assert (HAC1 : asan_cells m1).
    { apply (fl_asan_cells [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1
               (r10_cells_tr mem (normalize rsegs mem) TB0 HACm) MU1).
      intros x Hx. apply OUT1. unfold RT_LO, RT_HI in Hx. lia. }
    assert (Hrd1 : forall x, Sfr fr + 306 <= x < Sfr fr + 313 -> exists bb, mrd rsegs m1 (wa x) = Some bb).
    { intros x Hx. replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
      apply (r10_ba_rd m1 (Sfr fr + 306) l7); [exact Hb7 | rewrite Hl7; lia]. }
    assert (HSW1 : shadow_rw m1).
    { apply (r10_srw_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1
               (r10_srw_rel mem (normalize rsegs mem) HR0 HSWm) MU1 WM1).
      intros x _ Hno. apply r10_nout_cons in Hno. destruct Hno as [Hin|Hnil];
        [exact (Hrd1 x Hin) | exfalso; exact (r10_nout_nil x Hnil)]. }
    assert (HADph1 : addressable m1 phi 50).
    { apply (r10_addr_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1 phi 50).
      - apply (r10_addr_sub (normalize rsegs mem) phi (AC.a_size N));
          [apply TA0; exact (proj2 HHB) | lia | lia | lia].
      - exact MU1.
      - intros i Hi. apply OUTSH1. exact (proj2 (Hphifr (phi + i) ltac:(lia))). }
    assert (HADf1 : addressable m1 (fr + 2256) 72).
    { apply (r10_addr_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1 (fr + 2256) 72
               (TA0 _ _ HAD2256) MU1).
      intros i Hi. apply OUT1. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia.
      rewrite (HshFr (2256 + i) ltac:(lia)). Z.div_mod_to_equations. lia. }
    assert (HADa1 : addressable m1 (fr + 2448) 2).
    { apply (r10_addr_sh m1 (fr + 2448) 2 c0).
      - rewrite (HshFr 2448 ltac:(lia)). replace (2448 / 8) with 306 by reflexivity. exact Hc0.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - right. lia.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (HADp1 : addressable m1 (fr + 2464) 8).
    { apply (r10_addr_sh m1 (fr + 2464) 8 c1).
      - rewrite (HshFr 2464 ltac:(lia)). replace (2464 / 8) with 308 by reflexivity. exact Hc1.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - left. exact Hs1v.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (HADn1 : addressable m1 (fr + 2496) 8).
    { apply (r10_addr_sh m1 (fr + 2496) 8 c2).
      - rewrite (HshFr 2496 ltac:(lia)). replace (2496 / 8) with 312 by reflexivity. exact Hc2.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - left. exact Hs2v.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (Hwrat1 : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 <= n -> wr_at rsegs m1 a n)
      by (intros a n Ha Hn Hn0; apply (r10_wr_mono (normalize rsegs mem) m1); [apply TW0; lia | exact WM1]).
    assert (HRWf1 : rw_cells rsegs m1 (fr + 2256) [CB 72 st72]).
    { rewrite <- Hst72l. apply r10_rw_CB.
      - apply TB1; [apply TB0; exact (proj2 (proj2 (proj2 (proj2 (proj2 HRB)))))|].
        rewrite Hst72l. intros x Hx. apply NSH1. apply Hfrapp. cbn [Z.of_nat] in Hx. lia.
      - rewrite Hst72l. cbn [Z.of_nat]. apply Hwrat1; lia. }
    eapply evt_mono.
    + eapply (r10_frag5_call FRAG) with (spv := sp) (A := A) (phi := phi) (N := N) (fr := fr)
        (g50 := g50) (st72 := st72).
      * exact Hr2.
      * unfold rg in Hr9. exact Hr9.
      * unfold rg in Hr20. exact Hr20.
      * unfold rg in HrN. exact HrN.
      * unfold APPMEM_END in *. lia.
      * unfold APPMEM_END in *. lia.
      * lia.
      * lia.
      * lia.
      * unfold AC.GT in HGTfr. lia.
      * unfold APPMEM_END in *. lia.
      * exact Hfrm.
      * unfold APPMEM_END in *. lia.
      * exact Hspm.
      * unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia.
      * unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia.
      * unfold APPMEM_END in *. lia.
      * rewrite HbvA. exact (Hro1 112 _ ltac:(lia) H112).
      * rewrite HbvA. exact (Hro1 240 _ ltac:(lia) H240).
      * rewrite HbvA. exact (Hro1 232 _ ltac:(lia) H232).
      * rewrite HbvA. exact (Hro1 224 _ ltac:(lia) H224).
      * exact Hstw1.
      * exact MI1.
      * exact Hg50l.
      * intros _. apply TB1; [apply TB0; unfold g50, rt_g; apply r10_fr50; [exact HFb | lia]|].
        rewrite Hg50l. intros x Hx. apply NSH1.
        exact (proj1 (Hphifr x ltac:(cbn [Z.of_nat] in Hx; lia))).
      * exact Hst72l.
      * exact HRWf1.
      * apply Hwrat1; lia.
      * apply Hwrat1; lia.
      * apply Hwrat1; lia.
      * left. unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
      * exact Hphidj.
      * unfold FGC.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
      * exact HAC1.
      * exact HSW1.
      * intros _. exact HADph1.
      * exact HADf1.
      * exact HADa1.
      * exact HADp1.
      * exact HADn1.
      * apply Hfrapp. lia.
      * right. unfold RT_HI. unfold AC.GT in HGTfr. lia.
      * apply TB1; [apply TB0; exact HB1|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.REAL_BCMP in Hx. lia.
      * apply TB1; [apply TB0; exact HB2|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.REAL_MEMCMP in Hx. lia.
      * apply TB1; [apply TB0; exact HB3|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.GOT_CF in Hx. lia.
      * apply TB1; [apply TB0; exact HB4|]. intros x Hx. cbn [length Z.of_nat] in Hx.
        unfold BW.CF in Hx. lia.
      * apply TB1; [apply TB0; exact HB5|]. intros x Hx. cbn [length Z.of_nat] in Hx.
        unfold BW.CF in Hx. lia.
    + intros ms2 (R & m2 & Hms2 & Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 &
                  Q18 & Q27 & Q10 & MU2 & WM2 & MI2 & ST2 & MEM2 & AC2 & SW2).
      rewrite Ecls in MU2, Q10, MEM2.
      assert (Hfgb2 : bytes_at rsegs m2 (fr + 2256) (fg_st N st72 g50)).
      { apply (r10_fgb KF (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) sp st72 g50 N m1 m2);
          [exact Hrf' | | exact MU2 | | exact MEM2].
        - apply TB1; [apply TB0; exact (proj2 (proj2 (proj2 (proj2 (proj2 HRB)))))|].
          rewrite Hst72l. intros x Hx. apply NSH1. apply Hfrapp. cbn [Z.of_nat] in Hx. lia.
        - rewrite Hst72l. intros x Hx. cbn [Z.of_nat] in Hx. lia. }
      exists R, (Z_to_bv 64 0x81914), m2. split; [exact Hms2|].
      split; [reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q8|].
      split; [exact Q9|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|].
      split; [exact Q23|]. split; [exact Q24|]. split; [exact Q25|]. split; [exact Q26|]. split; [exact Q18|]. split; [exact Q27|].
      split; [exact Q10|].
      split; [exact (KindBGlue.munch_cat _ _ _ m1 _ MU1 MU2)|].
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|].
      split; [exact ST2|]. split; [exact AC2|]. split; [exact SW2|]. split; [exact MEM2|].
      split; [|exact Hfgb2].
      exists l7. split; [|exact Hl7].
      eapply fl_bytes; [exact Hb7 | exact MU2 |].
      intros x Hx. apply OUTW2SH. rewrite Hl7 in Hx. cbn [Z.of_nat] in Hx.
      replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K18 & K27 & K10 &
       MU0 & WM0 & ST0 & AC0 & SW0 & MEM0 & (l7 & Hb7' & Hl7') & Hfgb0) Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E21 : getr regs'' 21 = Z_to_bv 64 36) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (TB' : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (r10_stk_back mem' m0' (sp - KF) sp HRel ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia) ST0) as ST.
    pose proof (r10_srw_back mem' m0' HRel SW0) as HSW'.
    pose proof (TB' _ _ Hb7') as Hb7''.
    pose proof (r10_fgmem_tr _ _ _ _ _ _ _ m0' mem' TB' MEM0) as MEM'.
    assert (Hrd : forall x, ~ outside W x -> exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
      - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exfalso; exact (r10_nout_nil x Hnil)].
        replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
        apply (r10_ba_rd mem' (Sfr fr + 306) l7); [exact Hb7'' | rewrite Hl7'; lia].
      - exact (r10_fg_rd (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50 N mem' KF sp x
                 MEM' Hst72l Hg50l ST Hx). }
    assert (HDJ : rt_disjoint W).
    { apply r10_rt_disjoint. apply Forall_app. split.
      - repeat constructor. cbn [fst]. unfold AC.GT. lia.
      - unfold W2. destruct (fcls N st72 g50); cbn [RFr.fg_fp]; repeat constructor; cbn [fst];
          unfold AC.GT, HIGHMEM_BEG in *; lia. }
    assert (HPres : forall q, 0 <= q < 2 ^ 64 -> (exists bb, mbyte rsegs mem q = Some bb) ->
              exists bb, mbyte rsegs mem' q = Some bb).
    { intros q Hq (bb & Hb). destruct (r10_out_dec W q) as [Ho|Hno].
      - exists bb. rewrite (KindBGlue.mbyte_munch rsegs W mem mem' q MU Hq Ho). exact Hb.
      - rewrite r10_mbyte_mrd. exact (Hrd q Hno). }
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (r10_fsok_keep mem mem' W FS HFSok MU
               ltac:(intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)) HPres);
        [| unfold AC.GT in HGTFS; lia | unfold AC.FS_SIZE, APPMEM_END in *; lia].
      intros q Hq. apply OUTAPP; [apply HFSapp; unfold AC.FS_SIZE; lia | lia | lia | lia |
                                 intros Hc; discriminate Hc]. }
    assert (HADw : addressable mem' (AC.aspZ regs - KF) KF).
    { rewrite Haspz. apply (r10_addr_keep W mem mem' (sp - KF) KF HADwin MU).
      intros i Hi. apply OUTWSH; [lia | apply Hwapp; lia]. }
    destruct (r10_land g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md FS true false KF W
                HFRA HENT HFSw HFSr HFSOK' ltac:(rewrite HKF; unfold FN_STACK, AF.SLOT_STACK; lia)
                ltac:(rewrite HKF; reflexivity)
                MU WM HRO' HDJ Hsub Hrd HSW' HADw E2 E3 E4 E8 E9 E19 E26) as (HFRAm & HENTm).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAm);
          try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
    destruct (r10_base g fr b phi A regs regs'' mem mem' W Hr9 HAb HHB Hr22 HOUR HCUR HRBE MU
                OUTLO OUTIMSH OUTFRB OUTFRSH OUTREC OUTPHISH OUTA448 E9 E22 E23 E25)
      as (HHB' & Hr22' & HOUR' & HCUR' & HRBE').
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [lia|]. split; [exact HHB'|]. split; [exact Hr22'|].
    split; [exact HOUR'|]. split; [exact HCUR'|]. split; [exact HRBE'|].
    split; [unfold rg; rewrite E21; reflexivity|].
    rewrite EID, EFG.
    split.
    { split; [exact Hb6|]. split; [exact HCUR'|]. split; [exact HOUR'|]. split; [exact Hr22'|].
      split.
      { unfold IDBr in *. eapply fl_bytes; [exact (proj1 (proj2 (proj2 (proj2 (proj2 HRB))))) | exact MU |].
        rewrite r10_rid_len. intros x Hx. apply OUTFRB; lia. }
      { unfold FGBr. exact (TB' _ _ Hfgb0). } }
    split; [unfold rg; rewrite E20; exact Hr20|].
    split; [unfold a0v, rg; rewrite Hreg, K10; f_equal; exact Hrf'|].
    unfold rg in *. rewrite E27. exact Hr27.
Qed.

(* ---- the reply arm's side-stack package ---- *)

(* fp's write list is only read through fp_dj, so a range may be dropped from it. *)
Lemma r10_fp_tail : forall cs m TP FS lo hi w W0 D, fp cs m TP FS lo hi (w :: W0) D -> fp cs m TP FS lo hi W0 D.
Proof.
  intros cs m TP FS lo hi w W0 D (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  exists DT, TS, C, T, DB, k.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [|exact H10].
  unfold fp_dj in *. apply Forall_cons_iff in H9. exact (proj2 H9).
Qed.

(* The side stack of an fp package is the one the tp word names. *)
Lemma r10_fp_FS : forall cs m TP FS FS' lo hi W D, fp cs m TP FS' lo hi W D -> word_mem rsegs m TP FS ->
  0 <= FS < 2 ^ 64 -> 0 <= TP -> TP + 8 <= 2 ^ 64 -> FS' = FS.
Proof.
  intros cs m TP FS FS' lo hi W D (DT & TS & C & T & DB & k & _ & HTP & HP & _) Hw HFSr H0 H1.
  destruct HP as (HFSpos & _ & _ & _ & (_ & HFSb & _)).
  pose proof (KindBGlue.bytes_at_le8_word rsegs m _ _ HTP) as Hw'.
  assert (HFS'r : 0 <= FS' < 2 ^ 64) by (unfold FS_SIZE in HFSb; lia).
  rewrite MState.unsigned_lit in Hw' by exact HFS'r.
  exact (fsf_wm_uniq m TP FS' FS Hw' Hw HFS'r HFSr H0 H1).
Qed.

(* The class-1 write list of the side stack, in numbers. *)
Lemma r10_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS.
  assert (E1 : SMC.fs_hint FS 1 = FS + 8) by (unfold SMC.fs_hint; change (Z.of_nat 1) with 1; lia).
  assert (E2 : SMC.fs_flag FS 1 0 = FS + 20480).
  { unfold SMC.fs_flag. assert (P : 2 ^ 15 - 2 ^ (15 - Z.of_nat 1) = 16384) by reflexivity. lia. }
  assert (E3 : SMC.fs_M 1 = 8192) by reflexivity.
  assert (E4 : SMC.fs_frame FS 1 0 = FS + 1085440).
  { unfold SMC.fs_frame. assert (P : Z.of_nat 1 * 2 ^ 20 = 1048576) by reflexivity. rewrite P. lia. }
  assert (E5 : SMC.fs_frame FS 1 (SMC.fs_M 1) = FS + 2134016).
  { unfold SMC.fs_frame. assert (P : Z.of_nat 1 * 2 ^ 20 = 1048576) by reflexivity.
    assert (P2 : SMC.fs_M 1 * SMC.fs_B 1 = 1048576) by reflexivity. rewrite P, P2. lia. }
  unfold fp_w, fp_w1. cbn [flat_map app]. rewrite E1, E2, E4, E5, E3.
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma r10_hint1 : forall FS, SMC.fs_hint FS 1 = FS + 8.
Proof. intros FS. unfold SMC.fs_hint. change (Z.of_nat 1) with 1. lia. Qed.

Lemma r10_flag1 : forall FS, SMC.fs_flag FS 1 0 = FS + 20480.
Proof.
  intros FS. unfold SMC.fs_flag. assert (P : 2 ^ 15 - 2 ^ (15 - Z.of_nat 1) = 16384) by reflexivity. lia.
Qed.

Lemma r10_fpw1_in : forall FS x, ~ outside (fp_w [1%nat] FS) x ->
  (FS + 8 <= x < FS + 16) \/ (FS + 20480 <= x < FS + 28672) \/ (FS + 1085440 <= x < FS + 2134016) \/
  (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)).
Proof.
  intros FS x H. rewrite r10_fpw1 in H.
  repeat (apply r10_nout_cons in H; destruct H as [H|H]; [tauto|]).
  exfalso. exact (r10_nout_nil x H).
Qed.

Lemma r10_rfp_in : forall phi N pa pp pn S g x,
  ~ outside (RPC.reac_ctrl_identity_reply_fp phi N pa pp pn S g) x ->
  (pa <= x < pa + 2) \/ (pp <= x < pp + 8) \/ (pn <= x < pn + 8) \/
  (S - 9072 <= x < S).
Proof.
  intros phi N pa pp pn S g x H. unfold RPC.reac_ctrl_identity_reply_fp in H. revert H.
  destruct (RRp.reply_ok phi N pa pp pn g); intros H; cbn [app] in H;
    unfold RPC.REAC_CTRL_IDENTITY_REPLY_K in H;
    repeat (apply r10_nout_cons in H; destruct H as [H|H]; [tauto|]);
    exfalso; exact (r10_nout_nil x H).
Qed.

Lemma r10_stk_sub : forall m lo hi a b, stk rsegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk rsegs m a b.
Proof.
  intros m lo hi a b (H0 & H1 & H) Ha Hab Hb. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

Lemma r10_rw_back : forall m m0 a n bs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a [CB n bs] ->
  rw_cells rsegs m a [CB n bs].
Proof.
  intros m m0 a n bs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

Lemma r10_in_glob : forall a, 0x21200 <= a < 0x21207 -> in_globals AF.frame_AG a.
Proof.
  intros a Ha. exists 0x21200, 7. split; [|lia].
  unfold AF.frame_AG. repeat (first [left; reflexivity | right]).
Qed.

(* ---- b = 3, 4: 0x817a4 -> REPLY@0x817e8 -> 0x817ec (Inv_B817ec_at) ----
   The callee's class-1 side-stack package is rebuilt from FRA (Tac_fsfree fra_fp) with the head's three
   metadata stores in front of its write list, carried across those stores (r10_fp_head / r10_tls_head), and
   the front range dropped (r10_fp_tail). *)
Lemma r10_arm34 : forall (b : nat), (b = 3 \/ b = 4)%nat ->
  Hat B APIf ra (Inv_B817ec_at B APIf ra) b -> Hat B APIf ra (Inv_B817a4_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hb34 Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR &
                    HRBE & Hr21 & Ha0 & HRF & H24 & H16 & H96 & H120 & HAD2256 & H5rf & Hr27).
  subst c. rewrite SEGS.
  pose proof HRF as ((HRB & Hnz & Hr20 & HFb) & HrN).
  pose proof HRBE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H240 & H232 & H224 & _).
  destruct (r10_rtk (g_in g) b ltac:(lia) Hnz) as (Hk & Hn52 & Hlen).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hn52, Hlen.
  assert (Hkv : r10_kind b = 5) by (destruct Hb34 as [-> | ->]; reflexivity).
  rewrite Hk, Hkv in Ha0.
  destruct (fra_fsfree B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA)
    as (FS & HFSw & HFSr & HFSok & HFSGT & HFSal & HFSappA & HFSend & HFSfrb & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo2 & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (proj2 HHB) as (HpA0 & HnA0 & HpAe & _).
  set (KR := RPC.REAC_CTRL_IDENTITY_REPLY_K) in *.
  assert (HKR : KR = 9072) by reflexivity.
  set (g50 := rt_g (g_in g) (Z.of_nat b)) in *.
  set (N := rnb g b) in *.
  assert (Hsz : AC.a_size N = N) by (unfold AC.a_size; lia).
  assert (Hg50l : length g50 = 50%nat) by (unfold g50; apply r10_rtg_len).
  assert (Hphib : 0 < phi /\ phi + N <= 2 ^ 64 /\ phi + 50 <= 2 ^ 64).
  { pose proof (proj1 HHB) as Hphinz.
    pose proof HFb as HFb'. apply bytes_at_bound in HFb'. rewrite Hlen in HFb'. lia. }
  set (TP := AC.as_tp AC.ASYMS) in *.
  assert (HTPv : 0 <= TP /\ TP + 8 <= 2 ^ 64) by (unfold TP, AC.as_tp, AC.ASYMS; cbn; lia).
  set (Wr := RPC.reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) sp) in *.
  set (Dl := RPC.reac_ctrl_identity_reply_D phi N (fr + 2448) (fr + 2464) (fr + 2496)) in *.
  set (Wc := RPC.reac_ctrl_identity_reply_fp phi N (fr + 2448) (fr + 2464) (fr + 2496) sp g50 ++
             fp_w [1%nat] FS ++ [(shadow_addr (sp - KR), shadow_addr sp)]) in *.
  set (W := [(Sfr fr + 306, Sfr fr + 313)] ++ Wc) in *.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HFSZ' : FS_SIZE = 11571200) by reflexivity.
  (* the write set *)
  assert (Hsub : forall x, ~ outside W x -> r10_in false true fr (AC.aspZ regs) KR FS x).
  { intros x Hx. rewrite Haspz. apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
    - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [left; lia|].
      exfalso. exact (r10_nout_nil x Hnil).
    - apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
      + destruct (r10_rfp_in _ _ _ _ _ _ _ x Hx) as [H|[H|[H|H]]].
        * right. left. lia.
        * right. left. lia.
        * right. left. lia.
        * right. right. right. left. exact H.
      + apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
        * destruct (r10_fpw1_in FS x Hx) as [H|[H|[H|H]]].
          -- right. right. right. right. right. left. split; [reflexivity | lia].
          -- right. right. right. right. right. right. left. split; [reflexivity | lia].
          -- right. right. right. right. right. right. right. left. split; [reflexivity | exact H].
          -- right. right. right. right. right. right. right. right. split; [reflexivity | exact H].
        * apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exfalso; exact (r10_nout_nil x Hnil)].
          right. right. right. right. left. exact Hin. }
  destruct (r10_outs g fr (hb1 phi (rnb g b)) regs mem md FS false true KR W HFRA HFSw HFSr
              ltac:(rewrite HKR; unfold FN_STACK, AF.SLOT_STACK; lia) ltac:(rewrite HKR; reflexivity) Hsub)
    as (HGTFS & HFS8 & HFSapp & HFSstk & HFSfr2 & HGTfr & Hfr8 & Hfrapp & HfrE & Hstklo & Hhm & Hwlo & Hwhi &
        HSapp & Hwapp & HShm & OUTLO & OUTAPP & OUTSH).
  rewrite Haspz in Hwlo, Hwhi, Hwapp, OUTAPP, OUTSH, Hplace, Hlo, Hstkw.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAb : 0 <= A /\ A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(unfold AC.GT in HGTfr; lia) ltac:(lia)); lia).
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HGv : AC.GT = 6283264) by reflexivity.
  assert (HbvS3 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit; unfold HIGHMEM_BEG in HShm; lia).
  assert (HbvTP : bv_unsigned (getr regs 4) = TP)
    by (rewrite Hr4; apply MState.unsigned_lit; lia).
  assert (HshFr : forall i, 0 <= i -> shadow_addr (fr + i) = Sfr fr + i / 8).
  { intros i Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  pose proof (Hplace KR ltac:(rewrite HKR; unfold FN_STACK, AF.SLOT_STACK in *; lia)) as Hsep.
  assert (NSH1 : forall x, app_mem x -> ~ (Sfr fr + 306 <= x < Sfr fr + 313)).
  { intros x Hax Hc. apply (app_not_shadow x Hax).
    replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  assert (OUTSH1 : forall y, ~ (fr <= y < fr + FRAME_BYTES) -> outside [(Sfr fr + 306, Sfr fr + 313)] (shadow_addr y)).
  { intros y Hy. apply KindBGlue.outside_one.
    assert (E : shadow_addr (fr + 8 * FRAME_SHADOW) = Sfr fr + FRAME_SHADOW)
      by (rewrite (HshFr (8 * FRAME_SHADOW) ltac:(lia)); f_equal; reflexivity).
    pose proof (r10_shq fr FRAME_SHADOW y Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hq.
    rewrite E in Hq. unfold Sfr in Hq |- *. lia. }
  (* the heap block of the turn *)
  assert (HInb : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)) by (left; reflexivity).
  destruct (r10_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInb)
    as (_ & Hp4096 & Hpstklo & _ & Hblkb).
  try change (rnb g b) with N in Hpstklo.
  assert (Hphifr : forall x, phi <= x < phi + N -> app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros x Hx. destruct (Hblkb x Hx) as (Happx & _ & _ & _ & Hnfs).
    split; [exact Happx|]. intros Hc.
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - destruct (Hreal x Hc) as (Hlo' & _). lia.
    - exact (Hnfs (Hfs x Hc)). }
  assert (Hphidj : fr + FRAME_BYTES <= phi \/ phi + 50 <= fr).
  { destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (phi + 50) fr) as [H2|H2]; [right; exact H2|].
    exfalso. apply (proj2 (Hphifr (Z.max phi fr) ltac:(lia))). lia. }
  (* the frame as a stack range *)
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [unfold AC.GT in HGTfr; lia|]. split; [unfold APPMEM_END in *; lia|].
    intros a Ha. split; [exact (Hfrw a Ha)|].
    destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSbr & Hwb & Hlob & Hhib).
      destruct (r10_fs_ok_cells mem FSb (r10_fs_state (hb1 phi (rnb g b) ++ g_H g) mem md FSb HAH Hwb HFSbr) a
                  ltac:(lia)) as (_ & bb & Hb).
      exists bb. rewrite <- r10_mbyte_mrd. exact Hb. }
  (* the callee's package at the entry, with the head's stores in front *)
  assert (Hcs1 : forall c, In c [1%nat] -> (c <= 5)%nat) by (intros c0 Hc0; destruct Hc0 as [<-|[]]; lia).
  assert (HWp : forall w, In w ((Sfr fr + 306, Sfr fr + 313) :: Wr) ->
     (g_S g - AF.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
     (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)).
  { intros w Hw. destruct Hw as [<-|Hw]; [right; right; cbn [fst snd]; lia|].
    unfold Wr, RPC.reac_ctrl_identity_reply_W in Hw. destruct Hw as [<-|Hw].
    - left. cbn [fst snd]. unfold RPC.REAC_CTRL_IDENTITY_REPLY_K. lia.
    - revert Hw. destruct (RRp.reply_args phi (fr + 2448) (fr + 2464) (fr + 2496)); intros Hw; [|contradiction].
      destruct Hw as [<-|[<-|[<-|[]]]]; right; left; cbn [fst snd]; lia. }
  assert (HDp : forall d, In d Dl -> snd d <= AC.GT \/ (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
     (fst d < snd d /\ exists p n, In (p, n) (hb1 phi (rnb g b) ++ g_H g) /\ p <= fst d /\ snd d <= p + n)).
  { intros d Hd. unfold Dl, RPC.reac_ctrl_identity_reply_D in Hd. revert Hd.
    destruct (RRp.reply_args phi (fr + 2448) (fr + 2464) (fr + 2496)); intros Hd; [|contradiction].
    apply in_app_or in Hd. destruct Hd as [Hd|Hd].
    - revert Hd. destruct (N <? 50); intros Hd; [contradiction|]. destruct Hd as [<-|[]].
      right. right. cbn [fst snd]. split; [lia|]. exists phi, N. split; [left; reflexivity | lia].
    - destruct Hd as [<-|[<-|[<-|[]]]]; right; left; cbn [fst snd]; lia. }
  destruct (fra_fp B APIf ra g fr (hb1 phi (rnb g b)) regs mem md [1%nat] KR
              ((Sfr fr + 306, Sfr fr + 313) :: Wr) Dl HFRA Hcs1 ltac:(rewrite HKR; unfold FN_STACK; lia) HWp HDp)
    as (FS' & FPm & TLSm & DJf & Hfs1).
  rewrite Haspz in FPm, TLSm.
  assert (EFS : FS' = FS) by exact (r10_fp_FS _ _ _ _ _ _ _ _ _ FPm HFSw HFSr (proj1 HTPv) (proj2 HTPv)).
  subst FS'.
  (* the normalized memory *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TBb : forall a bs, bytes_at rsegs (normalize rsegs mem) a bs -> bytes_at rsegs mem a bs)
    by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TA0 : forall p n, addressable mem p n -> addressable (normalize rsegs mem) p n)
    by (intros p n Ha; exact (r10_addr_rel mem (normalize rsegs mem) p n HR0 Ha)).
  pose proof (r10_fp_tr mem (normalize rsegs mem) _ _ _ _ _ _ _ TB0
                (fun l h Hl Hs => r10_stk_rel mem (normalize rsegs mem) l h HR0 Hl Hs) FPm) as FPm0.
  assert (TLSm0 : forall DT TS C T DB k, asan_tls_cells (normalize rsegs mem) TP DT TS C T DB k ->
            fp_dj (fp_tls TP DT TS C T DB k) (fp_w [1%nat] FS ++ [(shadow_addr (sp - KR), shadow_addr sp)])).
  { intros DT TS C T DB k H. apply TLSm. exact (r10_tls_tr _ mem _ _ _ _ _ _ _ TBb H). }
  assert (Hst7 : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 7)).
  { split; [lia|]. split; [cbn [Z.of_nat]; unfold HIGHMEM_BEG, APPMEM_END in *; lia|].
    intros a Ha. cbn [Z.of_nat] in Ha. apply HSWm.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10_fsh; [exact Hfrapp | lia]. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (Sfr fr + 306) _ HR0 ltac:(lia) Hst7) as Hst7n.
  destruct (r10_rw_stkn (normalize rsegs mem) (Sfr fr + 306) 7%nat Hst7n) as (junk7 & Hj7l & HRW7).
  assert (Hstw : stk rsegs mem (sp - KR) sp).
  { destruct (stk_split rsegs mem (sp - FN_STACK) (sp - KR) sp Hstkw
                ltac:(rewrite HKR in *; unfold FN_STACK, AF.SLOT_STACK in *; lia)) as (_ & Hw). exact Hw. }
  pose proof (r10_stk_rel mem (normalize rsegs mem) (sp - KR) sp HR0 ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia) Hstw)
    as Hstwn.
  pose proof (r10_stk_rel mem (normalize rsegs mem) fr (fr + FRAME_BYTES) HR0 ltac:(unfold AC.GT in *; lia) Hfstk)
    as Hfstkn.
  assert (HADwin : addressable mem (sp - KR) KR).
  { apply r10_addr_of1; [unfold HIGHMEM_BEG in *; lia | lia | unfold APPMEM_END in *; lia|].
    intros i Hi. apply HWA; [lia|]. lia. }
  assert (HADbc : addressable mem PC.REAC_CTRL_PARSE_BC 6).
  { apply r10_addr_of1; [unfold PC.REAC_CTRL_PARSE_BC; lia | lia | unfold PC.REAC_CTRL_PARSE_BC, APPMEM_END; lia|].
    intros i Hi. apply HAG. apply r10_in_glob. unfold PC.REAC_CTRL_PARSE_BC. lia. }
  destruct (r10_bw_cells sp mem md HRT) as (HB1 & HB2 & HB3 & HB4 & HB5).
  assert (Hqof : forall off v, 0 <= off <= 440 -> spill regs mem off v ->
            q64 (normalize rsegs mem) (A + off) v).
  { intros off v Hoff (A' & HA' & Hq).
    assert (EA : A' = A).
    { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
      pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
      change (2 ^ 64) with 18446744073709551616 in *. cbn [Z.of_nat] in Hq.
      Z.div_mod_to_equations. lia. }
    subst A'. apply TB0. exact Hq. }
  apply (r10_run regs (Z_to_bv 64 0x817a4) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x817ec /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 20 = getr regs 20 /\ getr R 21 = Z_to_bv 64 36 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27 /\
       getr R 10 = Z_to_bv 64 (RRp.reply_ret phi N (fr + 2448) (fr + 2464) (fr + 2496) g50) /\
       munch W (normalize rsegs mem) m0' /\ wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (sp - KR) sp /\
       (RRp.reply_ok phi N (fr + 2448) (fr + 2464) (fr + 2496) g50 = true ->
          rw_cells rsegs m0' (fr + 2448) [CB 2 (RRp.reply_addr g50)] /\
          rw_cells rsegs m0' (fr + 2464) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
          rw_cells rsegs m0' (fr + 2496) [CB 8 (le8 (Z_to_bv 64 (RRp.ir_s g50 - 13)))]) /\
       shadow_rw m0' /\ addressable m0' (sp - KR) KR /\
       fp [1%nat] m0' TP FS (sp - KR) sp Wr Dl /\
       (exists l7, bytes_at rsegs m0' (Sfr fr + 306) l7 /\ length l7 = 7%nat))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r10_mkR_of.
    eapply evt_cut.
    { apply (r10_head_reply (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr (normalize rsegs mem) (Z.of_nat b) junk7).
      - exact Hr21.
      - unfold rg in Hr22. exact Hr22.
      - exact Ha0.
      - destruct Hb34 as [-> | ->]; [left | right]; reflexivity.
      - rewrite HbvS3. exact HRW7.
      - exact HMI0. }
    intros ms1 (m1 & l7 & c0 & c1 & c2 & Hms1 & MU1 & WM1 & MI1 & Hc0 & Hs0 & Hc1 & Hs1v & Hc2 & Hs2v & Hb7 & Hl7).
    subst ms1. rewrite HbvS3 in MU1, Hc0, Hc1, Hc2, Hb7.
    assert (OUT1 : forall x, ~ (Sfr fr + 306 <= x < Sfr fr + 313) ->
              outside [(Sfr fr + 306, Sfr fr + 313)] x)
      by (intros x Hx; apply KindBGlue.outside_one; lia).
    assert (TB1 : forall a bs, bytes_at rsegs (normalize rsegs mem) a bs ->
              (forall x, a <= x < a + Z.of_nat (length bs) -> ~ (Sfr fr + 306 <= x < Sfr fr + 313)) ->
              bytes_at rsegs m1 a bs).
    { intros a bs Hb Hx. eapply fl_bytes; [exact Hb | exact MU1 |]. intros x Hxr. apply OUT1. exact (Hx x Hxr). }
    assert (Hro1 : forall off v, 0 <= off <= 440 -> spill regs mem off v ->
              ro_cells rsegs m1 (A + off) [C8 (Z_to_bv 64 v)]).
    { intros off v Hoff Hs. apply r10_ro8. apply TB1; [exact (Hqof off v Hoff Hs)|].
      rewrite length_le8. intros x Hx. apply NSH1. unfold app_mem. right. lia. }
    assert (Hstk1 : forall lo hi, fr <= lo -> lo <= hi -> hi <= fr + FRAME_BYTES -> stk rsegs m1 lo hi).
    { intros lo hi H1 H2 H3.
      apply (r10_stk_tr _ (normalize rsegs mem) m1 _ _ (r10_stk_sub _ _ _ lo hi Hfstkn H1 H2 H3) MU1 WM1).
      intros x Hx. left. apply OUT1. apply NSH1. apply Hfrapp. lia. }
    assert (Hstw1 : stk rsegs m1 (sp - KR) sp).
    { apply (r10_stk_tr _ (normalize rsegs mem) m1 _ _ Hstwn MU1 WM1).
      intros x Hx. left. apply OUT1. apply NSH1. apply Hwapp. lia. }
    destruct (r10_rw_stkn m1 (fr + 2448) 2%nat ltac:(apply Hstk1; cbn [Z.of_nat]; lia)) as (ja & _ & RWa).
    destruct (r10_rw_stkn m1 (fr + 2464) 8%nat ltac:(apply Hstk1; cbn [Z.of_nat]; lia)) as (jp & _ & RWp).
    destruct (r10_rw_stkn m1 (fr + 2496) 8%nat ltac:(apply Hstk1; cbn [Z.of_nat]; lia)) as (jn & _ & RWn).
    assert (HAC1 : asan_cells m1).
    { apply (fl_asan_cells [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1
               (r10_cells_tr mem (normalize rsegs mem) TB0 HACm) MU1).
      intros x Hx. apply OUT1. unfold RT_LO, RT_HI in Hx. lia. }
    assert (Hrd1 : forall x, Sfr fr + 306 <= x < Sfr fr + 313 -> exists bb, mrd rsegs m1 (wa x) = Some bb).
    { intros x Hx. replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
      apply (r10_ba_rd m1 (Sfr fr + 306) l7); [exact Hb7 | rewrite Hl7; lia]. }
    assert (HSW1 : shadow_rw m1).
    { apply (r10_srw_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1
               (r10_srw_rel mem (normalize rsegs mem) HR0 HSWm) MU1 WM1).
      intros x _ Hno. apply r10_nout_cons in Hno. destruct Hno as [Hin|Hnil];
        [exact (Hrd1 x Hin) | exfalso; exact (r10_nout_nil x Hnil)]. }
    assert (HADph1 : addressable m1 phi 50).
    { apply (r10_addr_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1 phi 50).
      - apply (r10_addr_sub (normalize rsegs mem) phi (AC.a_size N));
          [apply TA0; exact (proj2 HHB) | lia | lia | lia].
      - exact MU1.
      - intros i Hi. apply OUTSH1. exact (proj2 (Hphifr (phi + i) ltac:(lia))). }
    assert (HADw1 : addressable m1 (sp - KR) KR).
    { apply (r10_addr_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1 (sp - KR) KR
               (TA0 _ _ HADwin) MU1).
      intros i Hi. apply OUTSH1. lia. }
    assert (HADbc1 : addressable m1 PC.REAC_CTRL_PARSE_BC 6).
    { apply (r10_addr_keep [(Sfr fr + 306, Sfr fr + 313)] (normalize rsegs mem) m1 _ 6 (TA0 _ _ HADbc) MU1).
      intros i Hi. apply OUTSH1. unfold PC.REAC_CTRL_PARSE_BC. unfold AC.GT in HGTfr. lia. }
    assert (HADa1 : addressable m1 (fr + 2448) 2).
    { apply (r10_addr_sh m1 (fr + 2448) 2 c0).
      - rewrite (HshFr 2448 ltac:(lia)). replace (2448 / 8) with 306 by reflexivity. exact Hc0.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - right. lia.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (HADp1 : addressable m1 (fr + 2464) 8).
    { apply (r10_addr_sh m1 (fr + 2464) 8 c1).
      - rewrite (HshFr 2464 ltac:(lia)). replace (2464 / 8) with 308 by reflexivity. exact Hc1.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - left. exact Hs1v.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    assert (HADn1 : addressable m1 (fr + 2496) 8).
    { apply (r10_addr_sh m1 (fr + 2496) 8 c2).
      - rewrite (HshFr 2496 ltac:(lia)). replace (2496 / 8) with 312 by reflexivity. exact Hc2.
      - clear - Hfr8. Z.div_mod_to_equations. lia.
      - lia.
      - left. exact Hs2v.
      - intros i Hi. apply Hfrapp. lia.
      - unfold AC.GT in HGTfr. lia.
      - unfold APPMEM_END in *. lia. }
    (* the package across the head's stores *)
    assert (BEL : forall x, FS <= x < FS + FS_SIZE -> outside [(Sfr fr + 306, Sfr fr + 313)] x).
    { intros x Hx. apply OUT1. apply NSH1. apply HFSapp. unfold FS_SIZE, AC.FS_SIZE in *. lia. }
    assert (SUB1 : sub_fp [(Sfr fr + 306, Sfr fr + 313)] [(Sfr fr + 306, Sfr fr + 313)]) by (intros x Hx; exact Hx).
    pose proof (r10_fp_tail _ _ _ _ _ _ _ _ _
                  (r10_fp_head _ _ _ _ _ _ _ _ _ _ _ _ FPm0 MU1 WM1 SUB1 BEL)) as FPm1.
    pose proof (r10_tls_head _ _ _ _ _ _ _ _ _ _ _ _ _ FPm0 MU1 SUB1 TLSm0) as TLSm1.
    eapply evt_mono.
    + eapply (r10_reply_call REPLY) with (spv := sp) (A := A) (phi := phi) (N := N) (fr := fr) (FS := FS)
        (g50 := g50) (ja := ja) (jp := jp) (jn := jn).
      * exact Hr2.
      * unfold rg in Hr9. exact Hr9.
      * unfold rg in Hr20. exact Hr20.
      * unfold rg in HrN. exact HrN.
      * unfold APPMEM_END in *. lia.
      * unfold APPMEM_END in *. lia.
      * lia.
      * lia.
      * lia.
      * unfold AC.GT in HGTfr. lia.
      * unfold APPMEM_END in *. lia.
      * exact Hfrm.
      * unfold APPMEM_END in *. lia.
      * exact Hspm.
      * unfold RPC.REAC_CTRL_IDENTITY_REPLY_K, HIGHMEM_BEG in *. lia.
      * unfold RPC.REAC_CTRL_IDENTITY_REPLY_K, HIGHMEM_BEG in *. lia.
      * unfold APPMEM_END in *. lia.
      * rewrite HbvA. exact (Hro1 240 _ ltac:(lia) H240).
      * rewrite HbvA. exact (Hro1 232 _ ltac:(lia) H232).
      * rewrite HbvA. exact (Hro1 224 _ ltac:(lia) H224).
      * exact Hstw1.
      * exact MI1.
      * exact Hg50l.
      * intros _. apply TB1; [apply TB0; unfold g50, rt_g; apply r10_fr50; [exact HFb | lia]|].
        rewrite Hg50l. intros x Hx. apply NSH1.
        exact (proj1 (Hphifr x ltac:(cbn [Z.of_nat] in Hx; lia))).
      * left. unfold RPC.REAC_CTRL_IDENTITY_REPLY_K. lia.
      * exact Hphidj.
      * unfold RPC.REAC_CTRL_IDENTITY_REPLY_K. lia.
      * exact RWa.
      * exact RWp.
      * exact RWn.
      * exact HAC1.
      * exact HSW1.
      * exact HADw1.
      * intros _. exact HADph1.
      * exact HADa1.
      * exact HADp1.
      * exact HADn1.
      * right. unfold RT_HI. unfold AC.GT in HGTfr. lia.
      * exact HADbc1.
      * apply TB1; [apply TB0; exact HB1|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.REAL_BCMP in Hx. lia.
      * apply TB1; [apply TB0; exact HB2|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.REAL_MEMCMP in Hx. lia.
      * apply TB1; [apply TB0; exact HB3|]. intros x Hx. rewrite length_le8 in Hx.
        unfold BW.GOT_CF in Hx. lia.
      * apply TB1; [apply TB0; exact HB4|]. intros x Hx. cbn [length Z.of_nat] in Hx.
        unfold BW.CF in Hx. lia.
      * apply TB1; [apply TB0; exact HB5|]. intros x Hx. cbn [length Z.of_nat] in Hx.
        unfold BW.CF in Hx. lia.
      * rewrite HbvTP. exact FPm1.
      * rewrite HbvTP. exact TLSm1.
    + intros ms2 (R & m2 & Hms2 & Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 &
                  Q18 & Q27 & Q10 & MU2 & WM2 & MI2 & ST2 & RW2 & AC2 & SW2 & AD2 & FP2).
      rewrite HbvTP in FP2.
      exists R, (Z_to_bv 64 0x817ec), m2. split; [exact Hms2|].
      split; [reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q8|].
      split; [exact Q9|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|].
      split; [exact Q23|]. split; [exact Q24|]. split; [exact Q25|]. split; [exact Q26|]. split; [exact Q18|]. split; [exact Q27|].
      split; [exact Q10|].
      split; [exact (KindBGlue.munch_cat _ _ _ m1 _ MU1 MU2)|].
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|].
      split; [exact ST2|]. split; [exact RW2|]. split; [exact SW2|]. split; [exact AD2|].
      split; [exact FP2|].
      exists l7. split; [|exact Hl7].
      eapply fl_bytes; [exact Hb7 | exact MU2 |].
      intros x Hx. rewrite Hl7 in Hx. cbn [Z.of_nat] in Hx.
      apply r10_out_app; [|apply r10_out_app].
      * destruct (r10_out_dec (RPC.reac_ctrl_identity_reply_fp phi N (fr + 2448) (fr + 2464) (fr + 2496) sp g50) x)
          as [Ho|Hno]; [exact Ho|]. exfalso.
        destruct (r10_rfp_in _ _ _ _ _ _ _ x Hno) as [H|[H|[H|H]]];
          [apply (NSH1 x (Hfrapp x ltac:(lia))) | apply (NSH1 x (Hfrapp x ltac:(lia)))
          | apply (NSH1 x (Hfrapp x ltac:(lia))) | apply (NSH1 x (Hwapp x ltac:(lia)))]; lia.
      * exact (fsf_dj_out_r _ _ (Sfr fr) (Sfr fr + FRAME_SHADOW) x DJf ltac:(right; left; reflexivity) ltac:(lia)).
      * apply KindBGlue.outside_one. try change RPC.REAC_CTRL_IDENTITY_REPLY_K with KR.
        assert (Hsw : shadow_addr (fr + FRAME_BYTES) <= shadow_addr (sp - KR) \/ shadow_addr sp <= shadow_addr fr).
        { unfold shadow_addr. destruct Hsep as [H|H]; [left | right]; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
        rewrite (HshFr FRAME_BYTES ltac:(lia)) in Hsw. replace (shadow_addr fr) with (Sfr fr) in Hsw by reflexivity.
        replace (FRAME_BYTES / 8) with FRAME_SHADOW in Hsw by reflexivity. lia.
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K18 & K27 & K10 &
       MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0 & (l7 & Hb7' & Hl7')) Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E21 : getr regs'' 21 = Z_to_bv 64 36) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (RRp.reply_ret phi N (fr + 2448) (fr + 2464) (fr + 2496) g50))
      by (rewrite Hreg; exact K10).
    assert (TB' : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (r10_stk_back mem' m0' (sp - KR) sp HRel ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia) ST0) as ST.
    pose proof (r10_srw_back mem' m0' HRel SW0) as HSW'.
    pose proof (r10_addr_back mem' m0' _ _ HRel AD0) as AD'.
    pose proof (TB' _ _ Hb7') as Hb7''.
    pose proof (r10_fp_tr m0' mem' _ _ _ _ _ _ _ TB'
                  (fun l h Hl Hs => r10_stk_back mem' m0' l h HRel Hl Hs) FP0) as FP'.
    (* the side stack's state after the call *)
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (fp_post_fs_ok mem mem' [1%nat] TP FS (sp - KR) sp Wr Dl W Hcs1 HFSok ltac:(lia)
               ltac:(unfold APPMEM_END in *; lia) FP' MU WM).
      intros q Hq Hnc. destruct (Hnc 1%nat ltac:(left; reflexivity)) as (Hnh & Hnf).
        rewrite r10_hint1 in Hnh. rewrite r10_flag1 in Hnf. change (SMC.fs_M 1) with 8192 in Hnf.
        destruct (r10_out_dec W q) as [Ho|Hno]; [exact Ho|]. exfalso.
        assert (Happq : app_mem q) by (apply HFSapp; unfold AC.FS_SIZE; lia).
        apply r10_nout_app in Hno. destruct Hno as [Hx|Hx].
        + apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [exact (NSH1 q Happq Hin) | exact (r10_nout_nil q Hnil)].
        + apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
          * destruct (r10_rfp_in _ _ _ _ _ _ _ q Hx) as [H|[H|[H|H]]]; lia.
          * apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
            -- destruct (r10_fpw1_in FS q Hx) as [H|[H|[H|H]]]; [lia | lia | lia |].
               exact (app_not_shadow q Happq (fsf_sh_in_win (FS + 1085440) (FS + 2134016) q ltac:(lia)
                        ltac:(intros a Ha; apply HFSapp; unfold AC.FS_SIZE; lia) H)).
            -- apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exact (r10_nout_nil q Hnil)].
               exact (app_not_shadow q Happq (fsf_sh_in_win (sp - KR) sp q ltac:(lia) Hwapp Hin)). }
    (* every written byte reads back *)
    assert (Hrd : forall x, ~ outside W x -> exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
      - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exfalso; exact (r10_nout_nil x Hnil)].
        replace x with (Sfr fr + 306 + (x - (Sfr fr + 306))) by lia.
        apply (r10_ba_rd mem' (Sfr fr + 306) l7); [exact Hb7'' | rewrite Hl7'; lia].
      - assert (HSR : in_shadow x -> exists bb, mrd rsegs mem' (wa x) = Some bb)
          by (intros Hs; exact (proj2 (HSW' x Hs))).
        assert (HWR : sp - KR <= x < sp -> exists bb, mrd rsegs mem' (wa x) = Some bb)
          by (intros Hw; destruct ST as (_ & _ & Hs); exact (proj2 (Hs x Hw))).
        apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
        + unfold RPC.reac_ctrl_identity_reply_fp in Hx. revert Hx.
          destruct (RRp.reply_ok phi N (fr + 2448) (fr + 2464) (fr + 2496) g50) eqn:Eok; intros Hx;
            cbn [app] in Hx.
          * destruct (RW0 ltac:(first [exact Eok | reflexivity])) as (RA & RP & RN).
            apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
            { replace x with (fr + 2448 + (x - (fr + 2448))) by lia.
              apply (r10_ba_rd mem' (fr + 2448) (RRp.reply_addr g50));
                [exact (TB' _ _ (r10_cells_bytes _ _ _ _ RA)) | rewrite (r10_cb_len _ _ _ _ RA); lia]. }
            apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
            { replace x with (fr + 2464 + (x - (fr + 2464))) by lia.
              apply (r10_ba_rd mem' (fr + 2464) _ _ (TB' _ _ (r10_cells_bytes _ _ _ _ RP))).
              rewrite (r10_cb_len _ _ _ _ RP). lia. }
            apply r10_nout_cons in Hx. destruct Hx as [Hin|Hx].
            { replace x with (fr + 2496 + (x - (fr + 2496))) by lia.
              apply (r10_ba_rd mem' (fr + 2496) _ _ (TB' _ _ (r10_cells_bytes _ _ _ _ RN))).
              rewrite (r10_cb_len _ _ _ _ RN). lia. }
            apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [exact (HWR Hin) | exfalso; exact (r10_nout_nil x Hnil)].
          * apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [exact (HWR Hin) | exfalso; exact (r10_nout_nil x Hnil)].
        + apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
          * destruct FP' as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
            destruct HPl as (_ & _ & _ & _ & (_ & _ & HPs)).
            destruct (r10_fpw1_in FS x Hx) as [H|[H|[H|H]]];
              [exact (proj2 (HPs x ltac:(unfold FS_SIZE; lia))) | exact (proj2 (HPs x ltac:(unfold FS_SIZE; lia)))
              | exact (proj2 (HPs x ltac:(unfold FS_SIZE; lia))) |].
            apply HSR. apply (fsf_sh_in_win (FS + 1085440) (FS + 2134016) x); [lia | | exact H].
            intros a Ha. apply HFSapp. unfold AC.FS_SIZE. lia.
          * apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exfalso; exact (r10_nout_nil x Hnil)].
            apply HSR. exact (fsf_sh_in_win (sp - KR) sp x ltac:(lia) Hwapp Hin). }
    assert (HDJ : rt_disjoint W).
    { apply r10_rt_disjoint. unfold W, Wc. apply Forall_app. split.
      - repeat constructor. cbn [fst]. unfold AC.GT. lia.
      - apply Forall_app. split.
        + unfold RPC.reac_ctrl_identity_reply_fp.
          destruct (RRp.reply_ok phi N (fr + 2448) (fr + 2464) (fr + 2496) g50); cbn [app];
            repeat constructor; cbn [fst]; unfold AC.GT, HIGHMEM_BEG, RPC.REAC_CTRL_IDENTITY_REPLY_K in *; lia.
        + apply Forall_app. split.
          * rewrite r10_fpw1. repeat constructor; cbn [fst]; unfold AC.GT in *; try lia.
            unfold shadow_addr. pose proof (Z.div_pos (FS + 1085440) 8 ltac:(lia) ltac:(lia)). lia.
          * repeat constructor. cbn [fst]. unfold AC.GT, shadow_addr.
            pose proof (Z.div_pos (sp - KR) 8 ltac:(unfold HIGHMEM_BEG in *; lia) ltac:(lia)). lia. }
    assert (HADw : addressable mem' (AC.aspZ regs - KR) KR) by (rewrite Haspz; exact AD').
    destruct (r10_land g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md FS false true KR W
                HFRA HENT HFSw HFSr HFSOK' ltac:(rewrite HKR; unfold FN_STACK, AF.SLOT_STACK; lia)
                ltac:(rewrite HKR; reflexivity)
                MU WM HRO' HDJ Hsub Hrd HSW' HADw E2 E3 E4 E8 E9 E19 E26) as (HFRAm & HENTm).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAm);
          try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
    (* the frame bytes outside the reply slots, and the shadow outside the frame *)
    assert (OUTWSH : forall y, ~ (fr <= y < fr + FRAME_BYTES) -> app_mem y -> ~ (sp - KR <= y < sp) ->
              ~ (FS + 1085440 <= y < FS + 2134016) -> outside W (shadow_addr y)).
    { intros y Hy Hay Hyw Hyf. apply OUTSH; [exact Hay | exact Hy | exact Hyw | intros _; exact Hyf]. }
    assert (OUTFRB : forall x, fr <= x < fr + FRAME_BYTES -> ~ (2448 <= x - fr < 2504) -> outside W x).
    { intros x Hx H1. destruct (r10_out_dec W x) as [Ho|Hno]; [exact Ho|]. exfalso.
      assert (Happx : app_mem x) by (apply Hfrapp; lia).
      destruct (Hsub x Hno) as [H|[H|[(Hc & _)|[H|[H|[(_ & H)|[(_ & H)|[(_ & H)|(_ & H)]]]]]]]].
      -
        apply (app_not_shadow x Happx). replace x with (Sfr fr + (x - Sfr fr)) by lia.
        apply r10_fsh; [exact Hfrapp | lia].
      - lia.
      - discriminate Hc.
      - rewrite Haspz in H. lia.
      - rewrite Haspz in H. exact (app_not_shadow x Happx (fsf_sh_in_win (sp - KR) sp x ltac:(lia) Hwapp H)).
      - lia.
      - lia.
      - lia.
      - exact (app_not_shadow x Happx (fsf_sh_in_win (FS + 1085440) (FS + 2134016) x ltac:(lia)
                 ltac:(intros a Ha; apply HFSapp; unfold AC.FS_SIZE; lia) H)). }
    assert (OUTFRSH0 : forall i, 0 <= i < FRAME_BYTES -> ~ (2448 <= i < 2504) -> outside W (shadow_addr (fr + i))).
    { intros i Hi H1. destruct (r10_out_dec W (shadow_addr (fr + i))) as [Ho|Hno]; [exact Ho|]. exfalso.
      rewrite (HshFr i ltac:(lia)) in Hno.
      assert (Hs : in_shadow (Sfr fr + i / 8)) by (apply r10_fsh; [exact Hfrapp | Z.div_mod_to_equations; lia]).
      apply r10_nout_app in Hno. destruct Hno as [Hx|Hx].
      - apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [Z.div_mod_to_equations; lia | exact (r10_nout_nil _ Hnil)].
      - apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
        + destruct (r10_rfp_in _ _ _ _ _ _ _ _ Hx) as [H|[H|[H|H]]];
            [apply (app_not_shadow _ (Hfrapp (Sfr fr + i / 8) ltac:(lia)) Hs)
            | apply (app_not_shadow _ (Hfrapp (Sfr fr + i / 8) ltac:(lia)) Hs)
            | apply (app_not_shadow _ (Hfrapp (Sfr fr + i / 8) ltac:(lia)) Hs)
            | apply (app_not_shadow _ (Hwapp (Sfr fr + i / 8) ltac:(lia)) Hs)].
        + apply r10_nout_app in Hx. destruct Hx as [Hx|Hx].
          * exact (Hx (fsf_dj_out_r _ _ (Sfr fr) (Sfr fr + FRAME_SHADOW) (Sfr fr + i / 8) DJf
                         ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia))).
          * apply r10_nout_cons in Hx. destruct Hx as [Hin|Hnil]; [|exact (r10_nout_nil _ Hnil)].
            assert (Hsw : shadow_addr (fr + FRAME_BYTES) <= shadow_addr (sp - KR) \/ shadow_addr sp <= shadow_addr fr).
            { unfold shadow_addr. destruct Hsep as [H|H]; [left | right]; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
            rewrite (HshFr FRAME_BYTES ltac:(lia)) in Hsw. replace (shadow_addr fr) with (Sfr fr) in Hsw by reflexivity.
            replace (FRAME_BYTES / 8) with FRAME_SHADOW in Hsw by reflexivity. Z.div_mod_to_equations. lia. }
    assert (OUTFRSH : forall i, 0 <= i < FRAME_BYTES -> ~ (2256 <= i < 2544) -> outside W (shadow_addr (fr + i)))
      by (intros i Hi H1; apply OUTFRSH0; lia).
    assert (OUTREC : forall i, 0 <= i < 72 -> outside W (shadow_addr (fr + 2256 + i))).
    { intros i Hi. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia. apply OUTFRSH0; lia. }
    assert (OUTA448 : forall x, A <= x < A + 448 -> outside W x).
    { intros x Hx. apply OUTAPP; [unfold app_mem; right; lia | lia | lia | lia | intros _; repeat split; lia]. }
    assert (OUTIMSH : forall y, 0 <= y < 6283264 -> outside W (shadow_addr y)).
    { intros y Hy. apply OUTWSH; [lia | unfold app_mem, LOWMEM_END; left; lia | lia | lia]. }
    assert (OUTPHISH : forall x, phi <= x < phi + AC.a_size N -> outside W (shadow_addr x)).
    { intros x Hx. rewrite Hsz in Hx. destruct (Hphifr x Hx) as (Happx & Hnfr).
      destruct (Hblkb x Hx) as (_ & _ & _ & _ & Hnfs).
      apply OUTWSH; [exact Hnfr | exact Happx | lia |].
      intros Hc. apply Hnfs. apply (Tac_fs.a_fs_in AC.ASYMS mem FS x HFSw HFSr). lia. }
    destruct (r10_base g fr b phi A regs regs'' mem mem' W Hr9 HAb HHB Hr22 HOUR HCUR HRBE MU
                OUTLO OUTIMSH ltac:(intros x Hx H1; apply OUTFRB; lia) OUTFRSH OUTREC OUTPHISH OUTA448
                E9 E22 E23 E25)
      as (HHB' & Hr22' & HOUR' & HCUR' & HRBE').
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [lia|]. split; [exact HHB'|]. split; [exact Hr22'|].
    split; [exact HOUR'|]. split; [exact HCUR'|]. split; [exact HRBE'|].
    split; [unfold rg; rewrite E21; reflexivity|].
    split; [exact Hb34|].
    split.
    { split; [|unfold rg in *; rewrite E18; exact HrN].
      split.
      { destruct HRB as (Hb6' & HCURb & HOURb & Hr22b & HIDB & HFGB).
        split; [exact Hb6'|]. split; [exact HCUR'|]. split; [exact HOUR'|]. split; [exact Hr22'|].
        split.
        { unfold IDBr in *. eapply fl_bytes; [exact HIDB | exact MU |].
          rewrite r10_rid_len. intros x Hx. apply OUTFRB; lia. }
        { unfold FGBr in *. eapply fl_bytes; [exact HFGB | exact MU |].
          rewrite r10_rfg_len. intros x Hx. apply OUTFRB; lia. } }
      split; [exact Hnz|].
      split; [unfold rg in *; rewrite E20; exact Hr20|].
      eapply fl_bytes; [exact HFb | exact MU |]. rewrite Hlen. intros x Hx.
      destruct (Hphifr x ltac:(lia)) as (Happx & Hnfr).
      destruct (Hblkb x ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      assert (Hnf : ~ (FS <= x < FS + AC.FS_SIZE))
        by (intros Hc; apply Hnfs; exact (Tac_fs.a_fs_in AC.ASYMS mem FS x HFSw HFSr Hc)).
      apply OUTAPP; [exact Happx | lia | lia | lia |].
      intros _. repeat split; lia. }
    split; [unfold a0v, rg; rewrite E10; reflexivity|].
    split.
    { intros Hok. destruct (RW0 Hok) as (RA & RP & RN).
      split; [exact (r10_rw_back mem' m0' _ _ _ HRel RA)|].
      split; [exact (r10_rw_back mem' m0' _ _ _ HRel RP) | exact (r10_rw_back mem' m0' _ _ _ HRel RN)]. }
    unfold rg in *. rewrite E27. exact Hr27.
Qed.

(* ==== seg_R10: the dispatch on the turn index b (forms-asan-ubsan.md S_R10, on the official cuts) ==== *)
Lemma seg_R10 : forall b : nat,
  Hat B APIf ra (Inv_B817ec_at B APIf ra) b -> Hat B APIf ra (Inv_B81834_at B APIf ra) b ->
  Hat B APIf ra (Inv_B818a8_at B APIf ra) b -> Hat B APIf ra (Inv_B81914_at B APIf ra) b ->
  Hat B APIf ra (Inv_B8194c_at B APIf ra) b -> Hat B APIf ra (Inv_B817a4_at B APIf ra) b.
Proof.
  intros b H88 Hd0 H44 Hb0 He8 g c HInv.
  assert (Hb6 : (b <= 6)%nat)
    by (destruct HInv as (phi & regs & mem & md & fr & _ & _ & _ & _ & Hb & _); exact Hb).
  destruct b as [|[|[|[|[|[|[|b]]]]]]]; [..|lia].
  - exact (r10_arm0 0%nat eq_refl H44 g c HInv).
  - exact (r10_arm12 1%nat (or_introl eq_refl) He8 g c HInv).
  - exact (r10_arm12 2%nat (or_intror eq_refl) He8 g c HInv).
  - exact (r10_arm34 3%nat (or_introl eq_refl) H88 g c HInv).
  - exact (r10_arm34 4%nat (or_intror eq_refl) H88 g c HInv).
  - exact (r10_arm5 5%nat eq_refl Hb0 g c HInv).
  - exact (r10_arm6 6%nat eq_refl Hd0 g c HInv).
Qed.

End R10.
