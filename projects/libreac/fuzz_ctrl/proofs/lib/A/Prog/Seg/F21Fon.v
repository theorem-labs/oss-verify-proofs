(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 594 of its 661 lines of code are new or changed and 2490 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F21.v; 108 of its 236 lines of code are new or changed and 533 lines of the source are left out. *)
(* lib/A/Prog/Seg/F21Fon.v -- route (C) twin of Seg/F21F.v's three footprint runs, WITHOUT the universal
   `shadow_rw m` premise.  ADDITIVE beside-file (a Theorem Labs lane 12:52Z twin rule): Seg/F21F.v stays unchanged apart from comment text.
   Writer: a Theorem Labs lane for a Theorem Labs lane.  proves no function (kind: segment lemma).

   BASE: a Theorem Labs lane's fold blob of Seg/F21F.v, a working branch 4bae33fdf54, blob efae945746f;
   a working branch 1899bed1aee carries the SAME blob (an earlier version, blob efae945746f, not in this delivery) (diffed: empty), so the base is both.

   MEASURED (why the premise is removed, not narrowed): in F21F.v the premise `shadow_rw m` (named HSW) is never read
   and never stored through.  f21_evt_F hands it to f21_t2_F (by eassumption), f21_t2_F hands it to f21_harvc_F, and
   f21_harvc_F's only use is `exact HSW` at the record verifier's contract (F21F.v:118).  The two shadow LOADS of the
   segment (0x82504 / 0x82524, the bytes of phi+18 / phi+19) are read from the byte premises Hs18 / Hs19, and the
   segment STORES no shadow byte.  So the twin drops the premise, and the callee is taken in its route-(C) form.

   CALLEE FORM: reac_ctrl_headamp_record_verify_contract_F_on (premise DROPPED; LANDED.md (a working note, not in this delivery), a Theorem Labs lane
   a working branch 9509908083d, statement blob reac_ctrl_headamp_record_verify_c.v 86718f5a3d6), discharged
   by its proof reac_ctrl_headamp_record_verify_holds_F_on (LANDED.md (a working note, not in this delivery), a Theorem Labs lane 36bfd511da3, in
   a working branch 330e60af39d, blob reac_ctrl_headamp_record_verify_F.v 67d0e3dc3d4).

   THE TWINS (same statements as F21F.v's, minus the one premise; the proofs are F21F.v's text minus the hand-on):
     f21_harvc_F_on  <- f21_harvc_F  (0x82598 / 0x8259c, the record verifier call, landing at 0x825a0)
     f21_t2_F_on     <- f21_t2_F     (0x82504 -> 0x82554 / 0x825a0)
     f21_evt_F_on    <- f21_evt_F    (0x824b4 -> 0x82554 / 0x825a0)
   f21_sh_rng is cited from F21F.v, not copied.  No pin back to the old lemmas.  No unproved step, no Axiom. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcFrag RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_headamp_record_verify_c.
(* The record verifier's owner proof; not imported, so its helper names shadow nothing here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_headamp_record_verify_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F21.
(* a Theorem Labs lane's footprint runs: only f21_sh_rng is cited; not imported. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F21F.
(* StepF after the old engine: its step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* YK11 last, as in F21.v (its seg_rom). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
Import ListNotations.
Local Open Scope Z_scope.

Lemma f21_harvc_F_on :
  forall (RNG : ExecF.footprint)
         (ra1 gp tp t0 t1 t2 s0 s1 c0 c1 c2 c3 c4 c5 a6 a7 s2 s3 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rest g6 : list byte),
    0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) (b0 :: b1 :: rest) ->
    length g6 = 6%nat -> bytes_at rsegs m (phi + 34) g6 ->
    stk rsegs m lo sp ->
    asan_cells m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    ExecF.rng RNG (phi + 18) 2 -> ExecF.rng RNG (phi + 34) 6 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.rng RNG (shadow_addr (phi + 34)) (shadow_addr (phi + 39) - shadow_addr (phi + 34) + 1) ->
    ExecF.rng RNG (sp - 16) 16 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 g6 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (-1)) s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x825a0) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp)
      (MS (mkR ra1 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 c0 c1 c2 c3 c4 c5 a6 a7
               s2 s3 (Z_to_bv 64 (-1)) s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82598) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra1 gp tp t0 t1 t2 s0 s1 c0 c1 c2 c3 c4 c5 a6 a7 s2 s3 s5 s6 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rest g6 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC Hadr2 Hadr6
    R18 R34 RS18 RS34 RFr RGOT RCK.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  (* 0x82598 mv a0,s7 ; 0x8259c jal reac_ctrl_headamp_record_verify *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply reac_ctrl_headamp_record_verify_F.reac_ctrl_headamp_record_verify_holds_F_on with (p := phi) (lo := lo) (b0 := b0) (b1 := b1) (rec := g6);
      unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME; rewrite ?Esp.
    - reflexivity.
    - lia.
    - unfold APPMEM_END in HpE. lia.
    - exact (ba_pre2 m (phi + 18) b0 b1 rest Hblk).
    - exact Lg6.
    - exact Hg6.
    - exact Hstk.
    - lia.
    - left. lia.
    - left. lia.
    - exact HAC.
    - exact Hadr2.
    - exact Hadr6.
    - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
      lia.
    - exact RFr.
    - exact RGOT.
    - exact RCK.
    - exact R18.
    - exact R34.
    - exact RS18.
    - exact RS34. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
  unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  apply ExecF.evtF_done.
  do 7 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

Lemma f21_t2_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rest g6 : list byte),
    s7 = Z_to_bv 64 phi -> s10 = Z_to_bv 64 ASAN_K -> 0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) (b0 :: b1 :: rest) ->
    length g6 = 6%nat -> bytes_at rsegs m (phi + 34) g6 ->
    stk rsegs m lo sp ->
    asan_cells m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    b8 m (Z.shiftr (phi + 18) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 19) 3 + ASAN_K) 0 ->
    ExecF.rng RNG (phi + 18) 2 -> ExecF.rng RNG (phi + 34) 6 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.rng RNG (shadow_addr (phi + 34)) (shadow_addr (phi + 39) - shadow_addr (phi + 34) + 1) ->
    ExecF.rng RNG (sp - 16) 16 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte) (pcv : Z),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 pcv) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp /\
         ((pcv = 0x82554 /\ a0' = Z_to_bv 64 (phi + 34) /\ a1' = Z_to_bv 64 0 /\
           a2' = Z_to_bv 64 (phi + 34) /\ a3' = Z_to_bv 64 6 /\
           bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3)
          \/ (pcv = 0x825a0 /\ a0' = Z_to_bv 64 (if hv b0 b1 g6 then 0 else -1) /\ hv b0 b1 g6 = false)))
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (phi + 18)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82504) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rest g6 Es7 Es10 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC Hadr2 Hadr6 Hs18 Hs19
    R18 R34 RS18 RS34 RFr RGOT RCK.
  subst s7 s10.
  (* the two instrumented shadow loads, in the address form the code computes *)
  pose proof (F21F.f21_sh_rng RNG (phi + 18) (phi + 18) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC18.
  pose proof (F21F.f21_sh_rng RNG (phi + 18) (phi + 19) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC19.
  pose proof (ubyte b0) as Rb0. pose proof (ubyte b1) as Rb1.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 0 (phi + 18) Hblk ltac:(cbn; lia) ltac:(lia)) as Hy0.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 1 (phi + 19) Hblk ltac:(cbn; lia) ltac:(cbn; lia)) as Hy1.
  cbn [nth] in Hy0, Hy1.
  apply rd1 in Hy0, Hy1, Hs18, Hs19.
  (* the record verifier call at 0x82598 / 0x8259c, used by both failure arms *)
  pose proof (fun ra1 c0 c1 c2 c3 c4 c5 =>
    f21_harvc_F_on RNG ra1 gp tp t0 t1 t2 s0 s1 c0 c1 c2 c3 c4 c5 a6 a7 s2 s3 s5 s6 s8 s9 s11 t3 t4 t5 t6 Fr fc m
      phi lo sp b0 b1 rest g6 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC Hadr2 Hadr6
      R18 R34 RS18 RS34 RFr RGOT RCK) as HARVC.
  (* 0x82504 srli ; add ; lb shadow(phi+18) ; bnez (0, not taken) *)
  step. step. ush. step. step. if_false.
  (* 0x82514 lbu a0 = b0 ; li s4,-1 ; li a1,4 ; bne a0,a1,82598 *)
  step. zx. step. step. step.
  destruct (Z.eq_dec (bv_unsigned b0) 4) as [Ey0|Ny0].
  2: { assert (C : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 4)) = true) by (apply neqb_lit; lia).
       rewrite C; cbv iota.
       eapply ExecF.evtF_mono; [apply HARVC|].
       intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & ST'). subst ms'.
       do 8 eexists. exists m', 0x825a0. split; [reflexivity|].
       split; [exact MU|]. split; [exact WM|]. split; [exact ST'|].
       right. split; [reflexivity|]. split; [reflexivity | apply hv_false; left; lia]. }
  rewrite Ey0. if_false.
  (* 0x82524 addi a0,s7,19 ; srli ; add ; lb shadow(phi+19) ; bnez (0) *)
  step. step. step. ush. step. step. if_false.
  (* 0x82538 lbu a0 = b1 ; li a1,3 ; bne a0,a1,82598 *)
  step. zx. step. step.
  destruct (Z.eq_dec (bv_unsigned b1) 3) as [Ey1|Ny1].
  2: { assert (C : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b1)) (Z_to_bv 64 3)) = true) by (apply neqb_lit; lia).
       rewrite C; cbv iota.
       eapply ExecF.evtF_mono; [apply HARVC|].
       intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & ST'). subst ms'.
       do 8 eexists. exists m', 0x825a0. split; [reflexivity|].
       split; [exact MU|]. split; [exact WM|]. split; [exact ST'|].
       right. split; [reflexivity|]. split; [reflexivity | apply hv_false; right; lia]. }
  rewrite Ey1. if_false.
  (* 0x82544 li a1,0 ; addi a2,s7,34 ; li a3,6 ; mv a0,a2 : the loop head 0x82554 *)
  step. step. step. step.
  apply ExecF.evtF_done.
  do 8 eexists. exists m, 0x82554. split; [reflexivity|].
  split; [apply munch_refl|]. split; [intros x Hx; exact Hx|]. split; [exact Hstk|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; first [reflexivity | assumption].
Qed.

Lemma f21_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A k sv lo sp : Z) (b0 b1 : byte) (rest g6 : list byte),
    s1 = Z_to_bv 64 A -> s8 = Z_to_bv 64 k -> s10 = Z_to_bv 64 ASAN_K -> 0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    sp <= A -> A + 288 <= 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) (b0 :: b1 :: rest) ->
    length g6 = 6%nat -> bytes_at rsegs m (phi + 34) g6 ->
    q64 m (A + 280) sv ->
    stk rsegs m lo sp ->
    asan_cells m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    b8 m (Z.shiftr (phi + 18) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 19) 3 + ASAN_K) 0 ->
    (k = 6 -> bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3) ->
    ExecF.rng RNG (phi + 18) 2 -> ExecF.rng RNG (phi + 34) 6 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.rng RNG (shadow_addr (phi + 34)) (shadow_addr (phi + 39) - shadow_addr (phi + 34) + 1) ->
    ExecF.rng RNG (sp - 16) 16 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (A + 280) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte) (pcv : Z),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (-1)) s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 pcv) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp /\
         ((pcv = 0x82554 /\ a0' = Z_to_bv 64 (phi + 34) /\ a1' = Z_to_bv 64 0 /\
           a2' = Z_to_bv 64 (phi + 34) /\ a3' = Z_to_bv 64 6 /\
           bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3)
          \/ (pcv = 0x825a0 /\ a0' = Z_to_bv 64 (if hv b0 b1 g6 then 0 else -1) /\ hv b0 b1 g6 = false)))
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sv + -1)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (phi + 18)) s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x824b4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi A k sv lo sp b0 b1 rest g6 Es1 Es8 Es10 Rsp Hp0 HpE Hpsp HspA HA Hk Hlo Hlo16 Hblk Lg6 Hg6 Hq Hstk HAC
    Hadr2 Hadr6 Hs18 Hs19 Hk6 R18 R34 RS18 RS34 RFr RGOT RCK RQ.
  subst s1 s8 s10.
  pose proof (F21F.f21_sh_rng RNG (phi + 18) (phi + 18) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC18.
  pose proof (F21F.f21_sh_rng RNG (phi + 18) (phi + 19) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC19.
  pose proof (ubyte b0) as Rb0. pose proof (ubyte b1) as Rb1.
  pose proof Hs18 as Sh18. pose proof Hs19 as Sh19.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 0 (phi + 18) Hblk ltac:(cbn; lia) ltac:(lia)) as Hy0.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 1 (phi + 19) Hblk ltac:(cbn; lia) ltac:(cbn; lia)) as Hy1.
  cbn [nth] in Hy0, Hy1.
  pose proof (rd8 m _ _ Hq) as RDq.
  pose proof (rd1 m _ _ Hy0) as RDy0. pose proof (rd1 m _ _ Hy1) as RDy1.
  pose proof (rd1 m _ _ Hs18) as RD18. pose proof (rd1 m _ _ Hs19) as RD19.
  (* 0x824b4 ld a1,280(s1) ; addi a1,a1,-1 ; bne a0,a1 (equal: not taken) *)
  step. step. step. if_false.
  (* 0x824c0 li a0,6 ; bne s8,a0,82504 *)
  step. step.
  destruct (Z.eq_dec k 6) as [Ek|Hk6n].
  - subst k. destruct (Hk6 eq_refl) as [Ey0 Ey1]. if_false.
    (* k = 6: srli ; add ; lb shadow(phi+18) ; bnez ; lbu a0 = 4 ; li a1,4 ; bne (not taken) *)
    step. step. ush. step. step. if_false.
    step. zx. step. step.
    assert (C0 : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 4)) = false)
      by (rewrite Ey0, bv_eqb_refl; reflexivity).
    rewrite C0; cbv iota.
    (* addi a0,s7,19 ; srli ; add ; lb shadow(phi+19) ; bnez ; lbu a0 = 3 ; li a1,3 ; bne (not taken) *)
    step. step. step. ush. step. step. if_false.
    step. zx. step. step.
    assert (C1 : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b1)) (Z_to_bv 64 3)) = false)
      by (rewrite Ey1, bv_eqb_refl; reflexivity).
    rewrite C1; cbv iota.
    eapply f21_t2_F_on with (RNG := RNG) (b0 := b0) (b1 := b1) (rest := rest) (g6 := g6) (lo := lo) (sp := sp);
      try eassumption; reflexivity.
  - assert (C : negb (bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 6)) = true) by (apply neqb_lit; lia).
    rewrite C; cbv iota.
    eapply f21_t2_F_on with (RNG := RNG) (b0 := b0) (b1 := b1) (rest := rest) (g6 := g6) (lo := lo) (sp := sp);
      try eassumption; reflexivity.
Qed.
