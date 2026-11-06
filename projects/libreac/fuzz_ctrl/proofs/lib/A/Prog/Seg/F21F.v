(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 594 of its 661 lines of code are new or changed and 2490 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F21.v; 202 of its 337 lines of code are new or changed and 526 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F21.v blob 2ea8e91ed500 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F21.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F21.<r> after F21's own first premise (the plain record-verifier contract). Mechanical re-run,
   route (a) (lead 22:15Z); input to the ported walk only.
   Callee _F cited: reac_ctrl_headamp_record_verify_contract_F, proved by
   lib/A/Prog/reac_ctrl_headamp_record_verify_F.v (blob 87d3a9c0822b, copied byte-for-byte from 911c6aa5d24 with its
   statement's home lib/A/Prog/reac_ctrl_headamp_record_verify_c.v blob a751f3b5d3ae; neither is on fdd2ed9f9d7). *)
(* Footprint twins of Seg/F21.v f21_t2 / f21_evt (re-walk form, RECIPE.md steps 1-2 (a working note, not in this delivery)): the same runs as
   ExecF.evtF under a footprint RNG, with one rng premise per region the run (or the record verifier it calls through
   its footprint contract reac_ctrl_headamp_record_verify_contract_F) reads or writes: the record bytes
   [phi+18, phi+20) and [phi+34, phi+40), the shadow bytes of those bytes, the callee frame [sp-16, sp), the GOT cell
   of the shadow-offset cell and that cell, and (f21_evt_F) the sum_ok spill [A+280, A+288).
   F21.v is unchanged; f21_t2_of_F / f21_evt_of_F re-derive its statements from the twins with RNG_all.

   v1.9.0 (2026-10-28): moved onto a Theorem Labs lane's v1.9 F21 runs (a working branch 3b23b0e7141, Seg/F21.v f21_t2 :244,
   f21_evt :360; the two statements are byte-identical to the ones at 5eecbc43670). Every pc is copied from a Theorem Labs lane's
   text: v1.8 0x82408 / 0x82458 / 0x824a8 / 0x824ec / 0x824f4 -> v1.9 0x824b4 / 0x82504 / 0x82554 / 0x82598 /
   0x825a0. The footprint regions are the v1.8 ones; the image cells are named GOT_CELL_K / CELL_K (lib/A/AsanRT.v,
   v1.9 0x9fad0 / 0xa8878). The record verifier is no longer a Section hypothesis: f21_harvc_F, the file's one use
   of the callee contract, applies its owner's proof reac_ctrl_headamp_record_verify_holds_F (lib/A/Prog/
   reac_ctrl_headamp_record_verify_F.v, a working branch dcf92cb416a). So the twins and the _of_F corollaries
   take no hypothesis; the owner's f21_t2 / f21_evt take the plain contract as their first premise (F21.v Section S,
   Hypothesis HARV), and the *_of_F_verbatim checks pin each corollary with constr_eq to the owner's statement after
   that premise. *)
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
(* StepF after the old engine: its step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* YK11 last, as in F21.v (its seg_rom). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
Import ListNotations.
Open Scope Z_scope.

Module HRVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_headamp_record_verify_F.

(* The instrumented check of byte y loads the shadow byte at (y >> 3) + ASAN_K; it lies in the shadow range of a block
   [x, z] that contains y. *)
Lemma f21_sh_rng : forall (RNG : ExecF.footprint) x y z, 0 <= x <= y -> y <= z ->
  ExecF.rng RNG (shadow_addr x) (shadow_addr z - shadow_addr x + 1) ->
  ExecF.rng RNG (Z.shiftr y 3 + ASAN_K) 1.
Proof.
  intros RNG x y z Hxy Hyz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono y z 8 ltac:(lia) ltac:(lia)).
  eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr; lia.
Qed.

(* ---- The record verifier call 0x82598 `mv a0,s7` / 0x8259c `jal reac_ctrl_headamp_record_verify`, landing at
   0x825a0, under the callee's footprint contract. This is the file's one use of that contract: its owner's proof
   reac_ctrl_headamp_record_verify_holds_F. ---- *)
Lemma f21_harvc_F :
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
    asan_cells m -> shadow_rw m ->
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
    phi lo sp b0 b1 rest g6 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC HSW Hadr2 Hadr6
    R18 R34 RS18 RS34 RFr RGOT RCK.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  (* 0x82598 mv a0,s7 ; 0x8259c jal reac_ctrl_headamp_record_verify *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply HRVF.reac_ctrl_headamp_record_verify_holds_F with (p := phi) (lo := lo) (b0 := b0) (b1 := b1) (rec := g6);
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
    - exact HSW.
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

(* ---- f21_t2 as an evtF: the run from 0x82504 to 0x82554 or, through the record verifier, 0x825a0. ---- *)
Lemma f21_t2_F :
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
    asan_cells m -> shadow_rw m ->
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
    phi lo sp b0 b1 rest g6 Es7 Es10 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC HSW Hadr2 Hadr6 Hs18 Hs19
    R18 R34 RS18 RS34 RFr RGOT RCK.
  subst s7 s10.
  (* the two instrumented shadow loads, in the address form the code computes *)
  pose proof (f21_sh_rng RNG (phi + 18) (phi + 18) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC18.
  pose proof (f21_sh_rng RNG (phi + 18) (phi + 19) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC19.
  pose proof (ubyte b0) as Rb0. pose proof (ubyte b1) as Rb1.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 0 (phi + 18) Hblk ltac:(cbn; lia) ltac:(lia)) as Hy0.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 1 (phi + 19) Hblk ltac:(cbn; lia) ltac:(cbn; lia)) as Hy1.
  cbn [nth] in Hy0, Hy1.
  apply rd1 in Hy0, Hy1, Hs18, Hs19.
  (* the record verifier call at 0x82598 / 0x8259c, used by both failure arms *)
  pose proof (fun ra1 c0 c1 c2 c3 c4 c5 =>
    f21_harvc_F RNG ra1 gp tp t0 t1 t2 s0 s1 c0 c1 c2 c3 c4 c5 a6 a7 s2 s3 s5 s6 s8 s9 s11 t3 t4 t5 t6 Fr fc m
      phi lo sp b0 b1 rest g6 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC HSW Hadr2 Hadr6
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

(* ---- f21_evt as an evtF: the run from 0x824b4 (the checksum call returned) to 0x82554 / 0x825a0. ---- *)
Lemma f21_evt_F :
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
    asan_cells m -> shadow_rw m ->
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
    HSW Hadr2 Hadr6 Hs18 Hs19 Hk6 R18 R34 RS18 RS34 RFr RGOT RCK RQ.
  subst s1 s8 s10.
  pose proof (f21_sh_rng RNG (phi + 18) (phi + 18) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC18.
  pose proof (f21_sh_rng RNG (phi + 18) (phi + 19) (phi + 19) ltac:(lia) ltac:(lia) RS18) as RC19.
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
    eapply f21_t2_F with (RNG := RNG) (b0 := b0) (b1 := b1) (rest := rest) (g6 := g6) (lo := lo) (sp := sp);
      try eassumption; reflexivity.
  - assert (C : negb (bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 6)) = true) by (apply neqb_lit; lia).
    rewrite C; cbv iota.
    eapply f21_t2_F with (RNG := RNG) (b0 := b0) (b1 := b1) (rest := rest) (g6 := g6) (lo := lo) (sp := sp);
      try eassumption; reflexivity.
Qed.

(* ---- F21.f21_t2 / F21.f21_evt restated (RECIPE step 1): evtF_evt of the twins at RNG_all, each rng by rng_all. ---- *)
Ltac f21_rng_all :=
  apply ExecF.rng_all;
  unfold shadow_addr, GOT_CELL_K, CELL_K, ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia.

Lemma f21_t2_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rest g6 : list byte),
    s7 = Z_to_bv 64 phi -> s10 = Z_to_bv 64 ASAN_K -> 0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) (b0 :: b1 :: rest) ->
    length g6 = 6%nat -> bytes_at rsegs m (phi + 34) g6 ->
    stk rsegs m lo sp ->
    asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    b8 m (Z.shiftr (phi + 18) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 19) 3 + ASAN_K) 0 ->
    evt rsegs
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
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rest g6 Es7 Es10 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC HSW Hadr2 Hadr6 Hs18 Hs19.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f21_t2_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m phi lo sp b0 b1 rest g6); try assumption; f21_rng_all.
Qed.

Lemma f21_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    b8 m (Z.shiftr (phi + 18) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 19) 3 + ASAN_K) 0 ->
    (k = 6 -> bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3) ->
    evt rsegs
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
  intros ra0 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi A k sv lo sp b0 b1 rest g6 Es1 Es8 Es10 Rsp Hp0 HpE Hpsp HspA HA Hk Hlo Hlo16 Hblk Lg6 Hg6 Hq Hstk HAC
    HSW Hadr2 Hadr6 Hs18 Hs19 Hk6.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f21_evt_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m phi A k sv lo sp b0 b1 rest g6); try assumption; f21_rng_all.
Qed.

(* ---- The pins: each *_of_F states the owner's v1.9 text after the owner's first premise, the plain record-verifier
   contract (F21.v Section S, Hypothesis HARV), term for term (constr_eq: syntactic, not up to conversion). The
   corollaries need no premise in its place: the callee is proved (f21_harvc_F). *)
Example f21_t2_of_F_verbatim : True.
Proof.
  lazymatch type of F21.f21_t2 with ?P -> ?A =>
    constr_eq P reac_ctrl_headamp_record_verify_contract;
    let B := type of f21_t2_of_F in constr_eq A B
  end.
  exact I.
Qed.

Example f21_evt_of_F_verbatim : True.
Proof.
  lazymatch type of F21.f21_evt with ?P -> ?A =>
    constr_eq P reac_ctrl_headamp_record_verify_contract;
    let B := type of f21_evt_of_F in constr_eq A B
  end.
  exact I.
Qed.
