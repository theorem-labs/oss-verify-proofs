(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its numbers changed; 891 of its 928 lines of code are new or changed and 359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/X12.v; 113 of its 238 lines of code are new or changed and 803 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/X12.v a0b6ac9aa84d (the blob this tree had at release c5e779efe8c) (x12_a_evt :360-466); footprint
   forms of record: Seg/X12F.v blob 257dd19e2822.  Tools: lib/Lib/StepF.v, lib/Lib/ExecF.v, The Rocq Prover 9.2.
   Written by a Theorem Labs lane's glue lane (the split rule of a Theorem Labs lane with a Theorem Labs lane, 04:01Z: a split goes in a
   NEW file Seg/<S>Fs.v that only Requires <S>F.v and the sources).  rule 24: no function proved; mechanical cut of
   an already-proved run.

   THE SPLIT (spec segF-v19-spec.md "SPLIT STRETCHES", items 1-3 (a working note, not in this delivery)).  x12_a_evt (X12.v:360)
   runs 0x82b04 -> 0x82b20 THROUGH the memchr wrapper call `jal 0x42974` at 0x82b1c.  The wrapper's footprint form
   X12F.memchr_wrap_F is proved only at ExecF.RNG_all (X12F.memchr_wrap_F_all), so the call has no _F for a general
   footprint: split case (b) of the 04:01Z rule (a runtime callee with no proved general-RNG _F).  The walk applies
   the memchr SITE RULE at the wrapper's entry instead (plan (a working note, not in this delivery): a Theorem Labs lane's amemchr_realizesM at
   0x42974, c := 0, n := 17).
   1. x12_a_pre_F: 0x82b04 -> 0x42974, the seven instructions before and including the call, cut from X12.v:405-415
      (x12_a_evt's own script):
        0x82b04 ld a1,144(s1)  0x82b08 lbu a0,20(a1)  0x82b0c beqz a0,0x82b24 (NOT taken, byte 20 <> 0)
        0x82b10 addi a0,a1,3   0x82b14 li a2,17       0x82b18 mv a1,zero   0x82b1c jal ra,0x42974
      ending at the callee entry state (pc = MW.MEMCHR_WRAP = 0x42974, ra = the return pc 0x82b20), as the allocator
      runs end.  x12_a_pre_F carries x12_a_evt's binders and premises with the stretch's two rng premises appended
      (spec segF-v19-spec.md item 1 (a working note, not in this delivery)).  Under the NARROWED-STRETCH rule (a Theorem Labs lane 04:23Z, relayed 04:34Z), x12_a_pre_Fs carries only
      the four premises its own steps use (s1 = A, the spill cell [A + 144], the record byte at fr + 2708,
      b20 <> 0) and x12_a_pre_F_of_Fs re-derives x12_a_pre_F from it, pinned by constr_eq to x12_a_pre_F's
      statement.  The callee-only premises (buf / j / ro_agree / addressable / app_mem / the wrapper's stack window /
      asan_cells / shadow_rw / the REAL_MEMCHR cell) are read by no instruction of the stretch; the walk consumes
      x12_a_pre_Fs, because at the split site it discharges the site rule's premises instead (the REAL_MEMCHR cell,
      for one, is no fact of the cut layer).
   2. NO post stretch: the source run ENDS at the callee's own post (x12_a_evt's post is stated at the return pc
      0x82b20, read straight off memchr_wrap_post), so zero instructions run after the return; as A1F.v's a1_req_evt
      split (A1F.v:249-254).  X12Fs.rng.tsv carries the callee_split row.
   3. x12_a_evt_of_pre_post: x12_a_pre_F at RNG_all + the PLAIN callee contract memchr_wrap.memchr_wrap_holds
      (the in-tree theorem X12.v:416 applies) re-derive X12.x12_a_evt; the script after the call is X12.v:416-465,
      unchanged.  x12_a_evt_of_pre_post_verbatim pins it by constr_eq against the type of X12.x12_a_evt. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memchr_c memchr_wrap_c memchr_wrap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs X12 X12F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all RngBytes.
(* LAST: StepF's step / store_done / finish match evtF goals and shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* After StepF: the image-A YK11 by full path, as in X12.v / X12F.v, to restore getr. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module SX12 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12.

(* ---- the NARROWED pre stretch (a Theorem Labs lane 04:23Z narrowed-stretch rule): 0x82b04 -> the memchr wrapper's entry
   0x42974, ra = 0x82b20 (X12.v:405-415), carrying only the four premises its own steps use.  The glue consumes this. *)
Lemma x12_a_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr : Z) (b20 : byte),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    (* the spill reload 0x82b04 and the record byte 0x82b08 *)
    ExecF.rng RNG (A + 144) 8 -> ExecF.rng RNG (fr + 2708) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82b20) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (fr + 2691))
                               (Z_to_bv 64 0) (Z_to_bv 64 17) a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 MW.MEMCHR_WRAP) fc None m (A.Reusable.YK11.seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr b20 -> H144 H20 Hb20 R144 R20.
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite kb_unsigned_zxb in E. rewrite LMS.unsigned_lit in E by lia. exact (Hb20 E). }
  pose proof (x12_rd_le8 _ _ _ H144) as HR144.
  step.
  pose proof (x12_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12f_br false HB.
  step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- the pre stretch in the split spec's form (segF-v19-spec.md "SPLIT STRETCHES" item 1 (a working note, not in this delivery)): x12_a_evt's binders and
   premises, RNG first, the stretch's two rng premises appended; the steps of X12.v:405-415. *)
Lemma x12_a_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr lo spZ : Z) (buf : list byte) (b20 : byte) (j : nat),
    s1v = Z_to_bv 64 A -> bv_unsigned sp = spZ ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    bytes_at rsegs m (fr + 2691) buf -> length buf = 17%nat -> SF.find_byte 0 buf = Some j ->
    ro_agree rsegs m -> addressable m (fr + 2691) 17 ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spZ - 2208 \/ spZ <= fr) ->
    stk rsegs m lo spZ -> lo + 2208 <= spZ ->
    HIGHMEM_BEG <= lo -> spZ <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) ->
    (* the spill reload 0x82b04 and the record byte 0x82b08 *)
    ExecF.rng RNG (A + 144) 8 -> ExecF.rng RNG (fr + 2708) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82b20) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (fr + 2691))
                               (Z_to_bv 64 0) (Z_to_bv 64 17) a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 MW.MEMCHR_WRAP) fc None m (A.Reusable.YK11.seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr lo spZ buf b20 j -> Esp H144 Hfr0 HfrA H20 Hb20 Hbuf HbufL HFB HRO Hadr Happ Hdisj
    HST Hlo1 Hlo2 Hspa HAC HSW HRM R144 R20.
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite kb_unsigned_zxb in E. rewrite LMS.unsigned_lit in E by lia. exact (Hb20 E). }
  pose proof (x12_rd_le8 _ _ _ H144) as HR144.
  step.
  pose proof (x12_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12f_br false HB.
  step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- x12_a_pre_F re-derived from the narrowed stretch, pinned to x12_a_pre_F's statement (the narrowed-stretch
   rule: x12_a_pre_Fs is provably the same stretch). *)
Lemma x12_a_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr lo spZ : Z) (buf : list byte) (b20 : byte) (j : nat),
    s1v = Z_to_bv 64 A -> bv_unsigned sp = spZ ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    bytes_at rsegs m (fr + 2691) buf -> length buf = 17%nat -> SF.find_byte 0 buf = Some j ->
    ro_agree rsegs m -> addressable m (fr + 2691) 17 ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spZ - 2208 \/ spZ <= fr) ->
    stk rsegs m lo spZ -> lo + 2208 <= spZ ->
    HIGHMEM_BEG <= lo -> spZ <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) ->
    (* the spill reload 0x82b04 and the record byte 0x82b08 *)
    ExecF.rng RNG (A + 144) 8 -> ExecF.rng RNG (fr + 2708) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82b20) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (fr + 2691))
                               (Z_to_bv 64 0) (Z_to_bv 64 17) a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 MW.MEMCHR_WRAP) fc None m (A.Reusable.YK11.seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr lo spZ buf b20 j Hs1 _ H144 _ _ H20 Hb20 _ _ _ _ _ _ _ _ _ _ _ _ _ _ R144 R20.
  exact (x12_a_pre_Fs RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
           t5 t6 sp F fc m A fr b20 Hs1 H144 H20 Hb20 R144 R20).
Qed.

Lemma x12_a_pre_F_of_Fs_verbatim : True.
Proof.
  let A := type of x12_a_pre_F in let B := type of x12_a_pre_F_of_Fs in constr_eq A B; exact I.
Qed.

(* ---- X12.x12_a_evt from the pre stretch at RNG_all and the callee's own proved contract
   memchr_wrap.memchr_wrap_holds, which the source applies (X12.v:416).  Everything after the jal is the source script
   X12.v:416-465, unchanged; the source's preparation X12.v:392-404 is kept, its four steps are pre_F. *)
Lemma x12_a_evt_of_pre_post :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr lo spZ : Z) (buf : list byte) (b20 : byte) (j : nat),
    s1v = Z_to_bv 64 A -> bv_unsigned sp = spZ ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    bytes_at rsegs m (fr + 2691) buf -> length buf = 17%nat -> SF.find_byte 0 buf = Some j ->
    ro_agree rsegs m -> addressable m (fr + 2691) 17 ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spZ - 2208 \/ spZ <= fr) ->
    stk rsegs m lo spZ -> lo + 2208 <= spZ ->
    HIGHMEM_BEG <= lo -> spZ <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) ->
    LE.evt rsegs
      (fun ms' => exists (x1 a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR x1 sp gp tp t0' t1' t2' s0 s1v (Z_to_bv 64 (fr + 2691 + Z.of_nat j))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82b20) fc None m' (A.Reusable.YK11.seg_rom rsegs)
         /\ munch [(spZ - 2208, spZ)] m m'
         /\ wmono rsegs m m' /\ ro_same rsegs m m' /\ stk rsegs m' lo spZ
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr lo spZ buf b20 j -> Esp H144 Hfr0 HfrA H20 Hb20 Hbuf HbufL HFB HRO Hadr Happ Hdisj
    HST Hlo1 Hlo2 Hspa HAC HSW HRM.
  pose proof (x12f_ba_bounds _ _ _ H144) as B144. rewrite length_le8 in B144.
  pose proof (x12f_ba_bounds _ _ _ H20) as B20. cbn [length] in B20.
  (* the pre stretch (X12.v:405-415's four steps), at RNG_all *)
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (x12_a_pre_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6 sp F fc m A fr lo spZ buf b20 j eq_refl Esp H144 Hfr0 HfrA H20 Hb20
             Hbuf HbufL HFB HRO Hadr Happ Hdisj HST Hlo1 Hlo2 Hspa HAC HSW HRM);
      apply ExecF.rng_all; lia. }
  intros ms' ->.
  (* X12.v:392-404, the source's preparation *)
  subst spZ. pose proof FRAME_BYTES_val as HFBv.
  unfold APPMEM_END in HfrA.
  assert (HPb : 0 <= fr + 2691 < 2 ^ 64) by lia.
  pose proof (SF.find_byte_Some 0 buf j HFB) as (Hjl & _ & _).
  assert (HFF : SF.find_byte 0 (firstn (Z.to_nat 17) buf) = Some j).
  { rewrite firstn_all2 by (rewrite HbufL; cbn [Z.to_nat]; lia). exact HFB. }
  assert (HRES : SF.memchr_res (fr + 2691) 0 17 buf = fr + 2691 + Z.of_nat j)
    by (unfold SF.memchr_res; rewrite HFF; reflexivity).
  assert (HN : MW.memchr_n (fr + 2691) 0 17 buf = Z.of_nat j + 1).
  { unfold MW.memchr_n. rewrite HRES.
    replace (fr + 2691 + Z.of_nat j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  assert (HOK : SF.memchr_ok (fr + 2691) 0 17 buf).
  { unfold SF.memchr_ok. rewrite HFF. left. rewrite HbufL. cbn [Z.of_nat]. lia. }
  (* X12.v:416-465, unchanged *)
  pose proof MWH.memchr_wrap_holds as HM. unfold MW.memchr_wrap_contract, MW.MEMCHR_WRAP_K in HM. cbv zeta in HM.
  assert (EP : bv_unsigned (Z_to_bv 64 (fr + 2691)) = fr + 2691) by (apply LMS.unsigned_lit; lia).
  assert (E0 : bv_unsigned (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity).
  assert (E17 : bv_unsigned (Z_to_bv 64 17) = 17) by (vm_compute; reflexivity).
  eapply LE.evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (A.Reusable.YK11.seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO).
    pose proof (mem_rel_normalize rsegs m HRO) as REL.
    eapply HM with (buf := buf) (lo := lo).
    all: rewrite ?EP, ?E0, ?E17, ?Zmod_0_l, ?HN.
    - exact (bytes_at_normalize rsegs m (fr + 2691) buf HRO Hbuf).
    - exact HOK.
    - apply mem_inv_normalize.
    - lia.
    - apply (x12_addr_rel m (normalize rsegs m) (fr + 2691) (Z.of_nat j + 1) REL).
      pose proof (addressable_sub m (fr + 2691) 17 0 (Z.of_nat j + 1) Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as HA2.
      rewrite Z.add_0_r in HA2. exact HA2.
    - right. apply Happ. lia.
    - right. apply Happ. lia.
    - rewrite HbufL. cbn [Z.of_nat]. destruct Hdisj as [Hd|Hd]; lia.
    - exact (x12_stk_rel m (normalize rsegs m) lo (bv_unsigned sp) REL Hlo2 Hspa HST).
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact (x12_ac_rel m (normalize rsegs m) REL HAC).
    - exact (x12_sw_rel m (normalize rsegs m) REL HSW).
    - exact (bytes_at_normalize rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) HRO HRM). }
  intros ms' (s0' & HP & HMS & HRS).
  destruct HP as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
              & m0' & E & MU0 & WM0 & MI0 & ST0 & AC0 & SW0 & HB0).
  subst s0'.
  destruct HMS as (HRg & HFg & HPc & HSvc & HRes & HFc & HRom & HMR).
  destruct ms' as [regs2 fregs2 pc2 svc2 resv2 fcsr2 mem2 rom2].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HRg, HFg, HPc, HSvc, HRes, HFc, HRom, HMR, HRS.
  subst regs2 fregs2 pc2 svc2 resv2 fcsr2 rom2.
  rewrite EP, E0, E17, Zmod_0_l, HRES.
  replace (ret_pc (Z_to_bv 64 0x82b20)) with (Z_to_bv 64 0x82b20)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply LE.evt_done. cbv beta.
  exists (Z_to_bv 64 0x82b20), a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'',
         mem2.
  split; [reflexivity|].
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) mem2 m0' REL HMR HRS MU0)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mem2 m0' REL HMR HRS WM0)|].
  split; [exact HRS|].
  split; [exact (x12_stk_rel_back mem2 m0' lo (bv_unsigned sp) HMR Hlo2 Hspa ST0)|].
  split; [exact (x12_ac_rel_back mem2 m0' HMR AC0) | exact (x12_sw_rel_back mem2 m0' HMR SW0)].
Qed.

(* The pin: x12_a_evt_of_pre_post states X12.v's x12_a_evt term for term (constr_eq: syntactic). *)
Lemma x12_a_evt_of_pre_post_verbatim : True.
Proof.
  let A := type of SX12.x12_a_evt in let B := type of x12_a_evt_of_pre_post in constr_eq A B; exact I.
Qed.
