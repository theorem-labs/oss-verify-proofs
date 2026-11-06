(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 554 of its 653 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P4.v; 138 of its 266 lines of code are new or changed and 525 lines of the source are left out. *)
(* PROVENANCE. Image A = fuzz_ctrl.asan, libreac v1.9.0 (the binary of Seg/P4F.v's header). Route (C) twin of
   Seg/P4F.v (an earlier version, blob f0603ec57bb, not in this delivery) (UNCHANGED; this file only adds), written by a Theorem Labs lane (slice P4).

   Sources: Seg/P4F.v (an earlier version, blob f0603ec57bb, not in this delivery) (p4_evt_F, p4_evt_of_F, p4_evt_ro_F, p4_evt_ro_of_F and their scripts);
   a Theorem Labs lane's Seg/P4.v (an earlier version, blob 1a1be5f1321, not in this delivery) (p4_evt_shadow_R :89, p4_evt_on :91, p4_evt_ro_shadow_R :341,
   p4_evt_ro_on :344); a Theorem Labs lane's lib/A/Prog/asan_memset_cF_on.v 6137e3c5f10 (the blob this tree had at release c5e779efe8c) (asan_memset_contract_F_on, proved
   by asan_memsetF_on.v blob 34752af7b24 asan_memset_holds_F_on).
   rule 24: no function proved

   WHAT CHANGED, AND WHY. Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the walk's cut no longer carries the
   universal `shadow_rw m` (a Theorem Labs lane's truth audit found it false at an AR state); it carries shadow_rw_on of the cut's
   own regions. So the run the glue stage lifts must take the shadow it reads as a REGION. Each lemma below is its
   P4F.v original with exactly these changes:
     - the callee premise asan_memset_contract_F becomes a Theorem Labs lane's asan_memset_contract_F_on;
     - p4_evt_F_on: the premise `shadow_rw m` becomes `A.ShadowRwOn.shadow_rw_on (P4.p4_evt_shadow_R D) m` (a Theorem Labs lane's
       region: the memset's asan_memset_shadow_R at the call, a0 = D, a2 = 72), and the post's `shadow_rw m'`
       becomes `forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'` (asan_memset_post_on's
       last conjunct). Every other binder, premise (footprint ones included) and post conjunct is p4_evt_F's.
     - p4_evt_ro_F_on: the premise `shadow_rw m` becomes `A.ShadowRwOn.shadow_rw_on (P4.p4_evt_ro_shadow_R D) m`;
       its POST is p4_evt_ro_F's, character for character (it has no shadow conjunct). In the proof the region is
       moved to the normalized memory by A.ShadowRwOnT.shadow_rw_on_rel, in the place of P4.p4_shadow_rw_norm
       (as a Theorem Labs lane's P4.p4_evt_ro_on does).
   Compare (P4F.v's own style; P4F.v is not in this delivery): p4_evt_of_F_on / p4_evt_ro_of_F_on re-derive a Theorem Labs lane's P4.p4_evt_on / P4.p4_evt_ro_on at
   ExecF.RNG_all, and the two Examples check by constr_eq that their types are those of P4.p4_evt_on /
   P4.p4_evt_ro_on (premise asan_memset_contract_on there, asan_memset_contract_F_on here). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c asan_memset_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_memset_c_on asan_memset_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.
(* a Theorem Labs lane's regions p4_evt_shadow_R / p4_evt_ro_shadow_R and the _on runs the Examples compare against *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P4.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* ---- p4_evt_F (P4F.v:35) with the region premise: P4.p4_evt_on (P4.v:91) under a footprint RNG. ---- *)
Lemma p4_evt_F_on : asan_memset_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m D [CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (P4.p4_evt_shadow_R D) m -> mem_inv rsegs m ->
    (* the segment's own access: the spill load [A + 192, A + 200) *)
    ExecF.rng RNG (A + 192) 8 ->
    (* the callee's regions (asan_memset_contract_F_on's rng premises at this call site), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG D 72 ->
    sh_word_rng RNG D 72 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         rw_cells rsegs m' D [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk -> -> HA HD Hspv HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HMI
    G192 Gby Gimg Gstk Gd Gshd Gshs.
  unfold asan_memset_contract_F_on in MSET. cbv zeta in MSET.
  step. step. step. step.
  eapply ExecF.evtF_cut.
  { eapply MSET with (RNG := RNG) (junk := junk) (lo := lo).
    - rewrite !MState.unsigned_lit by lia. exact RW.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact HAD.
    - rewrite !MState.unsigned_lit by lia. exact HE.
    - rewrite !MState.unsigned_lit by lia. right. exact HA7.
    - rewrite !MState.unsigned_lit by lia. exact HRT.
    - rewrite !MState.unsigned_lit by lia. exact HSEP.
    - rewrite !MState.unsigned_lit by lia. exact ST.
    - rewrite !MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !MState.unsigned_lit by lia. exact HAE.
    - exact HAC.
    - exact HSW.
    - exact HMI.
    - exact Gby.
    - exact Gimg.
    - rewrite !MState.unsigned_lit by lia. exact Gstk.
    - rewrite !MState.unsigned_lit by lia. exact Gd.
    - rewrite !MState.unsigned_lit by lia. exact Gshd.
    - rewrite !MState.unsigned_lit by lia. exact Gshs. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & RWc & HAC' & HSW').
  subst ms'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply MState.unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite ED in MUc, RWc. rewrite E72 in MUc, RWc. rewrite Esp in MUc, STc.
  fold_lit_ux_in RWc.
  replace (ret_pc (Z_to_bv 64 0x81b90)) with (Z_to_bv 64 0x81b90)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact MIc|].
  split; [exact STc|]. split; [exact HAC'|]. split; [exact HSW' | exact RWc].
Qed.

(* a Theorem Labs lane's P4.p4_evt_on's conclusion under the footprint contract: p4_evt_F_on at ExecF.RNG_all. *)
Lemma p4_evt_of_F_on : asan_memset_contract_F_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m D [CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (P4.p4_evt_shadow_R D) m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         rw_cells rsegs m' D [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk E1 E2 HA HD Hspv HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HMI.
  pose proof (rw_cells_bound rsegs m (A + 192) [C8 (Z_to_bv 64 D)] HLD) as HB192.
  cbn [cells_size csize Nat.add] in HB192.
  pose proof HAD as (HAD0 & HAD1 & HAD2 & _).
  pose proof ST as (HST0 & HST1 & _).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p4_evt_F_on MSET ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 F fc m spv A D lo junk E1 E2 HA HD Hspv HLD RW HAD HE HA7 HRT HSEP
           ST HLO HHM HAE HAC HSW HMI).
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG in *; lia.
  - unfold APPMEM_END in HAD2. apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

(* ---- p4_evt_ro_F (P4F.v:164) with the region premise: p4_evt_F_on on the normalized memory, moved back by
   MemNormF.evtF_normalize_ro.  From here on `getr` is YK11's, as it is in P4.v from its second import block on. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P4.
Import YK11.
Open Scope Z_scope.

Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

Lemma p4_evt_ro_F_on : asan_memset_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    0x5fe000 <= A -> 0x5fe000 <= D ->
    LStep.rw_cells rsegs m (A + 192) [LCells.C8 (Z_to_bv 64 D)] ->
    LStep.rw_cells rsegs m D [LCells.CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (P4.p4_evt_ro_shadow_R D) m -> MemNorm.ro_agree rsegs m ->
    ExecF.rng RNG (A + 192) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG D 72 ->
    sh_word_rng RNG D 72 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         LFr.munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ LFr.wmono rsegs m m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         LStep.rw_cells rsegs m' D [LCells.CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (LFr.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk E1 E2 HA HD Hspv HAg HDg HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HRO
    G192 Gby Gimg Gstk Gd Gshd Gshs.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  eapply ExecF.evtF_mono.
  - eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    apply (p4_evt_F_on MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6 F fc (MemNorm.normalize rsegs m) spv A D lo junk E1 E2 HA HD Hspv).
    + exact (P4.p4_rw_cells_rel m _ (A + 192) _ REL ltac:(lia) HLD).
    + exact (P4.p4_rw_cells_rel m _ D _ REL ltac:(lia) RW).
    + exact (P4.p4_addressable_rel m _ _ _ REL HAD).
    + exact HE.
    + exact HA7.
    + exact HRT.
    + exact HSEP.
    + exact (P4.p4_stk_rel m _ lo spv REL ltac:(lia) ltac:(lia) ST).
    + exact HLO.
    + exact HHM.
    + exact HAE.
    + exact (P4.p4_cells_norm m _ REL HAC).
    + exact (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
    + exact G192.
    + exact Gby.
    + exact Gimg.
    + exact Gstk.
    + exact Gd.
    + exact Gshd.
    + exact Gshs.
  - intros s (s0' & (R & m0' & -> & P2 & P3 & P4' & P8 & P9 & P19 & P26 & P22 & P25 & MU0 & WM0 & _ & ST0 & _ & _
              & RW0)
              & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4'|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (P4.p4_stk_rel_back ms m0' lo spv Hmem ltac:(lia) ltac:(lia) ST0)|].
    exact (P4.p4_rw_cells_back ms m0' _ _ Hmem RW0).
Qed.

(* a Theorem Labs lane's P4.p4_evt_ro_on's conclusion under the footprint contract, by p4_evt_ro_F_on at ExecF.RNG_all. *)
Lemma p4_evt_ro_of_F_on : asan_memset_contract_F_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    0x5fe000 <= A -> 0x5fe000 <= D ->
    LStep.rw_cells rsegs m (A + 192) [LCells.C8 (Z_to_bv 64 D)] ->
    LStep.rw_cells rsegs m D [LCells.CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (P4.p4_evt_ro_shadow_R D) m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         LFr.munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ LFr.wmono rsegs m m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         LStep.rw_cells rsegs m' D [LCells.CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (LFr.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk E1 E2 HA HD Hspv HAg HDg HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof (rw_cells_bound rsegs m (A + 192) [LCells.C8 (Z_to_bv 64 D)] HLD) as HB192.
  cbn [cells_size csize Nat.add] in HB192.
  pose proof HAD as (HAD0 & HAD1 & HAD2 & _).
  pose proof ST as (HST0 & HST1 & _).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p4_evt_ro_F_on MSET ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
           s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv A D lo junk E1 E2 HA HD Hspv HAg HDg HLD RW HAD HE HA7 HRT HSEP
           ST HLO HHM HAE HAC HSW HRO).
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG in *; lia.
  - unfold APPMEM_END in HAD2. apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

Example p4_evt_ro_of_F_on_verbatim : True.
Proof.
  lazymatch type of P4.p4_evt_ro_on with ?P -> ?A =>
    constr_eq P asan_memset_contract_on;
    lazymatch type of p4_evt_ro_of_F_on with ?Q -> ?B =>
      constr_eq Q asan_memset_contract_F_on; constr_eq A B
    end
  end.
  exact I.
Qed.
Example p4_evt_of_F_on_verbatim : True.
Proof.
  lazymatch type of P4.p4_evt_on with ?P -> ?A =>
    constr_eq P asan_memset_contract_on;
    lazymatch type of p4_evt_of_F_on with ?Q -> ?B =>
      constr_eq Q asan_memset_contract_F_on; constr_eq A B
    end
  end.
  exact I.
Qed.
