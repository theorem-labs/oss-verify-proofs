(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 528 of its 563 lines of code are new or changed and 361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P7.v, with its module paths and module names changed; 28 of its 121 lines of code are new or changed and 470 lines of the source are left out. *)
(* lib/A/Prog/Seg/P7F_on.v -- route (C): the region form of Seg/P7F.v's (not in this delivery) p7_evt_F, for the image-A glue stage
   seg_P7 (lib/A/ACtlG/P7.v).  Written by a Theorem Labs lane under a Theorem Labs lane's standing consent (12:55Z,
   relayed by a Theorem Labs lane) for beside-files <S>F_on.v; Seg/P7F.v itself (not in this delivery) is byte-identical.  rule 24: no function
   proved.

   SOURCE.  Seg/P7F.v (not in this delivery) at a Theorem Labs lane's fold a working branch 4bae33fdf54 (blob 74cf5675377): the
   lemma p7_evt_F, its statement and its proof, with exactly these changes:
   - the callee premise HFRAGF : reac_ctrl_identity_fragment_contract_F becomes
     HFRAGF_on : reac_ctrl_identity_fragment_contract_F_on (lib/A/Prog/reac_ctrl_identity_fragment_c.v, a Theorem Labs lane
     4777545c654 blob 0359af7161a; proved closed by a Theorem Labs lane's
     reac_ctrl_identity_fragment_F_on.reac_ctrl_identity_fragment_F_holds_on_closed, 6db4ffd630a);
   - the premise `shadow_rw m` is DROPPED (with its intro HSW, its normalized copy HSWn and their clear): the run
     reads and stores no shadow byte itself, and its one use was the callee's shadow premise.  The narrowed callee
     premise is shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g); its region starts with
     `fr <> 0`, and the run calls with fr = 0 (li a1,0), so the region is EMPTY and the premise holds vacuously (one
     added tactic line in the callee step).
   The callee's post now carries `forall P, shadow_rw_on P m -> shadow_rw_on P m'` in place of `shadow_rw m'`; the
   run's post never used it (the destruct pattern drops it as before).  The post of p7_evt_F_on is unchanged.  The
   corollary p7_evt_of_F and the pin p7_evt_of_F_verbatim stay in Seg/P7F.v (they state the old form). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 P1 P7.
(* The evtF form of MemNorm.evt_normalize; not imported, so its helper names shadow nothing here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last: StepF's step / if_true / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

Section CallFOn.
(* The callee's footprint contract in its region form, in the position of P7F.v's Section Hypothesis HFRAGF. *)
Hypothesis HFRAGF_on : reac_ctrl_identity_fragment_contract_F_on.

Lemma p7_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> 0 <= f < 2 ^ 64 ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 f)) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    ro_agree rsegs m -> asan_cells m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    ExecF.rng RNG (A + 192) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s2' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c20) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81c20) fc None m' (seg_rom rsegs) /\
         s2' = Z_to_bv 64 (-1) /\
         munch [(bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bf8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f -> -> Hf H208 Hal HST HRO HAC Hlo Hhi HRB HRM HGC HC254 HC255 R192 RBY RIMG RFR RFRS.
  assert (HL208 : ov_read_bytes rsegs m (wa (A + 192)) 8 = Some (le8 (Z_to_bv 64 f))).
  { pose proof (bytes_at_ov_read rsegs m (A + 192) (le8 (Z_to_bv 64 f)) 0 8 H208
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. (* 81bf8 li s2,-1 *)
  step. (* 81bfc beq a0,s2,81c04 *)
  if_true.
  step. (* 81c04 ld a0,192(s1) *)
  step. step. step. step. step. (* li a1,0; li a2,0; mv a3,s7; mv a4,s8; mv a5,s4 *)
  step. (* 81c1c jal reac_ctrl_identity_fragment *)
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  eapply ExecF.evtF_mono.
  { eapply MNF.evtF_normalize_ro; [exact HRO|].
    pose proof HFRAGF_on as HF.
    unfold reac_ctrl_identity_fragment_contract_F_on, REAC_CTRL_IDENTITY_FRAGMENT in HF.
    assert (HSTn : stk rsegs (normalize rsegs m) (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)).
    { apply (stk_rel_hi m (normalize rsegs m));
        [exact REL | unfold HIGHMEM_BEG in Hlo; lia | pose proof (u64_range sp) as Hu; lia | exact HST]. }
    assert (HACn : asan_cells (normalize rsegs m)) by exact (asan_cells_rel m (normalize rsegs m) REL HAC).
    pose proof (mem_inv_normalize rsegs m) as HMIn.
    assert (HRBn : bytes_at rsegs (normalize rsegs m) REAL_BCMP (le8 (wa BCMP)))
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HRB).
    assert (HRMn : bytes_at rsegs (normalize rsegs m) REAL_MEMCMP (le8 (wa MEMCMP)))
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HRM).
    assert (HGCn : bytes_at rsegs (normalize rsegs m) GOT_CF (le8 (wa CF)))
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HGC).
    assert (HC254n : bytes_at rsegs (normalize rsegs m) (CF + 254) [Z_to_bv 8 1])
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HC254).
    assert (HC255n : bytes_at rsegs (normalize rsegs m) (CF + 255) [Z_to_bv 8 1])
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HC255).
    (* Only the normalized copies may meet the assumption sweep below: matching a goal on normalize rsegs m
       against a hypothesis on m makes the unifier unfold normalize / ro_addr / rsegs. The rng premises are
       memory-free, so they stay. *)
    clear HST HAC HRB HRM HGC HC254 HC255 H208 HL208 HRO REL.
    eapply ExecF.evtF_cut.
    { eapply HF with (f := f) (fr := 0) (len := 0) (pa := bv_unsigned s7) (pp := bv_unsigned s8)
        (pn := bv_unsigned s4) (st := repeat (Z_to_bv 8 0) 72) (g := repeat (Z_to_bv 8 0) 50).
      all: try (symmetry; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.Z_to_bv_bv_unsigned).
      all: try reflexivity.
      all: try assumption.
      all: try (intros _ HH; exfalso; apply HH; reflexivity).
      (* route (C): the callee's shadow region is empty at fr = 0 (its second conjunct is fr <> 0) *)
      all: try (intros ? (_ & HH & _); exfalso; apply HH; reflexivity).
      all: try exact (u64_range _).
      all: lia. }
    intros ms0 Hpost. apply ExecF.evtF_done. exact Hpost. }
  { intros ms' (sn & HCP & HREL & HROS).
    destruct HCP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'0 &
      Esn & MUn & WMn & _ & STn & _ & _ & _).
    rewrite fg_refuse0 in Esn, MUn. cbn [fg_fp] in MUn. change (fg_ret FgRefuse) with (-1) in Esn.
    subst sn.
    destruct ms' as [R' F' pc' svc' rv' fc' mm' rom'].
    destruct HREL as (HRr & HRf & HRpc & HRsvc & HRrv & HRfc & HRrom & HRmem).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in
      HRr, HRf, HRpc, HRsvc, HRrv, HRfc, HRrom, HRmem, HROS.
    subst R' F' pc' svc' rv' fc' rom'.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (Z_to_bv 64 (-1)), mm'.
    split.
    { replace (ret_pc (Z_to_bv 64 531488)) with (Z_to_bv 64 531488)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      reflexivity. }
    split; [reflexivity|].
    split; [exact (munch_rel rsegs [(bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]
                     m (normalize rsegs m) mm' m'0 REL HRmem HROS MUn)|].
    split; [exact (wmono_rel rsegs m (normalize rsegs m) mm' m'0 REL HRmem HROS WMn)|].
    apply (stk_rel_hi_back mm' m'0);
      [exact HRmem | unfold HIGHMEM_BEG in Hlo; lia | pose proof (u64_range sp) as Hu; lia | exact STn]. }
Qed.

End CallFOn.
