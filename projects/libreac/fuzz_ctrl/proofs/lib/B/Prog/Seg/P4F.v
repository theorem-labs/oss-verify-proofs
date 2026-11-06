(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its addresses and numbers changed; 55 of its 127 lines of code are new or changed and 858 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P4.v p4_evt at a working branch 3803efccea0
     (blob 08a43f8a230603ec3391d0739adeed701d433325);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p4_evt_of_F composes p4_pre_F, the caller's asan_memset_contract premise and p4_post_F and
     re-derives the source statement of P4.p4_evt verbatim; p4_evt_same checks that type against P4.p4_evt.
     p4_pre_F re-runs P4.v line 65 (0x81d18 .. 0x81d24, up to the callee entry), p4_post_F lines 83-100
     (the return pc 0x81d28, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P4's run [0x81d18, 0x81d28), split at the call (parent ruling: every call splits):
     li a2,72; ld a0,208(s1); li a1,0; jal checked_memset -> p4_pre_F, stops AT the callee entry 0x52600
     with ra = 0x81d28.  The one access of the stretch is the fragment-scratch pointer [Ab + 208, Ab + 216),
     with no instrumented check; the 72 zero bytes at fg and the callee window [spv - 2208, spv) are the
     callee's own footprint and appear only in p4_post_F's premises. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P4.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module MSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset_c.

(* ---- 0x81d18 .. 0x81d24: li a2,72; ld a0,208(s1); li a1,0; jal checked_memset ---- *)
Lemma p4_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab fg : Z),
    s1 = Z_to_bv 64 Ab ->
    0 <= Ab -> Ab + 248 <= 2 ^ 64 -> 0 <= fg < 2 ^ 64 ->
    ro_cells rsegs m (Ab + 208) [C8 (Z_to_bv 64 fg)] ->
    rng RNG (Ab + 208) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81d28) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                                (Z_to_bv 64 fg) (Z_to_bv 64 0) (Z_to_bv 64 72) a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x52600) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d18) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab fg -> HA0 HA64 Hfg RO G208.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- the return pc 0x81d28: the premises are the callee post facts P4's proof uses ---- *)
Lemma p4_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word) (spv fg lo : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 26 = s10 -> getr R 24 = s8 -> getr R 23 = s7 -> getr R 25 = s9 ->
    munch [(fg, fg + 72); (spv - 2208, spv)] m m' -> wmono rsegs m m' ->
    mem_inv rsegs m' -> stk rsegs m' lo spv -> asan_cells m' -> shadow_rw m' ->
    rw_cells rsegs m' fg [CB 72 (repeat (Z_to_bv 8 0) 72)] ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81d28) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 26 = s10 /\ getr R' 24 = s8 /\ getr R' 23 = s7 /\ getr R' 25 = s9 /\
         munch [(fg, fg + 72); (spv - 2208, spv)] m m'' /\ wmono rsegs m m'' /\
         mem_inv rsegs m'' /\ stk rsegs m'' lo spv /\ asan_cells m'' /\ shadow_rw m'' /\
         rw_cells rsegs m'' fg [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS R F (Z_to_bv 64 0x81d28) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s7 s8 s9 s10 spv fg lo
    K2 K3 K4 K8 K9 K19 K26 K24 K23 K25 MU WM MI ST HAC HSW RW.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K26|]. split; [exact K24|]. split; [exact K23|]. split; [exact K25|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact HAC|]. split; [exact HSW | exact RW].
Qed.

(* ---- the compare lemma: the source statement of P4.p4_evt ---- *)
Lemma p4_evt_of_F : MSC.asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Ab fg lo : Z) (fgb : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 Ab ->
    HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    0 <= Ab -> Ab + 248 <= 2 ^ 64 ->
    RT_HI <= fg -> app_mem (fg + 7) -> app_mem (fg + 72) ->
    (fg + 72 <= spv - 2208 \/ spv <= fg) ->
    rw_cells rsegs m fg [CB 72 fgb] -> ro_cells rsegs m (Ab + 208) [C8 (Z_to_bv 64 fg)] ->
    addressable m fg 72 ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81d28) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = s8 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(fg, fg + 72); (spv - 2208, spv)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' fg [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d18) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Ab fg lo fgb -> -> HHM HLO HAE HA0 HA64 Hfrt Hf7 Hf72 Hsep RW RO ADR HMI ST HAC HSW.
  unfold MSC.asan_memset_contract, MSC.ASAN_MEMSET_K, MSC.ASAN_MEMSET in MSET. cbv zeta in MSET.
  pose proof (rw_cells_bound rsegs m fg _ RW) as Hfb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hfb.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 fg) = fg) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p4_pre_F with (Ab := Ab) (fg := fg); try assumption; try reflexivity; try lia.
    apply rng_all; lia. }
  intros ms' ->.
  eapply evt_cut.
  { eapply MSET with (junk := fgb) (lo := lo).
    all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 72)) with 72.
    - exact RW.
    - lia.
    - exact ADR.
    - unfold end_in_app. right. exact Hf72.
    - right. exact Hf7.
    - right. unfold RT_HI. lia.
    - lia.
    - exact ST.
    - lia.
    - unfold HIGHMEM_BEG. lia.
    - unfold APPMEM_END. lia.
    - exact HAC.
    - exact HSW.
    - exact HMI. }
  intros ms' PO. unfold MSC.asan_memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & ST2 & RW2 & AC2 & SW2).
  subst ms'.
  unfold MSC.ASAN_MEMSET_K in MU2.
  rewrite EU1, EU2 in MU2. rewrite EU2 in ST2. rewrite EU1 in RW2.
  change (bv_unsigned (Z_to_bv 64 72)) with 72 in MU2, RW2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in RW2.
  change (Z.to_nat 72) with 72%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  replace (ret_pc (Z_to_bv 64 0x81d28)) with (Z_to_bv 64 0x81d28)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p4_post_F with (m := m) (spv := spv) (fg := fg) (lo := lo); try reflexivity; assumption.
Qed.

(* p4_evt_of_F has exactly the statement of the source lemma P4.p4_evt. *)
Definition p4_evt_same : ltac:(let T := type of P4.p4_evt in exact T) := p4_evt_of_F.
