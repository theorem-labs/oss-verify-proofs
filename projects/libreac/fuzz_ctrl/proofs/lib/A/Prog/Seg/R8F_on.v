(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 877 of its 987 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R8.v, with its module paths, addresses and numbers changed; 132 of its 168 lines of code are new or changed and 951 lines of the source are left out. *)
(* lib/A/Prog/Seg/R8F_on.v -- route (C) twin of Seg/R8F.v's (not in this delivery) r8_evt_F (fuzz_ctrl image A, segment R8 = 0x81640 ->
   0x81658, the call of checked_memcpy at 0x81654).  Written by a Theorem Labs lane for the stage glue ACtlG/R8.v,
   with the standing consent of R8F.v's (not in this delivery) owner a Theorem Labs lane (12:55Z, relayed by a Theorem Labs lane).  R8F.v (not in this delivery) is unchanged
   (blob ca7f11f02ca, a Theorem Labs lane's fold a working branch 4bae33fdf54).
   rule 24: no function proved (a mechanical re-run of an already-proved segment run).

   r8_evt_F_on is r8_evt_F (R8F.v:62) with the wave's route (C) changes (L3-recipe.md, WORKLIST.tsv:376 "additive
   r8_evt_F_on; post form: forall P, shadow_rw_on P m -> shadow_rw_on P m'"), and nothing else:
     - the callee premise asan_memcpy_contract_F becomes a Theorem Labs lane's asan_memcpy_contract_F_on (asan_memcpy_cF_on.v,
       proved by asan_memcpyF_on.v asan_memcpy_holds_F_on);
     - the premise `shadow_rw m` becomes `shadow_rw_on (r8_evt_shadow_R S phi N) m`: r8_evt_shadow_R is the callee's
       region asan_memcpy_shadow_R a0 a1 a2 at the call (a0 = phi, a1 = S loaded from [A + 128], a2 = s2 = N), i.e.
       the contiguous aligned shadow-word spans of the source [S, S + N) and of the destination [phi, phi + N).  The
       segment's own instructions (bnez, mv, ld, mv, jal) read and write no shadow byte;
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (the callee's post at
       P, carried through the normalization by ShadowRwOnT.shadow_rw_on_normalize / shadow_rw_on_of_rel).
   Every other binder, premise (the footprint ones included) and post conjunct is r8_evt_F's, in the same order. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require BzBridge KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R8.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF_on.
(* Last: StepF's step / if_true_by (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module MCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SROT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Module MCO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c_on.
Module MCFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF_on.

(* R8F.v's r8_accF (R8F.v:49-59), verbatim. *)
Ltac r8_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?LMS.unsigned_lit_wrap; Z.div_mod_to_equations; lia
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= r8_accF.

(* The shadow the run reads through its shadow premise: the callee's asan_memcpy_shadow_R at the call, over Z. *)
Definition r8_evt_shadow_R (S phi N : Z) (a : Z) : Prop :=
  SWO.sh_word_on S N a \/ SWO.sh_word_on phi N a.

(* ---- the run 0x81640 -> 0x81654 (the call) -> 0x81658 under a footprint RNG, route (C) ---- *)
Lemma r8_evt_F_on : forall (RNG : ExecF.footprint),
  MCFO.asan_memcpy_contract_F_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S N phi lo : Z) (src junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N ->
    0 < phi < 2 ^ 64 -> phi + N <= 2 ^ 64 -> 0 <= A < 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 <= N -> 0 <= spv < 2 ^ 64 ->
    ro_cells rsegs m (A + 128) [C8 (Z_to_bv 64 S)] ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    (phi = S \/ S + N <= phi \/ phi + N <= S) ->
    N <= 2 ^ 40 ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    (N = 0 \/ app_mem (S + 7) /\ app_mem (phi + 7)) ->
    (phi + N <= RT_LO \/ RT_HI <= phi) ->
    (phi + N <= spv - MCC.ASAN_MEMCPY_K \/ spv <= phi) -> (S + N <= spv - MCC.ASAN_MEMCPY_K \/ spv <= S) ->
    stk rsegs m lo spv -> lo + MCC.ASAN_MEMCPY_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (r8_evt_shadow_R S phi N) m -> ro_agree rsegs m ->
    (forall i, 0 <= i < N -> ro_addr rsegs (wa (phi + i)) = false) ->
    (* the segment's own access: the 8-byte load of the source pointer at [A + 128, A + 136) *)
    ExecF.rng RNG (A + 128) 8 ->
    (* the callee's regions (asan_memcpy_contract_F_on's footprint premises), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - MCC.ASAN_MEMCPY_K) MCC.ASAN_MEMCPY_K ->
    ExecF.rng RNG phi N -> ExecF.rng RNG S N ->
    sh_word_rng RNG phi N -> sh_word_rng RNG S N ->
    sh_word_rng RNG (spv - MCC.ASAN_MEMCPY_K) MCC.ASAN_MEMCPY_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81658) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 phi /\ getr R 24 = Z_to_bv 64 phi /\ getr R 18 = Z_to_bv 64 N /\
         munch [(phi, phi + N); (spv - MCC.ASAN_MEMCPY_K, spv)] m m' /\ wmono rsegs m m' /\
         ro_agree rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P : Z -> Prop, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P m') /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81640) fc None m (seg_rom rsegs)).
Proof.
  intros RNG MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S N phi lo src junk -> -> -> -> Hphi0 HphiN HA HS HN Hspv
    RO HbS HLsrc RWd HAL HNb AS AD ES ED APP HRT HSEPd HSEPs ST HLO HHM HAE HAC HSW HRO HROphi
    Rld Rby Rimg Rstk RngD RngS RngDs RngSs RngKs.
  unfold MCFO.asan_memcpy_contract_F_on in MCPY.
  (* the spill slot does not wrap: solve_accs needs it for the load at s1 + 128 *)
  pose proof (ro_cells_bound rsegs m (A + 128) _ RO) as HBnd.
  cbn [cells_size csize Nat.add] in HBnd.
  assert (HHMv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  (* the call's premises on the normalized memory *)
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HbS0 : bytes_at rsegs (normalize rsegs m) S src) by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HbS).
  assert (RWd0 : rw_cells rsegs (normalize rsegs m) phi [CB (Z.to_nat N) junk]).
  { apply (R8.r8_rel_rwcb m _ phi (Z.to_nat N) junk REL); [|exact RWd]. intros i Hi. apply HROphi. lia. }
  assert (AS0 : addressable (normalize rsegs m) S N) by exact (proj1 (R8.r8_rel_ad m _ _ _ REL) AS).
  assert (AD0 : addressable (normalize rsegs m) phi N) by exact (proj1 (R8.r8_rel_ad m _ _ _ REL) AD).
  assert (ST0 : stk rsegs (normalize rsegs m) lo spv)
    by exact (proj1 (R8.r8_rel_stk m _ lo spv REL ltac:(lia) ltac:(lia)) ST).
  assert (HAC0 : asan_cells (normalize rsegs m)) by exact (proj1 (R8.r8_rel_cells m _ REL) HAC).
  assert (HSW0 : SRO.shadow_rw_on (r8_evt_shadow_R S phi N) (normalize rsegs m))
    by exact (SROT.shadow_rw_on_normalize _ m HRO HSW).
  step. if_true_by (R8.r8_neqb0 phi ltac:(lia)).
  step. step. step. step.
  eapply ExecF.evtF_cut.
  { eapply MNF.evtF_normalize_ro; [exact HRO|].
    eapply MCPY with (RNG := RNG) (src := src) (junk := junk) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HbS0.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HLsrc.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RWd0.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAL.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HNb.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact AS0.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact AD0.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ES.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ED.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact APP.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HRT.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSEPd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSEPs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ST0.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact HAC0.
    - (* the callee's region at the call is r8_evt_shadow_R S phi N *)
      unfold MCO.asan_memcpy_shadow_R.
      rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSW0.
    - exact (mem_inv_normalize rsegs m).
    - exact Rby.
    - exact Rimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Rstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngD.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngS.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngDs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngSs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngKs. }
  intros ms' (s0' & PO & HREL & HROS). unfold MCO.asan_memcpy_post_on in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & RWc & HBc & AC' & SW').
  subst s0'.
  destruct HREL as (ER & EF & EP & Esv & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, Esv, EV, EC, ERo,
    HMR.
  pose proof (R8.r8_ms_eta ms' Esv) as Ems.
  rewrite ER, EF, EP, EC, EV, ERo in Ems.
  rewrite Ems.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (ESv : bv_unsigned (Z_to_bv 64 S) = S) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  rewrite Ephi in MU, RWc. rewrite EN in MU, RWc. rewrite Esp in MU, STc. rewrite ESv in HBc.
  replace (ret_pc (Z_to_bv 64 0x81658)) with (Z_to_bv 64 0x81658)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  (* the post on the real memory *)
  split; [exact (munch_rel rsegs _ m _ _ m' REL HMR HROS MU)|].
  split; [exact (wmono_rel rsegs m _ _ m' REL HMR HROS WM)|].
  split; [exact (ro_agree_same rsegs m _ HRO HROS)|].
  split; [exact (proj2 (R8.r8_rel_stk _ m' lo spv HMR ltac:(lia) ltac:(lia)) STc)|].
  split; [exact (proj2 (R8.r8_rel_cells _ m' HMR) AC')|].
  split.
  { (* any region held before the call is held after it: the callee's post, across the normalization *)
    intros P HP. exact (SROT.shadow_rw_on_of_rel P _ m' HMR (SW' P (SROT.shadow_rw_on_normalize P m HRO HP))). }
  split; [exact (R8.r8_rel_rwcb_back _ m' phi _ src HMR RWc)
         | exact (proj2 (bytes_at_rel rsegs _ m' _ _ HMR) HBc)].
Qed.
