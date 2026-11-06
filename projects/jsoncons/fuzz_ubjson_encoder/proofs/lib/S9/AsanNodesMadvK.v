(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes AsanAcctShape Scfg KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanNodesLibEK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Madv.
Context {fxg : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.

Lemma madvise_check : forall ms x8 model eff,
  bv_unsigned x8 = 233 ->
  check_syscall (sys_input segs ms x8) eff model
  = Madvise.check_madvise (ms_gpr ms 0) (ms_gpr ms 1) (int32 (ms_gpr ms 2)) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma srz_madvise_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 233 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z -> (len mod 4096 = 0)%Z -> (bv_unsigned a + len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 4 ->
  madvise_dontneed_ok (m_vmmaps model) a (Z_to_bv 64 len) = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill a (Z_to_bv 64 len) mem) rom)
                      (madvise_dontneed_next model a (Z_to_bv 64 len))) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hll Hend H12 Hok Hc.
  pose proof (u64_range a) as Hra.
  assert (Hlen' : (len < 2 ^ 64)%Z) by lia.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 233%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (unfold ms; rewrite ms_gpr_epend1, H11; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (H2 : int32 (ms_gpr ms 2) = Z_to_bv 64 4) by (unfold ms; rewrite ms_gpr_epend2, H12; vm_compute; reflexivity).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  assert (Hchk : forall eff, check_syscall (sys_input segs ms (getr regs 17)) eff model
                 = match eff with
                   | mkEffectU r [] zs [] [] [] =>
                       if (w_is0 r && listNN_eqb zs [(a, Z_to_bv 64 len)])%bool
                       then CheckOk (madvise_dontneed_next model a (Z_to_bv 64 len)) [] else CheckReject
                   | _ => CheckReject
                   end).
  { intros eff. rewrite (madvise_check ms (getr regs 17) model eff Hno). unfold Madvise.check_madvise.
    rewrite H0, H2, Hu1, Hpr.
    replace (bv_unsigned a mod page_size =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hal).
    cbn [negb]. change (madvise_dontneed_b (Z_to_bv 64 4)) with true. cbn [negb].
    replace (w_is0 (ms_gpr ms 1)) with false.
    2:{ symmetry. unfold w_is0. apply bv_eqb_neq. intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
    replace (two_pow_64 <=? bv_unsigned a + len)%Z with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    rewrite Hok. reflexivity. }
  eapply (srz_det_noacc segs scfg ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [(a, Z_to_bv 64 len)] [] [] [])
            (madvise_dontneed_next model a (Z_to_bv 64 len)));
    [exact Hh | reflexivity | rewrite Hno; reflexivity | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb zs [(a, Z_to_bv 64 len)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. cbn [andb] in Hck. injection Hck as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
    + intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct us; [destruct cs; [destruct ci; [|discriminate]|discriminate]|discriminate].
    destruct (w_is0 r && listNN_eqb zs _)%bool; discriminate.
  - exact Hh.
  - unfold ms. rewrite adv_zeros1_epend. exact Hc.
Qed.
End Madv.
