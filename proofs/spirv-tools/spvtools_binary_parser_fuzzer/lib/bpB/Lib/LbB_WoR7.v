(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BSymTac.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_FS6_RA : Z := 0xec3d8.
Definition WO_RET : Z := 0xec428.

Lemma vlw_small : forall r, -2 ^ 31 <= r < 2 ^ 31 -> v_lw (Z_to_bv 64 r) = Z_to_bv 64 r.
Proof.
  intros r Hr. unfold v_lw. rewrite Z_to_bv_unsigned. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

Section WoR7.
  Context {HCEIL : HeapCeil}.

  Lemma we2 : forall (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (gp tp s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 : word) (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP r : Z),
    2 ^ 45 <= SP -> SP <= 2 ^ 47 -> -2 ^ 31 <= r < 2 ^ 31 ->
    rw_cells asegs m (SP - 104) [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'] ->
    exists R',
      CatSim.msteps asegs
        (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SP) s1 x10
                 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11
                 x28 x29 x30 x31) F (Z_to_bv 64 WO_FS6_RA) fc None m ro)
        (MS R' F (Z_to_bv 64 WO_RET) fc None m ro)
      /\ R' = mkR ra' (Z_to_bv 64 SP) gp tp x5 x6 x7 s0' s1' (Z_to_bv 64 r) x11
                 x12 x13 x14 x15 x16 x17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' x28 x29 x30 x31.
  Proof.
    intros until r. intros SPL SPH RR CSF.
    remember (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SP) s1 x10
                 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11
                 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 SP; s11'; s10'; s9'; s8'; s7'; s6'; s5'; s4'; s3'; s2'; s1'; s0'; ra'; Z_to_bv 64 r]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32); (24%bv, EVar 46)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        reflexivity. }
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) (-104)) 8 (EVar 33); KWord (SA (EVar 32) (-96)) 8 (EVar 34); KWord (SA (EVar 32) (-88)) 8 (EVar 35);
         KWord (SA (EVar 32) (-80)) 8 (EVar 36); KWord (SA (EVar 32) (-72)) 8 (EVar 37); KWord (SA (EVar 32) (-64)) 8 (EVar 38);
         KWord (SA (EVar 32) (-56)) 8 (EVar 39); KWord (SA (EVar 32) (-48)) 8 (EVar 40); KWord (SA (EVar 32) (-40)) 8 (EVar 41);
         KWord (SA (EVar 32) (-32)) 8 (EVar 42); KWord (SA (EVar 32) (-24)) 8 (EVar 43); KWord (SA (EVar 32) (-16)) 8 (EVar 44);
         KWord (SA (EVar 32) (-8)) 8 (EVar 45);
         KRange (EVar 32) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CSF 0%nat (C8 s11'). }
      apply Forall_cons. { kword_cell CSF 8%nat (C8 s10'). }
      apply Forall_cons. { kword_cell CSF 16%nat (C8 s9'). }
      apply Forall_cons. { kword_cell CSF 24%nat (C8 s8'). }
      apply Forall_cons. { kword_cell CSF 32%nat (C8 s7'). }
      apply Forall_cons. { kword_cell CSF 40%nat (C8 s6'). }
      apply Forall_cons. { kword_cell CSF 48%nat (C8 s5'). }
      apply Forall_cons. { kword_cell CSF 56%nat (C8 s4'). }
      apply Forall_cons. { kword_cell CSF 64%nat (C8 s3'). }
      apply Forall_cons. { kword_cell CSF 72%nat (C8 s2'). }
      apply Forall_cons. { kword_cell CSF 80%nat (C8 s1'). }
      apply Forall_cons. { kword_cell CSF 88%nat (C8 s0'). }
      apply Forall_cons. { kword_cell CSF 96%nat (C8 ra'). }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_FS6_RA m ro HR HK 60%nat [WO_RET] (SCR [] [] []) 60%N.
    { first [apply Forall_nil | split_scs].
      all: cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?EP; evs; rewrite ?u64_of_Z by lia; lia. }
    clear HK.
    exists R'. split; [exact Hms|].
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
    rreg HR' 24%bv L24. rreg HR' 25%bv L25. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 SP) by (rewrite L2; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 r) by (rewrite L10, BSymTac.aluw_add_0; apply vlw_small; exact RR).
    rewrite HRe at 1; rewrite L1, L2', L8, L9, L10', L18, L19, L20, L21, L22, L23, L24, L25, L26, L27; subst R; reflexivity.
  Qed.
End WoR7.
