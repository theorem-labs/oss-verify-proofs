(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX HArr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_FKit LbA_RGb2 LbA_WoR1 LbA_WoR2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_PrsStmt LbA_StateStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition SX_SF_RA : Z := 0xf9590.
Definition SX_RET : Z := 0xf95e0.

Section SnXZ.
  Context {HCEIL : HeapCeil}.

  Lemma sn_xe2 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (gp tp : word) (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff fp SP S1 r : Z),
    2 ^ 45 <= S1 -> S1 + 128 <= SP -> SP <= 2 ^ 47 ->
    rw_cells asegs m (SP - 104) [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'] ->
    exists R',
      CatSim.msteps asegs
        (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) x19 (Z_to_bv 64 r) x21
                 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31) F (Z_to_bv 64 SX_SF_RA) fc None m ro)
        (MS R' F (Z_to_bv 64 SX_RET) fc None m ro)
      /\ R' = mkR ra' (Z_to_bv 64 SP) gp tp x5 x6 x7 s0' s1' (Z_to_bv 64 r) x11
                 x12 x13 x14 x15 x16 x17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' x28 x29 x30 x31.
  Proof.
    intros until r. intros S1L S1H SPH CSF.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) x19 (Z_to_bv 64 r) x21
                 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 SP; s11'; s10'; s9'; s8'; s7'; s6'; s5'; s4'; s3'; s2'; s1'; s0'; ra']).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 34); (18%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity. }
    assert (EP : bv_unsigned (edenot E (EVar 34)) = SP) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 34) (-104)) 8 (EVar 35); KWord (SA (EVar 34) (-96)) 8 (EVar 36); KWord (SA (EVar 34) (-88)) 8 (EVar 37);
         KWord (SA (EVar 34) (-80)) 8 (EVar 38); KWord (SA (EVar 34) (-72)) 8 (EVar 39); KWord (SA (EVar 34) (-64)) 8 (EVar 40);
         KWord (SA (EVar 34) (-56)) 8 (EVar 41); KWord (SA (EVar 34) (-48)) 8 (EVar 42); KWord (SA (EVar 34) (-40)) 8 (EVar 43);
         KWord (SA (EVar 34) (-32)) 8 (EVar 44); KWord (SA (EVar 34) (-24)) 8 (EVar 45); KWord (SA (EVar 34) (-16)) 8 (EVar 46);
         KWord (SA (EVar 34) (-8)) 8 (EVar 47);
         KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
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
    unfold SX_SF_RA.
    xrun_at (PropExec.mkFP F fc) asegs R 0xf9590 m ro HR HK 60%nat [SX_RET] (SCR [] [] []) 44%N.
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
    assert (L2' : getr R' 2 = Z_to_bv 64 SP) by (rewrite L2; evs; rewrite ?w_add, ?w_addm, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
    assert (L10' : getr R' 10 = Z_to_bv 64 r) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | evs; reflexivity]).
    rewrite HRe at 1. rewrite L1, L2', L8, L9, L10', L18, L19, L20, L21, L22, L23, L24, L25, L26, L27. subst R. reflexivity.
  Qed.
End SnXZ.
