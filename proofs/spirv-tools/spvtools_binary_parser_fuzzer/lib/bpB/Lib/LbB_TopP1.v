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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_TopH2 LbB_TopT1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma sra2_4n : forall n, 0 <= n < 2 ^ 60 ->
  alu64 ALU_SRA (mul_div M_MUL (Z_to_bv 64 4) (Z_to_bv 64 n)) (Z_to_bv 64 2) = Z_to_bv 64 n.
Proof.
  intros n Hn. rewrite w_mul by lia. unfold alu64, alu.
  replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 63)) with (Z_to_bv 64 2) by (apply bv_eq; vm_compute; reflexivity).
  apply bv_eq. rewrite bv_ashiftr_unsigned, Z_to_bv_signed, !Z_to_bv_unsigned.
  rewrite (bv_swrap_small 64 (4 * n)) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  rewrite (bv_wrap_small 64 2) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Section TopP1.
  Context {HCEIL : HeapCeil}.

  Lemma hPO1 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 V A P n : Z),
    2 ^ 45 <= S1 <= 2 ^ 47 -> 0 <= V -> V + 24 <= 2 ^ 47 -> 0 <= A < 2 ^ 64 -> 0 <= P -> P + 4 * n <= 2 ^ 47 -> 0 <= n ->
    rw_cells asegs m (S1 + 24) [C8 (wz A)] -> rw_cells asegs m (S1 + 80) [C8 (wz V)] ->
    rw_cells asegs m V [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))] ->
    evt asegs (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 0xe8c10) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 A)
                      (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) x17
                      (Z_to_bv 64 A) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0xea7bc) fc None m (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8be0) fc None m (seg_rom asegs)).
  Proof.
    intros until n. intros S1R V0 V1 A0 P0 P1 N0 CA CVf CV.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 V; Z_to_bv 64 P; Z_to_bv 64 n; Z_to_bv 64 A]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 80) 8 (EVar 33); KWord (SA (EVar 32) 24) 8 (EVar 36);
         KWord (SA (EVar 33) 0) 8 (EVar 34); KWord (SA (EVar 33) 8) 8 (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35)));
         KRange (EVar 32) (2 ^ 45) (2 ^ 47); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 34) 0 (2 ^ 47); KRange (EVar 35) 0 (2 ^ 45) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CVf 0%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell CA 0%nat (C8 (wz A)). }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz P)). }
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 8%nat (C8 (wz (P + 4 * n)))); [exact CV | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        cbn [cbytes edenot]. evs. rewrite w_mul, w_add by lia. reflexivity. }
      do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xe8be0 m (seg_rom asegs) HR HK 40%nat [0xea7bc] (SCR [] [] []) 50%N.
    { split_scs; cbn [sc_denot]; unfold flat; evs; rewrite ?u64_of_Z by lia; lia. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 13%bv L13. rreg HR' 14%bv L14. rreg HR' 15%bv L15. rreg HR' 16%bv L16. rreg HR' 18%bv L18.
    assert (L13' : getr R' 13 = Z_to_bv 64 n) by (rewrite L13; apply sra2_4n; lia).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L9, L10, L11, L12, L13', L14, L15, L16, L18.
    subst R. cbn [getr mkR]. apply evt_done. cbn [mem_denot]. reflexivity.
  Qed.
End TopP1.
