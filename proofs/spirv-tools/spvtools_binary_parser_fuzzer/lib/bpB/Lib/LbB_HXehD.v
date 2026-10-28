(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HXmpS LbB_HXmpD LbB_HRehK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition R_EXIT : Z := 0xfc33c.
Definition R_RET : Z := 0xfc35c.

Section RehC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).
  #[local] Notation n := (bseq_next bc).

  Definition QR : config -> Prop :=
    reh_post H ra (Z_to_bv 64 spz) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sk0 LB0 LF obj n ents lo B shi m0 mo0.

  Definition spr : Z := spz - 64.

  Definition RFRAME (m : mem) : Prop :=
    rw_cells asegs m (spz - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma stage_repi : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (bl' : Z) (ents' : list (Z * (Z * Z))),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spr) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                             y18 y19 y20 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 R_EXIT) fc None m (seg_rom asegs) ->
    frm_zero fc ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    RFRAME m -> spz mod 16 = 0 -> 2 ^ 45 <= spr -> spz <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 ->
    mem_inv asegs m -> stk asegs m lo spz -> rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    umapx MI_A 24 (nval24 ASEGS) (lbl LB') m obj bl' n ents' -> umap_sh m 24 (bl', n, ents') -> Permutation ents' ents ->
    addressable m obj 40 -> wr_at asegs m obj 40 ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ LBm') -> Permutation (lbl LBm') (umap_blocks 24 bl' n ents') ->
    lb_own LBm' m ->
    xpres H LB0 spz [(obj, obj + 40)] m0 m ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    as_SR H QR (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31
      errv' LB' LBm' bl' ents'
      VIS FRZ KR MP FR SP16 SPL SPH RAE MI ST ERR RA U SH PENTS AD WR RH PE PM OWN XP RF AC S0 AL.
    unfold RFRAME, spr in *.
    remember (mkR y1 (Z_to_bv 64 (spz - 64)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                  y18 y19 y20 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (spz - 64); s5; s4; s3; s2; s1; s0; ra]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 8) 8 (EVar 33); KWord (SA (EVar 32) 16) 8 (EVar 34); KWord (SA (EVar 32) 24) 8 (EVar 35);
         KWord (SA (EVar 32) 32) 8 (EVar 36); KWord (SA (EVar 32) 40) 8 (EVar 37); KWord (SA (EVar 32) 48) 8 (EVar 38);
         KWord (SA (EVar 32) 56) 8 (EVar 39); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 64) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell FR 0%nat (C8 s5). }
      apply Forall_cons. { kword_cell FR 8%nat (C8 s4). }
      apply Forall_cons. { kword_cell FR 16%nat (C8 s3). }
      apply Forall_cons. { kword_cell FR 24%nat (C8 s2). }
      apply Forall_cons. { kword_cell FR 32%nat (C8 s1). }
      apply Forall_cons. { kword_cell FR 40%nat (C8 s0). }
      apply Forall_cons. { kword_cell FR 48%nat (C8 ra). }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R R_EXIT m (seg_rom asegs) HR HK 20%nat [R_RET] (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    clear HK.
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with m in Hms end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 18%bv G18.
    rreg HR' 19%bv G19. rreg HR' 20%bv G20. rreg HR' 21%bv G21.
    assert (G2' : getr R' 2 = Z_to_bv 64 spz) by (rewrite G2; rewrite ?w_addm, ?w_add, ?v_addi_Z by lia; try reflexivity; f_equal; lia).
    rewrite G1, G2', G8, G9, G18, G19, G20, G21 in HRe.
    eapply (sr_evt H HH) with
      (P := fun ms => exists u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6,
              ms = MS (mkR ra (Z_to_bv 64 spz) gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc ra) fc None m (seg_rom asegs));
      [exact KR | exact VIS | |].
    { eapply evt_of_msteps; [exact Hms|].
      rewrite mkst_MS, HRe. step. apply evt_done. do 15 eexists. reflexivity. }
    intros msF' mo' KR' MP' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & HP).
    unfold QR, reh_post.
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m, errv', s, LB', LBm', F, fc, bl', ents'.
    rewrite u64_of_Z by lia.
    split; [exact HP|]. split; [exact FRZ|]. split; [exact KR'|]. split; [eapply (ah_mpres_trans H HH); [exact MP | exact MP']|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact RA|].
    split; [exact U|]. split; [exact SH|]. split; [exact PENTS|]. split; [exact AD|]. split; [exact WR|].
    split; [exact RH|]. split; [exact PE|]. split; [exact PM|]. split; [exact OWN|]. split; [exact XP|].
    split; [exact RF|]. split; [exact AC|]. split; [exact S0|]. exact AL.
  Qed.
End RehC.
