(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HBytes HZBridge TacX HSFModel HSysStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsWalk FakeStackRep N5_tls N5_smkit RtA_Iface RtA_SMKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import N8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SF5.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Lemma stack_free_5_ok : stack_free_stmt H 5 AFS_FREE_5.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LF ff fp lo.
    intros RFS IN Ha0 FPC ST0 LO LOSP MI AC. subst a0.
    pose proof (proj1 (RFS_is LF m) RFS) as R.
    remember (as_FSB H) as fsb eqn:Hfsb.
    pose proof R as ((G1 & G2 & G3 & G4) & TLS & HDR & SL & ND & FL & STF & STS).
    acb; unfold AFS_STACK, AFS_FREE_5, AFS_SIZE, AFS_HDR, AIMG_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.

    destruct (SL _ IN) as (pos & SOK & EFF & EFP). cbn [ff_class ff_addr ff_flag fst snd] in SOK, EFF, EFP.
    pose proof SOK as [[K0 K1] PR]. unfold NF in PR. change (2 ^ (14 - 5)) with 512 in PR.
    assert (EFF' : ff = fsb + 5279744 + 2048 * pos) by (rewrite EFF; unfold frame_addr, AFS_HDR, fsz; cbn; lia).
    assert (EFP' : fp = fsb + 35840 + pos) by (rewrite EFP; unfold flag_addr, AFS_HDR; cbn; lia).
    clear EFF EFP.

    pose proof (FL 5 pos SOK) as CFP. unfold flagv in CFP.
    replace (liveb LF (flag_addr fsb 5 pos)) with true in CFP.
    2:{ symmetry. apply liveb_true. exists (5, ff, fp). split; [exact IN|]. cbn. rewrite EFP'. unfold flag_addr, AFS_HDR. cbn. lia. }
    replace (flag_addr fsb 5 pos) with fp in CFP by (rewrite EFP'; unfold flag_addr, AFS_HDR; cbn; lia).
    unfold fsz in FPC. change (64 * 2 ^ 5) with 2048 in FPC. replace (ff + 2048 - 8) with (ff + 2040) in FPC by lia.

    remember (sh ff) as SF eqn:HSF.
    assert (SFR : 2148355072 <= SF /\ SF + 256 <= 17594333495296 /\ sh fsb <= SF /\ SF + 256 <= sh (fsb + 11571200)).
    { subst SF. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    assert (SEP : fsb + 11571200 <= 2147446784 \/ 17594333495296 <= fsb)
      by (clear - G4; destruct G4 as [[X1 X2]|[X1 X2]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AFS_SIZE in X1, X2; lia).
    destruct (stk_split asegs m _ (SF + 256) _ STS ltac:(lia)) as [SSa SSc].
    destruct (stk_carve asegs m _ _ 256 SSa ltac:(lia)) as [SSa' [sjunk SRM]].
    replace (SF + 256 - Z.of_nat 256) with SF in SSa', SRM by lia. clear SSa SSc.

    pose proof (ACONST_mts m AC) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_MIDBEG, AMIDBEG_CELL, AGOT_MIDEND, AMIDEND_CELL, AGOT_HIEND, AHIEND_CELL, wz in Q1, Q2, Q3, Q4, Q5, Q6.

    pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (fp, fp + 1); (SF, SF + 256)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 16%nat ST.

    zstep. st1. st1.

    st1. zstep. st1.

    zstep.
    call_pure mts_spec; try reflexivity; try eassumption;
      [clear - G4 EFF' PR; destruct G4 as [[G4a G4b]|[G4a G4b]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, AFS_SIZE in *; [left | right]; acb; lia|].
    rewrite <- HSF.

    zstep. zstep. do 32 st1.

    zstep. zstep. zstep. zstep.
    clear ST0. release_frame FR ST (bv_unsigned sp).
    assert (FF8 : 0 <= ff /\ ff mod 8 = 0) by (rewrite EFF'; Z.div_mod_to_equations; lia).
    subst SF fsb. unfold stack_free_post. finish.
    all: lazymatch goal with
         | |- munch _ _ _ => exact MU
         | |- SHAD _ _ _ => apply (shad_of_f5_words 32); [lia| lia| exact SRM]
         | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU| exact WM|];
                          repeat apply Forall_cons; [| | |apply Forall_nil]; aconst5 G1 G4
         | |- as_RFS _ _ _ =>
              eapply (RFSI_release H RFS_is LF m _ _ 5 ff fp); [exact RFS| exact IN| exact MU| exact WM| |];
              [ unfold afs_write_ok, AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *;
                repeat apply Forall_cons; [left; left; cbn; split; lia | right; cbn; split; reflexivity | left; left; cbn; split; lia | apply Forall_nil ]
              | erewrite rw_cells_C1_mrd; [reflexivity| eassumption] ]
         | _ => idtac
         end.
  Qed.
End SF5.
