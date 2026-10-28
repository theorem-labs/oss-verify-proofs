(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Ox Require F02.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel BSysStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk BakeStackRep B5_tls B5_smkit B6_poison RtB_Iface RtB_SMKit RtB_SM8a.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import B8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SM8.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Lemma stack_malloc_8_ok : stack_malloc_sz_stmt H 8 AFS_MALLOC_8.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LF lo sz.
    intros Ha0 SZ SZ8 RFS LEN ST0 LO LOSP MI Htp AC ATH. subst tp a0.
    unfold fsz in SZ. change (64 * 2 ^ 8) with 16384 in SZ.
    pose proof (proj1 (RFS_is LF m) RFS) as R. clear RFS.
    remember (as_FSB H) as fsb eqn:Hfsb.
    pose proof (RFSI_geom _ _ _ R) as (G1 & G2 & G3 & G4).
    acb; unfold AFS_STACK, AFS_MALLOC_8, AFS_SIZE in *. unfold AIMG_TOP in G1.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    destruct ATH as (ctx & T & D & tb & te & A1 & A2 & A3 & A4 & A5 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    acb; unfold ATSD0, ATP, wz in A1, A2, A3, A4, A5, B3, B6, B9. change (7100504 + 8) with 7100512 in A4.
    pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 48%nat ST.

    zstep. st1. st1. st1. st1. st1. zstep. zstep. zstep. zstep. zstep.
    call2 tls_icpt_spec.
    all: lazymatch goal with
         | |- mem_inv _ _ => eassumption
         | |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
         | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU| exact WM|]; apply Forall_cons; [|apply Forall_nil]; aconst5 G1 G4
         | |- athr_cells _ => exists ctx, T, D, tb, te;
              split; [exact A1|]; split; [exact A2|]; split; [exact A3|]; split; [exact A4|]; split; [exact A5|]; acb; repeat split; lia
         | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
         | |- _ <= _ => rewrite ?unsigned_lit by lia; acb; lia
         | |- evt _ _ _ => idtac
         end.
    rewrite ?unsigned_lit in * by lia.
    match goal with Hst : stk asegs ?mx lo (bv_unsigned sp + -48), Hac : ACONST ?mx |- _ => rename Hst into ST; rename Hac into AC2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (R2 : RFSI fsb LF mx) by (eapply RFSI_stack_frame; [exact R| exact MU| exact WM| acb; lia]) end.
    pose proof (RFSI_tls _ _ _ R2) as TLS. pose proof (RFSI_hdr _ _ _ R2) as (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR).
    unfold ATP, wz in TLS |- *. unfold hdr, wz, b8 in HDR.

    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
    st1. zstep. unfold wz. zstep. if_true.

    zstep. zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3; [exfalso; revert K3; vm_compute; lia|].

    do 15 zstep.

    pose proof R2 as (_ & _ & _ & _ & _ & FL & _).
    eapply evt_cut.
    { eapply sm8_loop with (FV := fun pos => flagv LF (flag_addr fsb 8 pos)) (n := 64%nat).
      - intros pos Hpos. cbn beta. replace (fsb + 36736 + pos) with (flag_addr fsb 8 pos) by (unfold flag_addr, AFS_HDR; cbn; lia).
        apply FL. split; [unfold KMAX; lia| unfold NF; cbn; lia].
      - intros pos. apply flagv_01.
      - reflexivity.
      - lia.
      - destruct (RFSI_free_slot_bp fsb LF _ 8 (bv_unsigned h8) R2 ltac:(lia) LEN) as (j & J1 & J2). exists j.
        change (NF 8) with 64 in J1, J2. exact (conj J1 J2). }
    intros ms' PO. destruct PO as (cur' & t0' & c' & p & -> & HP & HPM & FV0 & HC').
    subst fsb. eapply (sm8_found H RFS_is); eassumption.
  Qed.
End SM8.
