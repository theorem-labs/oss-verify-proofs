(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BAgentLib BFrame BReach BeapCeil BSpec BSymRun BRefPrintfLib BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BMState BSysStep BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 BXXRep DvB_FuzzStmt BsPrintfFirst BsExitDefs BsDrvDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_DStat.
Import BPropExec.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Section MainPre.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable P : fuzz_params.

  Definition AMLO (sp0 : word) : Z := bv_unsigned sp0 - 128 - ATR_STACK.

  Definition AMAIN_COST : Z :=
    12 * (as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26)) + (as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26) + 4 * fz_cost P (2 ^ 26)).

  Definition astr_at (mem : word -> option byte) (sp0 : word) (p : Z) (s : list byte) : Prop :=
    bv_unsigned sp0 <= p /\ p + Z.of_nat (length s) + 17 <= 0x800000000000 /\ ~ In (Z_to_bv 8 0) s
    /\ rdn RSEGS mem (Z_to_bv 64 p) (length s + 1) = Some (s ++ [Z_to_bv 8 0])
    /\ exists t8, rdn RSEGS mem (Z_to_bv 64 (p + Z.of_nat (length s))) 8 = Some t8.

  Record AMpre (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF : machine_state) (mo : Model)
                (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z) : Prop := AMPRE {

    am_vis  : as_VIS H s0 msF = mkst regs (Z_to_bv 64 0xe83f4) mem (seg_rom asegs);
    am_krel : as_AKREL H s0 (mkCfg msF mo);

    am_ra : getr regs 1 = Z_to_bv 64 0x164cb0;
    am_sp : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
    am_tp : getr regs 4 = Z_to_bv 64 ATP;
    am_a0 : getr regs 10 = Z_to_bv 64 (Z.of_nat (length argv));
    am_a1 : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);

    am_vsp  : valid_sp sp0;
    am_ceil : hceil + 8388608 <= bv_unsigned sp0;

    am_stk : stk asegs mem (AMLO sp0) (bv_unsigned sp0);
    am_sh0 : exists shi, stack0 mem (AMLO sp0) shi /\ 0x800000000000 <= shi;

    am_args : forall (i : nat) (s : list byte), (i < 2)%nat -> nth_error argv i = Some s -> exists p : Z,
                rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p))
                /\ astr_at mem sp0 p s;

    am_inv   : mem_inv asegs mem;
    am_relro : arelro_none mem;
    am_glb   : aglb_none mem;
    am_ac    : ACONST mem;
    am_cells : cells_ok mem adrv_cells;
    am_out   : cells_ok mem astdout0;
    am_tid   : atid_cell mem tid;
    am_errno : exists e, rw_cells asegs mem AERRNO [C4 e];
    am_can   : acanary mem can;
    am_rfs   : as_RFS H [] mem;
    am_latch : exists ib : byte, rdn RSEGS mem (Z_to_bv 64 0x6c3690) 1 = Some [ib];

    am_heap : as_RHEAP H s0 [] mem;
    am_aux  : as_rauxv_ok H mem B /\ bv_unsigned sp0 <= B < 2 ^ 64;
    am_al   : AMAIN_COST <= as_AL H s0;
    am_tr   : adrv_traces H P;

    am_fds : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];

    am_dstat : LbB_DStat.dstat mem }.

  Definition as_main_realizes_stmt : Prop :=
    forall (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF : machine_state) (mo : Model)
           (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z),
      valid_argv argv -> valid_fs (m_fs mo) ->
      AMpre sp0 argv s0 msF mo regs mem B tid can ->
      realizes asegs (mkCfg msF mo) (spec argv (m_fs mo)).
End MainPre.
