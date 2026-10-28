(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame SReach HeapCeil Spec SymRun RefPrintfLib
  LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 AsAuxv
  ECH_Xpres ECH_Iface AsPrintfFirst AsDrvDefs.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)

Section MainPre.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable L : alib.

  (* [comment removed for export] *)
  Definition AMLO (sp0 : word) : Z := bv_unsigned sp0 - 128 - ATR_STACK.

  (* [comment removed for export] *)
  Definition AMAIN_COST : Z :=
    12 * (as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26)) + (as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26) + 4 * fuzz_cost H L (2 ^ 26)).

  (* [comment removed for export] *)
  Definition astr_at (mem : word -> option byte) (sp0 : word) (p : Z) (s : list byte) : Prop :=
    bv_unsigned sp0 <= p /\ p + Z.of_nat (length s) + 17 <= 0x800000000000 /\ ~ In (Z_to_bv 8 0) s
    /\ rdn RSEGS mem (Z_to_bv 64 p) (length s + 1) = Some (s ++ [Z_to_bv 8 0])
    /\ exists t8, rdn RSEGS mem (Z_to_bv 64 (p + Z.of_nat (length s))) 8 = Some t8.

  Record AMpre (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF : machine_state) (mo : Model)
                (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z) : Prop := AMPRE {
    (* [comment removed for export] *)
    am_vis  : as_VIS H s0 msF = mkst regs (Z_to_bv 64 0x1eed1c) mem (seg_rom asegs);
    am_krel : as_AKREL H s0 (mkCfg msF mo);
    (* [comment removed for export] *)
    am_ra : getr regs 1 = Z_to_bv 64 0x55de4c;
    am_sp : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
    am_tp : getr regs 4 = Z_to_bv 64 ATP;
    am_a0 : getr regs 10 = Z_to_bv 64 (Z.of_nat (length argv));
    am_a1 : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
    (* [comment removed for export] *)
    am_vsp  : valid_sp sp0;
    am_ceil : hceil + 8388608 <= bv_unsigned sp0;
    (* [comment removed for export] *)
    am_stk : stk asegs mem (AMLO sp0) (bv_unsigned sp0);
    am_sh0 : exists shi, stack0 mem (AMLO sp0) shi /\ 0x800000000000 <= shi;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    am_args : forall (i : nat) (s : list byte), (i < 2)%nat -> nth_error argv i = Some s -> exists p : Z,
                rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p))
                /\ astr_at mem sp0 p s;
    (* [comment removed for export] *)
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
    am_reg   : cells_ok mem aatexit_pre_cells;                                       (* [comment removed for export] *)
    am_lib   : forall i, rin_ivs (al_LIBX0 L) i -> mem (Z_to_bv 64 i) = None;       (* [comment removed for export] *)
    am_ossl  : mem (Z_to_bv 64 0xbdd420) = None /\ mem (Z_to_bv 64 ACLEANUP) = None;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    am_heap : as_RHEAP H s0 [] mem;
    am_aux  : as_rauxv_ok H mem B /\ bv_unsigned sp0 <= B < 2 ^ 64 /\ aauxv_ok mem B;   (* [comment removed for export] *)
    am_al   : AMAIN_COST <= as_AL H s0;
    am_tr   : adrv_traces H L;
    (* [comment removed for export] *)
    am_fds : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
    (* [comment removed for export] *)
    am_musl0 : amusl0 mem }.

  (* [comment removed for export] *)
  Definition as_main_realizes_stmt : Prop :=
    forall (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF : machine_state) (mo : Model)
           (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z),
      valid_argv argv -> valid_fs (m_fs mo) ->
      AMpre sp0 argv s0 msF mo regs mem B tid can ->
      realizes asegs (mkCfg msF mo) (spec argv (m_fs mo)).
End MainPre.
