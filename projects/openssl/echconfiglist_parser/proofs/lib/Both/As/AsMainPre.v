(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main precondition gains am_rdr, the launch's channel reader; astr_at's room above an argument string is 10 bytes, the exec name's NUL and the top slot of the revised entry block; the main statement concludes over the run's segment list asegs ++ rt_tail from the configuration with that list's read-only backing). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame SReach HeapCeil Spec SymRun RefPrintfLib
  LazyRestrict LazySR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 AsAuxv
  ECH_Xpres ECH_Iface AsPrintfFirst AsDrvDefs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomBase RunTail.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)

Section MainPre.
  Context {HCEIL : HeapCeil}.
  (* the run's tail ([RunTail.RunTail]): main reaches the target, which calls time(), so main's
     walk is over the run's segment list *)
  Context {RT : RunTail.RunTail}.
  Variable H : asr.
  Variable L : alib.

  (* [comment removed for export] *)
  Definition AMLO (sp0 : word) : Z := bv_unsigned sp0 - 128 - ATR_STACK.

  (* [comment removed for export] *)
  Definition AMAIN_COST : Z :=
    12 * (as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26)) + (as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26) + 4 * fuzz_cost H L (2 ^ 26)).

  (* [comment removed for export] *)
  (* LPS 727298f3: the strings sit at the TOP of the entry block, so above an argv string's NUL there are at
     least the exec name's NUL and the eight-byte top slot (StackLayout.launch_string_bytes,
     StackLayout.string_base_addr), and the block ends at or below 0x800000000000 (Run.valid_stack_top_va):
     hence 10, where the old block's sixteen AT_RANDOM bytes above the strings gave 17.  Proved in
     AsMainIfaceArgs.arg_string. *)
  Definition astr_at (mem : word -> option byte) (sp0 : word) (p : Z) (s : list byte) : Prop :=
    bv_unsigned sp0 <= p /\ p + Z.of_nat (length s) + 10 <= 0x800000000000 /\ ~ In (Z_to_bv 8 0) s
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
    (* 08b1429: the far end of the standard channels has a reader; [Run.valid_input] pins it,
       [State.init_model] copies it and no step writes it *)
    am_rdr : m_channel_reader mo = true;
    (* [comment removed for export] *)
    am_musl0 : amusl0 mem }.

  (* [comment removed for export] *)
  Definition as_main_realizes_stmt : Prop :=
    forall (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF : machine_state) (mo : Model)
           (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z),
      valid_argv argv -> valid_fs (m_fs mo) ->
      AMpre sp0 argv s0 msF mo regs mem B tid can ->
      realizes (asegs ++ RunTail.rt_tail)
        (RomBase.cwrom (mkCfg msF mo) (seg_rom (asegs ++ RunTail.rt_tail))) (spec argv (m_fs mo)).
End MainPre.
