(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_MILB LbB_PrsStmt LbB_Own LbB_ContStmt LbB_DiagStmt LbB_TablStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ASN_STACK : Z := ADS_STACK + 256.

Definition SN_FRAMES : nat := S DS_FRAMES.
Definition SN_FCLASS : Z := 4.
Definition SN_FSIZE : Z := 960.

Definition SN_DTOR_RA1 : Z := 0xf99ec.
Definition SN_DTOR_RA2 : Z := 0xf9d14.
Definition SN_PF : list (Z * list Z) := [(APC0_FREE, [0xfd148; SN_DTOR_RA1]); (APC0_FREE, [0xfd148; SN_DTOR_RA2])].

Definition SN_COST : Z := 2 ^ 20.
Definition SN_ERR : Z := 2 ^ 64 - 4.

Definition sn_nw (bw : Z) : Z := (((bw + 31) mod 2 ^ 32) / 32) mod 2 ^ 16.

Definition sn_X (po : Z) : list (Z * Z) := [(po + 2, po + 4); (po + 8, po + 20)].

Definition sn_XT (po : Z) : list (Z * Z) := sn_X po ++ [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)].

Definition sn_kinds_ok (ents : list (Z * (Z * (Z * Z * Z)))) : Prop :=
  Forall (fun e => 0 <= t3a (snd (snd e)) < 4 /\ 0 <= t3c (snd (snd e)) < 16) ents.

Section Stmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

  Definition sn_res (LB : list block) (po tid : Z) (ents : list ent) (r : Z) (LB' : list block) (m' : mem) : Prop :=
    Permutation LB' LB /\ wr_at asegs m' po 20 /\
    ((r = SN_ERR)
     \/ (r = 0 /\ LB' = LB /\ exists node nk bw enc, In (node, (tid, (nk, bw, enc))) ents /\ nk <> 0
                  /\ rw_cells asegs m' (po + 8) [C4 (Z_to_bv 64 nk)] /\ rw_cells asegs m' (po + 12) [C4 (Z_to_bv 64 bw)]
                  /\ rw_cells asegs m' (po + 16) [C4 (Z_to_bv 64 enc)]
                  /\ rw_cells asegs m' (po + 2) [C2 (Z_to_bv 64 (sn_nw bw))]
                  /\ 0 <= nk < 2 ^ 32 /\ 0 <= bw < 2 ^ 32 /\ 0 <= enc < 2 ^ 32)).

  Definition sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (X : list (Z * Z)) (lo B shi : Z) (m : mem) (mo : Model)
      (Q : Z -> list block -> mem -> Prop) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block)
                    (XS : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32) (r : Z),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ a0 = Z_to_bv 64 r
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Q r LB' m'
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB (bv_unsigned sp) (X ++ XS) m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ LINV m'
      /\ as_AL H s' >= as_AL H s - (if r =? 0 then 0 else SN_COST).

  Definition setnum_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (this po tid pcons icount bl bc : Z) (ents : list ent),
      ds_pre H LINV ASN_ENTRY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB [] LF CH SN_COST lo B shi errv ->

      lo <= bv_unsigned sp - ASN_STACK -> (length LF + SN_FRAMES <= AFS_MAXLIVE_BP)%nat ->

      lb_small LB + 3 * 64512 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 3 <= RT_CNT_MAX -> nlarge LB + 3 <= RT_LARGE_MAX ->
      pf_ok (as_TR H) SN_PF (bv_unsigned ra) CH ->

      a0 = Z_to_bv 64 this -> a1 = Z_to_bv 64 po -> a2 = Z_to_bv 64 (sx32A tid) -> 0 <= tid < 2 ^ 32 ->

      ds_obj H LF m (bv_unsigned sp) this 288 -> obj_inframe LF this 288 ->
      rw_cells asegs m (this + 8) [C8 (Z_to_bv 64 pcons)] -> rw_cells asegs m (this + 80) [C8 (Z_to_bv 64 icount)] ->
      0 <= icount < 2 ^ 63 ->
      ds_obj H LF m (bv_unsigned sp) pcons 48 -> obj_inframe LF pcons 48 ->
      rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)] -> pcons mod 16 = 0 ->
      umapx MI_A 32 (nval32 ASEGS) (lbl LB) m (this + 136) bl bc ents -> umap_sh m 32 (bl, bc, ents) ->
      sn_kinds_ok ents ->

      ds_obj H LF m (bv_unsigned sp) po 20 -> obj_inframe LF po 20 -> wr_at asegs m po 20 ->

      (forall a, po <= a < po + 20 -> ~ (pcons <= a < pcons + 48)) ->
      as_SR H (sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF (sn_XT po) lo B shi m mo
                       (sn_res LB po tid ents))
              (mkCfg msF mo).
End Stmts.
