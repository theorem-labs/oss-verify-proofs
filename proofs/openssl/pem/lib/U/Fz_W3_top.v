(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_W1_defs Fz_W3_iface Fz_W2_rep Fz_W3_defs
     Fz_W3_end Fz_W3_tail Fz_W3_rzt Fz_W3_dec Fz_W3_ini Fz_W3_tl Fz_W3_free2 Fz_W3_endl Fz_W3_hdloop Fz_W3_free1 Fz_W3_ngets Fz_W3_name Fz_W3_gnloop
     Fz_W3_j0r Fz_W3_j0g Fz_W3_j0n Fz_W3_j0.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  (* [comment removed for export] *)
  Local Notation A11 x := (x libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where errst_rest_live) (only parsing).
  Local Notation A10 x := (x libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where) (only parsing).
  Local Notation A9 x := (x libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where) (only parsing).
  Local Notation A3 x := (x libenv errst_at_rest errst_live) (only parsing).

  Theorem pem_read_bio_proof : bio_free_null_stmt -> pem_read_bio_deps libenv errst_at_rest errst_live.
  Proof.
    intros BFN PM PM0 PF PFN SAN ENEW EDBG ESET BN BF BG BP BCP BCI BRD ECN ECF ECFN.
    pose proof (A11 END0_proof ECFN PFN BFN) as END0P.
    pose proof (A11 END_proof ECF ECFN PF PFN BF) as ENDP.
    pose proof (A10 OUTFREE_proof PF PFN ENDP) as OUTP.
    pose proof (A3 RZT_proof ENEW EDBG ESET ENDP) as RZTP.
    pose proof (A9 DEC_proof BCI PM PM0 BRD ENDP OUTP) as DECP.
    pose proof (A9 INI_proof RZTP DECP) as INIP.
    pose proof (A9 TAIL_proof BCP ECN ENDP INIP) as TAILP.
    pose proof (A10 FREE2_proof PF ENDP) as FREE2P.
    pose proof (A3 RAISE2_proof ENEW EDBG ESET FREE2P) as RAISE2P.
    pose proof (A9 LFREE_proof PF TAILP) as LFREEP.
    pose proof (A9 ENDLINE_proof RAISE2P LFREEP) as ENDLP.
    pose proof (A9 HD_proof SAN BP BG ENDLP RAISE2P FREE2P) as HDP.
    pose proof (A10 FREE1_proof PF ENDP) as FREE1P.
    pose proof (A3 RAISE1_proof ENEW EDBG ESET FREE1P) as RAISE1P.
    pose proof (A9 NGETS_proof BG RAISE2P HDP) as NGETSP.
    pose proof (A9 NAME_proof PM PF NGETSP) as NAMEP.
    pose proof (A9 GN_proof SAN BG NAMEP RAISE1P) as GNP.
    pose proof (A9 J0G_proof BG RAISE1P GNP) as J0GP.
    pose proof (A9 J0N_proof BN PM J0GP) as J0NP.
    pose proof (A3 RAISE0_proof ENEW EDBG ESET END0P) as RAISE0P.
    exact (A9 J0_proof RAISE0P J0NP).
  Qed.
End W3.
