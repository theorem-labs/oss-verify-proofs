(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Image ZBridge Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface
     ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep AFake0k_iface AFake_arep0k AF_huf_tbl_iface2 AF_huf_tbl_iface3
     AF_huf_fdwc AF_huf_rs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_rsc () := "C46Stdlib5Lists4List2hdC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5AsanW;AF_huf_fdwcBfse_decomp_closedAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AF_huf_rsAhuf_rstats_proofAC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5AsanW;AFake_iface9afake_rngC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  (* [comment removed for export] *)
  Theorem huf_rstats_closedA : forall k, Z.of_nat k < 16382 -> huf_rstats_stmtA AI afake_rng k.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_rsc ()) ["CANSEC1"; "Inst"] "h02Hkh11kp;1p;2p;<p;5p-1p10000p4p710p8g000Gj17Tg000gj13Tg001Lj12Tg001jj26Tg002Fl<5Tg003Oj54Tg004Uj11Tf0R0#1#1p=0g005:%70g005Y#0#0#0#0#0#0#3#2'6p,2rcR1p,2AIR2g006>f1R3P1p,2DIp,2AQp,4ASECp,2HLp,2CIp,5CI_OKP2p,1Ep,2ECP3P0M<5D4W0W1o"). Qed.
End Inst.
End CANSEC1.
