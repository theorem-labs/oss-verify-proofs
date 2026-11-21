(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (amalloc_all)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase AMalloc_iface ADepot_iface APoisonR_iface ARep AHeapP ASec
     F_amalloc_arep AMallocPG AMallocS.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMalloc () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_amalloc_arep2AHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface8aresv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<amalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AMallocPG<amalloc_primC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AMallocS;amalloc_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<amalloc_stmtC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase=AMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase:AMALLOC_PCC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase;AMALLOC_SYMC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem amalloc_all : amalloc_stmt CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold amalloc_stmt. intros.
  destruct (is_primary n) eqn:P.
  - eapply (amalloc_prim DI AQ ASEC_of AFK HL CI CI_OK CI_OK2); eassumption.
  - eapply (amalloc_sec DI AQ AFK HL PR CI CI_OK CI_OK2); eassumption.
Qed.
End S.
End CANSEC1.
