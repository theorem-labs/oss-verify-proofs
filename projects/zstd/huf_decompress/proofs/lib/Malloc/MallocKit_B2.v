(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_enframe MallocTree MallocKit_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocKit_B2 () := "C35stdpp4base6LookupC59OSSVerify5KrLib6Malloc:MallocTree>pans_mem_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introC59OSSVerify5KrLib4Spec6Malloc>peek_answer_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B2 ()) ["CANSEC1"] "h04__p1h14__x1h21mh31nh42H0h57__arithh64__ffh78__varmaph85__with91ch:1hh;1oh<1ph=1Hp;4p;2p;1p;6p;3p;7p;8p-1R0p10000R1p4p710p8P0P1p4p7210p8g000Dj4TTg001Ij46Tg002Hj23Tg002dj11Tg003Ij1STg003gj22Tg004CR1j27Tg004^j24Tg005;j25Tg005Xj2@Tg0068j1>Tg006Xj1=Tg0078j2RTg007Vj1QTg0084j1KTg008_j2<Tg009Bj2FTg009ej4;Tg00:Pj6ETg00;4j1DTg00;Vj2CTg00<8j2BTg00<Rj2GTg00=>j3HTg00=]j4ATg00>Oj2ITg00>oj4JTg00?Jj3?Tg00@3j1LTg00A2j3MTg00ALj7NTg00B0j7OTg00BTj8PTg00C8R0f0R2g00CXR33Mp=0f1R4g00D8R5g00DWR6P6g00E7R7P2g00EWFNp=:f2R8P5P6P6P7P4P2FOp=9f3R9P5P6P6P7P8P4P2GPp=8g00F7R:g00G1R;g00GfR<P9P8P4P2CTg00HDR=P9P8P4P2C6R>'3g00HbR?#1#1#1#1#1#1#1#1#SR@,2>'7f4R>P9P8P4C6RA,4=RB15A@RC%0B%0CP11442#01384RC[13421484#0[RB1498#0\C1@42P2n2001000000120000000X2<X3<PB^2<^3<P2P=f5RBP>P9P8C6RCp-0RDg00IGRE#>RF%=ERE1R<4RG%Q<RH%K<RIP<1<<=g00J31F<?R?C;,:IRJPIP5P6P6P7P9EER559I%D6R6PJC81CI7R7P2P81B031G28#0dAH<=4CAR3b6b7b8X1<W013=2/7413=4[^1<^0DP2f6PBP>P9C6R>/2@P>P8O3b5O3b4P11542#01284R1[12421584#0[RB1598#0\11I42P2n2001000000120000000X2<X3<PB^2<^3<P2PCP@PFPEPGPHPIP<P?g00JZ1<<@C;,:IR?99I5P6P?C8P7P3b6b7b8X1<X0D122@,74124@[^1<^0DP213=>P>P8O3b5O3b4CJ3?%LA#0eb=X:<X9<X<;X;:P9P8P4P2O4X:<W9W<W;o"). Qed.



(* [comment removed for export] *)
Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

End CANSEC1.
