(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcSubst AcMALlib AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition F300 : nat := 300.
Definition MCP : Type := MCF.

(* [comment removed for export] *)
Definition KAFTERP : MCP := KAFTERSF.
(* [comment removed for export] *)
Definition P2AW : plan := PRun F3000 [0xd2db0; 0x614b0; 0x639e0] [].
Definition NAF : lin := LIN 0 [(1204%positive, 65536); (1205%positive, 4096)].   (* [comment removed for export] *)
Definition SEG3W : MCP := MSegK 20 P2AW (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x614b0 0 (MAlt MVoid MEnd) KNil)).
Definition RP3W : MCP := MSplitG 0 (0x7fff7000 - 0x12000) (MCall (inr PRP) SEG3W) (MCall (inr PRP) SEG3W).
Definition SEG2W : MCP := MSegK 20 P2AW (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x639e0 0 RP3W (KCons 0x614b0 0 (MAlt MVoid MEnd) KNil))).
Definition RP2W : MCP := MSplitG 0 (0x7fff7000 - 0x12000) (MCall (inr PRP) SEG2W) (MCall (inr PRP) SEG2W).
Definition SEG1W : MCP := MSegK 20 P2AW (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x639e0 0 RP2W (KCons 0x614b0 0 (MAlt MVoid MEnd) KNil))).
Definition RP1W : MCP := MSplitG 0 (0x7fff7000 - 0x12000) (MCall (inr PRP) SEG1W) (MCall (inr PRP) SEG1W).
Definition K2AW (k : MCP) : MCP := MJoin (MSegK 20 P2AW (KCons 0xd2db0 0 (MAlt MVoid MEnd) (KCons 0x639e0 0 RP1W (KCons 0x614b0 0 (MAlt MVoid MEnd) KNil)))) 0xd2db0 k.
Definition P_IT : plan := PRun F300 [0xd2db0; 0xd2de0] [].
Definition K2BP (k1 k2 : MCP) : MCP := MSegK 20 P_IT (KCons 0xd2db0 0 k1 (KCons 0xd2de0 0 k2 KNil)).
Definition LOOPP (kx : MCP) : MCP := MLoopW 12 (MSegK 20 P_IT (KCons 0xd2db0 0 MEnd (KCons 0xd2de0 0 MEnd KNil))) (KCons 0xd2de0 0 kx KNil).
Definition P_TAIL : plan := PRun F3000 [0x614b0; 0x639e0] [].
Definition KTP : MCP := MSegK 20 P_TAIL (KCons 0x614b0 0 MEnd (KCons 0x639e0 0 MEnd KNil)).
(* [comment removed for export] *)
Definition KTPc : MCP := MConcR KTP.
Definition SPL12 (c : Z) (ka kb : MCP) : MCP := MSplitR 12 c ka kb.
Definition KTPS : MCP :=
  SPL12 7 (SPL12 3 (SPL12 1 (SPL12 0 KTPc KTPc) (SPL12 2 KTPc KTPc)) (SPL12 5 (SPL12 4 KTPc KTPc) (SPL12 6 KTPc KTPc)))
          (SPL12 11 (SPL12 9 (SPL12 8 KTPc KTPc) (SPL12 10 KTPc KTPc)) (SPL12 13 (SPL12 12 KTPc KTPc) (SPL12 14 KTPc KTPc))).
Definition P_TOR2 : plan := PRun F8000 [0xd3954; 0x639e0] [].
Definition P_TOCL : plan := PRun F8000 [0xd3954] [].
Definition KTOCLW : MCP := MSegK 20 P_TOCL (KCons 0xd3954 57 MEnd KNil).
Definition KTOR2W : MCP := MSegK 20 P_TOR2 (KCons 0xd3954 63 (MRead IBR 0x10 KTOCLW MEnd) (KCons 0x639e0 0 MEnd KNil)).
Definition KRDW : MCP := MJoin (K2AW (K2BP (LOOPP KTPS) KTPS)) 0x614b0 KTOR2W.
(* [comment removed for export] *)
Definition P_WVO : plan := PJoin F8000 [] 0xca390 PFin [].
Definition P_RETRYO : plan := PRun F3000 [0xca418; 0xca39c] [].
Definition WBOP : MCP := MWritev 0x15f87 (MSegK 20 P_RETRYO (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition KWV : MCP :=
  MJoin (MWritev 0x15f87 (MSegK 20 P_RETRYO (KCons 0xca418 66 (MLoopW 22 WBOP (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c KAFTERP.
(* [comment removed for export] *)
Definition P_TR : plan := PRun F8000 [0x8fe60; 0x61d38] [].
Definition P_FLAG : plan := PRun F3000 [0x8fde0] [].
(* [comment removed for export] *)
Definition KTK (kh kp : nat -> MCP) (n : nat) : MCP :=
  MJoin (MSegK 20 P_FLAG (KCons 0x8fde0 0 MEnd KNil)) 0x8fde0 (MSegK 20 P_TR (KCons 0x8fe60 0 (kh n) (KCons 0x61d38 0 (kp n) KNil))).
Definition KSELK (kh kp : nat -> MCP) : MCP := MSelB (MSelB (KTK kh kp 4) (KTK kh kp 3)) (MSelB (KTK kh kp 2) (KTK kh kp 1)).
Definition KBITSK (kh kp : nat -> MCP) : MCP := MSplitB (hvar 2) 0 0 (MSplitB (hvar 2) 1 0 (KSELK kh kp) (KSELK kh kp)) (MSplitB (hvar 2) 1 1 (KSELK kh kp) (KSELK kh kp)).
Definition KBODYK (kh kp : nat -> MCP) (cl : lin) : MCP := MSplit cl 0 (MSel (KTK kh kp 1) MEnd) (MSel MEnd (KBITSK kh kp)).
Definition P_HDR : plan := PRun F8000 [0x8fc9c; 0x8fd98; 0x8fc80] [].
Definition KHDRBK (kh kp : nat -> MCP) (cl : lin) : MCP := MSegK 20 P_HDR (KCons 0x8fc9c 0 (MSel (MSegK 20 P_WVO (KCons 0xca390 66 MEnd KNil)) MEnd)
                            (KCons 0x8fd98 0 (MSel MEnd (KBODYK kh kp cl)) (KCons 0x8fc80 0 MVoid KNil))).
Definition KCLOSEBK (kh kp : nat -> MCP) : MCP := MClose (MJoin (MSplit (hvar 1) 127 (MSel (KHDRBK kh kp CLA) MEnd) (MSel MEnd (KHDRBK kh kp CLB))) 0xca390 KWV).
(* [comment removed for export] *)
Definition KNONE : nat -> MCP := fun _ => MEnd.
Definition KT : MCP := KTK KNONE KNONE 1.
Definition KCLOSEB : MCP := KCLOSEBK KNONE KNONE.
Definition KRDJB : MCP := MJoin (MSplit (hvar 16) 15 KRDW KRDW) 0xd3954 KCLOSEB.
Definition KM5W : MCP := MSegK 20 P_TO_READ (KCons 0xd3954 63 (MReadH IBR 0x10 6 KRDJB MEnd) (KCons 0x3febc 0 MVoid KNil)).
Definition KM4W : MCP := MSegK 20 P_TO_PUT (KCons 0x81f88 0 (NPUT KM5W) (KCons 0x3febc 0 MVoid KNil)).
Definition KM3W : MCP := MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x20000 11))) KM4W) (KCons 0x44360 0 MVoid KNil)).
Definition KM2W : MCP := MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63a000) KM3W))) KNil).
Definition KOKOB : MCP := MSegK 20 P_MAL_U (KCons 0x82914 0 (NUNW KM2W) (KCons 0x8fd58 0 MVoid KNil)).
Definition KFILEW : MCP := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen MEnd KOKOB) (KCons 0x8fc60 0 MVoid KNil)).
Definition MAINWF : MCP := TOPK KFILEW.
(* [comment removed for export] *)
Definition KRDJBK (kh kp : nat -> MCP) : MCP := MJoin (MSplit (hvar 16) 15 KRDW KRDW) 0xd3954 (KCLOSEBK kh kp).
Definition MAINWFK (kh kp : nat -> MCP) : MCP :=
  TOPK (MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen MEnd
    (MSegK 20 P_MAL_U (KCons 0x82914 0 (NUNW
      (MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63a000)
        (MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x20000 11)))
          (MSegK 20 P_TO_PUT (KCons 0x81f88 0 (NPUT
            (MSegK 20 P_TO_READ (KCons 0xd3954 63 (MReadH IBR 0x10 6 (KRDJBK kh kp) MEnd) (KCons 0x3febc 0 MVoid KNil)))) (KCons 0x3febc 0 MVoid KNil))))
        (KCons 0x44360 0 MVoid KNil)))))) KNil))) (KCons 0x8fd58 0 MVoid KNil)))) (KCons 0x8fc60 0 MVoid KNil))).
Definition S1WF : sst := S1c 6 65535.
Definition SHWF : shp := SH_TOP FILE_W.

Definition mainwf_res : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLMd IMGMd PV 6 65535 false (Some H0) apostF anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] [] MAINWF S1WF M1c FSClosed SHWF A1c.
Definition mainwf_chk : bool := is_some mainwf_res.
