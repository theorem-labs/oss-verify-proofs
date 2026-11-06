(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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

Module AsanSpecF.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition M1c : smodel := MMAIN.
Definition A1c : ast := AMAIN.
Definition H0 : positive := Eval vm_compute in s_next TMAIN.
Definition hvar (k : nat) : lin := lvar (dvar H0 k).
Definition HFACTS (lo hi : Z) : list fact :=
  FRange (hvar 17) 1 4095 :: FRange (hvar 16) lo hi :: List.map (fun k => FRange (hvar k) 0 255) (List.seq 0 16).
Definition S1c (lo hi : Z) : sst := SST (s_pc TMAIN) (s_regs TMAIN) (s_rgs TMAIN) (HFACTS lo hi ++ s_facts TMAIN) (dvar H0 18) (s_resv TMAIN).
(* [comment removed for export] *)
Definition IBF : nat := Eval vm_compute in rg_index (s_rgs TMAIN) 0x607400 O.
(* [comment removed for export] *)
Definition IBR : nat := Eval vm_compute in (IBF + 4)%nat.
Definition ARGC : lin := lvar 5.
Definition LARGV0 : lin := lvar 11.

(* [comment removed for export] *)
Definition USAGE_PRE : list Z := [117;115;97;103;101;58;32].                        (* [comment removed for export] *)
Definition USAGE_SUF : list Z := [32;73;78;80;85;84;10].                            (* [comment removed for export] *)
Definition CANNOT_PRE : list Z := [99;108;105;58;32;99;97;110;110;111;116;32;111;112;101;110;32].   (* [comment removed for export] *)
Definition MSG_SHORT : list Z := [99;108;105;58;32;105;110;112;117;116;32;115;104;111;114;116;101;114;32;116;104;97;110;32;104;101;97;100;101;114;10].
Definition MSG_OVR : list Z := [99;108;105;58;32;99;111;110;102;105;103;95;108;101;110;32;111;118;101;114;114;117;110;115;32;105;110;112;117;116;10].
Definition SH_USAGE : shp := ShEmit [PD 2 (SArgs USAGE_PRE 0 LARGV0 USAGE_SUF) (lconst 0)] 2.
Definition SH_CANNOT : shp := ShEmit [PD 2 (SArgs CANNOT_PRE 1 (hvar 17) [10]) (lconst 0)] 2.
Definition SH_TOP (file : shp) : shp := ShIf ARGC 2 2 (ShAlt2 SH_CANNOT file) SH_USAGE.

(* [comment removed for export] *)
Definition SH_SHORT : shp := ShEmit [PD 2 (SLit MSG_SHORT) (lconst 0)] 2.
Definition SH_OVR : shp := ShEmit [PD 2 (SLit MSG_OVR) (lconst 0)] 2.
Fixpoint zl (n : nat) : list Z := match n with O => [] | Datatypes.S k => 48 :: 10 :: zl k end.
Definition CALLS (n : nat) : shp := ShEmit [PD 1 (SLit (zl n)) (lconst 0)] 0.
Definition BODYC (cl : lin) : shp :=
  ShIf cl 0 0 (CALLS 1) (ShBit (hvar 2) 1 (ShBit (hvar 2) 0 (CALLS 4) (CALLS 3)) (ShBit (hvar 2) 0 (CALLS 2) (CALLS 1))).
Definition T63 : Z := 9223372036854775808.
Definition CLA : lin := Eval vm_compute in ladd (hvar 0) (lscale 256 (hvar 1)).
Definition CLB : lin := Eval vm_compute in laddc CLA (- 32768).
Definition LA : lin := Eval vm_compute in ladd (laddc CLA 5) (lneg (hvar 16)).      (* [comment removed for export] *)
Definition LB : lin := Eval vm_compute in laddc LA (- 32768).
Definition FILE_W : shp := ShIf (hvar 1) 0 127 (ShIf LA 0 T63 SH_OVR (BODYC CLA)) (ShIf LB 0 T63 SH_OVR (BODYC CLB)).

(* [comment removed for export] *)
Definition TOPK {N : Type} (kfile : @mchain N) : @mchain N :=
  MSplit ARGC 1 (MSel MEnd MEnd) (MSplit ARGC 2 (MSel kfile MEnd) (MSel MEnd MEnd)).
End AsanSpecF.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcSubst AcMALlib AcFam2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition NPF : Type := anode2 + pnode.
Definition MCF : Type := @mchain NPF.
Definition apostF : NPF -> sst -> smodel -> ast -> option (sst * smodel * ast) := apostP (apost_alloc2 LIM) (ppostA IMGMd QSITES_P MCSITES_P).
Definition NUNW : MCF -> MCF := MCall (inl (A1 NUnw)).
Definition NPUT : MCF -> MCF := MCall (inl (A1 NPut)).
(* [comment removed for export] *)
Fixpoint jplanF (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c44; 0xca418; 0x82914; 0x81f88; 0xc4798] []
  | Datatypes.S k' => let p := jplanF k' in PJoin F30000 [0x73c44; 0xca418; 0x82914; 0x81f88; 0xc4798; 0x73458; 0x7348c; 0xd3160] 0x632dc p
       [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)]);
        (0xd3160, PLoopW 200 [0xd317c] [(0xd317c, p)])] end.
(* [comment removed for export] *)
Fixpoint jplanFW (k : nat) : plan := match k with
  | O => PRun F30000 [0x73c44; 0xca418; 0x82914; 0x81f88; 0xc4798] []
  | Datatypes.S k' => let p := jplanFW k' in PJoin F30000 [0x73c44; 0xca418; 0x82914; 0x81f88; 0xc4798; 0x73458; 0x7348c] 0x632dc p
       [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)])] end.
(* [comment removed for export] *)
Definition KF5 : MCF := MSegK 40 (jplanF 8) (KCons 0xc4798 94 MExit KNil).
Definition KF4 : MCF := MSegK 40 (jplanF 8) (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x40000 12))) KF5) KNil).
Definition KF3 : MCF := MSegK 40 (jplanFW 10) (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x40000 12))) KF4) KNil).
Definition KF2 : MCF := MSegK 40 (jplanFW 10) (KCons 0x81f88 0 (NPUT KF3) KNil).
Definition KAFTERSF : MCF := MSegK 40 (jplanFW 10) (KCons 0x82914 0 (NUNW KF2) KNil).
Definition WBSF : MCF := MWritev 0x21087 (MSegK 20 P_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition KWSF : MCF := MJoin (MWritev 0x21087 (MSegK 20 P_RETRY (KCons 0xca418 66 (MLoopW 22 WBSF (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c KAFTERSF.
Definition KCLSF : MCF := MSegK 20 P_WV (KCons 0xca390 66 KWSF KNil).
Definition KJSF : MCF := MSegK 20 P_R2 (KCons 0xd3954 63 (MRead IBR 0x10 (MSegK 20 P_R3 (KCons 0xd3954 57 MEnd KNil)) MEnd) (KCons 0xd3954 57 MEnd KNil)).
(* [comment removed for export] *)
Definition P_MAL_U : plan := PJoin F5000 [0x8fd58] 0x82914 PFin [].
Definition P_TO_MMAP1 : plan := PJoin F5000 [] 0x73c44 PFin [].
Definition P_TO_PUT : plan := PJoin F8000 [0x3febc] 0x81f88 PFin [].
Definition KM5 : MCF := MSegK 20 P_TO_READ (KCons 0xd3954 63 (MJoin (MRead IBR 0x10 KJSF MEnd) 0xd3954 (MClose KCLSF)) (KCons 0x3febc 0 MVoid KNil)).
Definition KM4 : MCF := MSegK 20 P_TO_PUT (KCons 0x81f88 0 (NPUT KM5) (KCons 0x3febc 0 MVoid KNil)).
Definition KM3 : MCF := MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x20000 11))) KM4) (KCons 0x44360 0 MVoid KNil)).
Definition KM2 : MCF := MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) KM3)) KNil).
Definition KOKSF : MCF := MSegK 20 P_MAL_U (KCons 0x82914 0 (NUNW KM2) (KCons 0x8fd58 0 MVoid KNil)).
Definition KFILESF : MCF := MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen MEnd KOKSF) (KCons 0x8fc60 0 MVoid KNil)).
Definition MAINSF : MCF := TOPK KFILESF.
Definition S1SF : sst := S1c 0 5.
Definition SHSF : shp := SH_TOP SH_SHORT.
Definition mainsf_res : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLMd IMGMd PV 0 5 false (Some H0) apostF anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] [] MAINSF S1SF M1c FSClosed SHSF A1c.
Definition mainsf_chk : bool := is_some mainsf_res.
