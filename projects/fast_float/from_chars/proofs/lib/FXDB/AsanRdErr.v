(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChAdd FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDir FxWvC FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC.FxChDirDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart AsanFinC AsanTblAll.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode AsanQSites FxHNodes FxDirConv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxHNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxDirConv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition F3000 : nat := 3000.
Definition F5000 : nat := 5000.
Definition F8000 : nat := 8000.
Definition F30000 : nat := 30000.

(* [comment removed for export] *)
Definition TBLR : tree xi := AsanTblAll.TBLA.      (* [comment removed for export] *)
Definition IMGR : tree Z := mk_img_runs U_WR TEmpty.

(* [comment removed for export] *)
Definition QSITES : list qsite := [QS_PRINTF; QS_MEMCHR; QS_STRNLEN; QS_MEMCPY_S; QS_MEMCPY_D].
Definition MCSITES : list Z := [MC_PCW].
Definition apostR (nk : hnode) (S : sst) (M : smodel) (a : unit) : option (sst * smodel * unit) := hpost IMGR QSITES MCSITES nk S M a.
Definition anilR (a : unit) : bool := true.
Definition aeqbR (a b : unit) : bool := true.
Definition awfR (n : positive) (a : unit) : bool := true.
Definition HAR (E : valu) (M : smodel) (a : unit) (m0 : word -> option byte) : Prop := True.
Definition acopyR (a : unit) : list srec := [].
Definition MC : Type := @mchain hnode.
Definition MK : Type := @mks hnode.

(* [comment removed for export] *)
Definition F0 : sst * smodel := List.nth 0 FINC (S0c 176 4080 5, M0).
Definition S1 : sst := fst F0.
Definition M1 : smodel := snd F0.
Definition PV : lin := lvar 8.
(* [comment removed for export] *)
Definition RANDP16 : lin := {| l_c := 8; l_t := [(1%positive, 32768); (2%positive, 4096); (7%positive, 64); (15%positive, 8)] |}.
Definition SZR : lin := lsub RANDP16 PV.
Definition FARGC : fact := FRange (lvar 5) 2 2.
Definition FV8 : fact := FRange PV 140735332483072 140737488355326.
Definition FV8SP : fact := FRange (lsub PV (sm_sp M1)) 0 4194304.
Definition FRND : fact := FRange SZR 18 2400000.
Definition FSR : list fact := [FARGC; FV8; FV8SP; FRND].
Definition drop_rand (R : region) : bool := lin_eqb (rg_base R) (laddc RANDP16 (-16)).
Definition SR0 : sst := conv_post S1 drop_rand FSR PV SZR [46; 0].
Definition MR0 : smodel := frz_clear M1.

(* [comment removed for export] *)
Definition MSG_CO : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 46; 10].
Definition MSG_RD : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 46; 10].
Definition SHD : shp := ShAlt2 (ShEmit [PD 2 (SLit MSG_CO) (lconst 0)] 2) (ShEmit [PD 2 (SLit MSG_RD) (lconst 0)] 2).

(* [comment removed for export] *)
Definition IB : nat := 69.
Definition P_OPEN : plan := PJoin F3000 [0x8fc54] 0xd51d0 PFin [].
Definition P_MALLOC : plan := PJoin F5000 [0x8fd4c] 0x73c38 PFin [].
Definition P_TO_MMAP : plan := PJoin F5000 [] 0x73c38 PFin [].
Definition P_TO_READ : plan := PJoin F8000 [] 0xd51d0 PFin [].
(* [comment removed for export] *)
Definition STOPS : list Z := [0x5329c; 0x51c2c; 0x5077c; 0x61420; 0x61468; 0xd4478; 0xcbc0c; 0xcbc94].
Definition PST : plan := PRun F30000 STOPS [].
(* [comment removed for export] *)
Definition B0R : lin := {| l_c := 18446744073709551024; l_t := [(1%positive, 32768); (2%positive, 4096); (3%positive, 64); (4%positive, 16)] |}.
Definition P_RETRY : plan := PRun F3000 [0xcbc94; 0xcbc18] [].
Definition P_EXIT : plan := PRun F30000 [0xcbc0c; 0xcbc94; 0xc6014; 0xd51d0] [].
Definition KAFTER : MC := MSegK 40 P_EXIT (KCons 0xc6014 94 MExit KNil).
Definition WB2 : MC := MWritev2 B0R (MSegK 20 P_RETRY (KCons 0xcbc94 66 MEnd (KCons 0xcbc18 0 MEnd KNil))).
Definition KWL : MC := MJoin (MWritev2 B0R (MSegK 20 P_RETRY (KCons 0xcbc94 66 (MLoopW 22 WB2 (KCons 0xcbc18 0 (MPop MEnd) KNil))
                                                               (KCons 0xcbc18 0 (MPop MEnd) KNil)))) 0xcbc18 KAFTER.
Definition KW : MC := KWL.
(* [comment removed for export] *)
Definition NODE (nk : hnode) (k : MC) : MC := MAlt (MCall nk k) k.
(* [comment removed for export] *)
Definition KSTG (n : nat) (stops : list Z) (ends : MK) : MC := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 stops []) (KCons 0x5329c 0 (NODE (HQC 0) k) (KCons 0x51c2c 0 (NODE (HQC 1) k) (KCons 0x5077c 0 (NODE (HQC 2) k)
                   (KCons 0x61420 0 (NODE (HQC 3) k) (KCons 0x61468 0 (NODE (HQC 4) k) (KCons 0xd4478 0 (NODE (HMC 0) k) ends))))))) MEnd.
(* [comment removed for export] *)
Definition STOPS_A : list Z := [0x5329c; 0x61420; 0x61468; 0xd4478; 0x51bfc; 0xcbc0c; 0xcbc94].
Definition KSTA (n : nat) : MC := Nat.iter n (fun k =>
      MSegK 20 (PRun F30000 STOPS_A []) (KCons 0x5329c 0 (NODE (HQC 0) k) (KCons 0x61420 0 (NODE (HQC 3) k) (KCons 0x61468 0 (NODE (HQC 4) k)
                   (KCons 0xd4478 0 (MCall (HMC 0) MEnd) (KCons 0x51bfc 0 MEnd KNil)))))) MEnd.
(* [comment removed for export] *)
Definition STOPS_B : list Z := [0x5329c; 0x51c2c; 0x5077c; 0x61420; 0x61468; 0xd4478; 0xcbc0c; 0xcbc94; 0xcd728].
Definition F6 : nat := 6.
Definition F8 : nat := 8.
Definition KJOIN (kc : MC) : MC := MJoin (KSTA F8) 0x51bfc (MJoin (KSTG F6 STOPS_B (KCons 0xcd728 0 MEnd KNil)) 0xcd728 kc).
(* [comment removed for export] *)
Definition KTAIL : MC := KJOIN (KSTG F6 STOPS (KCons 0xcbc0c 66 KW KNil)).
Definition KOK : MC :=
  MSegK 20 P_MALLOC (KCons 0x73c38 222
    (MChain (CNode (NNull 0x12000 GE true true false) (COp (TSepW 0 12) CEnd))
      (MSegK 20 P_TO_MMAP (KCons 0x73c38 222
         (MChain (CNode (NFixNew 0x20000 11) CEnd)
           (MSegK 20 P_TO_READ (KCons 0xd51d0 63 (MReadDir KTAIL) (KCons 0x401d8 0 MVoid KNil)))) (KCons 0x4467c 0 MVoid KNil))))
    (KCons 0x8fd4c 0 MEnd KNil)).
(* [comment removed for export] *)
Definition KERR : MC := KTAIL.
Definition RDCH : MC := MSegK 20 P_OPEN (KCons 0xd51d0 56 (MOpenDir KERR KOK) (KCons 0x8fc54 0 MVoid KNil)).

(* [comment removed for export] *)
Definition rd_res : option (list (sst * smodel * fstate * shp * unit)) :=
  mcheck ASEGS LIM TBLR IMGR PV 0 0 true None apostR anilR aeqbR awfR acopyR asub_id agok_t alins_nil aset_id amod_t [] [] RDCH SR0 MR0 FSClosed SHD tt.
Definition is_some {X} (o : option X) : bool := match o with Some _ => true | None => false end.
Definition rd_chk : bool := is_some rd_res.
(* [comment removed for export] *)
