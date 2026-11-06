(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "obj_range"; "sobj"; "valuation"; "ob_base"; "ob_hi"; "ob_lo"; "@Corelib.Init.Datatypes"; "bool"; "false"; "andb"; "fst"; "prod"; "snd"; "true"; "list"; "option"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins.W"; "robj_inw"; "wins_ok"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "le"; "leb"; "lt"; "ltb"; "pow"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "img_ok_rangeb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "caddr"; "img_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@Stdlib.Lists.List"; "existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface MallocLaws Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV DrvPristine.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section W.
Variable segs : list Segment.
Variable C : mconsts.

Definition robj_inw (wins : list (Z * Z)) (o : sobj) : bool := ltac2:(tb__ "0|9|
S3SaLx;M0S7Vo;A1S0S0SaLz;R1G0S9Vo;A1S0G0S8Vo;A1S0S23SeS0S0A2M1G1ScS17SdS0S0R1A3R3A2S17SfS0S0R1A3R2A2A2Llh;Vwins;A3Lhi;S1SbLi;M2S1dS3S3SbLb;La;M3Lop;M4G4S1eG3Lop;M5G5SaS2S3SbLa;Lw;Lsgn;M6S1S3S0SbLk;Li;Ll;M7X3x8Llo;G2G4G4G5G5G6G7X3x8S1SbLp;M8G8X0x3Lz;G2G4G4G5G5G6G7X3x8").

Definition wins_ok (wins : list (Z * Z)) : bool := ltac2:(tb__ "0|3|
S24SeS0S0A2M0G0ScScScS19Z0SdS0S0R1A3M1A2S19G1SfS0S0R1A3M2A2A2S1bG2S1cZ2Z3eA2A2A2S1fVsegs;VC;G1G2A4A2Llh;Vwins;A3").

Lemma robj_inw_sound : ltac2:(tb__ "0|1|
S11SeS0S0A2A1S6S5S0S13SaS16R4A1S10A3S13SaS15R5R3A2S10A3S14S18SdS0S0S4R5R4A2M0A3R3A2S1aR3SfS0S0G0A3A2A2S21Vsegs;VC;R4A3F_;F_;F_;Fa;Fo;Frho;Fwins;").
Proof using .
  intros wins rho o a Hw H Hr. unfold robj_inw in H.
  destruct (ob_base o) as [b| | | | | | |] eqn:Eb; try discriminate. destruct b; try discriminate.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
  apply existsb_exists in H as ([lo' hi'] & Hin & He). cbn [fst snd] in He. apply andb_prop in He as [E1 E2].
  apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst lo' hi'.
  pose proof (proj1 (forallb_forall _ _) Hw _ Hin) as Hc. cbn [fst snd] in Hc.
  apply andb_prop in Hc as [Hc Hf]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [H0 H1].
  apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Eb, El, Eh in Hr. cbn [fst snd eval] in Hr.
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 in Hr by reflexivity.
  rewrite !soff_lit_small in Hr by lia.
  apply img_okb_sound. apply (img_ok_rangeb_sound segs C lo hi a); [lia|lia|exact Hf|lia].
Qed.

Lemma robj_inw_caddr : ltac2:(tb__ "0|1|
S11SeS0S0A2A1S6S22S12S0A1S5S0S13SaS16R6A1S10A3S13SaS15R7R3A2S10A3S14S18SdS0S0S4R7R4A2M0A3R3A2S1aR3SfS0S0G0A3A2A2S20Vsegs;VC;R7R6R4A5F_;F_;F_;Fa;Fo;Fx;FAi;Frho;Fwins;").
Proof using . intros wins rho Ai x o a Hw H Hr. right; left. exact (robj_inw_sound wins rho o a Hw H Hr). Qed.
End W.
