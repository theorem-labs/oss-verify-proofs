(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "sprop"; "SVar"; "SPUle"; "sv"; "sobj"; "ss_next"; "ss_objs"; "ss_facts"; "cell"; "mkObj"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "DUnknown"; "DZero"; "SPAlign"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "app"; "pair"; "prod"; "option"; "true"; "list"; "bool"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SUB"; "ALU_SLL"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "sym_runA"; "axst"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST.NX"; "vMAPn"; "L2"; "B2"; "Bw"; "L1"; "B1"; "F_cls"; "shS"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NS"; "V_MS"; "V_NCH"; "V_PAB"; "msx"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "rstS"; "carveS"; "Bw"; "F_g3"; "F_l2"; "F_map"; "O_1"; "O_2"; "O_blk"; "O_w"; "fx1"; "fx2"; "ru1"; "ru2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "leaf"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST.W"; "genL"; "CT1"; "CT2"; "GS"; "L3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_OFF"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2"; "clz_sv"; "@Stdlib.Lists.List"; "tl"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition rstS (E : axst) (ru : list (nat * sv)) (fx : list sprop) : axst := ltac2:(tb__ "0|0|
S27VE;A1S13S28VE;ScS10R1A1S4dS11R1A1Vru;A2SeR1A1SdR1A1S12R1A1S8R1A1S1aS2S9R1A1Vfx;A3S7R1A1SfR1A1A9A2TS;").

Definition carveS (E : axst) (o : sobj) : axst := ltac2:(tb__ "0|0|
S27VE;A1S13S28VE;ScS10R1A1S11R1A1SeR1A1SdR1A1S12R1A1S1aS6S8R1A1S17S6Vo;S18S6A1A3A3S9R1A1S7R1A1SfR1A1A9A2TS;").

Definition callsub (C Pre : axst) : wsub := ltac2:(tb__ "0|0|
S4eP1S27VC;A1S27VPre;A1A3").
Definition callR (C Pre : axst) (s : wsub) : list sobj := ltac2:(tb__ "0|1|
S1dS1fS6A1M0A1G0Lx;S5fVC;VPre;Vs;A3G0R1LR;S18S6A1X1dx2").
Definition callT (C Pre Pret : axst) (s : wsub) (R : list sobj) : axst := ltac2:(tb__ "0|0|
S60Vs;VPre;VPret;VC;VR;A5").

Definition rotp (n : nat) : list nat := ltac2:(tb__ "0|0|
S1aS19S5bU1Vn;A2S17S19U0S18S19A1A3A3").
Definition afterS (E C T : axst) : axst := ltac2:(tb__ "0|0|
S5eVT;S9S27VC;A1A1A2S2aS28R1S5dS27R1A1S8S27VE;A1A1A2A2TD;").
Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
Definition leafS (i : nat) (l : option (list leafA)) : axst := ltac2:(tb__ "0|1|
S1dS1fS2bA1M0A1S2aLl;Vl;G0S50Vi;R1A2Ll';S50U0S18S2bA1A2X1dx2").

Definition Pret_ms : axst := liftA (P_ret_memset memset_entryA).
Definition Pret_mz : axst := liftA P_msz.

Section NX.
Variable nx : positive.
Definition vMAPn : sv := SVar nx.
Definition shS (e : sv) : sv := ltac2:(tb__ "0|0|
S1S21S1S22Ve;S0Z3A1A3S0S5aA1A3").

Definition F_cls (hi : bool) : list sprop := ltac2:(tb__ "0|2|
S20S1fS2A1Lhi;Vhi;S17S2S4S0S59A1S2cA2S17S2S4S2cS0S4bZ7fffff800000Z12000M0A2A1A2S18S2A1M1A3A3S17S2S4S2cS0S4bS57G0A2A1A2S17S2S4S1S21S2cS3S36A1A3S0S57A1A2G1A3A3X20x2").
Definition F_map (hi : bool) : list sprop := ltac2:(tb__ "0|0|
S1aS2S17S2S16Vnx;ZcA2S17S2S4S0S58A1S2cA2S17S2S4S1S21S2cS3S36A1A3S0Z7fffff800000A1A2S18S2A1A3A3A3S32Vhi;A1A3").

Definition a2e1 : sv := ltac2:(tb__ "0|1|
S1S24S1S21S1S22S1S21S2cS0Zff8A1A3S0Z3A1M0A3S0Z1A1A3S1S22S2cG0A3A3").
Definition B1 : sv := shS vMAPn.
Definition L1 : sv := SLit 512.
Definition O_1 : sobj := ltac2:(tb__ "0|0|
SbS31S0Z0A1S30S18SaA1S14A5").
Definition ru1 : list (nat * sv) := ltac2:(tb__ "0|1|
S17S1cS19S5A2M0S1bS19S5UcS30A4S18G0A1A3").
Definition fx1 : list sprop := [].

Definition a0e2 : sv := ltac2:(tb__ "0|0|
S1S21S1S22S1S23S1S21S1S21S2cS0Z1000A1A3S3S35A1A3S0Zfffffffffffffff8A1A3S0Z3A1A3S0Z7fff8000A1A3").
Definition a2e2 : sv := ltac2:(tb__ "0|1|
S1S24S1S21S1S22S1S21S1S21S39S2cA3S0N8A1A3S0Z3A1M0A3S0Z1A1A3S1S22S1S23S1S21S1S21S2cS0Z1000A1A3S3S35A1A3S0Zfffffffffffffff8A1A3G0A3A3").

Definition BR : sv := ltac2:(tb__ "0|0|
S1S21S33S2cA1S1S21S1S22S3S35A1S0Z3A1A3S0Z100A1A3A3").
Definition B2 : sv := SAlu ALU_ADD BR (SLit 256).
Definition L2 : sv := ltac2:(tb__ "0|1|
S1S24S1S22S3S36A1S0Z3A1M0A3S1S21S1S22S3S35A1G0A3S0Z200A1A3A3").
Definition O_2 : sobj := ltac2:(tb__ "0|0|
SbS2eS0Z0A1S2dS18SaA1S14A5").
Definition ru2 : list (nat * sv) := ltac2:(tb__ "0|1|
S17S1cS19S5A2M0S1bS19S5UaS2eA4S17G0S1bS19S5UcS2dA4S18G0A1A3A3").
Definition fx2 : list sprop := ltac2:(tb__ "0|0|
S17S2S4S2dS0Z1ffA1A2S18S2A1A3").

Definition F_g3 : list sprop := ltac2:(tb__ "0|1|
S17S2S4S3S37A1S0S4bS4cZ2M0Z14A2G0A2A1A2S18S2A1A3").
Definition Bw : sv := ltac2:(tb__ "0|0|
S1S21S3S38A1S1S25S3S37A1S0Z3A1A3A3").
Definition O_w : sobj := ltac2:(tb__ "0|0|
SbS2fS0Z0A1S0Z8A1S18SaA1S14A5").
Definition O_blk : sobj := ltac2:(tb__ "0|0|
SbS2fS0Z0A1S0Z20000A1S18SaA1S15A5").

Definition a0e3 : sv := ltac2:(tb__ "0|0|
S1S23S1S21S1S25S3S37A1S0Z3A1A3S3S38A1A3S0Zfffffffffffff000A1A3").

Definition x11e3 : sv := ltac2:(tb__ "0|0|
S1S26S61S39A1S0Z3fA1A3").
Definition F_l2 (v : positive) : list sprop := ltac2:(tb__ "0|1|
S17S2S4S0Z10A1S3Vv;A1M0A2S17S2S4G0S0Z28A1A2S18S2A1A3A3").
End NX.

Section W.
Variables (W : list ulink) (st : ustop) (tmax : Z) (hi : bool).
Let nx : positive := ltac2:(tb__ "0|0|
S3bVW;Vst;Vtmax;A3").

Definition GS : positive := Pos.succ nx.

Definition T0 : axst := ltac2:(tb__ "0|0|
S4fS41Vnx;Vhi;A2S3aVW;Vst;Vtmax;A3A2").

Definition runT0 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S29S4aUfa0S17S34S51S18S34A1A3VT;S1eA5").
Definition CT1 (E : axst) : axst := ltac2:(tb__ "0|0|
S3cVE;S48S46A3").
Definition CO1 (E : axst) : axst := ltac2:(tb__ "0|0|
S3dS53VE;A1S42Vnx;A1A2").

Definition CT2 (E : axst) : axst := ltac2:(tb__ "0|0|
S3cVE;S49Vnx;A1S47A3").
Definition CO2 (E : axst) : axst := ltac2:(tb__ "0|0|
S3dS54VE;A1S43Vnx;A1A2").

Definition U2p (E : axst) : axst := ltac2:(tb__ "0|0|
S3cVE;S18S1cS19S5A2A1S3fA3").
Definition runT2 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S29S4aUfa0S17S34Z706a0S17S34Z410f0S18S34A1A3A3VT;S1eA5").

Definition CS3a (E : axst) : axst := ltac2:(tb__ "0|1|
S3cVE;S17S1cS19S5A2M0S1bS19S5UaS3eA4S18G0A1A3S18S2A1A3").
Definition G3a (E : axst) : axst := ltac2:(tb__ "0|1|
S28VE;S5cS27VE;A1M0S3eS1aS6S8G0A1S17S6S44S18S6A1A3A3S7G0A1A4A2").
Definition runT3a (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S29S4aUfa0S17S34Z410f0S18S34A1A3VT;S1eA5").

Definition genL (E : axst) : axst := ltac2:(tb__ "0|2|
S27VE;A1S13S28VE;ScS10R1A1S4dS11R1A1S17S1cS19S5A2M0S1bS19S5UbS3S7R1A1M1A1A4S18G0A1A3A2SeR1A1SdR1A1S12R1A1S8R1A1S9R1A1S63G1A1SfR1A1A9A2TS;").
Definition L3 (E : axst) : axst := ltac2:(tb__ "0|0|
S4fS40S7S27VE;A1A1A1S52VE;A1A2").
Definition L3b (E : axst) : axst := ltac2:(tb__ "0|0|
S3dS56VE;A1S45A2").
Definition subL (E : axst) : wsub := ltac2:(tb__ "0|0|
S4eS55S27VE;A1S27S52VE;A1A1A3").

Definition runT4 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S29S4aUfa0S17S34Z3c614S18S34A1A3VT;S1eA5").
Definition dropF (E : axst) : axst := ltac2:(tb__ "0|0|
S27VE;A1S13S28VE;ScS10R1A1S11R1A1SeR1A1SdR1A1S12R1A1S8R1A1S62S2S9R1A1A2S7R1A1SfR1A1A9A2TS;").
End W.

