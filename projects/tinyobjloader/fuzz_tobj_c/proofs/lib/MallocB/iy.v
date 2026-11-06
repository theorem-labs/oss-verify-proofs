(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel RefillModelP RefillBits io j4 CRefillJ DrainModel.

(* [comment removed for export] *)
Module F0A_inst.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "app"; "nil"; "list"; "true"; "bool"; "None"; "false"; "Some"; "option"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "SVar"; "FcsrFrm0"; "mkSS"; "sprop"; "swf"; "valuation"; "DUnknown"; "cell"; "eval"; "mkObj"; "agree_below"; "rm"; "rw"; "soff"; "sprop_below"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "div"; "opp"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "ae_free"; "Pre_freeI"; "ulink"; "A_globals"; "GOT_HI"; "GOT_LO"; "J_free_preT"; "KcA"; "RTC_HI"; "RTC_LO"; "UStopLeOrPc"; "V_FREE_A1"; "free_depth"; "mkA"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "ustop"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "seqN"; "NFS"; "NRT"; "NV"; "sa_f"; "O_pad"; "XI"; "instF_facts"; "sb_f"; "sc_f"; "sd_f"; "se_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "NF"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXMerge"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "QG"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "O_sh"; "qvar"; "cA"; "O_blkN"; "RT_f"; "VOBJ"; "cQ"; "cp_baseF"; "iam_base"; "vHW"; "vMINq"; "vN8"; "vNLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "DPMCELL"; "MLIMCELL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "cells_in_view"; "cells_inside"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "P0_fc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineCacheMax"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "vQB"; "item_base"; "nb_base"; "vBS"; "vCP"; "vCS"; "vK"; "vMX"; "vNX"; "vPK"; "vQF"; "vQN"; "vQS"; "vSB"; "vST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit"; "N_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst.Iface"; "zone_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst.States"; "sd_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI";
"stopJ_stable"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition NRT : list carve_spec := ltac2:(tb__ "0|19|
S1S3S3S3S10SeA2M0SeA2M1S6S3S3SeS2A2M2S10A2M3A1M4A2M5S0G1G4S0G0SeS0S10SeS12Z0A1M6Z17db48M7A4Z17db4aA4S1G3S0G2S10S0SeS2G7U1M8A4S12Z1M9A1A4S1G3S0G2S10S0SeS2Z17db49G8A4G6A4S5G3A1MaA3A3A4S4S2dS90S1G5S0G1G4S0G0SeS0S10SeG6Z17fcd8MbA4Z17fcdcA4S1G3S0G2S10S0SeS2GbU4McA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z17fbdcMdA4Z17fbe0A4S1G3S0G2S10S0SeS2GdGcA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6S6bA4S23S6bG9A2A4S1G3S0G2S10S0SeS2S6bG8A4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6S6cA4S23S6cZ8A2A4S1G3S0G2S10S0SeS2S6cU8MeA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z17fb80MfA4Z17fb90A4S1G3S0G2S10S0SeS2GfGeA4G6A4S1G3S0G2S10S0SeS2Z17fb88GeA4G6A4GaA3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Ze6780M10A4Ze6788A4S1G3S0G2S10S0SeS2G10GeA4S12Zdb004A1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z17fc60M11A4Z17fc68A4S1G3S0G2S10S0SeS2G11GeA4S12ZffffffffffffffffA1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeb8e4M12A4Zeb8f0A4S1G3S0G2S10S0SeS2G12GcA4S12Z1000A1A4S1G3S0G2S10S0SeS2Zeb8e8GcA4G6A4S1G3S0G2S10S0SeS2Zeb8ecGcA4S12ZbeA1A4GaA3A3A3A4S1G5S0G1G4S0G0SeS0S10SeG6S23S59Z50A2M13A4S23S59Z58A2A4S1G3S0G2S10S0SeS2G13GeA4S12S7cA1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6S23S59Z40A2M14A4G13A4S1G3S0G2S10S0SeS2G14GeA4S12S7dA1A4S1G3S0G2S10S0SeS2S23S59Z48A2GeA4S68A4GaA3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeaa78M15A4Zeaa80A4S1G3S0G2S10S0SeS2G15GeA4S8bA4GaA3A4S1G5S0G1G4S0G0SeS0S10SeS75Zad0A4Zae0A4GaA4S1G5S0G1G4S0G0SeS0S10SeS60Za10M16A4Za18A4S1G3S0G2S10S0SeS2G16GeA4S8cA4GaA3A4S1G5S0G1G4S0G0SeS0S10SeS75Zae8A4Zc60A4GaA4S1G5S0G1G4S0G0SeS0S10SeS66Zef2c8M17A4Zef2d0A4S1G3S0G2S10S0SeS2G17GeA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeS13PcA1N10M18A4N8A4S1G3S0G2S10S0SeS2G18GcA4S67A4S1G3S0G2S10S0SeS2NcGcA4S6aA4GaA3A3A4S5G5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition NV (q : qvar) : list carve_spec := ltac2:(tb__ "0|19|
S5fS6S2dA1Lq;Vq;S1S3S3S3S10SeA2M0SeA2M1S6S3S3SeS2A2M2S10A2M3A1M4A2M5S0G1G4S0G0SeS0S10SeS64Z0M6A4Z20M7A4M8S1G3S0G2S10S0SeS2G6U8M9A4MaS89A4S1G3S0G2S10S0SeS2Z8G9A4MbS88A4S1G3S0G2S10S0SeS2Z10G9A4McS7eA4S1G3S0G2S10S0SeS2Z18MdG9A4S8aA4S5G3A1MeA3A3A3MfA3A4M10S1G5S0G1G4S0G0SeS0S10SeS7eG6A4GdA4M11S1G3S0G2S10GaS86A4M12S1G3S0G2S10GbS81A4M13S1G3S0G2S10GcS84A4GeA3A3A3A4S1G5S0G1G4S0G0SeS0S10SeS7fGdA4G7A4GeA4S5G5A1M14A3A3A3S1G5S0G1G4G8S1G3S0G2S10GaS12G6A1A4GfA3A4S1G5S0G1G4S0G0SeS0S10SeS60Z780M15A4Z790M16A4S1G3S0G2S10S0SeS2G15U4M17A4S87A4S1G3S0G2S10S0SeS2Z784G17A4S85A4S1G3S0G2S10S0SeS2Z788G9A4S83A4GeA3A3A3A4S1G5S0G1G4S0G0SeS0S10SeS65G16A4Z794A4S1G3S0G2S10S0SeS2G16G17A4S82A4GeA3A4S1G5S0G1G4S0G0SeS0S10SeS80G6A4Z2000A4GeA4G14A3A3A3M18A3S1G5G10S1G5S0G1G4G11S1G3G12S1G3G13S1G3S0G2S10GcS12Z3fdA1A4GeA3A3A3A4G18A3A3X5fx3").
Definition NFS (q : qvar) : list carve_spec := NRT ++ NV q.

Definition O_pad : sobj := ltac2:(tb__ "0|0|
S1cS13PcA1S13PdA1S69S5S1aA1S19A5").

Lemma NRT_ok : ltac2:(tb__ "0|0|
S29S6S11A1S4S11S43S2dS11S2eS46A4S1S11S5eS1S11S61S5S11A1A3A3A3S62A3").
Proof. reflexivity. Qed.
Lemma NV_ok : ltac2:(tb__ "0|0|
S5fS29S6S11A1S43S2dS11S2eS47R1A1A4S63R1A1A3Fq;").
Proof. destruct q; reflexivity. Qed.

Section States.
Variable khi : bool.
Variables (W : list ulink) (st : ustop) (q : qvar).
Let REGS : list sv := ltac2:(tb__ "0|1|
S53S52S1S3S2S10A2M0S0S2S10U4S12S74A1A4S1G0S0S2S10UbS13S3bA1A4S5G0A1A3A3A2").
Let PREOBJS : list sobj := ltac2:(tb__ "0|0|
S1S11S3fS4S11S41VW;A1S4S11S1S11S1cS13PcA1S12Z0A1S13PdA1S5S1aA1S19A5S5S11A1A3S33A3A3A3").
Let PREFACTS : list sprop := ltac2:(tb__ "0|0|
S4S16S40VW;Vst;A2S3eS3cA1A3").

Definition sa_f : sstate := ltac2:(tb__ "0|0|
S15S30S2fA1VREGS;S50S14S9S10A1VPREOBJS;VPREFACTS;S51SaA9").

Definition sb_f : sstate := ltac2:(tb__ "0|0|
S15S30S2fA1VREGS;S50S14S9S10A1S4S11VPREOBJS;S43S2dS11S2eS45Vq;A1A4A3VPREFACTS;S58SaA9").

Definition sc_f : sstate := ltac2:(tb__ "0|0|
S15S30S2fA1VREGS;S50S14S9S10A1S4S11S4S11VPREOBJS;S43S2dS11S2eS45Vq;A1A4A3S1S11S5eS5S11A1A3A3VPREFACTS;S58SaA9").
Definition sd_f : sstate := ltac2:(tb__ "0|1|
S15S30S2fA1VREGS;S50S14S9S10A1S4S11S4S11S4S11VPREOBJS;S43S2dS11S2eS45Vq;A1A4A3S1S11S5eS5S11A1M0A3A3S1S11S49G0A3A3VPREFACTS;S58SaA9").

Definition se_f : axst := ltac2:(tb__ "0|0|
S3dS8fS92S76Vkhi;VW;Vst;Vq;A4A2S5S3S10S10A2A1A2").
End States.

Definition seqN (s n : nat) : list nat := seq s n.
Definition XI (nW : nat) (q : qvar) : list axform := ltac2:(tb__ "0|7|
SdS2dS46A2S2SdS2dS47Vq;A1A2S2S2cU4VnW;A2S2S2cS2cS2cR1R3A2R2A2U1M0A2S2S2cG0VnW;A2M1S2S1S54S55S4S2S44U0M2S2cU2VnW;A2M3A2S4S2S1S2R2S5S2A1M4A3S44G3S2cS2cR5R4A2U3M5A2A2A3A3A1S1S54S56R1A1S1S54S55S4S2S44G2G1A2S4S2S1S2G3S1S2S2cG5VnW;A2G4A3A3S4S2S44R3R5A2S4S2S1S2S2cS2cR3R5A2M6R4A2G4A3S4S2S1S2R1G4A3S44G6R4A2A3A3A3A3A3A1S5S54A1A3A3A3Tiblk;Tipad;Tn0;Tnv;Tnrt;").

Section Iface.
Let segs : list Segment := segsA.

Definition carve_ok (rho : valuation) (k : carve_spec) : Prop := ltac2:(tb__ "0|8|
S3S3S3S10SeA2M0SeA2M1S6S3S3SeS2A2S10A2A1M2A2OLk;Vk;G1G2G1OLp;R2G0SeG0OLp0;R2S10SeS5cQ40M3S1bVrho;R2A2A2SeS28S22S27S25Z2M4Z3eA2M5A1R2A2S28S22R2R4A2S28S24R4G5A2S28S22Z0S23R1R2A2A2S28S22S23R1R4A2S25G4Z40A2A2S28S72R2R4R6A3S28SeS28S22R3R1A2S24R1R5A2A2S28S29S8S73Vsegs;S1eVrho;A1M6S5aG3S23R3R2A2A2A3S7A3S2bS5bQ8A1M7G7S29ScG7A1S70Vsegs;G6S5aG3S23R4R3A2A2A3SbG7R1A2A3Lx;A2A2F_;Foff;S71Vrho;S70Vsegs;G6A2R1R6A4A2A2A2A2A2A2A2Tb;Llo;Lbase;X3x1Lhi;Lp0;X3x1Lcs;Lp;X3x1").

Definition zone_ok (top p n8 lo hi : Z) : Prop := ltac2:(tb__ "0|0|
S28S22Vlo;Vhi;A2S2aS28S22Ze1000Vlo;A2S28S22Vhi;S78A2S28S2aS22Vhi;S35A2S22S34Vlo;A2A2S2aS22Vhi;S39A2S22S38Vlo;A2A2A2A2A2S28S22Z1000Vlo;A2S28S22Vhi;Vtop;A2S28S2aS22Vhi;S79A2S22S78Vlo;A2A2S28S2aS22Vhi;S7bA2S22S7aVlo;A2A2S2aS22Vhi;Vp;A2S22S23Vp;Vn8;A2Vlo;A2A2A2A2A2A2A2A2").
Definition spec_zone (rho : valuation) (top p n8 : Z) (k : carve_spec) : Prop := ltac2:(tb__ "0|3|
S3S3S3S10SeA2M0SeA2M1S6S3S3SeS2A2S10A2A1M2A2OLk;Vk;G1G2G1OLp0;R2G0SeG0OLp1;R2S10SeS5cQ40S1bVrho;R2A2A2SeS91Vtop;Vp;Vn8;S23R1R2A2S23R1R4A2A5Tb;Llo;Lbase;X3x1Lhi;Lp1;X3x1Lcs;Lp0;X3x1").

Record instF_facts (khi : bool) (W : list ulink) (st : ustop) (q : qvar) (rho1 : valuation) (if_p if_n if_n8 if_top : Z) : Prop := mkIF {
  if_p12 : rw rho1 12%positive = Z_to_bv 64 if_p;
  if_n13 : rw rho1 13%positive = Z_to_bv 64 if_n;
  if_105 : rw rho1 105%positive = Z_to_bv 64 if_n8;
  if_106 : rw rho1 106%positive = Z_to_bv 64 (if_n8 / 8);
  if_pn : blk_geo if_p if_n8 /\ if_p mod 16 = 0 /\ 1 <= if_n /\ if_n <= if_n8 /\ if_n8 mod 8 = 0 /\ if_n8 < if_n + 8 /\ if_p + if_n8 <= if_top
          /\ if_top <= 140737479966720;
  if_carve : Forall (carve_ok rho1) (NFS q);
  if_zone : Forall (spec_zone rho1 if_top if_p if_n8) (NFS q);
  if_pd : SymState.pairwise_disjoint rho1 (map carve_obj (NFS q));

  if_sh : forall z, Sh if_p <= z < Sh if_p + if_n8 / 8 -> exists x, rd_of segs (rm rho1) (Z_to_bv 64 z) = Some x;
  if_padm : forall z, if_p + if_n <= z < if_p + if_n8 -> exists x, rd_of segs (rm rho1) (Z_to_bv 64 z) = Some x;

  if_facts : Forall (holds rho1) (F_geom_fn ++ tl (F_pc khi) ++ F_cas ++ VFACT q);

  if_rig : forall rho, agree_vals NF rho rho1 -> rigF rho rho1 }.
End Iface.

Section INST.
Let segs : list Segment := segsA.
Variable khi : bool.
Variable nW : nat. Variable st : ustop. Variable q : qvar.
Let W : list ulink := Wcan nW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S36VAInv;VW;Vst;VA;VKc;A5").

Hypothesis Wa : ltac2:(tb__ "0|0|
S29S8S17S48VW;Vst;A2A1S7A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S29ScS3S6S3S10S10A2M0A1M1S6S16A1M2A2M3A1S8eS6fS31S2fVW;Vst;A3A1S48VW;Vst;A2A2SbG3S0G1G2S1G0S0S10S10S13P18A1S12S74A1A4S5G0A1A3S5S16A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S29S8S17S4cVW;Vst;Vq;A3A1S7A3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S29S8S17S4dVW;Vst;Vq;A3A1S7A3").
Hypothesis Wd : ltac2:(tb__ "0|0|
S29S8S17S4eVW;Vst;Vq;A3A1S7A3").
Hypothesis Fe : ltac2:(tb__ "0|0|
S29S8S99S16S21S58A1S76Vkhi;VW;Vst;Vq;A4A3S7A3").
Hypothesis AXI : ltac2:(tb__ "0|0|
S29ScS6eA1S57S4fVkhi;VW;Vst;Vq;A4S4aVnW;Vq;A2A2SbS6eS77Vkhi;VW;Vst;Vq;A4A2A3").

Lemma bv_signed_small : ltac2:(tb__ "0|1|
SeS28S22Z0R1A2S24R1S25Z2Z3fA2A2A2S29SeS5dQ40M0S5aG0R2A2A2R2A3F_;Fz;").
Proof.
  intros z Hz. rewrite bv_signed_U, u64_lit by lia. unfold Zsigned, H63v, M64v. destruct (Z.ltb_spec z 9223372036854775808); lia.
Qed.
Lemma div8_sum_le : ltac2:(tb__ "0|2|
SeSeS22Z0R2A2M0G0S22S23S26R4Z8M1A2S26R3G1A2A2S26S23R4R3A2G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
  apply Z.div_le_lower_bound; lia.
Qed.
Lemma soff_var : ltac2:(tb__ "0|1|
S18SfSeS29S5bQ40M0A1S1fR3R2A2S5aG0R1A2A3S28S22Z0R2A2S24R2S25Z2Z3fA2A2A2S29SeS20R5S13R4A1A2R3A3F_;F_;Fz;Fi;Frho;").
Proof. intros rho i z E Hz. unfold soff. cbn [eval]. rewrite E. apply bv_signed_small. exact Hz. Qed.

Theorem f_instantiate : ltac2:(tb__ "0|0|
S95S37S18S18S6S5bQ40A1A1S8dSeSeSeS29S42Vst;S3aA3S29S6S32A1VW;S5S32A1A3F_;S98VW;Vst;A2S1dS51R9R8A3S4bVkhi;VW;Vst;Vq;R9R6R5R4S97S96RcA1A1A9S6dVsegs;VJ;RdRcA2S31S2fVW;Vst;A3RbR9R8A6S28S94RcRbA2S6dVsegs;S93VnW;Vst;S7ReRdRbA6S77Vkhi;VW;Vst;Vq;A4RbRaR9A6A2F_;F_;F_;F_;F_;Fn8;Fn;Fp;Fw;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp w p n n8 HW HUS Hag IFF H.
  destruct IFF as [E12 E13 E105 E106 Hpn Hcarve Hzone Hpd Hsh Hpadm Hfacts Hrig].
  split; [exact (Hrig rho (agree_below_vals _ _ _ Hag))|]. unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hpn.
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  pose proof HA as (HG & _).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.

  assert (H1 : SPA segs (J A Kc) (Pre_freeI AE_A W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|exact Hag]; cbv; discriminate | apply (JFr_agree nW st true A Kc rho rho1); [exact HUS | exact Hag]]. }
  clear H HsmA.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by (symmetry; apply (proj1 Hag); unfold NF; lia).

  pose proof (proj2 H1) as (_ & _ & _ & _ & _ & _ & Htop1).
  assert (TOPlo : TOP <= fst (obj_range rho1 stack_win)) by exact Htop1.

  assert (H2 : SPA segs (J A Kc) (mkAX (sa_f W st) [] base_sv) rho1 tp w).
  { change (mkAX (sa_f W st) [] base_sv) with (ax_setS (Pre_freeI AE_A W st) (sa_f W st)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H1].
    constructor; [|constructor]. cbn [fst snd eval]. rewrite E24. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H1.

  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_f]; apply in_or_app; right; cbn; tauto).
  destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W'] eqn:EW; [constructor|].
    destruct st; [|discriminate (HW eq_refl)].
    assert (HC : Forall (holds rho1) (chain_pre (l :: W'))).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_f]. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }

  pose proof (urange (rw rho1 12%positive)) as U12. pose proof (urange (rw rho1 13%positive)) as U13.
  assert (Ep : bv_unsigned (rw rho1 12%positive) = p) by (rewrite E12; apply u64_lit; lia).
  assert (En : bv_unsigned (rw rho1 13%positive) = n) by (rewrite E13; apply u64_lit; lia).

  assert (H3 : SPA segs (J A Kc) (mkAX (sb_f W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sb_f W st q) [] base_sv) with
      (ax_setS (mkAX (sa_f W st) [] base_sv) (let S := ax_S (mkAX (sa_f W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj (NFS q)) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as C.
      destruct k as [[[base lo] hi] cs]. unfold carve_ok in C. cbn zeta in C |- *.
      destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 _)))))))). apply xwords_clear_nil.
    -
      apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
      pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
      destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
      destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia.
      set (b := bv_unsigned (eval rho1 base)) in *.
      cbn [ss_objs ax_S sa_f]. unfold A_globals, O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI, IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
      apply Forall_cons.
      { unfold ranges_disjoint. destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; lia. }
      apply Forall_app. split.
      { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
      apply Forall_cons.
      { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
        rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
    - exact Hpd. }
  clear H2.

  assert (Hshb : bv_unsigned (eval rho1 shb) = Sh p).
  { unfold shb. rewrite U_add, U_srl_lit, U_lit. cbn [eval]. rewrite Ep. change (3 mod 64) with 3. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF, M64v. change (2147450880 mod 18446744073709551616) with 2147450880.
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound p 8 (2 ^ 47 / 8) ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small; [reflexivity | lia]. }
  assert (SH1 : 2147450880 <= Sh p) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia).
  assert (SH2 : Sh p + n8 / 8 <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (div8_sum_le p n8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + n8) 140737479966720 8 ltac:(lia) ltac:(lia)) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  assert (SH3 : 0 <= n8 / 8) by (apply Z.div_pos; lia).
  assert (H4 : SPA segs (J A Kc) (mkAX (sc_f W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sc_f W st q) [] base_sv) with
      (ax_setS (mkAX (sb_f W st q) [] base_sv) (let S := ax_S (mkAX (sb_f W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj shb (SLit 0) vN8g [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SLit 0) = 0) by (apply soff_lit_small; lia).
    assert (Ehi : soff rho1 vN8g = n8 / 8).
    { unfold vN8g. apply (soff_var rho1 106%positive (n8 / 8) E106). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w shb (SLit 0) vN8g NW2 H3 Wc (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Hshb; try lia.
    -
      cbn [ss_objs ax_S sb_f]. apply Forall_app. split.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
          rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
    - intros a Ha. destruct (Hsh a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H3.

  assert (H5 : SPA segs (J A Kc) (mkAX (sd_f W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sd_f W st q) [] base_sv) with
      (ax_setS (mkAX (sc_f W st q) [] base_sv) (let S := ax_S (mkAX (sc_f W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SVar 12) (SVar 13) vN8 [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SVar 13) = n) by (apply (soff_var rho1 13%positive n E13); lia).
    assert (Ehi : soff rho1 vN8 = n8) by (unfold vN8; apply (soff_var rho1 105%positive n8 E105); lia).
    assert (Eb : bv_unsigned (eval rho1 (SVar 12)) = p) by (cbn [eval]; exact Ep).
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w (SVar 12) (SVar 13) vN8 NW2 H4 Wd (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Eb; try lia.
    -
      cbn [ss_objs ax_S sc_f sb_f]. apply Forall_app. split; [apply Forall_app; split|].
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia. rewrite Elo. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; unfold HIGH_SHADOW_END in *; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
      + apply Forall_cons; [|apply Forall_nil]. unfold ranges_disjoint, O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite Hshb, soff_lit_small by lia. unfold vN8g. rewrite (soff_var rho1 106%positive (n8 / 8) E106) by (split; [lia | apply Z.div_lt_upper_bound; lia]). lia.
    - intros a Ha. destruct (Hpadm a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(unfold HIGH_SHADOW_END in *; lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H4.

  assert (H6 : SPA segs (J A Kc) (se_f khi W st q) rho1 tp w).
  { unfold se_f. change (mkA (with_facts (sd_f W st q) (FACTSc khi W st q)) []) with (ax_with_facts (mkAX (sd_f W st q) [] base_sv) (FACTSc khi W st q)).
    eapply SPA_refacts; [exact H5 | exact Fe |].
    intros Hold. unfold FACTSc.
    assert (HP : Forall (holds rho1) (unwind_factsS W st ++ pre_facts free_depth)).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) Hold). cbn [ss_facts ax_S sd_f]. exact Hp. }
    assert (HD : holds rho1 (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))).
    { apply (proj1 (Forall_forall _ _) HP). apply in_or_app. right. unfold pre_facts, F_depth. cbn. tauto. }
    apply Forall_app in Hfacts as [HFg Hrest]. apply Forall_app in Hrest as [HFp Hrest]. apply Forall_app in Hrest as [HFc HFv].
    apply Forall_app; split; [|exact HFv]. apply Forall_app; split; [|exact HFc]. apply Forall_app; split; [apply Forall_app; split; [exact HP | exact HFg]|].
    assert (HFp' : holds rho1 (SPUle (SLit (atop_lo + 4096)) (SVar 10)) -> Forall (holds rho1) (F_pc khi)).
    { intros H0. clear -H0 HFp. destruct khi; (apply Forall_cons; [exact H0 | exact HFp]). }
    apply HFp'. clear HFp'.

    apply (proj2 (holds_ule rho1 _ _)). rewrite U_lit. cbn [eval]. change ((140735332483072 + 4096) mod M64v) with (140735332483072 + 4096).
    apply (proj1 (holds_bge rho1 _ _)) in HD. rewrite U_lit in HD. cbn [eval] in HD. change (Zsigned ((- free_depth) mod M64v)) with (-4096) in HD.
    unfold obj_range, obj_lo_of, stack_win in SW1. cbn [ob_base ob_lo fst] in SW1. unfold soff in SW1. cbn [eval] in SW1. rewrite bv_signed_U in SW1.
    unfold V_DEPTH in *. lia. }
  clear H5.

  pose proof (SPA_axforms segs (J A Kc) (XI nW q) rho1 (se_f khi W st q) (P0_fc khi W st q) tp w AXI H6) as H7.

  exact (SPA_withG_intro segs (J A Kc) GW (P0_fc khi W st q) rho1 tp w H7).
Qed.
End INST.
End F0A_inst.

(* [comment removed for export] *)
Module SpineMallocR7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SAlu"; "ss_next"; "eval"; "SVar"; "ss_facts"; "swf"; "valuation"; "SPNot"; "holds"; "ss_lenient"; "SPBranch"; "SPUle"; "rw"; "SMd"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "nil"; "pair"; "prod"; "Some"; "option"; "andb"; "false"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "cP2"; "GR"; "vMU"; "HINT_map"; "cPa"; "cPb"; "req_e"; "vAU"; "vK"; "vNF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "mul"; "sub"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "ALU_SRA"; "ALU_XOR"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7"; "F_mu0"; "F_hi"; "size_e_hi"; "size_e_lo"; "x19_e0"; "x19_e1"; "popfacts"; "total_e"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_free_array"; "cs_allocated_user"; "cs_mapped_user"; "AA"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "entryR"; "ph0"; "gh_nf"; "ghosts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "tab1_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit PrimCreditLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.PrimRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition size_e_hi : sv := ltac2:(tb__ "0|4|
SbS37SbS38SbS3cSbS39SeS40A1M0SaZ3fA1M1A3G1A3SbS3aSbS39SaZ200A1SbS3aSbS37G0SaN10A1A3SaZ1A1M2A3A3M3G2A3A3G3A3").
Definition size_e_lo : sv := ltac2:(tb__ "0|0|
SbS39SeS40A1SaZ5A1A3").
Definition tabS_okb : bool := ltac2:(tb__ "0|0|
S22S22S22S61S40S45S51Z11UeA5S60S40S45A2A2S61S40S46S51Z1U10A5A2S60S40S46A2A2").
Lemma tabS_ok : tabS_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Definition F_hi : sprop := ltac2:(tb__ "0|0|
S15S3bSaZ10A1SeS40A1A3").

Definition total_e : sv := ltac2:(tb__ "0|0|
SbS37S2dS18S3eSeS41A1S2cA3A3").
Definition x19_e0 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSaN1A1A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition x19_e1 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSbS3dS28SaZffffffffffffffffA1A3A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition F_mu0 : sprop := SPBranch BC_EQ vMU (SLit 0).

Definition popfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|1|
S4eQ40S17Vrb;PcA2A2S25S5eR1A1S25S5fVA;R2A2S57S6S31S33S24S25S53R1A1A2A1S52R2A1A2S6S30S32S55R1A1Z40000A2S65R2A1M0A2S30G0Ze0000000A2A2A2Tcs;Tc;Tnv;").

Lemma entry_popfacts : ltac2:(tb__ "0|1|
S56S11S1cS4dQ40M0A1A1S62S1cS63A1S64S11S5aR7R6R5R4R3R2R1A7S31S5cR8R7A2S52S5eS4eG0S17R7PcA2A2A1A1A2S49R9R8A2F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE HNP. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as (_ & HA & _). unfold popfacts. cbn zeta. unfold gh_nf in HNP. split; [exact HNP|].
  pose proof (populate_room segs A rb tp0 md0 _ HA C1 Hc0 ltac:(unfold cst_of in HNP; lia)) as [R1 R2].
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in *. unfold cst_of. split; [exact R1 | exact R2].
Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S66VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S5dVA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma size_hi_val : ltac2:(tb__ "0|0|
S13Vr;S44A2S5S4dQ40A1SdVr;S45A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. apply Z.ltb_lt in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T _]. apply andb_prop in T as [T _]. apply andb_prop in T as [T1 T2].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_hi Size 17 14 r c T1 T2 E158 ltac:(clear -C1 HF; lia)).
Qed.
Lemma size_lo_val : ltac2:(tb__ "0|0|
S7S13Vr;S44A2A1S5S4dQ40A1SdVr;S46A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  assert (C16 : c <= 16) by (destruct (Z.ltb_spec 16 c) as [X|X]; [exfalso; apply HF; reflexivity | exact X]).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_lo Size 1 16 r c T3 T4 E158 ltac:(clear -C1 C16; lia)).
Qed.

Lemma pop_nums : ltac2:(tb__ "0|4|
S51Vc;A1S25S52Vc;A1S25S33S24S25S53Vcs;A1A2A1S25S54Vcs;A1S25S55Vcs;A1S25S6S6S30Z20R5A2S30R5Z10000M0A2A2S6S6S30Z1R4A2S30R4Z8A2A2S6S6S30Z0M1R3A2S31R3R4A2A2S6S6S30G1R2A2S30R2R1A2A2S6S30R1Zdffc0000A2S6S31R1S32R2R5A2A2S6S6S31G1S34R5S35R4R3A2A2M2A2S30G2G0A2A2S6S31R1S32R2G2A2M3A2S30G3S32R1G0A2A2A2A2A2A2A2A2A2A2Tmu;Tau;Tnf;Tk;TS;").
Proof.
  intros S k nf au mu.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. fold S k nf au mu in CF.
  destruct CF as ((_ & _ & S1 & _) & (K1 & _ & K3) & (_ & AU0 & _ & _ & TI0) & _).
  destruct PF as (NP & RM & RC). fold nv c cs in NP, RM, RC. fold k nf mu in NP, RM.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. fold nf in NF0.
  clear -S1 K1 K3 AU0 TI0 NP RM RC NF0.
  assert (B1 : 0 < S * (k - nf)) by nia. assert (B2 : S * (k - nf) <= S * k) by nia. assert (B3 : S <= S * (k - nf)) by nia. lia.
Qed.

Lemma total_val : ltac2:(tb__ "0|0|
S5S25S4eQ40SdVr;S4aA2A2S32S54Vcs;A1S34S51Vc;A1S35S52Vc;A1S33S24S25S53Vcs;A1A2A1A2A2A2A3").
Proof.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & Q221 & _ & Q223 & _ & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q227.
  unfold total_e, req_e, vAU, vK, vNF, V_SIZE. cbn [eval]. rewrite add_val, mul_val, sub_val, E148, Q221, Q223, Q227.
  rewrite !u64_lit by (clear -N1 N2 N3 N4 N5; lia).
  rewrite (Z.mod_small (kchunks c - _)) by (clear -N2 N3; lia). rewrite (Z.mod_small (Size c * _)) by (clear -N7; lia).
  rewrite Z.mod_small by (clear -N4 N5 N7; lia). reflexivity.
Qed.

Lemma F_pop_hold : Forall (holds r) F_pop.
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227.
  unfold F_pop. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. unfold branch_taken, bv_ltu, vNF, vK. cbn [eval]. rewrite Q221, Q227. rewrite !u64_lit by (clear -N2 N3; lia). apply Z.ltb_lt. exact (proj2 N3).
  - unfold HINT_map. cbn [holds]. unfold branch_taken, bv_ltu. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224. rewrite u64_lit by (clear -N4 N5; lia).
    apply Z.ltb_lt. exact (proj1 N8).
  - cbn [holds]. unfold vMU. cbn [eval]. rewrite Q224. rewrite !u64_lit by (clear -N4 N5; lia). exact N5.
Qed.

Lemma x19_val1 : ltac2:(tb__ "0|0|
S5S4dQ40A1SdVr;S48A2SdVr;SaZ40000A1A2A3").
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  unfold x19_e1. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val, xor_val. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224.
  rewrite !u64_lit by (clear -N4 N5; lia).
  rewrite lxor_ones64 by (clear -N4 N5; lia).
  replace ((tot + (18446744073709551615 - cs_mapped_user cs)) mod 2 ^ 64) with (tot - cs_mapped_user cs - 1).
  2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N5 N8; lia. }
  rewrite land_m18_small by (clear -N8; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
Qed.
Lemma x19_val0 : ltac2:(tb__ "0|1|
S13Vr;S43A2S6S5S4dQ40A1M0SdVr;S47A2SdVr;SaZ40000A1A2A3S5G0SdVr;SaZ0A1A2SdVr;S28A2A3A2F_;").
Proof.
  intros HF. pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  unfold F_mu0 in HF. cbn [holds] in HF. unfold branch_taken, bv_eqb, vMU in HF. cbn [eval] in HF. rewrite Q224 in HF. rewrite !u64_lit in HF by (clear -N4 N5; lia). apply Z.eqb_eq in HF.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  split.
  - unfold x19_e0. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val. fold total_e. rewrite TV.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by reflexivity. rewrite !u64_lit by (clear; lia).
    replace ((tot + 18446744073709551615) mod 2 ^ 64) with (tot - 1).
    2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N8 HF; lia. }
    rewrite land_m18_small by (clear -N4 N8 HF; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
  - unfold vMU. cbn [eval]. rewrite Q224, HF. reflexivity.
Qed.
End VALS.

Section POP1.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S5aVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable F : nat.
Variables (E3 : axst) (LP : axst) (La Lb La0 La1 Lb0 Lb1 : leafA) (CP2C : axst) (sa0 sa1 sb0 sb1 : wsub).
Let FR : list sprop := factsR E3.
Let CPA : axst := ltac2:(tb__ "0|0|
S2aVFR;S1VLa;A1A2").
Let CPB : axst := ltac2:(tb__ "0|0|
S2bVFR;S1VLb;A1A2").
Hypothesis FP_in : ltac2:(tb__ "0|0|
S36S9S15S3bS2fS2eA3SfS0VLP;A1A1A3").
Hypothesis R_p1 : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41754S1bS25Z41794S1dS25A1A3A3VLP;S1aA5S20G0S1bS2VLa;S1bS2VLb;S1dS2A1A3A3A2A3").
Hypothesis LN_p : ltac2:(tb__ "0|0|
S5S19S14S0VLP;A1A1S23A3").
Hypothesis NX_p : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VLP;A1A1A2S1aA3").
Hypothesis Fa_in : ltac2:(tb__ "0|0|
S36S9S44SfS0S1VLa;A1A1A1A3").
Hypothesis Fb_in : ltac2:(tb__ "0|0|
S36S9S12S44A1SfS0S1VLb;A1A1A1A3").
Hypothesis W_pa : ltac2:(tb__ "0|0|
S5S19S10S0VCPA;A1A1S1aA3").
Hypothesis D_pa : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa;A1A1S0VCPA;A1A2S20G3S1eG1G2S1bG0S1eS8S8S45SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pa : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPA;A1A1ScS0S1VLa;A1A1A1A2S1aA3").
Hypothesis W_pb : ltac2:(tb__ "0|0|
S5S19S10S0VCPB;A1A1S1aA3").
Hypothesis D_pb : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb;A1A1S0VCPB;A1A2S20G3S1eG1G2S1bG0S1eS8S8S46SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pb : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPB;A1A1ScS0S1VLb;A1A1A1A2S1aA3").
Hypothesis R_p2a : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z417c4S1dS25A1A3VCPA;S1aA5S20G0S1bS2VLa0;S1bS2VLa1;S1dS2A1A3A3A2A3").
Hypothesis LN_pa : ltac2:(tb__ "0|0|
S5S19S14S0VCPA;A1A1S23A3").
Hypothesis NXr_pa : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPA;A1A1A2S1aA3").
Hypothesis R_p2b : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z417c4S1dS25A1A3VCPB;S1aA5S20G0S1bS2VLb0;S1bS2VLb1;S1dS2A1A3A3A2A3").
Hypothesis LN_pb : ltac2:(tb__ "0|0|
S5S19S14S0VCPB;A1A1S23A3").
Hypothesis NXr_pb : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPB;A1A1A2S1aA3").

Section LEAF.
Variables (L : leafA) (s : wsub) (mu0 : bool).
Let C2 : axst := ltac2:(tb__ "0|0|
S26VFR;S1VL;A1A2").
Hypothesis F_in : ltac2:(tb__ "0|0|
S36S9S19S9Lmu0;Vmu0;S43S12S43A1X19x2SfS0S1VL;A1A1A1A3").
Hypothesis W_2 : ltac2:(tb__ "0|0|
S5S19S10S0VC2;A1A1S1aA3").
Hypothesis D_2 : ltac2:(tb__ "0|6|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VL;A1A1S0VC2;A1A2S20G3S1eG1G2S19G1Lmu0;Vmu0;S1bG0S1eS8S8S47SaZ40000A1M4A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1M5A3A3S1bG0S1eS8S8S48G4A4G5A3X19x2S1dS9A1A4A2A3").
Hypothesis NX_2 : ltac2:(tb__ "0|0|
S5S19S4bScS0VC2;A1A1ScS0S1VL;A1A1A1A2S1aA3").
Hypothesis ENT_2 : ltac2:(tb__ "0|0|
S5S19S3VC2;VCP2C;Vs;A3S1aA3").
Hypothesis SID_2 : ltac2:(tb__ "0|0|
S5S19S4fVs;S27A2S1aA3").

Lemma join_leaf : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';VTR;S50S42G0S1VL;A1R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q PF HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L) (ax_S C2) _ _ ph0 r tp Q W_2 D_2 NX_2).
  { intros tr md (HFz & HGh & _) HF. split; [|constructor].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    pose proof (proj1 (Forall_forall _ _) HF _ F_in) as HB.
    unfold diffs_ok. destruct mu0.
    - destruct (x19_val0 A rb r CF PF RG HGh HB) as [X1 X2]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (x19_val1 A rb r CF PF RG HGh). }
  change (ax_setS (la_state L) (ax_S C2)) with C2.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph0) CP2C (rho_sub r s) tp)); [|exact (HC _)].
  intros w Hw. apply (SPA_entails_J (JRp ph0) (JRp ph0) C2 CP2C s r tp w ENT_2); [|exact Hw].
  intros HJ. eapply (JR_stable A Kc rb tp0 md0 ph0 GR HKc ltac:(lia)); [exact (rho_sub_agree s GR r SID_2) | apply mat_equiv_refl | exact HJ].
Qed.
End LEAF.

Hypothesis Fa0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLa0;A1A1A1A3").
Hypothesis Fa1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLa1;A1A1A1A3").
Hypothesis Fb0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLb0;A1A1A1A3").
Hypothesis Fb1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLb1;A1A1A1A3").
Hypothesis W_a0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa0;A1A2A1A1S1aA3").
Hypothesis W_a1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa1;A1A2A1A1S1aA3").
Hypothesis W_b0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb0;A1A2A1A1S1aA3").
Hypothesis W_b1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb1;A1A2A1A1S1aA3").
Hypothesis D_a0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_a1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis D_b0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_b1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis NX_a0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_a1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis ENT_a0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa0;A1A2VCP2C;Vsa0;A3S1aA3").
Hypothesis ENT_a1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa1;A1A2VCP2C;Vsa1;A3S1aA3").
Hypothesis ENT_b0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb0;A1A2VCP2C;Vsb0;A3S1aA3").
Hypothesis ENT_b1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb1;A1A2VCP2C;Vsb1;A3S1aA3").
Hypothesis SID_a0 : ltac2:(tb__ "0|0|
S5S19S4fVsa0;S27A2S1aA3").
Hypothesis SID_a1 : ltac2:(tb__ "0|0|
S5S19S4fVsa1;S27A2S1aA3").
Hypothesis SID_b0 : ltac2:(tb__ "0|0|
S5S19S4fVsb0;S27A2S1aA3").
Hypothesis SID_b1 : ltac2:(tb__ "0|0|
S5S19S4fVsb1;S27A2S1aA3").

Theorem populate_head : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';F_;VTR;S50S42G0VLP;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.

  apply (tr_facts Kc TR KIT). intros HF0. pose proof (proj1 (Forall_forall _ _) HF0 _ FP_in) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (popfacts A rb)).
  { intros w [_ (HFz & HGh & _)]. apply (entry_popfacts _ _ _ _ _ _ _ HE).
    destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. apply Z.ltb_lt in BF. exact BF. }
  intros PF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41754; 0x41794] LP [La; Lb] ph0 r tp Q R_p1 LN_p NX_p).
  intros L r1 [<-|[<-|[]]] _.
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state La) (ax_S CPA) _ _ ph0 r1 tp Q W_pa D_pa NX_pa).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_hi_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fa_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state La) (ax_S CPA)) with CPA.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x417c4] CPA [La0; La1] ph0 r1 tp Q R_p2a LN_pa NXr_pa).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf La0 sa0 true Fa0_in W_a0 D_a0 NX_a0 ENT_a0 SID_a0 r2 tp Q PF (HC PF)).
    + exact (join_leaf La1 sa1 false Fa1_in W_a1 D_a1 NX_a1 ENT_a1 SID_a1 r2 tp Q PF (HC PF)).
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state Lb) (ax_S CPB) _ _ ph0 r1 tp Q W_pb D_pb NX_pb).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_lo_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fb_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state Lb) (ax_S CPB)) with CPB.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x417c4] CPB [Lb0; Lb1] ph0 r1 tp Q R_p2b LN_pb NXr_pb).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf Lb0 sb0 true Fb0_in W_b0 D_b0 NX_b0 ENT_b0 SID_b0 r2 tp Q PF (HC PF)).
    + exact (join_leaf Lb1 sb1 false Fb1_in W_b1 D_b1 NX_b1 ENT_b1 SID_b1 r2 tp Q PF (HC PF)).
Qed.
End POP1.
End SpineMallocR7.

(* [comment removed for export] *)
Module SpineMallocS7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "Some"; "option"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "SAlu"; "sv"; "sobj"; "ss_facts"; "SLit"; "eval"; "sprop_below"; "ss_objs"; "swf"; "SVar"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "C6m"; "C6l"; "C6b"; "C7"; "E6l"; "E6s"; "E6m"; "O_U"; "C6"; "E6j"; "LUe"; "ube"; "F_gen"; "n8e"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "JGb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7"; "len3e"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "le"; "pow"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zero_covered"; "zobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4"; "pvals_ok"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition len3e : sv := ltac2:(tb__ "0|1|
S13S3aS13S38S13S39S13S38S13S38S29S2bA3S17N8A1A3S17Z3A1M0A3S17Z1A1A3S13S39S29G0A3A3").

Section PSVals3.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S5aVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S4cS4cVSB;S4dVc;S4fZ2Z20A2A2A2S4dZ10Vx;A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_len3 : ltac2:(tb__ "0|0|
S0S36Q40A1S18Vrho;S48A2S18Vrho;S28A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ub rho _ _ _ _ _ _ PV) as EUB. cbn zeta in EUB. fold ab in EUB.
  pose proof (pv_lu rho _ _ _ _ _ _ PV) as ELU.
  apply bv_eq. rewrite ELU. unfold len3e. cbn [eval]. fold ube. fold n8e.
  assert (EN8 : bv_unsigned (eval rho n8e) = n - n mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). apply land_M48. lia. }
  rewrite sub_val, add_val, srl_val, add_val, add_val, srl_val, EUB, EN8.
  replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity. rewrite !u64_lit by lia. change (3 mod 64) with 3.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (B1 : 17594333495296 <= ab + rzv /\ ab + rzv + n <= 140737479966720) by (unfold ab; lia).
  rewrite (Z.mod_small (ab + rzv + (n - n mod 8))) by lia.
  replace ((ab + rzv + (n - n mod 8) + (2 ^ 64 - 8)) mod 2 ^ 64) with (ab + rzv + (n - n mod 8) - 8).
  2:{ replace (ab + rzv + (n - n mod 8) + (2 ^ 64 - 8)) with ((ab + rzv + (n - n mod 8) - 8) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. rewrite (Z.mod_small (ab + rzv + (n - n mod 8) - 8)) by lia. reflexivity. }
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)).
  set (q := SB / 2 ^ 16) in *. set (r := rzv / 16) in *. set (k := n / 8) in *.
  replace (ab + rzv + (n - n mod 8) - 8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r + k - 1) * 8) by (unfold ab; lia).
  replace (ab + rzv) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r) * 8) by (unfold ab; lia).
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by lia. rewrite (Z.mod_small (_ - _)) by lia. lia.
Qed.
End PSVals3.

Section S7.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S42VAInv;VW;Vst;VA;VKc;S1cPcA1A6").

Section B10aS.
Hypothesis Cert6 : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZ5f9f8S9S2cZ3c82cSaS2cA1A3A3S34S9S2S26VW;Vst;Vtmax;A3SaS2A1M0A3S9S2S23VW;Vst;Vtmax;A3S9S2S22VW;Vst;Vtmax;A3G0A3A3A6S8A3").

Variable k6 : nat.
Hypothesis NTH6s : ltac2:(tb__ "0|0|
S0SdS15A1S4bS15S1aS1S23VW;Vst;Vtmax;A3A1A1Vk6;A3ScS15S25A2A3").
Hypothesis ZC6s : ltac2:(tb__ "0|0|
S0S7S55S16S1S23VW;Vst;Vtmax;A3A1A1S25A2S8A3").
Variable s7s : wsub.
Hypothesis ENT7s : ltac2:(tb__ "0|2|
S0S7S3S4S23VW;Vst;Vtmax;A3M0S53S1G0A1M1S52S15S1aG1A1Vk6;S56S25A1A4A2A2S21VW;Vst;Vtmax;A3Vs7s;A3S8A3").
Hypothesis SID7s : ltac2:(tb__ "0|0|
S0S7S3eVs7s;S34A2S8A3").

Hypothesis G6l : ltac2:(tb__ "0|0|
S4aS11S2aS16S1S22VW;Vst;Vtmax;A3A1A1A3").
Hypothesis W6l : ltac2:(tb__ "0|0|
S0S7S1bS1S1fVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D6l : ltac2:(tb__ "0|4|
S0SdSeSbSeS14S14A2M0A1M1SbS11A1M2A2M3A1S47S1S22VW;Vst;Vtmax;A3A1S1S1fVW;Vst;Vtmax;A3A1A2ScG3SfG1G2S9G0SfS14S14S48S28A4SaG0A1A3SaS11A1A4A2A3").
Hypothesis NX6l : ltac2:(tb__ "0|0|
S0S2dS12S1S1fVW;Vst;Vtmax;A3A1A1S12S1S22VW;Vst;Vtmax;A3A1A1A3").

Theorem spine_s6 : ltac2:(tb__ "0|1|
S30OF_;S44S40S10SbS36Q40M0A1A1S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S4eZ1S46R8S37G0S1dR6PcA2A2A2A2S10S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5S21VW;Vst;Vtmax;A3R1R7A5R6A4FrhoX;S10S2eVsegs;RcS31Vsegs;S35VW;Vst;RbRaR9A5S1fVW;Vst;Vtmax;A3R1R8A5R7A4FrhoX;S10S2eVsegs;RdS31Vsegs;S35VW;Vst;RcRbRaA5S26VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC7 HC6l rhoE.
  apply (cfg_soundA segs 4000%nat [0x5f9f8; 0x3c82c] GW [C6 W st tmax] [E6s W st tmax; E6l W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7 (rho_sub rhoX s7s))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW _ (C7 W st tmax) s7s rhoX tp w ENT7s SID7s); [apply JGb_stable; [exact HUS | exact HKc]|].
      apply (SPA_zero_fold segs (JGb W st A Kc rho) rhoX (E6s W st tmax) tp w k6 O_U NTH6s ZC6s Hw).
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC6l rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G6l Hcnt) as PV. cbn zeta in PV.
      unfold C6l, upd. lazy zeta. eapply SPA_restate; [exact W6l | exact D6l | exact NX6l | | constructor | exact Hw].
      unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len3 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End B10aS.

Section B10bS.
Hypothesis Cert6l : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZdb004SaS2cA1A3S34S9S2S1fVW;Vst;Vtmax;A3SaS2A1M0A3S9S2S24VW;Vst;Vtmax;A3G0A3A6S8A3").
Hypothesis W6m : ltac2:(tb__ "0|0|
S0S7S1bS1S1eVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D6m : ltac2:(tb__ "0|4|
S0SdSeSbSeS14S14A2M0A1M1SbS11A1M2A2M3A1S47S1S24VW;Vst;Vtmax;A3A1S1S1eVW;Vst;Vtmax;A3A1A2ScG3SfG1G2SaG0A1SaS11A1A4A2A3").
Hypothesis NX6m : ltac2:(tb__ "0|0|
S0S2dS12S1S1eVW;Vst;Vtmax;A3A1A1S12S1S24VW;Vst;Vtmax;A3A1A1A3").
Variables (s6 sd6 : wsub) (R6 : list sobj) (T6 : axst).
Hypothesis He6 : ltac2:(tb__ "0|1|
S0SdSbS15A1M0A1S58S1eVW;Vst;Vtmax;A3S3bVs6;A3ScG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S7S57S1eVW;Vst;Vtmax;A3S3bVs6;VR6;S50S6S2S5S3dA4A5S8A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S2S59Vs6;S3bS51S3cA1S1eVW;Vst;Vtmax;A3VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S7S49S11S19S12S1S1eVW;Vst;Vtmax;A3A1M0A1A1S16G0A1A3S8A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S7S49S11S19S12S1VT6;A1A1A1S16S1S1eVW;Vst;Vtmax;A3A1A1A3S8A3").
Hypothesis ENT6 : ltac2:(tb__ "0|0|
S0S7S3S54VT6;S16S1S1eVW;Vst;Vtmax;A3A1A1A2S20VW;Vst;Vtmax;A3Vsd6;A3S8A3").
Hypothesis SID6 : ltac2:(tb__ "0|0|
S0S7S3eVsd6;S34A2S8A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S5bS34S12S1S1eVW;Vst;Vtmax;A3A1A1A2").

Theorem spine_s6l : ltac2:(tb__ "0|2|
S30OF_;S44S40S10SbS36Q40A1A1M0S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S10G0S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5M1S20VW;Vst;Vtmax;A3R2R1A5R6A4FtpX;FrhoX;S10S2eVsegs;RbS31Vsegs;G1S1fVW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0xdb004] GW [C6l W st tmax] [E6m W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6l.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen nW st (C6m W st tmax) T6 (C6b W st tmax) s6 R6 sd6 Pre_mszA Posts_mszA P_msz
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memsetZ_sumA ok0 Jx Ho Hs r0 t0) He6 Hchk6 HT6 FBC6 FBT6 ENT6 SID6 NXC6 eq_refl
                ok A Kc rho tp rhoX Q HUS HKc Hokf HC). }
    unfold C6m, upd. lazy zeta. eapply SPA_restate; [exact W6m | exact D6m | exact NX6m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End B10bS.

Section B10cS.
Hypothesis Cert6b : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZ3c82cSaS2cA1A3S34S9S2S20VW;Vst;Vtmax;A3SaS2A1M0A3S9S2S27VW;Vst;Vtmax;A3G0A3A6S8A3").
Variable s7j : wsub.
Hypothesis ENT7j : ltac2:(tb__ "0|0|
S0S7S3S27VW;Vst;Vtmax;A3S21VW;Vst;Vtmax;A3Vs7j;A3S8A3").
Hypothesis SID7j : ltac2:(tb__ "0|0|
S0S7S3eVs7j;S34A2S8A3").
Theorem spine_s6b : ltac2:(tb__ "0|0|
S30OF_;S44S40S10SbS36Q40A1A1S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S10S2eVsegs;RaS31Vsegs;S35VW;Vst;R9R8R7A5S21VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S10S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5S20VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c82c] GW [C6b W st tmax] [E6j W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6b.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s7j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E6j W st tmax) (C7 W st tmax) s7j rhoX tp w ENT7j SID7j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End B10cS.
End S7.
End SpineMallocS7.

(* [comment removed for export] *)
Module SpineCallocS5.


From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint zseq1 (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq1 (lo + 1) n' end.
Lemma in_zseq1 : forall lo n z, lo <= z < lo + Z.of_nat n -> In z (zseq1 lo n).
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo z Hz; [lia|]. cbn [zseq1].
  destruct (Z.eq_dec z lo) as [->|Hne]; [left; reflexivity | right]. rewrite Nat2Z.inj_succ in Hz. apply IH. lia.
Qed.
Definition tab1_ok (i : positive) (e : sv) (g : Z -> Z) (lo : Z) (n : nat) : bool :=
  forallb (fun z => Z.eqb (bv_unsigned (eval (rho_one i (Z_to_bv 64 z)) e)) (g z)) (zseq1 lo n).
Lemma tab1_ok_sound : forall i e g lo n rho z,
  tab1_ok i e g lo n = true -> only_var i e = true ->
  rw rho i = Z_to_bv 64 z -> lo <= z < lo + Z.of_nat n ->
  eval rho e = Z_to_bv 64 (g z).
Proof.
  intros i e g lo n rho z Ht Ho Hi Hz.
  pose proof (proj1 (forallb_forall _ _) Ht z (in_zseq1 lo n z Hz)) as T. cbn beta in T. apply Z.eqb_eq in T.
  rewrite (eval_only_var i e rho Ho), Hi. rewrite <- T. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Definition depot_only (A A' : AA) : Prop :=
  aa_geom A' = aa_geom A /\ aa_cls A' = aa_cls A /\ aa_cache_inited A' = aa_cache_inited A /\ aa_sec A' = aa_sec A
  /\ aa_ptr_committed A' = aa_ptr_committed A /\ aa_live A' = aa_live A /\ aa_q_thread A' = aa_q_thread A
  /\ aa_q_global A' = aa_q_global A /\ aa_internal_inited A' = aa_internal_inited A
  /\ aa_fs_busy A' = aa_fs_busy A /\ aa_fs_hint A' = aa_fs_hint A
  /\ aa_V A' = aa_V A /\ aa_Km A' = aa_Km A /\ aa_Kf A' = aa_Kf A.
Lemma depot_only_refl : forall A, depot_only A A.
Proof. intros A. unfold depot_only. repeat split; reflexivity. Qed.

Definition depot_onlyK (A A' : AA) : Prop :=
  aa_geom A' = aa_geom A /\ aa_cls A' = aa_cls A /\ aa_cache_inited A' = aa_cache_inited A /\ aa_sec A' = aa_sec A
  /\ aa_ptr_committed A' = aa_ptr_committed A /\ aa_live A' = aa_live A /\ aa_q_thread A' = aa_q_thread A
  /\ aa_q_global A' = aa_q_global A /\ aa_internal_inited A' = aa_internal_inited A
  /\ aa_fs_busy A' = aa_fs_busy A /\ aa_fs_hint A' = aa_fs_hint A
  /\ aa_V A' = aa_V A /\ aa_Km A' = aa_Km A + 1 /\ aa_Kf A' = aa_Kf A.

Definition clsp_e : sv := SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SVar V_CLS) (SLit 32)) (SAlu ALU_SLL (SVar V_CH) (SLit 4))) (SLit 32).
Definition clsp_e31 : sv := SAlu ALU_AND clsp_e (SLit 31).

Lemma clsp_eval : forall rho c x, rw rho V_CLS = Z_to_bv 64 c -> rw rho V_CH = Z_to_bv 64 x -> 0 <= c <= 30 -> 0 <= x < 2 ^ 28 ->
  eval rho clsp_e = Z_to_bv 64 c /\ eval rho clsp_e31 = Z_to_bv 64 c.
Proof.
  intros rho c x Hc Hx Bc Bx.
  assert (E : eval rho clsp_e = Z_to_bv 64 c).
  { unfold clsp_e. cbn [eval]. rewrite Hc, Hx. apply bv_eq.
    rewrite srl_val, add_val, sll_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. change (4 mod 64) with 4.
    rewrite !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (x * 2 ^ 4)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + x * 2 ^ 4)) by lia.
    replace (c * 2 ^ 32 + x * 2 ^ 4) with (x * 2 ^ 4 + c * 2 ^ 32) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  split; [exact E|]. unfold clsp_e31. cbn [eval]. fold clsp_e. rewrite E. apply bv_eq. rewrite and_val, !u64_lit by lia.
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section S5.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := J_alloc_preT AInv W st A Kc (SVar 12).

Lemma JG_rigid : forall A Kc rho rhoE tp tr md,
  JG W st A Kc rho rhoE tp tr md ->
  rw rhoE 12%positive = rw rho 12%positive
  /\ rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of (bv_unsigned (rw rho 12%positive))))
  /\ rw rhoE 149%positive = Z_to_bv 64 (cnt_of A (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 150%positive = Z_to_bv 64 (rz (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 159%positive = Z_to_bv 64 (chk_of A (bv_unsigned (rw rho 12%positive))).
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct Hag as (Hagw & Hagl & Hagm).
  split; [rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 148%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 149%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 150%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 158%positive) by (unfold GW; lia); reflexivity|].
  rewrite <- (Hagw 159%positive) by (unfold GW; lia); reflexivity.
Qed.

Lemma JG_stable : forall A Kc rho, stopJ_stable W st -> Kc_ok Kc -> stableA segs GW (JG W st A Kc rho).
Proof.
  intros A Kc rho HUS HKc.
  apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
Qed.

Lemma JG_model : forall A Kc rho rhoE tp tr md,
  JG W st A Kc rho rhoE tp tr md ->
  let nv := bv_unsigned (rw rho 12%positive) in
  AInvA segs A rhoE tp md /\ 1 <= nv < 2 ^ 39.
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  destruct Hag as (Hagw & _ & _). cbn zeta. rewrite <- (Hagw 12%positive) in HN by (unfold GW; lia). exact (conj HA HN).
Qed.

Lemma fact_of_state : forall A Kc rho rhoE tp w (E : axst) p,
  SPA segs (JG W st A Kc rho) E rhoE tp w -> In p (ss_facts (ax_S E)) -> holds rhoE p.
Proof.
  intros A Kc rho rhoE tp w E p [HsmA _] Hp.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  exact (proj1 (Forall_forall _ _) (smatch_facts_hold _ _ _ _ Hsm) p Hp).
Qed.

Lemma cnt_pos_of_fact : forall A Kc rho rhoE tp w (E : axst),
  SPA segs (JG W st A Kc rho) E rhoE tp w -> In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S E)) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)).
Proof.
  intros A Kc rho rhoE tp w E H Hin. destruct w as [tr [ms md]].
  pose proof (JG_rigid A Kc rho rhoE tp tr md (proj2 H)) as (_ & _ & E149 & _).
  pose proof (fact_of_state A Kc rho rhoE tp _ E _ H Hin) as F. cbn [holds eval] in F. unfold V_CNT in F. rewrite E149 in F.
  rewrite (u64_lit 1) in F by lia.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as C0. unfold cnt_of in F |- *.
  set (len := Z.of_nat _) in F, C0 |- *.
  destruct (Z_lt_dec len (2 ^ 64)); [rewrite u64_lit in F by lia; exact F | lia].
Qed.

Definition J_alloc_preB (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) (n : sv) : jpredA :=
  fun rho tp tr md =>
    AInv A rho tp md /\ Kc tr md /\ tp_ok A rho /\ unwind_stopJ W st rho
    /\ True
    /\ 1 <= bv_unsigned (eval rho n) < 2 ^ 39
    /\ top_high A rho.
Definition JGb (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) (rho : valuation) : jpredA :=
  withGA (fun r => agree_below GW (rhoM_of A rho) r) (J_alloc_preB W st A Kc (SVar 12)).

Lemma JB_agree : forall A Kc rho rho' tp tr md,
  stopJ_stable W st -> agree_below NF rho rho' -> J_alloc_preB W st A Kc (SVar 12) rho tp tr md -> J_alloc_preB W st A Kc (SVar 12) rho' tp tr md.
Proof.
  intros A Kc rho rho' tp tr md HUS Hag (HA & HK & Htp & HU & HB & HN & Htop). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (E12 : eval rho' (SVar 12) = eval rho (SVar 12)) by (cbn; symmetry; apply Hw; unfold NF; lia).
  split; [unfold AInv, AInvA in *; rewrite Erm; exact HA|]. split; [exact HK|].
  split; [unfold tp_ok in *; rewrite <- (Hw 24%positive) by (unfold NF; lia); exact Htp|].
  split; [exact (HUS rho rho' Hag HU)|].
  rewrite E12. split; [exact I |]. split; [exact HN|].
  unfold top_high in *. rewrite <- (Hw 10%positive) by (unfold NF; lia). rewrite <- (Hw V_DEPTH) by (unfold NF, V_DEPTH; lia). exact Htop.
Qed.
Lemma JB_stableA : forall A Kc, stopJ_stable W st -> Kc_ok Kc -> stableA segs GW (J_alloc_preB W st A Kc (SVar 12)).
Proof.
  intros A Kc HUS HKc rho rho' tp tr md md' Hag Hme HJ.
  pose proof (JB_agree A Kc rho rho' tp tr md HUS ltac:(eapply agree_below_le; [|exact Hag]; cbv; discriminate) HJ) as (HA & HK & Htp & HU & HB & HN & Htop).
  split; [apply (AInvA_mat segs A rho' tp md md'); [exact HA | exact Hme]|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [exact Htp|]. split; [exact HU|]. split; [exact I|]. split; [exact HN | exact Htop].
Qed.
Lemma JG_JGb : forall A Kc rho rhoE tp tr md, JG W st A Kc rho rhoE tp tr md -> JGb W st A Kc rho rhoE tp tr md.
Proof.
  intros A Kc rho rhoE tp tr md [Hag (HA & HK & Htp & HU & HB & HN & Htop)]. split; [exact Hag|].
  exact (conj HA (conj HK (conj Htp (conj HU (conj I (conj HN Htop)))))).
Qed.
Lemma JGb_rigid : forall A Kc rho rhoE tp tr md,
  JGb W st A Kc rho rhoE tp tr md ->
  rw rhoE 12%positive = rw rho 12%positive
  /\ rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of (bv_unsigned (rw rho 12%positive))))
  /\ rw rhoE 149%positive = Z_to_bv 64 (cnt_of A (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 150%positive = Z_to_bv 64 (rz (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))
  /\ rw rhoE 159%positive = Z_to_bv 64 (chk_of A (bv_unsigned (rw rho 12%positive))).
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct Hag as (Hagw & Hagl & Hagm).
  split; [rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 148%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 149%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 150%positive) by (unfold GW; lia); reflexivity|].
  split; [rewrite <- (Hagw 158%positive) by (unfold GW; lia); reflexivity|].
  rewrite <- (Hagw 159%positive) by (unfold GW; lia); reflexivity.
Qed.
Lemma JGb_stable : forall A Kc rho, stopJ_stable W st -> Kc_ok Kc -> stableA segs GW (JGb W st A Kc rho).
Proof.
  intros A Kc rho HUS HKc.
  apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JB_stableA; [exact HUS | exact HKc]].
Qed.
Lemma JGb_model : forall A Kc rho rhoE tp tr md,
  JGb W st A Kc rho rhoE tp tr md ->
  let nv := bv_unsigned (rw rho 12%positive) in
  AInvA segs A rhoE tp md /\ 1 <= nv < 2 ^ 39.
Proof.
  intros A Kc rho rhoE tp tr md [Hag HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  destruct Hag as (Hagw & _ & _). cbn zeta. rewrite <- (Hagw 12%positive) in HN by (unfold GW; lia). exact (conj HA HN).
Qed.
Lemma fact_of_stateB : forall A Kc rho rhoE tp w (E : axst) p,
  SPA segs (JGb W st A Kc rho) E rhoE tp w -> In p (ss_facts (ax_S E)) -> holds rhoE p.
Proof.
  intros A Kc rho rhoE tp w E p [HsmA _] Hp.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  exact (proj1 (Forall_forall _ _) (smatch_facts_hold _ _ _ _ Hsm) p Hp).
Qed.
Lemma cnt_pos_of_factB : forall A Kc rho rhoE tp w (E : axst),
  SPA segs (JGb W st A Kc rho) E rhoE tp w -> In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S E)) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)).
Proof.
  intros A Kc rho rhoE tp w E H Hin. destruct w as [tr [ms md]].
  pose proof (JGb_rigid A Kc rho rhoE tp tr md (proj2 H)) as (_ & _ & E149 & _).
  pose proof (fact_of_stateB A Kc rho rhoE tp _ E _ H Hin) as F. cbn [holds eval] in F. unfold V_CNT in F. rewrite E149 in F.
  rewrite (u64_lit 1) in F by lia.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as C0. unfold cnt_of in F |- *.
  set (len := Z.of_nat _) in F, C0 |- *.
  destruct (Z_lt_dec len (2 ^ 64)); [rewrite u64_lit in F by lia; exact F | lia].
Qed.

Section B3S.
Hypothesis Cert3p : check_cfgA segsA 4000%nat [0x40e58; 0x3c614] GW [C2p W st tmax] [E3p W st tmax] = true.
Hypothesis SKY : map skel (ss_objs (ax_S (E3p W st tmax))) = map skel ((((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ [O_pcc; O_pcs; O_pck; O_st])).
Hypothesis YX : ax_X (E3p W st tmax) = [].
Hypothesis YF : incl (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis YP : In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis WY1 : swf (ax_S (Y1 (E3p W st tmax))) = true.
Hypothesis WY2 : swf (ax_S (Y2 (E3p W st tmax))) = true.
Hypothesis WY3 : swf (ax_S (Y3 (E3p W st tmax))) = true.
Hypothesis WY4 : swf (ax_S (Y4 (E3p W st tmax))) = true.
Hypothesis WY5 : swf (ax_S (Y5 (E3p W st tmax))) = true.
Hypothesis WY6 : swf (ax_S (Y6 (E3p W st tmax))) = true.
Hypothesis WY7 : swf (ax_S (Y7 (E3p W st tmax))) = true.
Variable s3 : wsub.
Hypothesis ENT3 : entailsA (Y7 (E3p W st tmax)) (C3 W st tmax) s3 = true.
Hypothesis SID3 : wsub_id_below s3 GW = true.

Theorem spine_s3p : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  (stopJ_w W st) -> stopJ_stable W st -> Kc_ok Kc -> sep_geom (aa_geom A) -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HW HUS HKc HSEP Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x40e58; 0x3c614] GW [C2p W st tmax] [E3p W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert3p.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s3))].
    apply (b3_carve nW st tmax (E3p W st tmax) SKY YX YF WY1 WY2 WY3 WY4 WY5 WY6 WY7 s3 ENT3 SID3 A Kc rho tp w rhoX HW HUS HKc HSEP); [|exact Hw].
    exact (cnt_pos_of_fact A Kc rho rhoX tp w _ Hw YP).
  - left. reflexivity.
Qed.
End B3S.

Section B2S.
Hypothesis Cert3r : check_cfgA segsA 4000%nat [0x40e58; 0x3c614] GW [C2r W st tmax] [E3r W st tmax] = true.
Theorem spine_s3r : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (E3r W st tmax) rhoE tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C2r W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HR rhoE.
  apply (cfg_soundA segs 4000%nat [0x40e58; 0x3c614] GW [C2r W st tmax] [E3r W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert3r.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End B2S.

Section B4S.
Hypothesis Cert4 : check_cfgA segsA 4000%nat [0x7e9e4] GW [C3 W st tmax] [E4d W st tmax] = true.

Definition hd_link (keep : Z -> Prop) (rho rho' : valuation) : Prop :=
  (forall i, rw rho' i = rw rho i) /\ (forall l, rl rho' l = rl rho l)
  /\ (forall a, keep (bv_unsigned a) -> rm rho' a = rm rho a)
  /\ (forall a, SHADOW_BAND_LO <= bv_unsigned a < SHADOW_BAND_HI -> rm rho a <> None -> rm rho' a <> None).
Lemma hd_link_refl : forall keep rho, hd_link keep rho rho.
Proof. intros keep rho. repeat split; intros; auto. Qed.

Definition HD_stmt (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho : valuation) (Q : assn) : Prop :=
  forall rhoE tp,
    (forall A' rho' rhoX tp', depot_onlyK A A' -> hd_link keep rho rho' ->
       triple segs ok (SPA segs (JGb W st A' Kc rho') (C5 W st tmax) rhoX tp') Q) ->
    triple segs ok (SPA segs (JG W st A Kc rho) (E4d W st tmax) rhoE tp) Q.

Theorem spine_s4 : forall keep (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  HD_stmt keep ok A Kc rho Q ->
  (forall A' rho' rhoX tp', depot_onlyK A A' -> hd_link keep rho rho' ->
     triple segs ok (SPA segs (JGb W st A' Kc rho') (C5 W st tmax) rhoX tp') Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q.
Proof.
  intros keep ok A Kc rho tp Q HUS HKc Hokf HD HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x7e9e4] GW [C3 W st tmax] [E4d W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert4.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HD; exact HC].
  - left. reflexivity.
Qed.
End B4S.

Section B5S.
Hypothesis Cert5 : check_cfgA segsA 4000%nat [0x3c774; 0x3c80c] GW [C5 W st tmax] [E5n W st tmax; E5f W st tmax] = true.
Variable s6n : wsub.
Hypothesis ENT6n : entailsA (E5n W st tmax) (C6 W st tmax) s6n = true.
Hypothesis SID6n : wsub_id_below s6n GW = true.
Hypothesis W5b : swf (ax_S (C5b W st tmax)) = true.
Hypothesis D5b : state_diff (ax_S (E5f W st tmax)) (ax_S (C5b W st tmax)) = Some ([(clsp_e31, SVar V_CLS); (clsp_e, SVar V_CLS)], []).
Hypothesis NX5b : ss_next (ax_S (C5b W st tmax)) = ss_next (ax_S (E5f W st tmax)).
Hypothesis F5f64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5f W st tmax))).

Theorem spine_s5 : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (liftKA Kc) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  (forall rhoX, triple segs ok (SPA segs (JGb W st A Kc rho) (C6 W st tmax) rhoX tp) Q) ->
  (forall rhoX, triple segs ok (SPA segs (JGb W st A Kc rho) (C5b W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JGb W st A Kc rho) (C5 W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt H6 H5b rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c774; 0x3c80c] GW [C5 W st tmax] [E5n W st tmax; E5f W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H6 (rho_sub rhoX s6n))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5n W st tmax) (C6 W st tmax) s6n rhoX tp w ENT6n SID6n); [|exact Hw].
      apply JGb_stable; [exact HUS | exact HKc].
    +
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H5b rhoX)].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F5f64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, E148, E149, E150, E158, E159, Hcnt |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      pose proof (pc_entry_facts segs A rhoX tp md nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & _ & Hch & _ & _).
      destruct (clsp_eval rhoX (cls_of nv) (chk_of A nv) E158 E159 ltac:(lia) Hch) as [EV1 EV2].
      unfold C5b, upd. lazy zeta. eapply SPA_restate; [exact W5b | exact D5b | exact NX5b | | constructor | exact Hw].
      unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold V_CLS; cbn [eval]; rewrite ?EV1, ?EV2, E158; reflexivity.
  - left. reflexivity.
Qed.
End B5S.

Section B6S.
Hypothesis Cert5b : check_cfgA segsA 4000%nat [0x3c7e0] GW [C5b W st tmax] [E5s1 W st tmax; E5s2 W st tmax] = true.

Definition E5s1' : axst := upd W st tmax (E5s1 W st tmax) 0x3c7e0 [(8%nat, SVar V_SIZE)] [] false [].
Definition E5s2' : axst := upd W st tmax (E5s2 W st tmax) 0x3c7e0 [(8%nat, SVar V_SIZE)] [] false [].
Hypothesis OV1 : only_var 158 (sreg1 W st tmax) = true.
Hypothesis OV2 : only_var 158 (sreg2 W st tmax) = true.
Hypothesis TAB1 : tab1_ok 158 (sreg1 W st tmax) Size 17 14%nat = true.
Hypothesis TAB2 : tab1_ok 158 (sreg2 W st tmax) Size 1 16%nat = true.
Hypothesis W1' : swf (ax_S E5s1') = true.
Hypothesis W2' : swf (ax_S E5s2') = true.
Hypothesis D1' : state_diff (ax_S (E5s1 W st tmax)) (ax_S E5s1') = Some ([(sreg1 W st tmax, SVar V_SIZE)], []).
Hypothesis D2' : state_diff (ax_S (E5s2 W st tmax)) (ax_S E5s2') = Some ([(sreg2 W st tmax, SVar V_SIZE)], []).
Hypothesis NX1' : ss_next (ax_S E5s1') = ss_next (ax_S (E5s1 W st tmax)).
Hypothesis NX2' : ss_next (ax_S E5s2') = ss_next (ax_S (E5s2 W st tmax)).
Hypothesis F1gt : In (SPBranch BC_LTU (SLit 16) (SVar V_CLS)) (ss_facts (ax_S (E5s1 W st tmax))).
Hypothesis F2le : In (SPNot (SPBranch BC_LTU (SLit 16) (SVar V_CLS))) (ss_facts (ax_S (E5s2 W st tmax))).
Hypothesis F1_64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5s1 W st tmax))).
Hypothesis F2_64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5s2 W st tmax))).
Variables s1 s2 : wsub.
Hypothesis ENT1 : entailsA E5s1' (C5c W st tmax) s1 = true.
Hypothesis ENT2 : entailsA E5s2' (C5c W st tmax) s2 = true.
Hypothesis SID1 : wsub_id_below s1 GW = true.
Hypothesis SID2 : wsub_id_below s2 GW = true.

Theorem spine_s5b : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (liftKA Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JGb W st A Kc rho) (C5c W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JGb W st A Kc rho) (C5b W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c7e0] GW [C5b W st tmax] [E5s1 W st tmax; E5s2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5b.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s1))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F1_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F1gt) as Fgt. cbn [holds eval] in Fgt. unfold V_CLS in Fgt. rewrite E158 in Fgt.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fgt, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fgt by lia. apply Z.ltb_lt in Fgt.
      assert (H' : SPA segs (JGb W st A Kc rho) E5s1' rhoX tp (tr, mkCfg ms md)).
      { unfold E5s1', upd. lazy zeta. eapply SPA_restate; [exact W1' | exact D1' | exact NX1' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 17 14%nat rhoX (cls_of nv) TAB1 OV1 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E5s1' (C5c W st tmax) s1 rhoX tp _ ENT1 SID1); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s2))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F2_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB A Kc rho rhoX tp _ _ _ Hw F2le) as Fle. cbn [holds eval] in Fle. unfold V_CLS in Fle. rewrite E158 in Fle.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fle, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fle by lia.
      assert (Hle : cls_of nv <= 16) by (destruct (Z.ltb_spec 16 (cls_of nv)); [exfalso; apply Fle; reflexivity | lia]).
      assert (H' : SPA segs (JGb W st A Kc rho) E5s2' rhoX tp (tr, mkCfg ms md)).
      { unfold E5s2', upd. lazy zeta. eapply SPA_restate; [exact W2' | exact D2' | exact NX2' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 1 16%nat rhoX (cls_of nv) TAB2 OV2 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E5s2' (C5c W st tmax) s2 rhoX tp _ ENT2 SID2); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End B6S.
End S5.
End SpineCallocS5.

(* [comment removed for export] *)
Module SpineCallocR1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "app"; "list"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "rw"; "valuation"; "holds"; "ss_facts"; "ss_objs"; "SLit"; "agree_below"; "obj_range"; "ranges_disjoint"; "smatch"; "sprop_below"; "ss_next"; "sstate"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "ag_spacebeg"; "ag_thread"; "aa_cache_inited"; "aa_geom"; "ag_ctx"; "ageom"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1"; "r0_of"; "ghostl"; "NR0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "unwind_objs"; "F_sp_high"; "KcA"; "V_DEPTH"; "chain_pre"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "FAb"; "JR"; "entryR"; "gh_chx"; "gh_new"; "gh_nf"; "ghosts"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "F_gen"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "F_r0"; "F_r1"; "GR"; "O_pcm"; "O_ri"; "cR0"; "cR0a"; "vAU"; "vMC"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kSpaceSize"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "geom_ok"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1.ZONE"; "armint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZONE.
Let segs : list Segment := segsA.
Variable W : list ulink.

Definition armint (G : ageom) (lo hi : Z) : Prop := ltac2:(tb__ "0|2|
S22S21S23S24S2aVG;A1M0Z120A2Vlo;A2S23Vhi;S24G0Zc60A2A2A2S22S21S23S29VG;A1M1Vlo;A2S23Vhi;S24S24G1S6bA2Z1000A2A2A2S21S23S6aVlo;A2S23Vhi;S69A2A2A2A2").

Lemma base_zone : ltac2:(tb__ "0|3|
S2eSdS18S2S5S49A1S48A2S5S9A1S1aS1aS6eR7A1S6fR8A1S15Vsegs;R8R7R6A4S9S38S9R1R7A3S38S9R2S10RaA1A3F_;Fo;S20S5S2S2SaSaA2SaA2M0A1S25S9G0S34R7A4S25S9G0S34S4S9S1S9S3cS4S9S3fVW;A1S3eA3A3S3dA3A4A3SeRbS40A2S26SbSeRcA1S43VW;A1A3S23S33ReA1S24S1eQ40M1ScRdPaA2A2S1fG1ScRdS42A2A2A2A2S20S1dG1A1M2ScReP97A2S1cG1S2aRfA1A2A3S20G2ScRfP98A2S1cG1S2dR10A1A2A3S71R11RcRbA3S26S9S9S14S13R12R1A2S0S1aS1aReRdA4A2Lo';ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fobjs;Fw;FS;FrhoE;FG;").
Proof.
  intros G rhoE S w objs lo hi HG0 HS3 Hsm Hsub HSK Hhigh HCH Htop E151 E152 HI.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21 G1 G2 G3 G4 G10 G11.
  pose proof (geom_bands _ HG0) as (_ & TB & CB & _ & TI & CI & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB, CB, TI, CI.
  destruct HS3 as (PS1 & PS2 & _). rewrite kSpaceSize_val in PS1, PS2.
  pose proof (topG_range G) as TG.
  unfold armint, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HI. rewrite kSpaceSize_val in HI.
  destruct objs as [|osw orest]; [cbn [map] in HSK; exfalso; clear -HSK; discriminate HSK|].
  cbn [map] in HSK.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HSK).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HSK).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm (Hsub osw (or_introl eq_refl)) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).
  assert (LNK : Forall (fun o => topG G + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG G)); [exact HCH | clear -SW0 SW2 SW3; lia | clear -TG; lia]. }
  constructor.
  - clear -SW0 G14 HI G6 TG. unfold ranges_disjoint. cbn [fst snd]. lia.
  - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (lo, hi)) orest _ SKrest).
    apply Forall_app. split.
    + apply Forall_app. split.
      * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by (clear -B TG; lia). cbn [fst snd]. clear -B G14 HI G6 TG. lia.
      * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia;
          clear -HI G5 G13 TI; lia.
    + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
             O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
      unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval];
        rewrite ?E151, ?E152, ?u64_lit by (first [ clear -G5 G6 TG; lia | clear -G8 G9 TG; lia | lia ]);
        (first [ clear -HI G5 G13 TI; lia | clear -HI G5 G6 TB TI PS1 G13 TG; lia | clear -HI G8 G9 CB CI PS2 G13 G24 TG G5 G6 G19; lia ]).
Qed.
End ZONE.

Definition NR0 : list carve_spec := ltac2:(tb__ "0|b|
S1S2S2S2SaS1aA2M0S1aA2M1S5S2S2S1aS3A2M2SaA2M3A1M4A2M5S0G1G4S0G0S1aS0SaS1aS5bZ4M6A4Z8A4S1G3S0G2SaS0S1aS3G6U4A4S64A4S6G3A1M7A3A4S1G5S0G1G4S0G0S1aS0SaS1aS68Z0M8A4Z80A4S1G3S0G2SaS0S1aS3G8U8M9A4S11G8A1MaA4S1G3S0G2SaS0S1aS3Z10G9A4S67A4S1G3S0G2SaS0S1aS3Z18G9A4S65A4S1G3S0G2SaS0S1aS3Z20G9A4S63A4S1G3S0G2SaS0S1aS3Z28G9A4GaA4S1G3S0G2SaS0S1aS3Z30G9A4S66A4S1G3S0G2SaS0S1aS3Z38G9A4GaA4S1G3S0G2SaS0S1aS3Z44U1A4GaA4G7A3A3A3A3A3A3A3A3A4S6G5A1A3A3").
Lemma NR0_objs : ltac2:(tb__ "0|0|
S20S5S9A1S25S4dS9S4cS37A4S1S9S5fS1S9S60S6S9A1A3A3A3"). Proof. reflexivity. Qed.

Definition ghostl (A : AA) (rb : valuation) : list (positive * word) := ltac2:(tb__ "0|3|
S1eQ40M0ScVrb;PcA2A2S1aS72R1A1S1aS74VA;R2A2S2fS29S2cVA;A1A1S1aS1S2S1bS1dG0A1M1A2M2S0S1bG1PdcS1cG0S6cR3A1A2A4S1G2S0S1bG1PddS1cG0S54VA;Vrb;A2A2A4S1G2S0S1bG1PdeS1cG0S31R2A1A2A4S1G2S0S1bG1PdfS1cG0S30R2A1A2A4S1G2S0S1bG1Pe0S1cG0S32R2A1A2A4S1G2S0S1bG1Pe1S1cG0S6dR1R3A2A2A4S1G2S0S1bG1Pe2S1cG0S4fVA;Vrb;A2A2A4S1G2S0S1bG1Pe3S1cG0S70R3A1A2A4S1G2S0S1bG1Pe4S1cG0S53VA;Vrb;A2A2A4S1G2S0S1bG1Pe5S1cG0S52VA;Vrb;A2A2A4S6G2A1A3A3A3A3A3A3A3A3A3A3TSB;Tcs;Tc;Tnv;").
Definition r0_of (A : AA) (rb : valuation) : valuation := ltac2:(tb__ "0|0|
S4eVrb;S36VA;Vrb;A2A2").

Lemma ghostl_ge : ltac2:(tb__ "0|1|
S28SdS1bS1dQ40A1M0S38S2S1bG0A2S0S1bG0R2R1A4S36R4R3A2A3S76PdcR3A2F_;Fv;Fj;Frb;FA;").
Proof. intros A rb j v H. unfold ghostl in H. cbn [In] in H. repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H. Qed.
Lemma r0_agree : ltac2:(tb__ "0|0|
S28SdS12PdcR1S35R2R1A2A3Frb;FA;").
Proof. intros A rb. apply agree_below_rho_sets. apply ghostl_ge. Qed.
Lemma r0_ghosts : ltac2:(tb__ "0|0|
S28SdS55R2R1S35R2R1A2A3Frb;FA;").
Proof.
  intros A rb. unfold ghosts, r0_of.
  assert (ND : List.NoDup (map fst (ghostl A rb))).
  { unfold ghostl. cbn [map fst]. repeat (constructor; [cbn [In]; intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H|]). constructor. }
  repeat split; apply (rw_rho_sets_in rb (ghostl A rb) _ _ ND); unfold ghostl; cbn [In]; tauto.
Qed.

Section ENTRY.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.

Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S20S5S2S2SaSaA2SaA2M0A1S25S9G0S34S10S27VE3;A1A1A4S25S9G0S34S4S9S4S9S1S9S3cS4S9S3fVW;A1S3eA3A3S3dA3S1S9S59S1S9S5aS6S9A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S3aSbS4SbS4SbS46VW;Vst;A2S45S44A1A3S58A3SfS27VE3;A1A1A3").
Hypothesis NX3 : ltac2:(tb__ "0|0|
S20S7S77S17S27VE3;A1A1PdcA2S8A3").
Hypothesis WR0a : ltac2:(tb__ "0|0|
S20S7S19S27S62VE3;A1A1A1S8A3").
Hypothesis FB0 : ltac2:(tb__ "0|0|
S20S7S39SbS16S5eA1S4SbSfS27VE3;A1A1S4SbS5cS5dA3A3A3S8A3").

Lemma refill_entry : ltac2:(tb__ "0|2|
S28S41SdSdS5S1dQ40M0A1A1S4bS57VW;Vst;A2S20S7S2bR7A1S8A3S20S1aS73R8S1eG0ScR6PcA2A2A2Z0A3S3bVsegs;S75VW;Vst;R9R8R7A5VE3;R6R5R4A6S21S51RaR7R6S47S4aR5A1A1M1VW;Vst;R8A7S3bVsegs;S50RaR9R7R6G1S56A6S61VE3;A1S35RaR7A2R6R5A6A2F_;F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w HW Hini Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite <- E12 in Hcnt. set (nv := bv_unsigned (rw rhoE 12%positive)) in *.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). cbn. rewrite <- E12. reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (XF3 p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F.
    rewrite u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  split.
  { unfold entryR. split; [exact Hag|]. split; [exact HA|]. split; [exact Htp|]. split; [exact HU|]. split; [exact HB|]. split; [lia|]. split; [exact Htop|]. split; [exact Hcnt|].
    exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  idtac "entry:1".

  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). pose proof HG as HG0.
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  pose proof (proj1 HI3) as HS3.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.
  pose proof (topG_range (aa_geom A)) as TG.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *.
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  assert (MS : forall z, SB <= z < SB + kSpaceSize + 4096 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. fold G SB in P4.
  destruct P4 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  idtac "entry:2".
  set (r0 := r0_of A rhoE).
  pose proof (r0_agree A rhoE) as AG0. pose proof (r0_ghosts A rhoE) as GH0. fold r0 in AG0, GH0.
  assert (Erm0 : rm r0 = rm rhoE) by (unfold r0, r0_of; apply rm_rho_sets).

  assert (Ha : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) E3 r0 tp w).
  { split.
    - eapply smatchA_agree; [|exact HsmA]. eapply agree_below_le; [|exact AG0]. apply Pos.leb_le. exact NX3.
    - unfold JR. split; [|split; [exact GH0|split; [exact HK|split; [|split]]]].
      + destruct AG0 as (Aw & Al & _). split; [exact Aw | exact Al].
      + unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
        repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia].
      + rewrite Erm0. unfold rlink, zoneR, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
        split; [intros; reflexivity|]. split.
        { intros z [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; exfalso; lia. }
        split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
      + intros a _. rewrite Erm0. reflexivity. }
  idtac "entry:3".

  destruct AG0 as (A0w & A0l & A0m).
  assert (R151 : rw r0 151%positive = Z_to_bv 64 T) by (rewrite <- (A0w 151%positive) by (clear; lia); exact E151).
  assert (R152 : rw r0 152%positive = Z_to_bv 64 (ag_ctx G)) by (rewrite <- (A0w 152%positive) by (clear; lia); exact E152).
  assert (R158 : rw r0 158%positive = Z_to_bv 64 c) by (rewrite <- (A0w 158%positive) by (clear; lia); exact E158).
  assert (R10 : rw r0 10%positive = rw rhoE 10%positive) by (rewrite <- (A0w 10%positive) by (clear; lia); reflexivity).
  assert (R15 : rw r0 V_DEPTH = rw rhoE V_DEPTH) by (rewrite <- (A0w V_DEPTH) by (unfold V_DEPTH; clear; lia); reflexivity).
  destruct GH0 as (Q220 & Q221 & Q222 & Q223 & Q224 & Q225 & Q226 & Q227 & Q228 & Q229).
  unfold gh_nf, FAb, cst_of in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold nv in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227. fold c in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold cs in Q221, Q222, Q223, Q224. fold G in Q225, Q226. fold SB in Q225, Q226.
  assert (EB : bv_unsigned (eval r0 pc_base) = T + 208 + 80 * c).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite R151, R158. rewrite add_val, add_val, mul_val, !u64_lit by (clear -C1 G5 G6 TG; lia).
    rewrite (Z.mod_small (c * 80)) by (clear -C1; lia). rewrite (Z.mod_small (T + 208)) by (clear -G5 G6 TG; lia). rewrite Z.mod_small by (clear -C1 G5 G6 TG; lia). clear; lia. }
  pose proof kSpaceSize_val as KSV.
  assert (RIr : SB + kSpaceSize <= region_info SB c /\ region_info SB c + 128 <= SB + kSpaceSize + 4096).
  { unfold region_info, kRegionInfoStride. clear -C1. lia. }
  assert (ERI : bv_unsigned (eval r0 vRI) = region_info SB c).
  { unfold vRI. cbn [eval]. rewrite Q225. apply u64_lit. rewrite kSpaceSize_val in *. clear -RIr G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }
  pose proof (proj1 Ha) as HsmA0. pose proof (proj1 HsmA0) as Hsm0. unfold virt in Hsm0. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm0.
  pose proof (smatch_facts_hold _ _ _ _ Hsm0) as HFa0.
  assert (HFX0 : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds r0 p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa0 p (XF3 p Hp)). }

  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact SK3)) as (ob & ox & EO & SKb & SKx).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range r0 oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel r0 oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r0 os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r0 os O_st SKs). unfold O_st, vT. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite R151, u64_lit by (clear -G5 G6 TG; lia). reflexivity. }
  assert (BZ : forall lo hi, armint G lo hi -> Forall (fun o' => ranges_disjoint (obj_range r0 o') (lo, hi)) ob).
  { intros lo hi HI. apply (base_zone W G r0 (ax_S E3) _ ob lo hi HG0 HS3 Hsm0); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | | exact R151 | exact R152 | exact HI].
    - apply HFX0. apply in_or_app; left. apply in_or_app; right. cbn; tauto.
    - apply Forall_forall. intros p Hp. apply HFX0. apply in_or_app; left. apply in_or_app; left.
      destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp).
    - rewrite R10, R15. exact Htop. }
  idtac "entry:4".

  assert (PRT : forall z, T <= z < T + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G5 G6 TG; lia).
    eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hz G5 G6 TG; lia | clear -Hz TI; lia]. }
  assert (PRS : forall z, SB <= z < SB + kSpaceSize + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite kSpaceSize_val in Hz. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    eapply wok_rd_off_image; [|exact Hb]. clear -Hz G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }

  assert (CVT : forall a k v (e : sv), T <= a -> a + Z.of_nat k <= T + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MT in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G5 G6 TG; lia). rewrite Erm0, Ee. exact Hc. }
  assert (CVS : forall a k v (e : sv), SB <= a -> a + Z.of_nat k <= SB + kSpaceSize + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MS in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite kSpaceSize_val in Ha2.
    rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G13 G14 TG; unfold HIGH_SHADOW_END in *; lia). rewrite Erm0, Ee. exact Hc. }
  idtac "entry:5".
  assert (Hb : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) (cR0a E3) r0 tp w).
  { apply (SPA_carve_list segs _ r0 E3 tp w NR0 GR Ha WR0a).
    - apply Pos.leb_le in NX3. clear -NX3. unfold GR. lia.
    - unfold NR0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 G5 TG; lia|]. split; [clear -C1 G5 G6 TG; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRT; [clear -Hoff C1; lia|]. destruct (PE (T + 208 + 80 * c + off) ltac:(unfold T, G, c; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MT by (clear -Hoff C1; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        apply Forall_cons; [|apply Forall_nil]. intros j Hj.
        exact (CVT (T + 208 + 80 * c + 4) 4%nat (max_count c) vMC ltac:(clear -C1; lia) ltac:(clear -C1; lia) Q220 D2 j Hj).
      + rewrite ERI. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
        split; [clear -RIr G13; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [clear -RIr G13 G14 TG; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRS; [clear -Hoff RIr KSV; lia|]. destruct (PRI (region_info SB c + off) ltac:(unfold kRegionInfoStride; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MS by (clear -Hoff RIr KSV; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted in *.
        repeat apply Forall_cons; try apply Forall_nil; intros j Hj.
        * exact (CVS (region_info SB c + 0) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R1 j Hj).
        * exact (CVS (region_info SB c + 16) 8%nat _ vNF ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q221 R2 j Hj).
        * exact (CVS (region_info SB c + 24) 8%nat _ vMFA ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q222 R3 j Hj).
        * exact (CVS (region_info SB c + 32) 8%nat _ vAU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q223 R4 j Hj).
        * exact (CVS (region_info SB c + 40) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R5 j Hj).
        * exact (CVS (region_info SB c + 48) 8%nat _ vMU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q224 R6 j Hj).
        * exact (CVS (region_info SB c + 56) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R7 j Hj).
        * exact (CVS (region_info SB c + 68) 1%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R8 j Hj).
    - idtac "entry:6". cbn [map carve_obj NR0].
      assert (RNm : obj_range r0 (carved pc_base 4 8 [(4, 4%nat, vMC)]) = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite EB. reflexivity. }
      assert (RNr : obj_range r0 (carved vRI 0 128 [(0, 8%nat, SLit 0); (16, 8%nat, vNF); (24, 8%nat, vMFA); (32, 8%nat, vAU); (40, 8%nat, SLit 0); (48, 8%nat, vMU); (56, 8%nat, SLit 0); (68, 1%nat, SLit 0)])
                    = (region_info SB c + 0, region_info SB c + 128)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite ERI. reflexivity. }
      destruct HS3 as (PS1 & _). fold T SB in PS1.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite EO; apply Forall_app; split.
      + rewrite RNm. apply BZ. left. fold T. clear -C1. lia.
      + rewrite RNm. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
      + rewrite RNr. apply BZ. right; left. fold SB. clear -RIr KSV. lia.
      + rewrite RNr. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1 RIr KSV PS1; lia.
    - cbn [map carve_obj NR0 pairwise_disjoint]. split; [|split; [constructor | exact I]].
      apply Forall_cons; [|apply Forall_nil]. unfold carved. rewrite !obj_range_mk by (clear; lia). rewrite EB, ERI.
      destruct HS3 as (PS1 & _). fold T SB in PS1. unfold ranges_disjoint; cbn [fst snd]. clear -C1 RIr KSV PS1. lia. }
  idtac "entry:7".

  unfold cR0. apply (SPA_refacts segs _ r0 (cR0a E3) _ tp w Hb FB0).
  intros HF0. apply Forall_app. split; [exact HF0|].
  assert (E155 : rw r0 155%positive = Z_to_bv 64 SB) by (rewrite <- (A0w 155%positive) by (clear; lia); rewrite <- (Hagw 155%positive) by (unfold GW; clear; lia); reflexivity).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0.
  assert (DSB : exists q, SB = q * 2 ^ 16) by (apply Z.mod_divide in G12; [destruct G12 as [q Hq]; exists q; exact Hq | clear; lia]).
  destruct DSB as [q Hq].
  unfold F_r0, F_r1, vMC, vK, vNF, vAU, vMU. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval].
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -K1 K2. lia.
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -C4. lia.
  - split; [clear; lia|]. rewrite Q225, u64_lit by (clear -RIr KSV G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    unfold region_info, kRegionInfoStride. rewrite KSV, Hq. replace (q * 2 ^ 16 + 2 ^ 37 + c * 128) with ((q * 512 + 2 ^ 30 + c) * 2 ^ 7) by (clear; lia). apply Z_mod_mult.
  - split; [clear; lia|]. rewrite Q226.
    unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize.
    rewrite u64_lit by (clear -C1 G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia).
    rewrite Hq. replace (q * 2 ^ 16 + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) with ((q * 16 + c * 2 ^ 20 + (2 ^ 20 - 2 ^ 17)) * 2 ^ 12) by (clear; lia). apply Z_mod_mult.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q221, !u64_lit by (clear -N6 NF0; lia). clear -N6. lia.
  - rewrite Q223, Q224, !u64_lit by (clear -N2 N3; lia). clear -N2. lia.
  - split; [clear; lia|]. rewrite Q224, u64_lit by (clear -N2 N3; lia). exact N1.
  - split; [clear; lia|]. rewrite E155, u64_lit by (clear -G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia). exact G12.
Qed.
End ENTRY.
End SpineCallocR1.

(* [comment removed for export] *)
Module DrainS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "nat"; "list"; "pair"; "prod"; "false"; "length"; "None"; "bool"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sprop"; "cell"; "mkCell"; "sv"; "rw"; "DUnknown"; "SAlu"; "mkObj"; "valuation"; "SPUle"; "SPAlign"; "rm"; "FcsrFrm0"; "SVar"; "mkSS"; "rl"; "SExt"; "SPBranch"; "SPNot"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "of_nat"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "pc_base"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vNF"; "vMFA"; "O_ri"; "fa_e"; "vAU"; "vMU"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "NXD"; "BASED"; "F_clsD"; "F_fast"; "F_ghD"; "L_dh_f"; "O_chkD"; "O_cntD"; "O_dstD"; "O_mcD"; "Pre_dh_f"; "dh_depth_f"; "drain_zone"; "idxs"; "vCH"; "ALLOC_A"; "DH_ENT"; "DH_RET"; "NXDP"; "O_riF"; "dst_cells"; "dst_e"; "regsD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ag_spacebeg"; "cs_mapped_free_array"; "cs_free_array"; "AA"; "aa_geom"; "ag_thread"; "ageom"; "class_state"; "cs_cache"; "aa_cache_inited"; "cs_allocated_user"; "cs_mapped_user"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "kFreeArraySize"; "region_info"; "free_array"; "kFreeArrayMapSize"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "kRegionInfoStride"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "cut_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drain_grows"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.DH"; "JD"; "JLD"; "dfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mkA"; "pre_facts"; "A_globals"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "O_insta"; "O_insta2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "O_pgb"; "@Stdlib.Lists.List"; "rev"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainModel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition vCH (i : nat) : sv := SVar (Pos.of_nat (170 + i)).
Definition idxs (n : Z) : list nat := seq 0 (Z.to_nat n).
Definition O_cntD (cnt : Z) : sobj := ltac2:(tb__ "0|2|
S16S35SdZ0A1M0SdZ4M1A1S0S10S11G0G1SdVcnt;A1A3S1S10A1A3S14A5").
Definition O_mcD (n : Z) : sobj := ltac2:(tb__ "0|2|
S16S35SdZ4M0A1M1SdZ8A1S0S10S11G1G0SdS2aZ2Vn;A2A1A3S1S10A1A3S14A5").
Definition O_chkD (n : Z) : sobj := ltac2:(tb__ "0|2|
S16S35SdS28Z10M0S2aZ4M1Vn;A2A2A1SdS28G0S2aZ8Vn;A2A2A1S71S3S10S3S11SdS28G0S2aG1S28Vn;S2cR1A1A2A2A2A1G1S4dR1A1A3Li;S4cVn;A1A4S14A5").
Definition dst_e : sv := ltac2:(tb__ "0|0|
S15S62S3bS15S63S38SdZ2A1A3A3").
Definition O_dstD (n : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S54SdZ0A1SdS2aZ4Vn;A2A1Vcells;S14A5").
Definition dst_cells (n : Z) : list cell := ltac2:(tb__ "0|1|
S91S10S71S3S10S3S11SdS2aZ4M0S2cR1A1A2A1G0S1fSbQ20S4dR1A1A3A3Li;S4cVn;A1A4A2").
Definition O_riF (n : Z) (mfa' : sv) : sobj := ltac2:(tb__ "0|2|
S16S3eSdZ0A1M0SdZ80A1S0S10S11G0Z8M1G0A3S0S10S11SdZ10A1G1S15S62S38SdVn;A1A3A3S0S10S11SdZ18A1G1Vmfa';A3S0S10S11SdZ20A1G1S3cA3S0S10S11SdZ28A1G1G0A3S0S10S11SdZ30A1G1S3dA3S0S10S11SdZ38A1G1G0A3S0S10S11SdZ44A1Z1G0A3S1S10A1A3A3A3A3A3A3A3A3S14A5").

Definition DH_ENT : Z := 0x3eefc.
Definition DH_RET : Z := 0x3ef78.
Definition NXD : positive := 240%positive.
Definition NXDP : positive := 400%positive.
Definition dh_depth_f : Z := 512.
Definition ALLOC_A : Z := 0xeaa58.
Definition regsD : list sv := ltac2:(tb__ "0|1|
S78S77S0S6S3S12A2M0S5S3S12UbS35A4S0G0S5S3S12UcSdS4eA1A4S0G0S5S3S12UdS1cS36A1A4S1G0A1A3A3A3A2").
Definition F_clsD : list sprop := ltac2:(tb__ "0|1|
S0SfS18SdZ1A1S1cS36A1M0A2S0SfS18G0SdZ1eA1A2S1SfA1A3A3").
Definition F_ghD : list sprop := ltac2:(tb__ "0|0|
S0SfS19Pe1Z7A2S0SfS19P9bZ10A2S0SfS18S38SdZ8000000A1A2S0SfS19PdeZ12A2S0SfS18S39SdZ20000000A1A2S1SfA1A3A3A3A3A3").
Definition F_fast (n : Z) : sprop := ltac2:(tb__ "0|0|
S21S20S64S39S15S63S15S62S38SdVn;A1A3SdZ2A1A3A3A1").
Definition BASED : list sobj := ltac2:(tb__ "0|0|
S0SeS86S2SeS85S0SeS8eS0SeS8fS0SeS90S1SeA1A3A3A3A3A3").
Definition Pre_dh_f (n : Z) : axst := ltac2:(tb__ "0|0|
S83S1dS4fS55S75S1bS9S12A1S2SeS40S0SeS45Vn;A1S0SeS48Vn;A1S0SeS46S2aZ2Vn;A2A1S0SeS3aS0SeS47Vn;S1S10A1A2S1SeA1A3A3A3A3A3A3S2SfS84S4aA1S2SfS41S2SfS43S0SfS42Vn;A1S1SfA1A3A3A3A3S3fS7A9S1S6S12S12A2A1A2").
Definition L_dh_f (n : Z) : axst := ltac2:(tb__ "0|0|
S83S1dS50S76S3fA1S75S1bS9S12A1S2SeS40S0SeS45Vn;A1S0SeS48Vn;A1S0SeS46Vn;A1S0SeS52Vn;S39A2S0SeS47Vn;S53Vn;A1A2S1SeA1A3A3A3A3A3A3S2SfS84S4aA1S2SfS41S2SfS43S0SfS42Vn;A1S1SfA1A3A3A3A3S51S7A9S1S6S12S12A2A1A2").

Definition drain_zone (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|2|
S5bVG;A1S26S56VG;A1S26S28S28R2Zd0A2S2aZ50Vc;A2A2S26S67R2Vc;A2S26S68R3Vc;A2S26S2cS8S26S58Vcs;A1A2A1S26S28R2S57Vcs;A1A2S26S24S22S29R5Vz;A2S2bVz;S28R5Z4M0A2A2A2S24S22S29S28R3S2aG0R2A2A2Vz;A2S2bVz;S28R3S2aG0S28R2S6fVc;A1A2A2A2A2A2S24S22S29R4Vz;A2S2bVz;S28R4Z80A2A2A2S22S23SaS7cVc;Vcs;A2SbA3S24S22S29R1Vz;A2S2bVz;S28R1S69A2A2A2S22S29S65R1A1M1Vz;A2S2bVz;S28G1Z8000A2A2A2A2A2A2A2A2TF0;Tnf;Tfa;Tri;Tpce;TSB;TT;").

Lemma drain_zone_where : ltac2:(tb__ "0|5|
S5cS26S5dS26S22S29Z1R3A2S29R3Z1eA2A2S29S28S57R3A1S69A2S66A2S29Z0M0S57R4A1A2S29S2aZ4S28S2cS8S26S58R5A1A2A1S6fR6A1A2A2S66A2S29G0S56R8A1A2S4bR9R8R7R6A4S5bRaA1S26S56RbA1S26S68R1RbA2S26S24S22S29S28S28R3Zd0A2S2aZ50M1RcA2A2M2RaA2S2bRaS28G2G1A2A2A2S24S22S29S67R2RcA2M3RaA2S2bRaS28G3S6dA2A2A2S24S22S29R1RaA2S2bRaS28R1S66A2M4A2A2S22S29S65R1A1RaA2S2bRaS65G4A1A2A2A2A2A2Tfa;TSB;TT;F_;F_;F_;F_;F_;F_;Fz;Fcs;Fc;FG;").
Proof.
  intros G c cs z Hc HM HM0 HN HSB HZ T SB fa. unfold drain_zone in HZ. cbv zeta in HZ. fold T SB fa in HZ.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. destruct (kchunks_facts c Hc) as (K1 & _).
  unfold kRegionInfoStride, kFreeArraySize, kFreeArrayMapSize in *.
  destruct HZ as [H|[H|[H|(_ & [H|H])]]].
  - left. lia.
  - right; right; left. lia.
  - right; left. lia.
  - right; right; left. lia.
  - right; right; right.
    assert (FA0 : 0 <= fa) by (unfold fa, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
    pose proof (Geometry.Sh_mono fa (fa + cs_mapped_free_array cs) ltac:(lia)) as M1.
    assert (M2 : Sh (fa + cs_mapped_free_array cs) + 32768 <= Sh (fa + 2 ^ 29)).
    { change (2 ^ 29) with 536870912. unfold Sh. pose proof (Z.div_le_mono (fa + cs_mapped_free_array cs + 262144) (fa + 536870912) 8 ltac:(lia) ltac:(lia)) as D.
      replace (fa + cs_mapped_free_array cs + 262144) with ((fa + cs_mapped_free_array cs) + 32768 * 8) in D by lia.
      rewrite Z.div_add in D by lia. lia. }
    lia.
Qed.

Section DH.
Variable n : Z.

Definition dfacts (g : bool) (A : AA) (c : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S5aVA;A1S5cS88VA;Vc;A2S5dS22S23SaS5fVA;A1SbA3S22S22S29Z1Vc;A2S29Vc;Z1eA2A2S22S23S26S6fVc;A1Vn;A3S22S23S26S2cS8S26S5eR1A1A2A1S6eVc;A1A3S22S23SaS7cVc;R1A2Vg;A3S22S23S30Q40M0A1M1S13Vrho;S36A2S2fG0Vc;A2A3S22S23G1S13Vrho;S37A2S2fG0S6cVc;A1A2A3S22S23G1S13Vrho;PddA2S2fG0S2cS8S26S58R1A1A2A1A2A3S22S23G1S13Vrho;PdeA2S2fG0S57R1A1A2A3S22S23G1S13Vrho;PdfA2S2fG0S60R1A1A2A3S22S23G1S13Vrho;Pe0A2S2fG0S61R1A1A2A3S22S23G1S13Vrho;Pe1A2S2fG0S67S56R2A1Vc;A2A2A3S3S89R1S2dVn;A1M2A2S23G1S13Vrho;S92S70UaaR2A2A1A2S2fG0S72S26S70G2R2A2S5eR3A1Z0A4A2A3F_;Fi;A2A2A2A2A2A2A2A2A2A2A2A2Tcs;TG;").
Definition JD (g : bool) (A : AA) (Kc : KcA) (c : Z) : jpredA := ltac2:(tb__ "0|0|
S17S4S30Q40A1A1S4S74A1S73S22S87VKc;VA;R4R3R2R1A6S80Vg;VA;Vc;R4A4A2Lmd;Ltr;Ltp;Lrho;").
Definition JLD (A : AA) (Kc : KcA) (c : Z) : jpostA := ltac2:(tb__ "0|8|
S17S4S30Q40M0A1M1A1M2S17G2S4S74A1S73S22S87VKc;S7dVA;Vc;A2R4R3R2R1A6S22G1S25S4bS5aVA;A1Vc;S88VA;Vc;A2S31G0R1A2M3A4A1S23ScS30Q8A1M4A1M5S1aR6R2A2S1aR8R2A2M6A3F_;Fa;S22G1S22S29S6bG3A2S2bG3S6aA2A2S25S23G5G6S9G4A1M7A3A1S25S23G5S1aR7R3A2G7A3A1F_;F_;Fa;S27S23S4G4A1S1eR5R1A2S1eR7R1A2A3Fl;A2A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition drain_contract_f : Prop := ltac2:(tb__ "0|1|
S8cOF_;S59S81S26S17S4S30Q40A1A1S82R4A1S7bS2eR7S7aR5A1A3S8dS2eR8S7aR6A1A3S8bS2eR9S79S2eS7eS7R8R7R6A4S49Vn;A1R5R4A5S34S2eS3fR5R4S0S6S32S33A2M0S5S32S33S44Vn;A1S7fR8R7R6A3A4S1G0A1A3A5A4F_;F_;F_;Ftp;Frho;Fc;FKc;FA;Fok;").
Definition drain_contract_fE : Prop := ltac2:(tb__ "0|1|
S59S81S26S17S4S30Q40A1A1S82R4A1S8aS2eS79S2eS7eS7R6R5R4A4S49Vn;A1R3R2A5S34S2eS3fR3R2S0S6S32S33A2M0S5S32S33S44Vn;A1S7fR6R5R4A3A4S1G0A1A3A5A3F_;Ftp;Frho;Fc;FKc;FA;").
End DH.
End DrainS.

