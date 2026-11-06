(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel af SpineCallocS4.
From Stdlib Require Permutation.
From stdpp Require list.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0 DrainModel.

(* [comment removed for export] *)
Module F0A_inst.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "app"; "nil"; "list"; "true"; "bool"; "None"; "false"; "Some"; "option"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "SVar"; "FcsrFrm0"; "mkSS"; "sprop"; "swf"; "valuation"; "DUnknown"; "cell"; "eval"; "mkObj"; "agree_below"; "rm"; "rw"; "soff"; "sprop_below"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "div"; "opp"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "ae_free"; "Pre_freeI"; "ulink"; "A_globals"; "GOT_HI"; "GOT_LO"; "J_free_preT"; "KcA"; "RTC_HI"; "RTC_LO"; "UStopLeOrPc"; "V_FREE_A1"; "free_depth"; "mkA"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "ustop"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "seqN"; "NFS"; "NRT"; "NV"; "sa_f"; "O_pad"; "XI"; "instF_facts"; "sb_f"; "sc_f"; "sd_f"; "se_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "NF"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXMerge"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "QG"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_sh"; "qvar"; "cA"; "O_blkN"; "RT_f"; "VOBJ"; "cQ"; "cp_baseF"; "iam_base"; "vHW"; "vMINq"; "vN8"; "vNLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "DPMCELL"; "MLIMCELL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "cells_in_view"; "cells_inside"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "FACTSc"; "P0_fc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineCacheMax"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "vQB"; "item_base"; "nb_base"; "vBS"; "vCP"; "vCS"; "vK"; "vMX"; "vNX"; "vPK"; "vQF"; "vQN"; "vQS"; "vSB"; "vST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit"; "N_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst.Iface"; "zone_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst.States"; "sd_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI";
"stopJ_stable"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition NRT : list carve_spec := ltac2:(tb__ "0|19|
S1S3S3S3S10SeA2M0SeA2M1S6S3S3SeS2A2M2S10A2M3A1M4A2M5S0G1G4S0G0SeS0S10SeS12Z0A1M6Z180e88M7A4Z180e8aA4S1G3S0G2S10S0SeS2G7U1M8A4S12Z1M9A1A4S1G3S0G2S10S0SeS2Z180e89G8A4G6A4S5G3A1MaA3A3A4S4S2dS90S1G5S0G1G4S0G0SeS0S10SeG6Z183018MbA4Z18301cA4S1G3S0G2S10S0SeS2GbU4McA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z182f1cMdA4Z182f20A4S1G3S0G2S10S0SeS2GdGcA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6S6bA4S23S6bG9A2A4S1G3S0G2S10S0SeS2S6bG8A4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6S6cA4S23S6cZ8A2A4S1G3S0G2S10S0SeS2S6cU8MeA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z182ec0MfA4Z182ed0A4S1G3S0G2S10S0SeS2GfGeA4G6A4S1G3S0G2S10S0SeS2Z182ec8GeA4G6A4GaA3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Ze9af0M10A4Ze9af8A4S1G3S0G2S10S0SeS2G10GeA4S12Zde378A1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z182fa0M11A4Z182fa8A4S1G3S0G2S10S0SeS2G11GeA4S12ZffffffffffffffffA1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeec24M12A4Zeec30A4S1G3S0G2S10S0SeS2G12GcA4S12Z1000A1A4S1G3S0G2S10S0SeS2Zeec28GcA4G6A4S1G3S0G2S10S0SeS2Zeec2cGcA4S12ZbeA1A4GaA3A3A3A4S1G5S0G1G4S0G0SeS0S10SeG6S23S59Z50A2M13A4S23S59Z58A2A4S1G3S0G2S10S0SeS2G13GeA4S12S7cA1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6S23S59Z40A2M14A4G13A4S1G3S0G2S10S0SeS2G14GeA4S12S7dA1A4S1G3S0G2S10S0SeS2S23S59Z48A2GeA4S68A4GaA3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeddb8M15A4Zeddc0A4S1G3S0G2S10S0SeS2G15GeA4S8bA4GaA3A4S1G5S0G1G4S0G0SeS0S10SeS75Zad0A4Zae0A4GaA4S1G5S0G1G4S0G0SeS0S10SeS60Za10M16A4Za18A4S1G3S0G2S10S0SeS2G16GeA4S8cA4GaA3A4S1G5S0G1G4S0G0SeS0S10SeS75Zae8A4Zc60A4GaA4S1G5S0G1G4S0G0SeS0S10SeS66Zf2608M17A4Zf2610A4S1G3S0G2S10S0SeS2G17GeA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeS13PcA1N10M18A4N8A4S1G3S0G2S10S0SeS2G18GcA4S67A4S1G3S0G2S10S0SeS2NcGcA4S6aA4GaA3A3A4S5G5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
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
S28S22Vlo;Vhi;A2S2aS28S22Ze4000Vlo;A2S28S22Vhi;S78A2S28S2aS22Vhi;S35A2S22S34Vlo;A2A2S2aS22Vhi;S39A2S22S38Vlo;A2A2A2A2A2S28S22Z1000Vlo;A2S28S22Vhi;Vtop;A2S28S2aS22Vhi;S79A2S22S78Vlo;A2A2S28S2aS22Vhi;S7bA2S22S7aVlo;A2A2S2aS22Vhi;Vp;A2S22S23Vp;Vn8;A2Vlo;A2A2A2A2A2A2A2A2").
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
Module SpineCallocS5.


From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
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
Hypothesis Cert3p : check_cfgA segsA 4000%nat [0x40cc4; 0x3c480] GW [C2p W st tmax] [E3p W st tmax] = true.
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
  apply (cfg_soundA segs 4000%nat [0x40cc4; 0x3c480] GW [C2p W st tmax] [E3p W st tmax] (JG W st A Kc rho) ok Q tp).
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
Hypothesis Cert3r : check_cfgA segsA 4000%nat [0x40cc4; 0x3c480] GW [C2r W st tmax] [E3r W st tmax] = true.
Theorem spine_s3r : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (E3r W st tmax) rhoE tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C2r W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HR rhoE.
  apply (cfg_soundA segs 4000%nat [0x40cc4; 0x3c480] GW [C2r W st tmax] [E3r W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert3r.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End B2S.

Section B4S.
Hypothesis Cert4 : check_cfgA segsA 4000%nat [0x7e850] GW [C3 W st tmax] [E4d W st tmax] = true.

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
  apply (cfg_soundA segs 4000%nat [0x7e850] GW [C3 W st tmax] [E4d W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert4.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HD; exact HC].
  - left. reflexivity.
Qed.
End B4S.

Section B5S.
Hypothesis Cert5 : check_cfgA segsA 4000%nat [0x3c5e0; 0x3c678] GW [C5 W st tmax] [E5n W st tmax; E5f W st tmax] = true.
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
  apply (cfg_soundA segs 4000%nat [0x3c5e0; 0x3c678] GW [C5 W st tmax] [E5n W st tmax; E5f W st tmax] (JGb W st A Kc rho) ok Q tp).
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
Hypothesis Cert5b : check_cfgA segsA 4000%nat [0x3c64c] GW [C5b W st tmax] [E5s1 W st tmax; E5s2 W st tmax] = true.

Definition E5s1' : axst := upd W st tmax (E5s1 W st tmax) 0x3c64c [(8%nat, SVar V_SIZE)] [] false [].
Definition E5s2' : axst := upd W st tmax (E5s2 W st tmax) 0x3c64c [(8%nat, SVar V_SIZE)] [] false [].
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
  apply (cfg_soundA segs 4000%nat [0x3c64c] GW [C5b W st tmax] [E5s1 W st tmax; E5s2 W st tmax] (JGb W st A Kc rho) ok Q tp).
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
Module InvQ9.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "qb_addr"; "ageom"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "q_ids"; "qitems"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3"; "KQ_regroup"; "KQ_secband"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws ContractFreeNull RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem K0_secband : ltac2:(tb__ "0|0|
S6SdS7R1A1A1FKc;").
Proof.
  intros Kc A rho tp tr md (HA & HK & Htp & Htop & HRG) it Hit EP.
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  destruct R5 as [QF _].
  unfold qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit).
  pose proof (proj1 (Forall_forall _ _) QF b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
  destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
  destruct R4 as [S1 _]. destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (rz_sec (snd it) IP2 EP) as RZ.
  assert (RU : snd it <= round_up (snd it) 8) by (unfold round_up; pose proof (Z.div_mod (snd it + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (snd it + 8 - 1) 8 ltac:(lia)); lia).
  destruct D10 as (_ & _ & _ & _ & DB). unfold PG in *. rewrite RZ. clear - DB Eu Esz D8 RU IP2. destruct DB as [DB|DB]; [left | right]; lia.
Qed.

Lemma q_ids_regroup : ltac2:(tb__ "0|1|
S3SaS1A1M0G0S0S4S0S5S1S0S2R3A4S5S1S0S2R2A4A3S4SbS0S0A2S9R4A1S9R3A1A3S4S0S8R6R5R3A3S8R6R4R3A3A3F_;F_;Fc;Fl';Fl;FG;").
Proof.
  intros G l l' c P1 P2. unfold q_ids. apply Permutation_app.
  - apply Permutation_map. apply Permutation_lfilter. exact P2.
  - destruct (c =? 24); [|apply Permutation_refl].
    assert (E : forall k, map (qb_id G) k = map (fun a => ptr_to_compact (ag_spacebeg G) 24 a) (map qb_addr k)) by (intros k; rewrite map_map; reflexivity).
    rewrite !E. apply Permutation_map. exact P1.
Qed.

Theorem K0_regroup : ltac2:(tb__ "0|0|
S6ScS7R1A1A1FKc;").
Proof.
  intros Kc A t g rho tp tr md P1 P2 P3 (HA & HK & Htp & Htop & HRG).
  split; [|exact (conj HK (conj Htp (conj Htop HRG)))].
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  change (aa_geom (set_q A t g)) with (aa_geom A).
  assert (OLDB : forall b, In b (t ++ g) -> exists b0, In b0 (qall A) /\ qb_addr b0 = qb_addr b).
  { intros b Hb. assert (HA0 : In (qb_addr b) (map qb_addr (qall A))) by (apply (Permutation_in _ (Permutation_sym P1)); apply in_map; exact Hb).
    apply in_map_iff in HA0 as (b0 & EA & Hb0). exists b0. split; assumption. }
  assert (OLDI : forall b it, In b (t ++ g) -> In it (qb_items b) -> exists b1, In b1 (qall A) /\ In it (qb_items b1)).
  { intros b it Hb Hit. assert (Hit0 : In it (qitems (qall A))) by (apply (Permutation_in _ (Permutation_sym P2)); unfold qitems; apply in_flat_map; exists b; split; assumption).
    unfold qitems in Hit0. apply in_flat_map in Hit0. exact Hit0. }
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|split; [exact HM|split; [|exact HB]]].
  - destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
    split; [exact R1|]. split; [exact R2|]. split.
    { destruct R3 as (Q1 & Q2 & Q3 & Q4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
      intros c Hc. specialize (Q4 c Hc). change (aa_cls (set_q A t g)) with (aa_cls A).
      unfold class_repr in Q4 |- *. change (aa_live (set_q A t g)) with (aa_live A). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      rewrite set_q_qall.
      destruct Q4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & ND & CL & CI1 & CI2 & CT & CC & CMU & CFA).
      repeat (split; [assumption|]). change (aa_geom (set_q A t g)) with (aa_geom A). change (live_ids (aa_geom A) (set_q A t g) c) with (live_ids (aa_geom A) A c).
      split; [|split; [exact CL | split; [exact CI1 | split; [exact CI2 | split; [exact CT | split; [|exact (conj CMU CFA)]]]]]].
      + eapply ND_permQ; [|exact ND]. rewrite !app_assoc. apply Permutation_app_head. apply q_ids_regroup; apply Permutation_sym; assumption.
      + rewrite <- (Permutation_length (q_ids_regroup (aa_geom A) _ _ c P1 P2)). exact CC. }
    split; [exact R4|]. split; [|exact (conj R6 (conj R7 (conj R8 R9)))].
    split; [|exact R5m]. destruct R5 as [QF QN]. unfold q_pure. rewrite set_q_qall. split.
    + apply Forall_forall. intros b Hb. destruct (OLDB b Hb) as (b0 & Hb0 & EA).
      pose proof (proj1 (Forall_forall _ _) QF b0 Hb0) as (B1 & B2 & B3 & B4).
      unfold batch_pure. rewrite <- EA. split; [exact B1|]. split; [exact (proj1 (Forall_forall _ _) P3 b Hb)|]. split; [exact B3|].
      apply Forall_forall. intros it Hit. destruct (OLDI b it Hb Hit) as (b1 & Hb1 & Hit1).
      pose proof (proj1 (Forall_forall _ _) QF b1 Hb1) as (_ & _ & _ & HIP). exact (proj1 (Forall_forall _ _) HIP it Hit1).
    + eapply ND_permQ; [exact (Permutation_sym P1) | exact QN].
  - destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbn zeta.
    change (aa_geom (set_q A t g)) with (aa_geom A). change (aa_live (set_q A t g)) with (aa_live A). change (aa_sec (set_q A t g)) with (aa_sec A).
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
    split.
    { intros z Hz. apply I4. unfold q_foot in *. change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g) in Hz.
      apply Exists_exists in Hz as (b & Hb & Hz). destruct Hz as [Hz|Hz].
      - destruct (OLDB b Hb) as (b0 & Hb0 & EA). apply Exists_exists. exists b0. split; [exact Hb0|]. left. rewrite EA. exact Hz.
      - apply Exists_exists in Hz as (it & Hit & Hz). destruct (OLDI b it Hb Hit) as (b1 & Hb1 & Hit1).
        apply Exists_exists. exists b1. split; [exact Hb1|]. right. apply Exists_exists. exists it. split; [exact Hit1 | exact Hz]. }
    split; [exact I5|]. split.
    { rewrite set_q_qall. eapply ND_permQ; [|exact I6]. apply Permutation_app_head. apply Permutation_map. apply Permutation_lfilter. exact (Permutation_sym P2). }
    split; [|split].
    { unfold qlarge, large_live in *. rewrite set_q_qall. change (aa_live (set_q A t g)) with (aa_live A).
      rewrite <- (Permutation_length (Permutation_lfilter is_large _ _ P2)). exact I7. }
    { exact I8. }
    { change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      intros NE. apply I9. intros E. apply NE. unfold qall in P1. rewrite E in P1. cbn [map] in P1. apply Permutation_nil in P1. exact (map_eq_nil _ _ P1). }
Qed.
End InvQ9.

(* [comment removed for export] *)
Module DrainS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "nat"; "list"; "pair"; "prod"; "false"; "length"; "None"; "bool"; "true"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sprop"; "cell"; "mkCell"; "sv"; "rw"; "DUnknown"; "SAlu"; "mkObj"; "valuation"; "SPUle"; "SPAlign"; "rm"; "FcsrFrm0"; "SVar"; "mkSS"; "rl"; "SExt"; "SPBranch"; "SPNot"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "of_nat"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "pc_base"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vNF"; "vMFA"; "O_ri"; "fa_e"; "vAU"; "vMU"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "BASED"; "F_clsD"; "F_fast"; "F_ghD"; "L_dh_f"; "O_chkD"; "O_cntD"; "O_dstD"; "O_mcD"; "Pre_dh_f"; "dh_depth_f"; "drain_zone"; "idxs"; "vCH"; "ALLOC_A"; "DH_ENT"; "DH_RET"; "NXDP"; "O_riF"; "dst_cells"; "dst_e"; "regsD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ag_spacebeg"; "cs_mapped_free_array"; "cs_free_array"; "AA"; "aa_geom"; "ag_thread"; "ageom"; "class_state"; "cs_cache"; "aa_cache_inited"; "cs_allocated_user"; "cs_mapped_user"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "kFreeArraySize"; "region_info"; "free_array"; "kFreeArrayMapSize"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "kRegionInfoStride"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "cut_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drain_grows"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.DH"; "JD"; "JLD"; "dfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mkA"; "pre_facts"; "A_globals"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "O_insta"; "O_insta2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "O_pgb"; "@Stdlib.Lists.List"; "rev"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

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

Definition DH_ENT : Z := 0x3ed68.
Definition DH_RET : Z := 0x3ede4.
Definition NXD : positive := 240%positive.
Definition NXDP : positive := 400%positive.
Definition dh_depth_f : Z := 512.
Definition ALLOC_A : Z := 0xedd98.
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

(* [comment removed for export] *)
Module InvQ2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "kUserSpaceSize"; "region_beg"; "free_array"; "kFreeArraySize"; "kSpaceSize"; "region_info"; "@Corelib.Init.Datatypes"; "option"; "None"; "Some"; "list"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "aa_live"; "ag_thread"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "cls_of"; "q_pure"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "present_but"; "QG"; "class_repr"; "geom_ok"; "primary_repr"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "present"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2"; "cls_metaV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2.QWhere"; "qw_where"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws RebuildM SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cls_metaV (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|3|
S11S18VG;A1M0Vc;A2S5SeG0Vc;A2S5S8S6S0R2Vz;A2S2Vz;S1R2Z80A2A2A2S8S6S0R1Vz;A2S2Vz;S1R1S1cVcs;A1A2A2A2S6S0S1S1S1fVG;A1Zd0A2S3Z50M1Vc;A2A2M2Vz;A2S2Vz;S1G2G1A2A2A2A2A2Tfa;Tri;").

Lemma class_repr_view_gen : ltac2:(tb__ "0|2|
S2cS2cS20S19S5S1aS6S0Z1R2A2S0R2Z1eA2A2S5S2dR6R4R3R1A4S7S12S24Q8A1A1R8R2A1R9R2A1A3F_;Fz;S25R7SdS18R6A1R4A2M0S1G0S1dR3A1A2S1eR5A1A4S2bR8SbSdS18R7A1R5A2M1A1SbS1G1S1dR4A1A2A1A3S27RaR8R7R6R5A5S27RaR9R8R7R6A5F_;F_;F_;F_;F_;Fcs;Fc;FA;FG;Fm';Fm;").
Proof.
  intros m m' G A c cs Hc AG PU' PS' P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat -> cls_metaV G c cs (c_addr cc + Z.of_nat k)) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  unfold class_repr in P4 |- *.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & CT & CC & CMU & CFA).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat -> cls_metaV G c cs (ri + off + Z.of_nat k)).
  { intros off w Ho Hw k Hk. left. unfold ri in *. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AG; left; unfold ri in *; unfold kRegionInfoStride in Hz; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right; left.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold fa in *. lia. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AG; right; left; unfold fa in *; lia|].
  split; [exact N7|].
  split; [exact PU'|].
  split; [exact PS'|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AG; right; right; lia|].
  split; [exact ND|].
  split; [exact LV|].
  split.
  - intros Hi. destruct (CI Hi) as (K1 & K2 & K3 & K4 & K5). split; [|split; [|split; [|split; [|exact K5]]]].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K1].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K2].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K3].
    + intros i x Hi'. apply CA; [|exact (K4 i x Hi')]. cbn [c_addr c_w]. intros k Hk. right; right.
      pose proof (nth_error_Some_lt _ _ _ Hi') as L. pose proof (max_count_le16 c Hc). lia.
  - split; [|exact (conj CT (conj CC (conj CMU CFA)))].
    intros Hn. destruct (CN Hn) as [K1 K2]. split; [exact K1|]. eapply filled_agree; [|exact K2]. intros z Hz. apply AG. right; right. lia.
Qed.

Section QWhere.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S5S6S0Z1R1A2S0R1Z1eA2A2S6S0Z0S1bS22VA;R2A2A1M0A2S0G0ScA2A2F_;Fc;").
Let G := aa_geom A. Let SB := ag_spacebeg G. Let T := ag_thread G.

Definition qw_where (z : Z) : Prop := ltac2:(tb__ "0|1|
S8SaS5S5S6S6S0Z1R1A2S0R1Z1eA2A2S6S0S1VSB;S3R1S4Z2Z20A2A2A2M0Vz;A2S2Vz;S1G0ScA2A2A2A2Lc;A2S8S6S0SbVSB;A1Vz;A2S2Vz;SbS1VSB;S10A2A1A2A2S8S6S0S1VT;Z50A2Vz;A2S2Vz;S1VT;Z70A2A2A2S8S6S0S1S26Z98A2Vz;A2S2Vz;S1S26Zc0A2A2A2S6S0S1VT;Zad0A2Vz;A2S2Vz;S1VT;Zc60A2A2A2A2A2A2A2").

Lemma Sh_mono : ltac2:(tb__ "0|0|
S5S5S0R2R1A2S0SbR3A1SbR2A1A2F_;Fb;Fa;").
Proof. intros a b H. unfold Sh. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma QW_where : ltac2:(tb__ "0|0|
S5S21VA;R1A2S2eR2A1F_;Fz;").
Proof.
  intros z [HZ|[HZ|HZ]].
  - unfold qzone in HZ. apply Exists_exists in HZ as (b & Hb & HZ). destruct HZ as [HZ|HZ].
    + destruct (batch_slot A HQP HAU HG b Hb) as (y & E & Y0 & _ & Y1 & _). left. exists 24. split; [lia|]. fold G SB in E. unfold kQuarantineBatchSize in HZ. lia.
    + apply Exists_exists in HZ as (it & Hit & EP & HZ).
      assert (Hit' : In it (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists b; exact (conj Hb Hit)).
      pose proof (item_slot A HQP HAU HG it Hit' EP) as IS. cbv zeta in IS. fold G SB in IS.
      destruct IS as (C1 & R1 & _ & U1 & _ & _ & _ & RZ & _ & EU & UN & N1 & HS & TOP).
      destruct HZ as [HZ|HZ].
      * left. exists (it_cls it). split; [exact C1|]. lia.
      * right. left. pose proof (item_zones A HQP HAU HG it Hit' EP) as IZ. cbv zeta in IZ. destruct IZ as (_ & _ & _ & Z4 & Z5 & _).
        pose proof (Sh_mono SB (it_ab it) ltac:(lia)). pose proof (Sh_mono (it_ab it + Size (it_cls it)) (SB + kSpaceSize) ltac:(lia)). lia.
  - unfold qhdr_zone in HZ. fold G T in HZ. right. right. destruct HZ as [HZ|[HZ|HZ]]; [left; exact HZ | right; left; lia | right; left; lia].
  - unfold qstat_zone in HZ. fold G T in HZ. do 4 right. exact HZ.
Qed.
End QWhere.

Lemma QW_not_metaV : ltac2:(tb__ "0|5|
S19S28S17R1A1A1S2aS17R2A1A1S23R3A1S5S6S0Z1M0R1A2S0R1Z1eM1A2A2S6S0Z0M2S1bS22R6R2A2A1M3A2S0G3ScA2A2F_;Fc;S5S1aS6S0G0R2A2S0R2G1A2A2S6S0G2S1cR2A1M4A2S0G4SfA2A2S5S21RaR1A2S9S2dS17RbA1R6R5R2A4A1F_;Fz;F_;F_;Fcs;Fc;F_;F_;F_;F_;FA;").
Proof.
  intros A HG H3 HQP HAU c cs Hc Hfa z HQ HM.
  pose proof (QW_where A HG HQP HAU z HQ) as W. unfold qw_where in W.
  pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & T0 & T1 & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _). destruct H3 as (TS & _). rewrite kSpaceSize_val in TS.
  pose proof (topG_range (aa_geom A)) as TG.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (T := ag_thread (aa_geom A)) in *.
  assert (SH1 : SHADOW_BAND_LO <= Sh SB) by (pose proof (Sh_in_band SB ltac:(unfold HIGH_SHADOW_END in S1; lia)); lia).
  assert (SH2 : Sh (SB + kSpaceSize) < HIGH_SHADOW_END) by (apply Sh_lt_HSE; rewrite kSpaceSize_val; unfold HIGH_SHADOW_END in S1; lia).
  unfold cls_metaV in HM. cbn zeta in HM. fold SB T in HM.
  unfold region_info, free_array, region_beg, kUserSpaceSize, kFreeArraySize in *. unfold kRegionSize, kRegionInfoStride in *. rewrite kSpaceSize_val in *.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, IMG_LO, IMG_HI, QG in *. unfold HIGH_SHADOW_END in *.
  change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. change (2 ^ 37) with 137438953472 in *.
  destruct W as [(c' & Hc' & W)|[W|[W|[W|W]]]]; destruct HM as [HM|[HM|HM]]; try lia.
  all: destruct TS as [TS|TS]; try lia.
  all: destruct TB as [TB|TB]; try lia.
Qed.

Section ViewQ.
Variables (A : AA) (m m' : bview).
Hypothesis HOUT : ltac2:(tb__ "0|0|
S5S9S21VA;R1A2A1S7S12S24Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S5S21VA;R1A2S9S7S12S24Q8A1M0A1M1Vm;R2A1S13G0A1M2A3A1S9S7G1Vm';R3A1G2A3A1F_;F_;Fz;").
Lemma vq_some : ltac2:(tb__ "0|3|
S5SaS24Q8A1M0G0S7S12G0A1M1Vm;R2A1S14G0R1A2M2A3Lb;A2SaG0G0S7G1Vm';R3A1G2A3Lb;A2F_;Fz;").
Proof.
  intros z [b Hb]. destruct (m' z) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  assert (NQ : ~ ~ QW A z) by (intros NQ; rewrite (HOUT z NQ), Hb in E; discriminate).
  apply NQ. intros HQ. apply (HIN z HQ); [rewrite Hb; discriminate | exact E].
Qed.
Lemma vq_present : ltac2:(tb__ "0|0|
S5S5S2bVm;R2R1A3S2bVm';R3R2A3F_;Fhi;Flo;").
Proof. intros lo hi H z Hz. exact (vq_some z (H z Hz)). Qed.
Lemma vq_present_but : ltac2:(tb__ "0|0|
S5S5S15S16S5S5A2A1S25Vm;R3R2R1A4S25Vm';R4R3R2A4F_;FL;Fhi;Flo;").
Proof. intros lo hi L H z Hz Hn. exact (vq_some z (H z Hz Hn)). Qed.

Lemma primary_repr_view : ltac2:(tb__ "0|1|
S28S17VA;A1M0A1S2aG0A1S23VA;A1S29Vm;VA;A2S29Vm';VA;A2F_;F_;F_;F_;").
Proof.
  intros HG H3 HQP (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  intros c Hc. pose proof (P4 c Hc) as HC.
  assert (HFA : 0 <= cs_mapped_free_array (nthZ (aa_cls A) c cs_empty) <= kFreeArraySize).
  { unfold class_repr in HC. cbn zeta in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N6 & _). lia. }
  apply (class_repr_view_gen m m' (aa_geom A) A c _ Hc); [| | | exact HC].
  - intros z Hz. apply HOUT. intros HQ. exact (QW_not_metaV A HG H3 HQP HAU c _ Hc HFA z HQ Hz).
  - unfold class_repr in HC. cbn zeta in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PU & _). exact (vq_present_but _ _ _ PU).
  - unfold class_repr in HC. cbn zeta in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PS & _). exact (vq_present _ _ PS).
Qed.
End ViewQ.
End InvQ2.

(* [comment removed for export] *)
Module InvEnsure.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "div"; "modulo"; "ge"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayCommit"; "kPtrArrayReserve"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "FS_total"; "IMG_LO"; "PG"; "kSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "AA"; "ag_pab"; "aa_ptr_committed"; "aa_sec"; "ageom"; "sec_chunk"; "topG"; "aa_cls"; "aa_live"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_spacebeg"; "ag_thread"; "ag_top"; "budget_bound"; "class_state"; "cs_empty"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "bool"; "option"; "false"; "true"; "Some"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "maps_subtract"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_noaccess"; "vm_limit"; "vm_maps"; "vm_reserved"; "iv_subtract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "secondary_repr"; "AInvA"; "SEC_INST"; "inv3"; "geom_ok"; "primary_repr"; "live_sep"; "nthZ"; "q_foot"; "quarantine_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "cell_ok"; "mkACell"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure"; "zens"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "cls_foot"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zens (G : ageom) (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|1|
ScSaS0S1S47Z30A2Vz;A2S2Vz;S1S47Z38A2A2A2SaS0S1S1cVG;A1S1dVA;A1A2M0Vz;A2S2Vz;S1G0SfA2A2A2A2").

Section Foot.
Let pabZ (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
SaS0S1cVG;A1M0Vz;A2S2Vz;S1G0S10A2A2A2").

Lemma pab_facts : ltac2:(tb__ "0|3|
S4fS1bS45R2R1A2S1aR2A1S1fSaS0S11S1cR1A1M0A2SaS0S1G0S10A2M1S21R1A1A2SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8S4S31S20S1eR3A1A2A1A2S1dR3A1M2A2S0G2S10A2A2SbS9S6G2SfA2Z0A3A2A2A2A2TG;F_;FA;Fm;").
Proof.
  intros m A HSR G. destruct HSR as (_ & _ & S2 & S3 & S45 & _). fold G in S45.
  pose proof (dyn_ok_big _ _ _ S45 ltac:(unfold kPtrArrayReserve; lia)) as B. destruct S45 as [_ (D1 & D2 & D3 & D4 & D5)].
  repeat split; try assumption; lia.
Qed.

Lemma sh_run_band : ltac2:(tb__ "0|2|
S9S9S9S0Z0R3A2M0G0S0S1R5R4A2Z7fffff800000A2SaS0S14R6A1M1R4A2S2R4S1G1S5S1R5Z7A2Z8A2A2A2A2SaS0S13R5A2S2R5S12A2A2F_;F_;F_;F_;Fy;Flen;Fb;").
Proof.
  intros b len y Hb Hl Htop Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono (b + len + 7) (140737479966720 + 7) 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (len + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (b + len + 7) 8 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (b + len + 7) 8 ltac:(lia)) as M3.
  lia.
Qed.
Lemma sh_run_band2 : ltac2:(tb__ "0|0|
S9S9S9S0Z0R3A2SaS0R4R3A2S0R3Z7fffff800000A2A2SaS0S14R5A1R3A2S2R3S14R4A1A2A2SaS0S13R4A2S2R4S12A2A2F_;F_;F_;Fy;Fe;Fb;").
Proof.
  intros b e y Hb He Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono e 140737479966720 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3. lia.
Qed.

Lemma live_foot_pab : ltac2:(tb__ "0|1|
S4fS1bS49S1aR1A1A1S4bR2A1S48R3A1S4aR5R4A2S45R6R5A2S9S9S9S56S30S9S9A2S32S9S9R3R2A4S23R9A1A3ScSaS0S8R4S19R3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S14R4A1M0R2A2S2R2S1G0S5S1R3Z7A2Z8A2A2A2A2A2SdVpabZ;S1aRbA1R3A2A1F_;F_;Fz;Fn;Fb;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG Hsep HI3 HPR HSR b n z Hin Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & _). unfold IMG_HI in L2. fold G in L3.
  pose proof (rz_bound n) as RZB.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct Hz as [Hz|Hz].
  2: { pose proof (sh_run_band b n z ltac:(clear -L2; lia) ltac:(clear -L1; lia) ltac:(clear -L3 ACV; lia) Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    clear -Hz BLO PS RZB. intros X. lia.
  - destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    destruct (SEC3 i ch Hi) as (_ & _ & SP & _). fold G in SP.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma q_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS49S1aR1A1A1S48R2A1S4aR4R3A2S45R5R4A2S4eR6R5A2S9S4dR7R1A2SdVpabZ;S1aR8A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG HI3 HPR HSR (Q1 & _) z Hq. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC).
  assert (REG : forall c, 1 <= c <= 30 -> SB <= region_beg SB c /\ region_beg SB c + cs_allocated_user (nthZ (aa_cls A) c cs_empty) <= SB + 2 ^ 37).
  { intros c Hc. pose proof (PC c Hc) as X. fold G SB in X. unfold class_repr in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *. unfold region_beg, kRegionSize. clear -Hc M1 M2 M3. nia. }
  assert (GSB : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). fold G SB in B7.
  destruct Hz as [Hz|Hz].
  { destruct B7 as (x & Ex & X0 & _ & XA). destruct (REG 24 ltac:(lia)) as [R1 R2]. unfold kQuarantineBatchSize in *. clear -Hz Ex X0 XA R1 R2 PS. intros X. lia. }
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ IT].
  destruct IT as (J1 & J2 & _ & _ & _ & _ & _ & _ & JP & JS & _). unfold IMG_HI in J1. fold G SB in JP.
  pose proof (rz_bound (snd it)) as RZ. set (u := fst it) in *. set (n := snd it) in *.
  destruct Hz as [Hz|Hz].
  2: {
       assert (UT : u + n <= 140737479966720).
       { destruct (is_primary n) eqn:PRM.
         - assert (Hn : 1 <= n <= 64512).
           { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
           pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
           rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
           set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -V1 V3 R1 R2 GSB ACV Y1 Y3 Hn. nia.
         - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
           destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in *.
           pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
           clear -Eu Esz D8 D11 D12 RU1 RU2 ACV J2. lia. }
       pose proof (sh_run_band u n z ltac:(clear -J1; lia) ltac:(clear -J2; lia) UT Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (is_primary n) eqn:PRM.
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
    set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -Hz V1 V3 R1 R2 PS Y1 Y3 Hn RZ. intros X. nia.
  - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in *.
    destruct (SEC3 j ch Hj) as (_ & _ & SP & _). fold G in SP.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eu Esz RZ D8 D11 RU1 RU2 J2; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma cls_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS9S49S1aR2A1A1S48R3A1S4aR5R4A2S45R6R5A2SaS0Z1R5A2S0R5Z1eA2A2S9S5eS1aR8A1R7S4cS2bS22R8A1R7S2cA4R1A4SdVpabZ;S1aR9A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c HG HI3 HPR HSR Hc z Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  destruct HI3 as (SG3 & _). fold G in SG3. destruct SG3 as (_ & _ & _ & PS & PT & _). fold SB in PS. fold T in PT. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. fold G in X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  pose proof (geom_old _ HG) as Y. rewrite kSpaceSize_val in Y. unfold HIGH_SHADOW_END in Y. fold G SB in Y.
  destruct Y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
  unfold cls_foot in Hz. cbn zeta in Hz. fold G T SB in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - clear -Hz Hc PS. intros X. lia.
  - clear -Hz Hc PS M5 M6. intros X. nia.
  - clear -Hz Hc PS M1 M2 M3. intros X. nia.
  - assert (BY : SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
    { apply (sh_run_band2 (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); [clear -Hc GS1; nia | clear -Hc M1 M2 M3 GS2 ACV; nia | exact Hz]. }
    clear -BY P3. intros X. lia.
  - clear -Hz Hc PT. intros X. lia.
Qed.
End Foot.

Lemma iv_subtract_apartE : ltac2:(tb__ "0|4|
S2dQ40M0A1M1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M2S2eG0R5A2A2R4A2S0R3G2A2A2SbS2fS30G1G1A2M3A1S44R7R6R5R4A4S38G3S32G1G1R7R6A4S39G3A1A3A3F_;F_;F_;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi Hlh Hs Hd. unfold iv_subtract. cbv zeta. destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_ge hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_lt hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma in_maps_subtract_apart : ltac2:(tb__ "0|4|
S2fS30S2dQ40M0A1M1G1A2M2A1G1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M3S2eG0R5A2A2R4A2S0R3G3A2A2S56G2S32G1G1R7R6A4R8A3S56G2S32G1G1R8R7A4S3cR9R6R5A3A3F_;F_;F_;F_;Fhi;Flo;Fsz;Fa;Fl;").
Proof.
  induction l as [|[a' s'] l IH]; intros a sz lo hi Hlh Hs Hd Hin; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [E|Hin].
  - left. injection E as -> ->. rewrite (iv_subtract_apartE a sz lo hi Hlh Hs Hd). left. reflexivity.
  - right. exact (IH _ _ _ _ Hlh Hs Hd Hin).
Qed.

Lemma maps_subtract_pos : ltac2:(tb__ "0|5|
S2fS30S2dQ40M0A1M1G1A2M2A1S9S9G1G1S56G2S32G1G1R2R1A4M3R5A3S2Z0S2eG0R2A2A2M4F_;Fs;Fb;G1G1S56G2G3S3cR6R5R4A3A3G4F_;Fs;Fb;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi H. induction l as [|[a sz] l IH]; [intros b s []|]. cbn [maps_subtract]. intros b s Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|exact (IH (fun b' s' Hi => H b' s' (or_intror Hi)) b s Hin)].
  pose proof (H a sz (or_introl eq_refl)) as Hsz. pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma covered_subtract_false : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57R6R3A2S35A3SbS33S57S3cR7R6R5A3R4A2S35A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C, H. reflexivity.
Qed.
Lemma covered_subtract_true : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57S3cR6R5R4A3R3A2S36A3SbS33S57R7R4A2S36A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C in H.
  destruct (covered l x); [reflexivity | discriminate H].
Qed.

Lemma secondary_repr_ensure : ltac2:(tb__ "0|1|
S4fS4fS1bS1aR1A1S1fS1dR2A1S9S9SdS5bR3R4R1A3A1ScS0S11R2A2SaS0S16R2A2S2R2S11A2A2A2SbS34S2dQ8A1A1R7R3A1R8R3A1A3F_;F_;Fz;S0S1R2SfA2S10A2S51R6S52S1S47Z30A2U8S5S1R3SfA2Z8A2A3A2S53R7S1S1cR5A1R4A2M0S1G0SfA2A3S48R7A1S45RaR8A2S45RaS5cR9A1A2F_;F_;F_;F_;F_;F_;Tc;TG;FA;Fm';Fm;").
Proof.
  intros m m' A. cbn zeta. intros AG HcR HC48 HPB HI3 HSR.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  destruct HI3 as (_ & _ & SEC3 & _).
  unfold secondary_repr. cbn [aa_geom aa_sec aa_ptr_committed bumpP].
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as ACV.
  assert (AGI : forall z, IMG_LO <= z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m' z = m z).
  { intros z H1 H2. apply AG; [|right; exact H1]. intros [X|X]; [exact (H2 X)|]. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (ag_pab G + c <= z < ag_pab G + c + kPtrArrayCommit) -> m' z = m z).
  { intros z H1 H2. apply AG; [|left; exact H1]. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. fold G in D10, D12.
    assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; lia).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB.
    destruct (SEC3 i ch Hi) as (_ & _ & SPB & _).
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w v) -> cell_ok m' (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGH; [clear -MB Ho; lia|]. unfold PG in D8. clear -SPB D8 D9 Ho Hw Hk P4 HcR. intros X. lia. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AGH; [clear -P1 Hk; lia | clear -L P4 Hk; intros X; lia]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply AGH; [clear -MB Hz; lia | clear -SPB Hz P4 HcR MS; intros X; lia]|].
    eapply present_agree; [|exact D14]. intros z Hz.
    pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -MB; unfold IMG_HI in MB; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
    apply AGH; [clear -BY; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; lia | clear -BY P3 P4 HcR; intros X; lia]. }
  split.
  {
    intros z Hz. destruct (Z_lt_dec z (ag_pab G + c)) as [Hlt|Hge].
    - rewrite AGH; [apply SP; lia | pose proof (Zle_0_nat (length (aa_sec A))); clear -Hz Hlt P1 H; lia | clear -Hlt; intros X; lia].
    - apply HPB. lia. }
  split; [clear -S2 HcR; unfold kPtrArrayCommit in *; lia|].
  split. { rewrite <- Z.add_mod_idemp_l by (unfold kPtrArrayCommit; lia). rewrite S3, Z.add_0_l. apply Z_mod_same_full. }
  split; [exact S45|].
  assert (CI : forall cc, (SEC_INST <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 48) \/ (SEC_INST + 56 <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= 0xee048) ->
               cell_ok m cc -> cell_ok m' cc).
  { intros cc H1. apply cell_ok_agree. intros k Hk. apply AGI; unfold SEC_INST, IMG_LO, IMG_HI in *; clear -H1 Hk; lia. }
  unfold SEC_INST in *.
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [exact HC48|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia|].
  split; [eapply cell_ok_agree; [|exact I8]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold IMG_LO, IMG_HI; clear -Hk; lia|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia.
Qed.

Theorem AInvA_ensure : ltac2:(tb__ "0|8|
S1bS54S54S2fS2dQ40A1M0A1S3dS3dS1aR6A1S1fS1dR7A1S9S1S1cR2A1R1A2S9S46S3aR9R8R6R5A5SbS9S3Z8M1S4S31S20S1eRaA1A2A1A2R3A3S0S1R4SfA2S10A2SbS2fS30G0G0A2A1M2S42S3bR7A1A1S42S3bR8A1M3A1A3SbG2S43G3A1S43S3bR9A1M4A1A3SbG2S40G4A1S3cS40S3bRaA1A1R6S1R6SfA2A3A3SbG2S3fRaA1S3cS3fRbA1R7S1R7SfA2A3A3SbS9S41S3bRbA1A1S41S3bRcA1M5A1A3SbS9S3eG5A1S3eS3bRdA1A1A3S58S40S3bReA1A1A1S58S3fRfA1A1S0S59RfR11A2S1S59R10R11A2SfA2A2S9SdS5bR10R16R1A3A1SbS34S2dQ8A1A1S50S3aS55R15A1M6R2A3S50S3aS55R16A1R2A3A3F_;Fz;S51S50S3aS55R14A1A2S52S1S47Z30A2U8S5S1RfSfA2M7G1A2A3A2S53S50S3aG6A2RfG7A3S46S3aS5cR18A1R16R15R13A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TPB;Tc;TG;Fmd';Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md md'. cbn zeta. intros HA HcN HcR EM ER EN EL ELIM ETOP WN WL HPAID VO HC48 HPB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5).
  pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3).
  pose proof SG3 as (_ & _ & _ & PS & PT & PF & PC & PD).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *. set (PB := ag_pab G + c) in *. set (T := ag_thread G) in *.
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & CI & DI). fold T in TB, TI. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI, CI, DI.
  assert (ZD : forall z, zens G A z \/ ~ zens G A z) by (intros z; unfold zens; clear; lia).

  assert (AGI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply AGH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGZ : forall z, ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H1 X)|]. apply H2. unfold PB in X. clear -X P4 HcR. lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (cc & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc. apply AGI; unfold IMG_HI, SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y; lia|]); destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      apply AGZ; unfold SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y;
        first [ clear -X Y TI PT; lia | clear -X Y CI PC; lia | clear -X Y DI PD; lia | clear -X Y G2 PF; lia ] |]); destruct Hc. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (bumpP A)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. unfold zens in Zz. fold G c in Zz.
         destruct Zz as [Zz|Zz].
         - rewrite (fs_footb_img G z HG) in Hz; [discriminate|]. unfold SEC_INST in Zz. clear -Zz. lia.
         - rewrite (fs_footb_false_intro G z) in Hz; [discriminate| | |].
           + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
             rewrite FS_frames_off_val, FS_total_val in *.
             destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
             destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
             specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
             clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    exact HF. }

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ zens G A z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGmH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGmP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> m3 z = mE z).
  { intros z H1 H2. apply AGmH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGmT : forall z, T <= z < T + 0x1000 -> m3 z = mE z).
  { intros z Hz. destruct (Z_lt_dec z IMG_HI) as [L|L].
    - apply AGmI; [exact L|]. unfold IMG_HI, SEC_INST in *. clear -Hz L TI. lia.
    - apply AGmP; [clear -L; lia|]. clear -Hz PT. intros X. lia. }
  assert (PRm : forall z, zens G A z -> exists b, m3 z = Some b).
  { intros z Hz. unfold m3.
    assert (FZ : fs_footb G z = false).
    { unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
      - apply (fs_footb_img G z HG). unfold SEC_INST in Zz. clear -Zz. lia.
      - apply (fs_footb_false_intro G z).
        + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
          rewrite FS_frames_off_val, FS_total_val in *.
          destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
          clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    rewrite maskv_out by exact FZ.
    unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
    - pose proof (HC48 (Z.to_nat (z - (SEC_INST + 48))) ltac:(cbn [c_w]; clear -Zz; lia)) as X. cbn [c_addr] in X.
      rewrite Z2Nat.id in X by (clear -Zz; lia). replace (SEC_INST + 48 + (z - (SEC_INST + 48))) with z in X by lia.
      eexists. exact X.
    - exact (HPB z Zz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (HLB : live_block_repr m3 (bumpP A)).
  { intros b n Hin. change (aa_live (bumpP A)) with (aa_live A) in Hin.
    destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
    { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & _ & _).
      pose proof (live_foot_pab mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as Y. fold G in Y. apply AGmP; [exact X | exact Y]. }
    pose proof (rz_bound n) as RZ. destruct (Hsep b n Hin) as (L1 & _).
    pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)) as DL. pose proof (Z.div_pos n 8 ltac:(clear -L1; lia) ltac:(clear; lia)) as DP.
    split; [rewrite NO by (left; clear -RZ L1; lia); exact B1|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [split|split].
    + intros g Hg. rewrite NO by (right; clear -Hg DL; lia). exact (B4 g Hg).
    + intros Hm. rewrite NO; [exact (B5 Hm)|]. right.
      replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
      clear -DP. lia.
    + apply (alloc_magic_ok_agree mE m3); [intros z Hz; apply NO; left; clear -Hz L1; lia | clear -RZ; lia | exact B6].
    + destruct B7 as (t & Ht & Hm4). exists t. split; [rewrite NO by (left; clear -RZ L1; lia); exact Ht | exact Hm4]. }
  assert (HPR' : primary_repr m3 (bumpP A)).
  { destruct HPR as (Q1 & Q2 & Q3' & P4'). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3'|].
    intros cl Hc. change (aa_geom (bumpP A)) with G. change (aa_cls (bumpP A)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (bumpP A) cl); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (P4' cl Hc)].
    intros z Hz.
    pose proof (cls_foot_pab mE A cl HG HI3 (conj Q1 (conj Q2 (conj Q3' P4'))) HSR Hc z Hz) as Y. fold G in Y.

    unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz.
    destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
    5: { apply AGmT. clear -Hz Hc. lia. }
    all: apply AGmP; [|exact Y].
    all: pose proof (geom_old _ HG) as X; rewrite kSpaceSize_val in X; unfold HIGH_SHADOW_END in X; fold G in X;
         destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
    all: unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize, kRegionInfoStride, Sh, SHADOW_OFF, IMG_HI in *.
    - clear -Hz Hc GS1. lia.
    - clear -Hz Hc GS1. nia.
    - clear -Hz Hc GS1. nia.
    - pose proof (Z.div_pos (ag_spacebeg G + cl * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2. clear -Hz D2. lia. }
  assert (HSR' : secondary_repr m3 (bumpP A)).
  { apply (secondary_repr_ensure mE m3 A); [| exact HcR | | | exact HI3 | exact HSR].
    - intros z Hz [H|H]; [|apply AGmI; [clear -H; unfold IMG_LO, IMG_HI in *; lia | intros X; apply Hz; left; exact X]].
      apply AGmH; [exact H | intros X; apply Hz; right; exact X].
    - intros k Hk. unfold m3. rewrite maskv_out; [exact (HC48 k Hk)|]. apply (fs_footb_img G _ HG). cbn [c_addr c_w] in *. unfold SEC_INST. clear -Hk. lia.
    - intros z Hz. apply PRm. right. exact Hz. }
  assert (HQR' : quarantine_repr m3 (bumpP A)).
  { apply (quarantine_repr_agreeQ mE m3 A (bumpP A)); try reflexivity.
    - exact (q_items_rz A).
    - intros z Hz. pose proof (q_foot_high mE A z HQR Hz) as QH. pose proof (q_foot_pab mE A HG HI3 HPR HSR HQR z Hz) as Y. fold G in Y.
      apply AGmP; [exact QH | exact Y].
    - intros z Hz. fold G T in Hz. apply AGmT. clear -Hz. lia.
    - intros z Hz. apply AGmI; unfold QG, SEC_INST, IMG_HI in *; clear -Hz; lia.
    - exact HQR. }
  assert (HIA' : ia_inv m3 (bumpP A)).
  { apply (ia_inv_agreeN mE m3 A (bumpP A)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, SEC_INST, IMG_HI in *; clear -Hz; lia. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. rewrite AGmT; [exact X | clear; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold SEC_INST, IMG_HI in *; clear -Hz; lia.
    - apply PRESX. destruct HMI as (_ & X & _). exact X.
    - apply PRESX. destruct HMI as (_ & _ & X). exact X. }

  unfold AInvA. change (aa_geom (bumpP A)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. split; [exact Hsep|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split.
    { unfold depot_wf in HDW |- *. change (aa_depot (bumpP A)) with (aa_depot A).
      eapply depot_mem_frame; [|exact HDW]. intros a Ha.
      destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
      - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold SEC_INST, IMG_HI; clear -Hs; lia.
      - destruct (dm_nb _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold NBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia].
      - destruct (dm_fbases _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold FBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia]. }
    split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split.
  {
    unfold model_inv in HM |- *. change (aa_geom (bumpP A)) with G in *. cbn [aa_V aa_Km aa_Kf bumpP].
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    assert (KLH : PB < PB + kPtrArrayCommit) by (unfold kPtrArrayCommit; clear; lia).
    split.
    { unfold vm_geom, in_maps in V1 |- *. cbn [aa_sec aa_geom bumpP]. fold G. fold G in V1. rewrite EM, EN, EL.
      destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      split.
      { intros e x He Hx.
        assert (CV : covered (vm_noaccess (m_vmmaps md)) x = true).
        { apply (covered_subtract_true _ PB (PB + kPtrArrayCommit) x WN ltac:(clear -KLH; lia)).
          unfold covered. apply existsb_exists. exists e. split; [exact He|]. unfold in_iv, in_rng, ivB, ivS. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        unfold covered in CV. apply existsb_exists in CV as (e0 & He0 & Hx0). unfold in_iv, in_rng, ivB, ivS in Hx0. apply andb_prop in Hx0 as [X1 X2].
        apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (N1 e0 x He0 (conj X1 X2)). }
      split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [exact N8|].
      intros p Hal Hband. destruct (N9 p Hal Hband) as [L1 L2]. split.
      - apply page_in_ranges_spec in L1 as (r & Hr & Hpr). apply page_in_range_spec in Hpr as [Q1 Q2]. change page_size with 4096 in Q2.
        assert (OUT : bv_unsigned p + 4096 <= PB \/ PB + kPtrArrayCommit <= bv_unsigned p).
        { unfold PB. clear -Hband P3 P4 HcR. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG, kPtrArrayReserve, kPtrArrayCommit in *. lia. }
        destruct (maps_subtract_keeps (m_vm_lazy md) PB (PB + kPtrArrayCommit) r (bv_unsigned p) (bv_unsigned p + 4096) WL ltac:(clear -KLH; lia) Hr Q1 Q2 ltac:(clear; lia) OUT)
          as (r' & Hr' & X1 & X2).
        apply page_in_ranges_spec. exists r'. split; [exact Hr'|]. apply page_in_range_spec. change page_size with 4096. clear -X1 X2. lia.
      - intros j Hj. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (L2 j Hj)]. }
    split; [rewrite (PrimCredit.prim_credit_same A (bumpP A) eq_refl); rewrite budget_boundD_bumpP; fold c;
            set (pcr := PrimCredit.prim_credit A) in *; clearbody pcr; clear -V2 HPAID; lia|].
    split; [rewrite ELIM; exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite ETOP; exact V7|].

    unfold ledger_inv in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_sec bumpP] in V8 |- *.
    destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    rewrite ER, EM.
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
    split.
    { unfold gap_ok, gapN_ok, gapS_ok, ledger in L4 |- *. cbn [aa_V aa_depot bumpP]. rewrite ER, EM. exact L4. }
    split.
    { destruct L5 as [D1 D2 D3 D4 D5 D6]. constructor.
      - intros bn Hbn. rewrite EM. exact (D1 bn Hbn).
      - intros b Hb. rewrite EL.
        destruct (DEP3 (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as (DY & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb, DY. fold G in SPb, DY.
        pose proof (dyn_in_big _ _ _ DY ltac:(unfold FBSZ; clear; lia)) as BB. destruct DY as (_ & _ & DT & _).
        pose proof (topG_range G) as TR.
        apply in_maps_subtract_apart; [exact KLH | rewrite u64_lit; unfold FBSZ; clear; lia | | exact (D2 b Hb)].
        rewrite !u64_lit by (unfold FBSZ, IMG_HI in *; clear -BB DT TR; lia).
        unfold PB. clear -SPb P4 HcR. unfold FBSZ, kPtrArrayReserve, kPtrArrayCommit in *. lia.
      - intros b j Hb Hj. rewrite EN. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (D3 b j Hb Hj)].
      - exact D4.
      - intros bn Hbn. rewrite ETOP. exact (D5 bn Hbn).
      - rewrite ETOP. exact D6. }
    split; [exact L6|]. split; [clear -L7 L9 HcN; fold c in L7 |- *; unfold kPtrArrayCommit in *; lia|].
    split; [unfold in_maps; rewrite ?EM; exact L8|]. split; [exact L9|]. rewrite EN. apply maps_subtract_pos. exact L10. }
  split; [exact HI3|].

  eapply bandtp_agree; [|exact HB]. intros z Hz. apply VO. unfold zens. fold G c.
  unfold SEC_INST, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve, kPtrArrayCommit in *. clear -Hz P3 P4 HcR. intros X. lia.
Qed.

Lemma AInvA_pab : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fS1dR6A1S9SaS0S11S1cR2A1M0A2SaS0S1G0S10A2M1S21R2A1M2A2SaSbS9S6G0S17A2Z0M3A3SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8M4S4S31S20S1eR7A1A2A1A2R1A2S0R1S10A2A2SaSbS9S6R1SfA2G3A3SaSbS9G2S29R2A1M5A3SaSbS9S3eS3bR4A1A1G5A3S9SaS0S1S1cR3A1M6S3G4S4S31S20S1eR8A1A2A1A2A2R1A2S2R1S1G6R2A2A2A2SeS2dQ8A1M7G7SbS34G7A1S50S3aS55R9A1R3A3S37G7R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2A2A2Tc;TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta.
  pose proof HA as (HG & _ & _ & HRest & HM & _). destruct HRest as (_ & _ & _ & HSR & _).
  pose proof (pab_facts _ X HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (_ & SP & _). destruct HM as (_ & _ & _ & _ & _ & _ & TOP & _).
  pose proof (geom_top _ HG) as GT. pose proof (geom_pab _ HG) as GP.
  repeat split; try assumption; try (clear -P4; lia).
  intros z Hz. destruct (SP z Hz) as [b Hb]. exists b. rewrite <- Hb. symmetry. apply maskv_out.
  apply (fs_footb_false_intro X.(aa_geom) z); pose proof HA as (_ & _ & _ & _ & _ & HI3 & _); destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _);
    pose proof (geom_numsS _ HG) as (_ & G2 & G3 & _); pose proof (topG_range (aa_geom X)) as TG.
  - clear -Hz PF P4. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - clear -Hz PF P4. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - rewrite FS_frames_off_val, FS_total_val in *.
    destruct (Z_lt_dec z (Sh (ag_fsb (aa_geom X) + 36864))) as [L|L]; [left; exact L|right].
    destruct (Z_le_dec (Sh (ag_fsb (aa_geom X) + 11571200)) z) as [R|R]; [exact R|exfalso].
    pose proof (sh_run_band2 (ag_fsb (aa_geom X) + 36864) (ag_fsb (aa_geom X) + 11571200) z ltac:(clear -G2; lia) ltac:(clear -G3 TG; lia) ltac:(clear -L R; lia)) as BY.
    clear -BY Hz P3 P4. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
Qed.

Lemma ensure_headroom : ltac2:(tb__ "0|0|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5SbS9S3Z8S4S31S20S1eR5A1A2A1A2S1dR5A1A3S0S2aR6A1S5dA2S7S5aR4R5A2SfA2F_;F_;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA HcN HB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _ & L9 & _).
  pose proof (budgetD_le_budget (bumpP X) (dep_cost_bound_mem _ _ HD) (dm_F_NFBLK _ _ HD) DN) as BD.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpP] in BD.
  rewrite budget_boundD_bumpP, budget_bound_bumpP in BD.
  pose proof (PrimCredit.prim_credit_nonneg X) as PCN.
  unfold headroom. rewrite VL. unfold kPtrArrayCommit in *. set (pcr := PrimCredit.prim_credit X) in *. clearbody pcr. clear -PB BD HB HcN L9 PC K0 F0 PCN. lia.
Qed.

Lemma AInvA_pabsep : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fSaScS0S1S1cR1A1M0S10A2M1S27R1A1M2A2S0S1S1G2S18A2Z1000M3A2G0A2A2SaScS0G1S28R1A1M4A2S0S1G4G3A2G0A2A2SaScS0G1S26R1A1M5A2S0S1G5S15A2G0A2A2SaScS0G1S24R1A1M6A2S0S1G6G3A2G0A2A2ScS0G1S25R1A1M7A2S0S1G7G3A2G0A2A2A2A2A2A2TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta. pose proof HA as (_ & _ & _ & _ & _ & HI3 & _).
  destruct HI3 as ((_ & _ & _ & PS & PT & PF & PC & PD) & _). repeat split; assumption.
Qed.
End InvEnsure.

