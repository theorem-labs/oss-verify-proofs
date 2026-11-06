(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "nat"; "cons"; "prod"; "nil"; "app"; "bool"; "list"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "modulo"; "mul"; "of_nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "sobj"; "SLit"; "holds"; "sprop"; "valuation"; "ss_facts"; "ss_next"; "ss_objs"; "SPBranch"; "SPNot"; "SPUle"; "SPUlt"; "mkSS"; "rm"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "zcheck"; "zdisjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "Sh"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "DQI0"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "present"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "QG"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "zloS"; "N1"; "ZUS"; "SS1"; "ZD_fixS"; "ZD_rtiS"; "ZD_sec1"; "fam_ok"; "zbS"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "topG"; "sc_size"; "@Stdlib.Lists.List"; "forallb"; "Forall2"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "vCTX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "top_high"; "GOT_HI"; "GOT_LO"; "RTC_HI"; "RTC_LO"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "vIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "F1"; "S0"; "OBJ1"; "vNCH"; "vNhi"; "vNlo"; "vPAB"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition N_sec1 : list carve_spec := ltac2:(tb__ "0|13|
S3S4S4S4S16S0A2M0S0A2M1S8S4S4S0S2A2M2S16A2M3A1M4A2M5S1G1G4S1G0S0S1S16S0S19Z0A1M6S2eA4SfS2eZ10A2A4S3G3S1G2S16S1S0S2S2eU8M7A4S19S33A1M8A4S3G3S1G2S16S1S0S2SfS2eZ8M9A2G7A4S6aA4S5G3A1MaA3A3A4S3G5S1G1G4S1G0S0S1S16S0G6SfS2eZ38A2MbA4SfS2eZ40A2McA4S3G3S1G2S16S1S0S2GbG7A4S67A4GaA3A4S3G5S1G1G4S1G0S0S1S16S0G6GcA4Zee040MdA4GaA4S3G5S1G1G4S1G0S0S1S16S0G6GdA4Zee044A4S3G3S1G2S16S1S0S2GdU4MeA4G6A4GaA3A4S3G5S1G1G4S1G0S0S1S16S0G6Zee048A4Zee070A4GaA4S3G5S1G1G4S1G0S0S1S16S0G6Z182fa0MfA4Z182fa8A4S3G3S1G2S16S1S0S2GfG7A4S19ZffffffffffffffffA1A4GaA3A4S3G5S1G1G4S1G0S0S1S16S0G6Z182fb8M10A4Z182fc0A4S3G3S1G2S16S1S0S2G10G7A4G6A4GaA3A4S3G5S1G1G4S1G0S0S1S16S0G6Z180ea0M11A4Z180ea8A4S3G3S1G2S16S1S0S2G11G7A4G8A4GaA3A4S3G5S1G1G4S1G0S0S1S16S0S5bZad0A4Zc60A4GaA4S3G5S1G1G4S1G0S0S1S16S0S63Z2M12A4G9A4S3G3S1G2S16S1S0S2G12U2A4S68A4S3G3S1G2S16S1S0S2Z4GeA4S69A4GaA3A3A4S5G5A1A3A3A3A3A3A3A3A3A3A3").
Definition N1 : list carve_spec := N_rti ++ N_sec1.
Lemma OBJ1_eq : ltac2:(tb__ "0|0|
SbS8S18A1S4fS53S18S52S47A4S66A3"). Proof. reflexivity. Qed.

Definition zloS (z : nat) : Z := match z with 0%nat => 0xe4000 | _ => 0 end.
Definition zhiS (ms : Z) (z : nat) : Z := match z with 0%nat => 0x646000 | 1%nat => 4096 | 2%nat => 4096 | 3%nat => 2 ^ 64 | _ => ms end.
Definition zbS (T CTX TOP h : Z) (z : nat) : Z := ltac2:(tb__ "0|0|
S2S0Lz;Vz;Z0S2S2S0Ln;R1VT;S2S2S0Ln0;R1VCTX;S2S2S0Ln1;R1VTOP;S2Vh;Ln2;X2x2Ln1;X2x2Ln0;X2x2Ln;X2x2").
Definition ZUS : list nat := ltac2:(tb__ "0|0|
S3S2U0S3S2U1S3S2U2S3S2U3S3S2U5S5S2A1A3A3A3A3A3").
Definition ZD_rtiS : list zdesc := ltac2:(tb__ "0|3|
S3S4S4S2S0A2M0S0A2M1S1G0S0S1S2S0U0M2Zeddb8A4Zeddc4A4S3G1S1G0S0S1S2S0G2Zeddc8A4Zeddd1A4S3G1S1G0S0S1S2S0G2Ze9af0A4Ze9af8A4S3G1S1G0S0S1S2S0G2Zf0c5cA4Zf0c5dA4S3G1S1G0S0S1S2S0G2Zf0c60A4Zf0c61A4S3G1S1G0S0S1S2S0G2Zf0c64A4Zf0c68A4S3G1S1G0S0S1S2S0G2Z624560A4Z624568A4S3G1S1G0S0S1S2S0G2Z645960A4Z645968A4S3G1S1G0S0S1S2S0U2Z98A4Za0A4S3G1S1G0S0S1S2S0G2Zf20d8A4Zf20daA4S3G1S1G0S0S1S2S0G2Zf20e0A4Zf20f8A4S5G1A1A3A3A3A3A3A3A3A3A3A3A3").
Definition ZD_sec1 : list zdesc := ltac2:(tb__ "0|5|
S3S4S4S2S0A2M0S0A2M1S1G0S0S1S2S0U0M2S2eA4SfS2eZ10A2A4S3G1S1G0S0S1S2S0G2SfS2eZ38A2A4SfS2eZ40A2M3A4S3G1S1G0S0S1S2S0G2G3A4Zee040M4A4S3G1S1G0S0S1S2S0G2G4A4Zee044A4S3G1S1G0S0S1S2S0G2Zee048A4Zee070A4S3G1S1G0S0S1S2S0G2Z182fa0A4Z182fa8A4S3G1S1G0S0S1S2S0G2Z182fb8A4Z182fc0A4S3G1S1G0S0S1S2S0G2Z180ea0A4Z180ea8A4S3G1S1G0S0S1S2S0U1Zad0A4Zc60A4S3G1S1G0S0S1S2S0U5Z17f2A4Z17f8A4S5G1A1A3A3A3A3A3A3A3A3A3A3").
Definition ZD_fixS : list zdesc := ltac2:(tb__ "0|5|
S3S4S4S2S0A2M0S0A2M1S1G0S0S1S2S0U3Z0A4S11Z2Z40M2A2A4M3S3G1G3S3G1G3S3G1G3S3G1S1G0S0S1S2S0U0M4SfS44Z98A2A4SfS44Z9cA2A4S3G1S1G0S0S1S2S0G4SfS44G2A2A4SfS44Z50A2A4S3G1S1G0S0S1S2S0G4S5fA4S5eA4S3G1S1G0S0S1S2S0G4S61A4S60A4S5G1A1A3A3A3A3A3A3A3A3").
Lemma ZDS_chk : ltac2:(tb__ "0|1|
SaSbS7S31S6S2fS4bS4cA3M0A1S9A3SbS7S56S2fS2fS56S2fS32R1A1S4aA3Ld;G0A3S9A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition SS1 : sstate := ltac2:(tb__ "0|0|
S3dS39A1S2dS24S2aR1A1S2bR1A1S28R1A1S27R1A1S2cR1A1S6S18S1fR1A1S4fS53S18S52S47A4A3S1dR1A1S1eR1A1S29R1A1A9TS;").
Lemma SS1_swf : swf SS1 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S0_eq : ltac2:(tb__ "0|1|
S2SbS3fS65R1A1S6dS3eS39S49A2M0S6S1bS1dS3dG0A1A1S64R1A1A3A2A3Ff;"). Proof. intros f. reflexivity. Qed.
Lemma S0_below : ltac2:(tb__ "0|1|
S2SbS7S56S1bS26S1eS3dS3eS39S49A2A1M0A1A1S6S1bS1dG0A1S64R1A1A3A3S9A3Ff;").
Proof. intros [|[|f]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma hle : ltac2:(tb__ "0|4|
S1cS16S16S0S0SbS3aQ40M0A1M1S17R5R4A2S3bG0R2A2M2A3SbG1S17R6R4A2G2A3SaSeZ0R4A2S10R4S11Z2Z40A2A2A2M3G3SeR6R5A2S1aRaS22R9R8A2A2F_;F_;F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof. intros rho a b x y Ea Eb Hx Hy H. cbn [holds]. rewrite Ea, Eb, !u64_lit by lia. exact H. Qed.
Lemma hlt : ltac2:(tb__ "0|4|
S1cS16S16S0S0SbS3aQ40M0A1M1S17R5R4A2S3bG0R2A2M2A3SbG1S17R6R4A2G2A3SaSeZ0R4A2S10R4S11Z2Z40A2A2A2M3G3S10R6R5A2S1aRaS23R9R8A2A2F_;F_;F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof. intros rho a b x y Ea Eb Hx Hy H. cbn [holds]. rewrite Ea, Eb, !u64_lit by lia. exact H. Qed.
Lemma hne0 : ltac2:(tb__ "0|2|
S1cS16S0SbS3aQ40M0A1S17R3R2A2S3bG0R1A2A3SaS10Z0M1R2A2S10R2S11Z2Z40A2A2A2S1aR5S21S20S6bR4S19G1A1A3A1A2F_;F_;Fx;Fa;Frho;").
Proof. intros rho a x Ea Hx. cbn [holds branch_taken eval]. intros E. unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite Ea, !u64_lit in E by lia. lia. Qed.
Lemma elit : ltac2:(tb__ "0|1|
S1cS0SbS3aQ40M0A1S17R2S19R1A1A2S3bG0R1A2A3Fk;Frho;"). Proof. reflexivity. Qed.

Definition fam_ok (f : nat) (SB h ms : Z) : Prop := ltac2:(tb__ "0|1|
S2OLf;Vf;SeSfVh;Vms;A2M0Z7fff7000A2S2S2OLn;R1SaSeZ10007fff8000Vh;A2SeG0VSB;A2A2S2SeSfSfVSB;S11Z2Z25A2A2Z1000A2Vh;A2Ln0;X2x2Ln;X2x2").

Section QSEnv.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk) (rho : valuation).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let CTX : Z := ag_ctx G.
Let SB : Z := ag_spacebeg G.
Let PAB : Z := ag_pab G.
Let h : Z := sc_map_beg ch.
Let ms : Z := sc_map_size ch.
Let u : Z := fst it.
Let n : Z := snd it.
Let NC : Z := Z.of_nat (length (aa_sec A)).
Let m : bview := ltac2:(tb__ "0|0|
S43S51S25Vrho;A1A2").

Record qsenv : Prop := mkQS {
  qs_hg : geom_ok G;
  qs_hsep3 : sep_geom3 G;
  qs_hrtc : rtc_inv m G;
  qs_hrig : rw rho 151%positive = Z_to_bv 64 T /\ rw rho 152%positive = Z_to_bv 64 CTX
            /\ rw rho 155%positive = Z_to_bv 64 SB /\ rw rho 156%positive = Z_to_bv 64 (SB + kSpaceSize);
  qs_hsr : secondary_repr m A;
  qs_hi : nth_error (aa_sec A) i = Some ch;
  qs_hu : u = h + PG + 2048;
  qs_hsz : sc_size ch = round_up n 8 + 4096;
  qs_hsep : (h + ms <= SB \/ SB + kSpaceSize + 4096 <= h) /\ (h + ms <= T \/ T + 0x1000 <= h) /\ (h + ms <= PAB \/ PAB + kPtrArrayReserve <= h)
            /\ (h + ms <= CTX \/ CTX + 0x1000 <= h)
            /\ (forall j ch', nth_error (aa_sec A) j = Some ch' -> i <> j -> h + ms <= sc_map_beg ch' \/ sc_map_beg ch' + sc_map_size ch' <= h);
  qs_him : item_mem m it;
  qs_hstat : present m (T + 2768) (T + 3168);
  qs_hn : 1 <= n;
  qs_hv : rw rho 165%positive = Z_to_bv 64 (u - 16) /\ rw rho 200%positive = Z_to_bv 64 PAB /\ rw rho 201%positive = Z_to_bv 64 NC
          /\ rw rho 207%positive = Z_to_bv 64 (n / 2 ^ 32) /\ rw rho 209%positive = Z_to_bv 64 (n mod 2 ^ 32)
}.
Hypothesis QS : qsenv.
Ltac qs_open := pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
Ltac qs_unf := unfold NC, m, n, u, ms, h, PAB, SB, CTX, T, G in *.

Lemma qs_chunk : ltac2:(tb__ "0|6|
SaSbS0S12Vh;S33A2Z0M0A3SaSbS0S12Vms;S33A2G0A3SaSeZ12000Vms;A2SaSeS35Vh;A2SaSeSfVh;Vms;A2M1S54VG;A1A2SaScSeG1S37A2SeS36Vh;A2A2SaSeSfS33S55Vch;A1M2A2Vms;A2SaSbS0Vms;SfS38G2S33A2S33A2A3SaS40Vm;S41Vh;U8M3Vh;A3A2SaS40Vm;S41SfVh;Z8M4A2G3Vms;A3A2SaS40Vm;S41SfVh;Z18A2G3S14Vi;A1M5A3A2SaS40Vm;S41SfVPAB;S13G4G5A2A2G3Vh;A3A2S42Vm;S34Vh;A1S34G1A1A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  qs_open. destruct HSR as (SC1 & _). destruct (SC1 i ch HI) as (C0 & C8 & _ & C24 & CP & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _ & D14).
  pose proof (dyn_in_big _ _ _ D10) as BIG. destruct D10 as (_ & _ & _ & _ & DB).
  qs_unf. rewrite Z.add_0_r in C0.
  assert (MS : 73728 <= sc_map_size ch).
  { rewrite D11. unfold round_up, PG in *. pose proof (Z.div_mod (sc_size ch + (4096 - 1)) 4096 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (sc_size ch + (4096 - 1)) 4096 ltac:(lia)). nia. }
  repeat split; try assumption; try lia.
Qed.

Lemma qs_nums : ltac2:(tb__ "0|6|
SaSeZ1000M0VT;A2SaSeSfVT;G0A2M1S54VG;A1M2A2SaSeG0VCTX;A2SaSeSfVCTX;G0A2M3G2A2SaSaSeZ7fff7f800000G2A2SeG2Z7fffff800000A2A2SaScSeG1Z10000M4A2SeZ646000M5VT;A2A2SaScSeG3G4A2SeG5VCTX;A2A2ScSeG1VCTX;A2SeG3VT;A2A2A2A2A2A2A2A2A2").
Proof.
  qs_open. pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1 & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). pose proof (geom_seps _ HG) as (_ & _ & _ & _ & Q5 & _).
  unfold IMG_LO, IMG_HI in *. qs_unf. repeat split; try assumption; lia.
Qed.

Lemma qs_E : ltac2:(tb__ "0|1|
SaSbS0S3cQ40M0S17Vrho;S5bA2A2VT;A3SaSbS0S3cG0S17Vrho;S5cA2A2VCTX;A3SbS0S3cG0S17Vrho;S63A2A2S15Vu;Z10A2A3A2A2").
Proof.
  qs_open. pose proof qs_nums as (T0 & T1 & C0 & C1 & TG & _). pose proof qs_chunk as (_ & _ & MS & IH & HT & _).
  destruct HRIG as (E151 & E152 & _). destruct HV as (E165 & _).
  unfold vT, vCTX, vIT. cbn [eval]. rewrite E151, E152, E165. unfold IMG_HI, PG in *. qs_unf. rewrite !u64_lit by lia. repeat split; reflexivity.
Qed.

Lemma carve_rtiS : Forall (carve_okq rho) N_rti.
Proof.
  qs_open. pose proof qs_nums as (T0 & T1 & C0 & C1' & TG & _ & CI & _).
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HR : cells_ok (view segsA (rm rho)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  qs_unf. clear HSEP3 HSR HI HU HSZ HSEP HIM HSTAT HN HV.
  unfold N_rti, vSB, vRIS, vCTX, vT. repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta; cbn [eval]; rewrite ?E152, ?u64_lit by lia.
  all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: split.
  all: try match goal with
       | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
       | |- forall off, _ -> wok_of _ _ _ = true /\ _ => intros off Hoff; wr_any2 HR ltac:(clear -CI; lia)
       end.
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E155, ?E156; civ_any2 HR.
Qed.

Lemma carve_sec1 : Forall (carve_okq rho) N_sec1.
Proof.
  qs_open. pose proof qs_nums as (T0 & T1 & C0 & C1' & TG & TI & _). pose proof qs_chunk as (_ & _ & MS & IH & HT & _).
  pose proof qs_E as (EvT & _ & EvIT).
  destruct HV as (E165 & E200 & E201 & E207 & E209).
  assert (HR : cells_ok (view segsA (rm rho)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  destruct HSR as (_ & _ & _ & _ & _ & S0c & S8 & _ & _ & _ & S56 & _ & SM & _).
  destruct HIM as (_ & _ & IM3 & IM4 & _).
  unfold N_sec1. repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta.
  all: rewrite ?EvT, ?EvIT; cbn [eval]; rewrite ?u64_lit by lia.
  all: unfold SEC_INST, PG, IMG_HI in *.
  all: split; [qs_unf; lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [qs_unf; lia|]. all: split; [qs_unf; lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: split.
  all: try match goal with
       | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
       end.
  all: try (unfold cells_in_view; apply Forall_nil).
  -   unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    + intros j Hj. apply (civ_cell rho (rm rho) 0 974296 8 4096 (SLit 4096)); [exact S0c | cbn [eval]; reflexivity | lia | lia | exact Hj].
    + intros j Hj. apply (civ_cell rho (rm rho) 0 974304 8 PAB vPAB); [exact S8 | unfold vPAB; cbn [eval]; exact E200 | lia | lia | exact Hj].
  -   unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    intros j Hj. apply (civ_cell rho (rm rho) 0 974352 8 NC vNCH); [exact S56 | unfold vNCH; cbn [eval]; exact E201 | lia | lia | exact Hj].
  -   unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    intros j Hj. apply (civ_cell rho (rm rho) 0 974912 4 0 (SLit 0)); [exact SM | cbn [eval]; reflexivity | lia | lia | exact Hj].
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
  -   intros off Hoff. apply (wr_present (rm rho) (T + 2768) (T + 3168) (T + off) HSTAT); qs_unf; lia.
  -   intros off Hoff. qs_unf.
    destruct (Z_lt_dec off 4); [eapply (cell_wok_rd _ _ _ _ _ IM3); cbn [Z.of_nat]; lia | eapply (cell_wok_rd _ _ _ _ _ IM4); cbn [Z.of_nat]; lia].
  - unfold cells_in_view. qs_unf. repeat apply Forall_cons; try apply Forall_nil.
    + intros j Hj. apply (civ_cell rho (rm rho) (fst it - 16) 2 2 (snd it / 2 ^ 32) vNhi); [replace (fst it - 16 + 2) with (fst it - 14) by lia; exact IM3 | unfold vNhi; cbn [eval]; exact E207 | lia | lia | exact Hj].
    + intros j Hj. apply (civ_cell rho (rm rho) (fst it - 16) 4 4 (snd it mod 2 ^ 32) vNlo); [replace (fst it - 16 + 4) with (fst it - 12) by lia; exact IM4 | unfold vNlo; cbn [eval]; exact E209 | lia | lia | exact Hj].
Qed.

Let zb : nat -> Z := ltac2:(tb__ "0|0|
S4eVT;VCTX;S54VG;A1Vh;A4").
Let zhi : nat -> Z := zhiS ms.
Lemma zsepS : ltac2:(tb__ "0|3|
S2S2S58S2R2S48A3M0G0SdSbS2R4R3A3A1ScSeSfVzb;R5A1M1Vzhi;R5A1A2SfVzb;R4A1M2S46R4A1A2A2SeSfG2Vzhi;R4A1A2SfG1S46R5A1A2A2A2F_;F_;F_;Fz';Fz;").
Proof.
  qs_open. pose proof qs_nums as (T0 & T1 & C0 & C1' & TG & TI & CI & TC). pose proof qs_chunk as (_ & _ & MS & IH & HT & _).
  destruct HSEP as (_ & HT' & _ & HC' & _).
  intros z z' Hz Hz' NE. unfold ZUS in Hz, Hz'. cbn [In] in Hz, Hz'. unfold zb, zhi, zbS, zloS, zhiS, IMG_HI in *. qs_unf.
  repeat (destruct Hz as [<-|Hz]); try (exfalso; exact Hz); repeat (destruct Hz' as [<-|Hz']); try (exfalso; exact Hz'); try (exfalso; apply NE; reflexivity); cbn [Nat.eqb]; lia.
Qed.

Lemma inz_fixS : ltac2:(tb__ "0|0|
S5dVA;Vrho;A2S50S1bS1aVrho;A1S62S45A1A3S57S18S2fS30Vrho;Vzb;S46Vzhi;S48A5S1fS3dS39A1A1S4aA5F_;F_;").
Proof.
  intros HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  destruct (stk_ranges rho _ _ cb_cells (ob_cells (SWD vXK vXF vXL vXS)) eq_refl eq_refl ltac:(lia) HD) as (R1 & R2 & R3 & R4).
  assert (R4' : obj_range rho (SWD vXK vXF vXL vXS) = (bv_unsigned (rw rho 10%positive) - 168, bv_unsigned (rw rho 10%positive))) by exact R4.
  assert (U0 : In 0%nat ZUS) by (cbn; tauto). assert (U3 : In 3%nat ZUS) by (cbn; tauto).
  rewrite DQI0_objs. unfold STK, A_globals, ZD_fixS. cbn [app].
  repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone.
  - split; [exact U3|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R1. unfold zb, zbS, G. cbn [fst snd]. lia.
  - split; [exact U3|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R2. unfold zb, zbS, G. cbn [fst snd]. lia.
  - split; [exact U3|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R3. unfold zb, zbS, G. cbn [fst snd]. lia.
  - split; [exact U3|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R4'. unfold zb, zbS, G. cbn [fst snd]. lia.
  - split; [exact U0|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. right.
    unfold O_mtx00, carved. rewrite obj_range_mk by (unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; lia). unfold zb, zbS. cbn [fst snd eval]. rewrite u64_lit by lia. unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG. lia.
  - split; [exact U0|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. right.
    unfold O_gmax, carved. rewrite obj_range_mk by (unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; lia). unfold zb, zbS. cbn [fst snd eval]. rewrite u64_lit by lia. unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG. lia.
  - split; [exact U0|]. split; [unfold GOT_LO, GOT_HI; cbn; lia|]. split; [unfold GOT_LO, GOT_HI; cbn; lia|]. right.
    unfold O_got. rewrite obj_range_mk by (unfold GOT_LO, GOT_HI; lia). unfold zb, zbS. cbn [fst snd eval]. rewrite u64_lit by lia. unfold GOT_LO, GOT_HI. lia.
  - split; [exact U0|]. split; [unfold RTC_LO, RTC_HI; cbn; lia|]. split; [unfold RTC_LO, RTC_HI; cbn; lia|]. right.
    unfold O_rtc. rewrite obj_range_mk by (unfold RTC_LO, RTC_HI; lia). unfold zb, zbS. cbn [fst snd eval]. rewrite u64_lit by lia. unfold RTC_LO, RTC_HI. lia.
Qed.

Lemma inz_N1 : ltac2:(tb__ "0|0|
S57S18S2fS30Vrho;Vzb;S46Vzhi;S48A5S4fS53S18S52S47A4S6S2fS4bS4cA3A5").
Proof.
  qs_open. pose proof qs_nums as (T0 & T1 & C0 & C1' & TG & _). pose proof qs_chunk as (_ & _ & MS & IH & HT & _). pose proof qs_E as (EvT & EvC & EvIT).
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (U0 : In 0%nat ZUS) by (cbn; tauto). assert (U1 : In 1%nat ZUS) by (cbn; tauto). assert (U2 : In 2%nat ZUS) by (cbn; tauto). assert (U5 : In 5%nat ZUS) by (cbn; tauto).
  unfold N1, N_rti, N_sec1, ZD_rtiS, ZD_sec1. cbn [map carve_obj app].
  repeat apply Forall2_cons; try apply Forall2_nil.
  all: unfold in_zone; split; [assumption | split; [unfold SEC_INST; cbn; lia | split; [unfold SEC_INST, zhi, zhiS; cbn; qs_unf; lia | right]]].
  all: unfold carved; rewrite obj_range_mk by (unfold SEC_INST; lia); unfold zb, zbS; cbn [fst snd]; rewrite ?EvT, ?EvC, ?EvIT; cbn [eval]; rewrite ?u64_lit by lia; unfold SEC_INST, PG in *; qs_unf; lia.
Qed.

Lemma qs_carve1 : ltac2:(tb__ "0|0|
S2S5aS8S3aQ40A1A1S6cS5dVA;Vrho;A2S4dR5VSB;Vh;Vms;A4S59S51R5S39Vrho;R4R3A6S59S51R6S65R7A1Vrho;R5R4A6F_;F_;F_;Fw;Ftp;FJ;Ff;").
Proof.
  intros f J tp w HTOPH HFAM H0. qs_open.
  pose proof (D_pre_facts DQI0 _ DQI0_facts rho (SPA_facts_hold segsA _ rho DQI0 tp _ H0)) as HFpre.
  assert (H1 : SPA segsA J (ax_setS DQI0 SS1) rho tp w).
  { pose proof (SPA_carve_list segsA J rho DQI0 tp w N1 (ss_next (ax_S DQI0)) H0) as X. cbn zeta in X. apply X; clear X.
    - exact SS1_swf.
    - apply Pos.le_refl.
    - unfold N1. apply carve_okq_list; [reflexivity|]. apply Forall_app. split; [exact carve_rtiS | exact carve_sec1].
    - exact (zones_cross rho zb zloS zhi ZUS zsepS _ _ _ _ inz_N1 (inz_fixS HTOPH HFpre) (proj2 ZDS_chk)).
    - exact (zones_pd rho zb zloS zhi ZUS zsepS _ _ inz_N1 (proj1 ZDS_chk)). }
  rewrite S0_eq. apply SPA_refacts; [exact H1 | exact (S0_below f) |]. intros HF. apply Forall_app. split; [exact HF|].
  pose proof qs_nums as (T0 & T1 & C0 & C1' & TG & _). pose proof qs_chunk as (_ & _ & MS & IH & HTG & _).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E207 & E209).
  assert (NCpos : 1 <= NC <= 2 ^ 20).
  { unfold NC. pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LT.
    destruct HSR as (_ & _ & (B1 & B2) & _). unfold kPtrArrayReserve in B2. lia. }
  unfold F1. apply Forall_app. split.
  -
    unfold F_m. destruct f as [|[|f]]; cbn [fam_ok] in HFAM; repeat apply Forall_cons; try apply Forall_nil; unfold IMG_HI, PG in *; qs_unf.
    + apply (hlt rho vIT vSB (fst it - 16) (ag_spacebeg (aa_geom A))); [exact E165 | exact E155 | lia | lia | lia].
    + apply (hlt rho vIT vSB (fst it - 16) (ag_spacebeg (aa_geom A))); [exact E165 | exact E155 | lia | lia | lia].
    + apply (hle rho (add vSB (SLit (2 ^ 37))) vIT (ag_spacebeg (aa_geom A) + 2 ^ 37) (fst it - 16)); [apply ev_add_lit; [exact E155 | lia | lia | lia] | exact E165 | lia | lia | lia].
  - unfold HIGH_SHADOW_END, TOPMAX, IMG_HI, PG in *. qs_unf. repeat apply Forall_cons; try apply Forall_nil.
    + apply (hle rho _ vSB 0x10007fff8000 (ag_spacebeg (aa_geom A))); [apply elit | exact E155 | lia | lia | lia].
    + apply (hle rho vSB _ (ag_spacebeg (aa_geom A)) (140737479966720 - 2 ^ 37 - 4096)); [exact E155 | apply elit | lia | lia | lia].
    + apply (hne0 rho vNCH (Z.of_nat (length (aa_sec A)))); [exact E201 | lia].
    + apply (hle rho vNCH _ (Z.of_nat (length (aa_sec A))) (2 ^ 20)); [exact E201 | apply elit | lia | lia | lia].
    + apply (hne0 rho vT (ag_thread (aa_geom A))); [exact E151 | lia].
    + apply (hne0 rho vCTX (ag_ctx (aa_geom A))); [exact E152 | lia].
Qed.
End QSEnv.
