(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From stdpp Require list.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.

(* [comment removed for export] *)
Module SegQ3D_qcs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "list"; "cons"; "nat"; "prod"; "nil"; "app"; "length"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "valuation"; "SAlu"; "SLit"; "SVar"; "sprop"; "sobj"; "ss_facts"; "eval"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "cs_cache"; "mkQB"; "aa_cache_inited"; "aa_geom"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ageom"; "class_fresh"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "add"; "le"; "lt"; "pow"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "HVX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRD"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs"; "TC1"; "TC2"; "KEPTC"; "RCr"; "TQCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "QW"; "push_cache"; "set_q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "max_count"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc"; "entC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs"; "cptrC"; "FTLC"; "N_qcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "cbC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qb_id"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "JOK"; "TR"; "@Corelib.Lists.ListDef"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop"; "INVD"; "INVI"; "QC_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs.QCStep"; "QC_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "DQCs"; "RC"; "clsB"; "vB"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cptrC : sv := ltac2:(tb__ "0|0|
S12S35S12S33S12S33S60S12S34S5fS13Z20A1A3A3S37A3S13Z4A1A3").
Definition N_qcP : list carve_spec := ltac2:(tb__ "0|e|
S3S5S5S5SfS0A2M0S0A2M1S2S5S5S0S4A2M2SfA2M3A1M4A2M5S1G1G4S1G0S0S1SfS0S47Z0M6A4Z10M7A4S3G3S1G2SfS1S0S4G6U4M8A4S36S14PceA1M9S13Z1A1A2A4S3G3S1G2SfS1S0S4Z4G8A4S14PcfA1A4S3G3S1G2SfS1S0S4Z8U8MaA4S14Pc9A1MbA4S6G3A1McA3A3A3A4S3G5S1G1G4S1G0S0S1SfS0S36S47S12S34G9S13Z2A1A3A2G7A4Z14A4S3G3S1G2SfS1S0S4G7G8A4S48A4GcA3A4S3G5S1G1G4S1G0S0S1SfS0S4cZa10MdA4Za18A4S3G3S1G2SfS1S0S4GdGaA4S36S14Pd1A1S12S33S13G6A1GbA3A2A4GcA3A4S6G5A1A3A3A3").
Lemma TC1_objsP : ltac2:(tb__ "0|0|
SbS2S16A1S19S2eS3bA1A1S7S16S3dS51S58S16S57S4aA4A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition FTLC : list sprop := ltac2:(tb__ "0|0|
S52S15S8S15S46S4bA1A2S17S2eS3cA1A1A3").
Lemma TC2_facts : ltac2:(tb__ "0|0|
SbS2S15A1S17S2eS3cA1A1S7S15S46S4bA1S49A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TC2_eq : ltac2:(tb__ "0|0|
SbS30S2fS3bS56S2eS3bA1S3dA2A2S3cA3"). Proof. reflexivity. Qed.

Lemma cptrC_val : ltac2:(tb__ "0|6|
S11S0S0S0SbS26Q40M0A1M1S10R4Pa6A2S25G0R2A2A3SbG1S10R5P9bA2S25G0R4A2A3SbS0R4S28S28R5S27Z18S2bZ2M2Z20A2M3A2A2S27Z10M4R3A2A2A3S29Z0M5R4A2S2aS27G4R5A2G3A2S29G5R8A2S2aR8S2bG2Z40A2A2SbG1S18RbS48A2S25G0R8A2A3F_;F_;F_;F_;F_;F_;F_;Fy;Fa;FSB;Frho;").
Proof.
  intros rho SB a y E166 E155 Ea Hy Hy2 HSB Ha. pose proof (clsB_val rho SB a y E166 E155 Ea Hy Hy2 HSB Ha) as EC.
  apply bv_eq. rewrite (u64_lit y) by lia. unfold cptrC. rewrite U_srl_lit, U_sub, U_sub, U_sll_lit, EC. unfold vB, vSB. cbn [eval]. rewrite E166, E155, !u64_lit by lia.
  change (32 mod 64) with 32. change (4 mod 64) with 4. unfold M64v. rewrite (Z.mod_small (24 * 2 ^ 32)) by lia.
  replace (a - 24 * 2 ^ 32) with (SB + 16 * y) by lia. rewrite (Z.mod_small (SB + 16 * y)) by lia.
  replace (SB + 16 * y - SB) with (y * 2 ^ 4) by lia. rewrite Z.mod_small by lia. apply Z.div_mul. lia.
Qed.
Lemma qb_id_val : ltac2:(tb__ "0|0|
S23S0S2S5S0S0A2A1S0S0SbS0R4S28S28S22R5A1S27Z18S2bZ2Z20A2A2A2S27Z10R1A2A2A3SbS0S4dR6S1dR5R4R3A3A2R2A3F_;Fy;Fs;Fits;Fa;FG;").
Proof.
  intros G a its s y E. unfold qb_id, ptr_to_compact, region_beg, kRegionSize, kCompactPtrScale. cbn [qb_addr]. rewrite Z.shiftr_div_pow2 by lia.
  replace (a - (ag_spacebeg G + 24 * 2 ^ 32)) with (y * 2 ^ 4) by lia. apply Z.div_mul. lia.
Qed.

Section QCPost.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Lemma qc_post : ltac2:(tb__ "0|7|
S1bS0S0S0S4S2S1aA1M0G0S11S2S26Q40M1A1M2A1S55S0SbG0S21RbA1S6S1aA1M3A3SbS9S1eRcA1SaA3S0S41ReR1A2S41VA0;R2A2F_;Fz;S3aVA0;ReA2SbG0S20RfA1S3S1aS1dReS6S5S0S0A2A1M4RdA3S7S1aRaR9A3A3A3S2aS2cS8S0S1cS40R10Z18M5A2A1A2A1S44G5A1M6A2S2dS31S39VK;VA0;Vrho0;R11R10ReRdG4RcRbAaS3fRaR9R8A6SbG2S10RbPa6A2S25G1R11A2A3SbG2S10RcPceA2S25G1S2cS8S0S1cS40R13G5A2A1A2A1A2A3SbG2S10RdPcfA2S25G1G6A2A3SbG2S10RePc9A2S25G1S45G5A1A2A3ScS29Z0RcA2S2aRcS2bZ2Z40A2A2A2SbG2S10R10Pd1A2S25G1RdA2A3S32R11R13A2SdS11S11ScS2dS31S38VK;VA0;Vrho0;S42S43R1aG3S7S1aR15R14A3A3G5S4dS1fR1aA1S1dR19G4R18A3A2A3R15R14A6S3eR1R12R11A6S32R1R15A2A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd tmp' rest rho tp w st HTH HCI HQW HQP0 HGL HNF H E166 E206 E207 E201 Hst E209 HVx. destruct w as [tr [ms md]].
  pose proof (SPA_axforms segsA _ _ rho _ _ tp _ TC1_eq H) as H1.
  destruct (proj2 H1) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H1)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  destruct HRIG as (E151 & E152 & E155 & E156). pose proof (HCLS HCI 24 ltac:(lia)) as CV.
  pose proof (cv_max _ _ _ _ _ CV) as C_max. pose proof (cv_size _ _ _ _ _ CV) as C_sz. pose proof (cv_len _ _ _ _ _ CV) as K_le.
  unfold pc_entry in C_max, C_sz. change (max_count 24) with 2 in *. change (Size 24) with 8192 in *.
  set (T := ag_thread (aa_geom A)) in *. set (k := Z.of_nat (length (cs_cache (cls_of A 24)))) in *.
  replace (T + 208 + 80 * 24 + 4) with (T + 2128 + 4) in C_max by lia. replace (T + 208 + 80 * 24 + 8) with (T + 2128 + 8) in C_sz by lia.
  pose proof (geom_old _ HG) as HG'. destruct HG' as (_ & _ & _ & _ & G5 & G6 & G7 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG) as (_ & TBD & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI, TBD. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  destruct BE as [_ _ HQP HAU _ _ _].
  destruct (batch_slot A HQP HAU HG (mkQB a [] s) ltac:(rewrite (qall_A1 A HTH), HGL; left; reflexivity)) as (y & Ey & Y0 & _ & Y1 & _). cbn [qb_addr] in Ey. rewrite kUserSpaceSize_val in Y1.
  pose proof (SB_facts A HG) as (_ & SBF1 & SBF2). unfold HIGH_SHADOW_END in SBF1. rewrite kSpaceSize_val in SBF2.
  assert (EC : eval rho clsB = Z_to_bv 64 24) by (apply (clsB_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  assert (ECP : eval rho cptrC = Z_to_bv 64 y) by (apply (cptrC_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  rewrite (qb_id_val (aa_geom A) a [] s y Ey).
  assert (EcbC : eval rho cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply (eval_add_lit A); try lia; unfold vT; cbn [eval]; exact E151).
  assert (Eent : bv_unsigned (eval rho entC) = T + 2128).
  { unfold entC, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval rho (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Eslot : bv_unsigned (eval rho (add entC (SAlu ALU_SLL (SVar 206) (SLit 2)))) = T + 2128 + 4 * k).
  { unfold add at 1. rewrite U_add, U_sll_lit, Eent. cbn [eval]. rewrite E206, u64_lit by lia. change (2 mod 64) with 2. unfold M64v. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Ek1 : eval rho (add (SVar 206) (SLit 1)) = Z_to_bv 64 (k + 1)) by (apply (eval_add_lit A); try lia; cbn [eval]; exact E206).
  set (R := map carve_obj N_qcP).
  set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTC R entC 0 16 _ Hsm TC1_objsP ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eent; lia) ltac:(rewrite Eent; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTC R (add entC (SAlu ALU_SLL (SVar 206) (SLit 2))) 16 20 _ Hsm TC1_objsP ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eslot; lia) ltac:(rewrite Eslot; lia)) as [AV2 PR2].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTC R cbC 2576 2584 _ Hsm TC1_objsP ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite EcbC, u64_lit by lia; lia) ltac:(rewrite EcbC, u64_lit by lia; lia)) as [_ PR3].
  fold rho3 v3 in AV1, PR1, AV2, PR2, PR3. rewrite Eent in AV1, PR1. rewrite Eslot in AV2, PR2. rewrite EcbC, u64_lit in PR3 by lia.
  assert (C_cnt3 : cell_ok v3 (mkACell (T + 2128) 4 (k + 1))) by (replace (T + 2128) with (T + 2128 + 0) by lia; exact (av_cell v3 (T + 2128) 0 4 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) Ek1)).
  assert (C_max3 : cell_ok v3 (mkACell (T + 2128 + 4) 4 2)) by exact (av_cell v3 (T + 2128) 4 4 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) E207).
  assert (C_sz3 : cell_ok v3 (mkACell (T + 2128 + 8) 8 8192)) by exact (av_cell v3 (T + 2128) 8 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) E201).
  assert (C_slot3 : cell_ok v3 (mkACell (T + 2128 + 4 * k + 16) 4 y)) by exact (av_cell v3 (T + 2128 + 4 * k) 16 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) ECP).
  clear AV1 AV2.
  set (P := fun z : Z => (T + 2128 <= z < T + 2144) \/ (T + 2144 + 4 * k <= z < T + 2148 + 4 * k) \/ (T + 2784 <= z < T + 2792)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (PT : forall z, P z -> T + 2128 <= z < T + 2792) by (intros z Hz; unfold P in Hz; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[<-|[]]]]; unfold carve_obj, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz;
      rewrite ?Eent, ?Eslot, ?EcbC, ?u64_lit in Hz by lia; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (PPR : forall z, P z -> v3 z <> None).
  { intros z Hz. destruct Hz as [Hz|[Hz|Hz]]; [destruct (PR1 z ltac:(lia)) as [x Hx] | destruct (PR2 z ltac:(lia)) as [x Hx] | destruct (PR3 z ltac:(lia)) as [x Hx]]; rewrite Hx; discriminate. }

  assert (HK3 : K (push_cache (set_q A [] (tmp' ++ rest)) 24 y) rho3 tp tr md).
  { rewrite <- (qb_id_val (aa_geom A) a [] s y Ey).
    apply (kq_push_batch segsA K HL A rho rho3 tp tr md [] (tmp' ++ rest) (mkQB a [] s) HTH HGL eq_refl HCI HNF); [intros i; reflexivity | intros l; reflexivity | | | | | exact HK].
    - intros z NQ NPZ. fold v3 v. destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. unfold push_zone, pc_entry in NPZ. fold T k in NPZ.
      destruct Hp as [Hp|[Hp|Hp]].
      + destruct (Z_lt_dec z (T + 2132)) as [|]; [exfalso; apply NPZ; left; lia|].
        destruct (Z_lt_dec z (T + 2136)) as [|]; [apply (cell_ok_same v v3 _ C_max C_max3); cbn [c_addr c_w]; lia | apply (cell_ok_same v v3 _ C_sz C_sz3); cbn [c_addr c_w]; lia].
      + exfalso. apply NPZ. right. lia.
      + exfalso. apply NQ. right. right. unfold qstat_zone. fold T. lia.
    - intros z _ Hd. fold v3. fold v in Hd. destruct (PD z) as [Hp|Np]; [exact (PPR z Hp) | rewrite (FR z Np); exact Hd].
    - fold v3. unfold pc_entry. fold T k. replace (T + 0xd0 + 80 * 24) with (T + 2128) by lia. exact C_cnt3.
    - fold v3. unfold pc_entry. fold T k. rewrite (qb_id_val (aa_geom A) a [] s y Ey). replace (T + 0xd0 + 80 * 24 + 16 + 4 * k) with (T + 2128 + 4 * k + 16) by lia. exact C_slot3. }

  assert (QF_OUT : forall z, q_foot A z -> ~ P z) by (intros z QF HP; pose proof (HSEP z QF) as NT; fold T in NT; pose proof (PT z HP); lia).
  assert (HR3 : RMEM2 v3 (aa_geom A) tmp' rest).
  { destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *.
    assert (INQ : forall b, In b (tmp' ++ rest) -> In b (qall A)) by (intros b Hb; rewrite (qall_A1 A HTH), HGL; right; exact Hb).
    split; [|split; [|split; [|split]]].
    - apply Forall_forall. intros b Hb.
      apply (batch_mem_frame A v v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b (INQ b Hb))); [|exact (proj1 (Forall_forall _ _) HBM b Hb)].
      intros z Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact (INQ b Hb)|]. unfold bfoot in Hz.
      destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right]. apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it.
      split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; left; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; right; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr. fold T in Q1, Q2, Q3, Q4 |- *.
      assert (TOUT : forall z, T + 0x50 <= z < T + 0x70 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    - destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (GOUT : forall z, QG + 160 <= z < QG + 192 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); unfold QG in *; lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia]. }

  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. pose proof (PT z Hz) as PTz. split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *; lia].
    destruct HQP0 as (ESB & _). assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
    destruct (Z_lt_dec z (T + 2768)) as [|]; [right; left; rewrite <- EG; fold T; lia | left; right; right; unfold qstat_zone; rewrite <- EG; fold T; lia]. }

  set (A' := push_cache (set_q A [] (tmp' ++ rest)) 24 y) in *.
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ TC1 rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H1) | exact I]).
  pose proof (SPA_unobj segsA TJ rho TC1 KEPTC R tp tr ms md TC1_objsP HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. rewrite TC2_eq in HU.
  assert (HU1 : SPA segsA (JRD K A0 rho0 A' tmp' rest) TC2 rho3 tp (tr, mkCfg ms md)).
  { split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HR3 | exact HF3]. }
  assert (HU2 : SPA segsA (JRD K A0 rho0 A' tmp' rest) TC4 rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact HU1 | exact TC4_below |]. intros HF. rewrite TC2_facts in HF. exact (proj1 (proj1 (Forall_app _ _ _) HF)). }
  pose proof (JRD_stable K HL A0 rho0 A' tmp' rest) as HSTD.
  destruct (entM_SPA _ _ RCr MC rho3 tp _ TC4_ent HSTD HU2) as (H7 & AG7 & V7 & RM7).
  assert (VV : forall i, In i [166; 184; 185; 186; 187; 208]%positive -> rw (rho_sub rho3 (infer_sub NPRE (ax_S TC4) (ax_S RCr))) i = rw rho i).
  { intros i Hi. rewrite (V7 i (SVar i)); [reflexivity|]. unfold MC, idm. apply in_map_iff. exists i. split; [reflexivity | exact Hi]. }
  eexists. split; [exact H7|]. destruct HVx as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !VV by (cbn; tauto). tauto.
Qed.
End QCPost.

Section QCStep.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJD : ltac2:(tb__ "0|1|
S1bS2S1aA1M0G0S4fVQ;VX;S38VK;VA0;Vrho0;R3R2R1A6A3Frest;Ftmp;FA;").
Hypothesis HJI : ltac2:(tb__ "0|1|
S1bS0S0S4S2S5S0S0A2A1S2S1aA1M0G0S4fVQ;VX;S39VK;VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.
Variable TPI : list word -> Prop.

Definition QC_full_step : Prop := ltac2:(tb__ "0|6|
S1bS0S0S4S2S1aA1S11S2S26Q40M0A1M1A1M2VTPI;R1A1M3S5aVA0;Vrest;R8R7S6S5S0S0A2A1M4R4A6S32R4R5A2SbG1S10R5Pa6A2S25G0R9A2A3S29S44Z18M5A1S2cS8S0S1cS40RbG5A2A1A2A1A2S1bS11G2G3S59VA0;Vrest;R4RcA4S32R4RdA2S50VQ;VX;S2dS31S38VK;VA0;Vrho0;R6ReVrest;A6S5eR5R4A5A3F_;F_;F_;Ftp';Frho';FA';S50VQ;VX;S2dS31S39VK;VA0;Vrho0;RdRcRbRaG4R9Vrest;AaS5dR8R7A5A3F_;F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fnd;Fn0;Fa;FA;").

Lemma cls24_not_fresh : ltac2:(tb__ "0|0|
S1bS1aS11S2S26Q40A1A1S2S54A1S53SbS9S1eR6A1SaA3S3aVA0;R7A2VK;R8R6R5R4R3A5S61S1aR8S4eR9A1A3SeS24VA0;Z18A2A1F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fb;FA;").
Proof.
  intros A b rho tp tr md HCI (_ & _ & EF) HK Hb HF. specialize (EF 24 HF). unfold class_fresh in HF. rewrite HF in EF.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (proj1 (Forall_forall _ _) (proj1 HQPU) b Hb) as (_ & _ & (y & _ & Y0 & _ & Y1) & _).
  unfold cls_of, nthZ in Y1. rewrite EF in Y1. unfold kQuarantineBatchSize in Y1. cbn in Y1. lia.
Qed.

Theorem QC_step_of_full : ltac2:(tb__ "0|0|
S5cS5bVK;VA0;Vrho0;VQ;VX;Vrest;VTPI;A7F_;").
Proof.
  intros HFULL A a n0 nd tmp' rho tp HTP HI HVx E166 HC.
  destruct (Z_lt_dec (Z.of_nat (length (cs_cache (cls_of A 24)))) (max_count 24)) as [HNF|HFL]; [|exact (HFULL A a n0 nd tmp' rho tp HTP HI HVx E166 ltac:(lia) HC)].
  pose proof HI as (I1 & I2 & I3 & I4 & (s & I5) & I6).
  set (k := Z.of_nat (length (cs_cache (cls_of A 24)))) in *. set (J := JRI K A0 rho0 A a n0 nd [] tmp' rest).
  apply (tr_pure X _ (~ class_fresh A0 24)).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & _). cbn [w_tr w_cfg cfg_model fst snd] in HK.
    apply (cls24_not_fresh A (mkQB a [] s) rho tp tr md I2 I4 HK). rewrite (qall_A1 A I1), I5. left. reflexivity. }
  intros NFR.
  apply (tr_glue X _ J Cqc tp (fun r => HVX r tmp' /\ rw r 166%positive = Z_to_bv 64 a /\ rw r 206%positive = Z_to_bv 64 k /\ rw r 207%positive = Z_to_bv 64 (max_count 24)
                                         /\ rw r 201%positive = Z_to_bv 64 (Size 24) /\ exists st, 0 <= st < 2 ^ 64 /\ rw r 209%positive = Z_to_bv 64 st)).
  { intros w Hw. destruct (qc_pre K HL A0 rho0 A a s n0 nd tmp' rest rho tp w I1 I2 I5 HNF Hw E166) as (st & Hst & _ & Hs). eexists. split; [exact Hs|].
    assert (OTH : forall i, i <> 206%positive -> i <> 207%positive -> i <> 201%positive -> i <> 209%positive ->
                   rw (rho_sets rho [(206%positive, Z_to_bv 64 k); (207%positive, Z_to_bv 64 (max_count 24)); (201%positive, Z_to_bv 64 (Size 24)); (209%positive, Z_to_bv 64 st)]) i = rw rho i).
    { intros i N1 N2 N3 N4. apply rho_sets_other. cbn. intros [E|[E|[E|[E|[]]]]]; congruence. }
    destruct HVx as (E184 & E185 & E186 & E187 & E208).
    split; [unfold HVX; rewrite !OTH by discriminate; tauto|]. split; [rewrite OTH by discriminate; exact E166|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists st. split; [exact Hst | reflexivity]. }
  intros rhoE (HVe & E166e & E206e & E207e & E201e & st & Hst & E209e).
  apply (qc_call X J rhoE tp (HJI _ _ _ _ _ _ _)). intros rho' Hag.
  assert (AGV : forall i, (i < ss_next (ax_S Cqc))%positive -> rw rho' i = rw rhoE i) by (intros i Hi; symmetry; exact (proj1 Hag i Hi)).
  set (A' := push_cache (set_q A [] (tmp' ++ rest)) 24 (qb_id (aa_geom A) (mkQB a [] s))).
  apply (tr_glue X _ (JRD K A0 rho0 A' tmp' rest) RCr tp (fun r => HVX r tmp')).
  { intros w Hw. apply (qc_post K HL A0 rho0 A a s n0 nd tmp' rest rho' tp w st I1 I2 I3 I4 I5 HNF Hw); try (rewrite AGV by reflexivity; assumption); [exact Hst|].
    destruct HVe as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !AGV by reflexivity. tauto. }
  intros rho5 HV5. apply (seg_D_CrM X _ rho5 tp (HJD _ _ _)). intros Tx M rho6 HIN HKp. cbn [In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  apply (HC A' rho6 tp HTP); [|exact (HVX_keep _ rho5 rho6 tmp' HKp ltac:(cbn; tauto) HV5)].
  split; [reflexivity|]. split; [exact I2|]. split; [|split; [|split; [reflexivity|]]].
  - intros z Hz. apply I3. exact (QW_push_batch A (mkQB a [] s) (tmp' ++ rest) _ z I1 I5 Hz).
  - apply QP_push; [exact I4 | lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_batch A (mkQB a [] s) (tmp' ++ rest) _ z I1 I5 Hz).
Qed.
End QCStep.
End SegQ3D_qcs.

(* [comment removed for export] *)
Module SegQS_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "bool"; "pair"; "prod"; "nil"; "list"; "app"; "true"; "length"; "false"; "option"; "Some"; "andb"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "ss_next"; "SPUle"; "valuation"; "SAlu"; "ss_lenient"; "SPBranch"; "ss_facts"; "SPNot"; "SPUlt"; "SVar"; "ss_objs"; "sv_eqb"; "SPAlign"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "DUnknown"; "agree_below"; "cell"; "mkObj"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vH"; "C5"; "vMS"; "T5f"; "SC"; "vNCH"; "AM"; "AU"; "EM"; "EU"; "GBEXIT"; "GBSCAN"; "S0"; "SX"; "s5"; "D_M"; "D_U"; "R5"; "T5of"; "VSX"; "dropk"; "MSENTS"; "O_clast"; "O_hidx"; "VS0"; "cntD"; "idxs_of"; "isin"; "runPA"; "runPB"; "runPC"; "runPD"; "runPE"; "runPL"; "selX"; "sel_last"; "setpc"; "vIDX"; "vPAB"; "vPTR"; "E5"; "EMd"; "EMx"; "EUd"; "EUx"; "LA"; "LENS"; "O_cidx"; "O_csh"; "O_hh"; "O_ihdr"; "O_lidx"; "O_secg"; "O_secm"; "O_secn"; "O_secs"; "O_stS"; "TOPMAX"; "TsPA"; "TsPB"; "TsPC"; "TsPD"; "TsPE"; "TsPL"; "addos"; "dropD"; "jregs"; "vEND"; "vLAST"; "AM_0_L"; "AM_0_M"; "AM_1_L"; "AM_1_M"; "AM_2_L"; "AM_2_M"; "AU_0_L"; "AU_0_M"; "AU_1_L"; "AU_1_M"; "AU_2_L"; "AU_2_M"; "BSHS"; "C5_0_L"; "C5_0_M"; "C5_1_L"; "C5_1_M"; "C5_2_L"; "C5_2_M"; "E5_0_L"; "E5_0_M"; "E5_1_L"; "E5_1_M"; "E5_2_L"; "E5_2_M"; "EM_0_L"; "EM_0_M"; "EM_1_L"; "EM_1_M"; "EM_2_L"; "EM_2_M"; "EMd_0_L"; "EMd_0_M"; "EMd_1_L"; "EMd_1_M"; "EMd_2_L"; "EMd_2_M"; "EMx_0_L"; "EMx_0_M"; "EMx_1_L"; "EMx_1_M"; "EMx_2_L"; "EMx_2_M"; "EU_0_L"; "EU_0_M"; "EU_1_L"; "EU_1_M"; "EU_2_L"; "EU_2_M"; "EUd_0_L"; "EUd_0_M"; "EUd_1_L"; "EUd_1_M"; "EUd_2_L"; "EUd_2_M"; "EUs"; "EUs_0_L"; "EUs_0_M"; "EUs_1_L"; "EUs_1_M"; "EUs_2_L"; "EUs_2_M"; "EUx_0_L"; "EUx_0_M"; "EUx_1_L"; "EUx_1_M"; "EUx_2_L"; "EUx_2_M"; "F1"; "F2"; "F_h"; "F_len"; "F_m"; "LA_0"; "LA_1"; "LA_2"; "LL"; "LL_0"; "LL_1"; "LL_2"; "LR"; "LR_0_L"; "LR_0_M"; "LR_1_L"; "LR_1_M"; "LR_2_L"; "LR_2_M"; "OBJ1"; "OBJ2"; "O_cfbS"; "O_cftS"; "O_chS"; "O_pgbS"; "O_seci"; "SC_0"; "SC_1"; "SC_2"; "SX_0_L"; "SX_0_M"; "SX_1_L"; "SX_1_M"; "SX_2_L"; "SX_2_M"; "T5f_0_L"; "T5f_0_M"; "T5f_1_L"; "T5f_1_M"; "T5f_2_L"; "T5f_2_M"; "VSC"; "rtiS"; "vCHV"; "vLIDX"; "vNEAR"; "vNhi"; "vNlo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "runA"; "NPRE"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "@Stdlib.Lists.List"; "In"; "forallb";
"@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "vIT"; "QIRET2"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "ALU_SRL"; "ALU_SLL"; "ALU_SUB"; "BC_LTU"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel"; "addf"; "addo"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vCTX"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "DQI0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states"; "optR"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition GBSCAN : Z := 0x3ea54.
Definition GBEXIT : Z := 0x3ea80.
Definition MSENTS : Z := 0xdb004.
Definition TOPMAX : Z := 140737479966720.
Definition vPAB := SVar 200. Definition vNCH := SVar 201. Definition vH := SVar 202. Definition vMS := SVar 203. Definition vIDX := SVar 204.
Definition vLAST := SVar 205. Definition vLIDX := SVar 206. Definition vNhi := SVar 207. Definition vNlo := SVar 209.
Definition vPTR := SVar 210. Definition vCHV := SVar 211. Definition vNEAR := SVar 212. Definition vEND := SVar 213.

Definition O_seci : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1SfdS10bSfdZ10A2S1S4S4S14S0A2M0S16A2M1S3G0S16S3S14S0SfdU8M2A4S19S11bA1A4S1G1S3G0S16S3S14S0S10bSfdZ8A2G2A4S60A4S5G1A1A3A3A4").
Definition O_secn : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1S10bSfdZ38A2M0S10bSfdZ40A2S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4S3fA4S5G2A1A3A4").
Definition O_secs : sobj := ltac2:(tb__ "0|0|
Sf5S19Z0A1S10bSfdZ40A2Zead00S5S4S4S14S0A2S16A2A1A4").
Definition O_secm : sobj := ltac2:(tb__ "0|4|
Sf5S19Z0A1M0Zead00M1Zead04S1S4S4S14S0A2M2S16A2M3S3G2S16S3S14S0G1U4A4G0A4S5G3A1A3A4").
Definition O_secg : sobj := carved (SLit 0) 0xead08 0xead30 [].
Definition O_cftS : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1Z17fc60M0Z17fc68S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4S19ZffffffffffffffffA1A4S5G2A1A3A4").
Definition O_cfbS : sobj := ltac2:(tb__ "0|4|
Sf5S19Z0A1M0Z17fc78M1Z17fc80S1S4S4S14S0A2M2S16A2M3S3G2S16S3S14S0G1U8A4G0A4S5G3A1A3A4").
Definition O_pgbS : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1Z17db60M0Z17db68S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4S19S11bA1A4S5G2A1A3A4").
Definition O_stS : sobj := carved vT 2768 3168 [].
Definition O_ihdr : sobj := ltac2:(tb__ "0|3|
Sf5S109Z2M0Z8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U2A4Sf1A4S1G2S3G1S16S3S14S0Z4U4A4Sf2A4S5G2A1A3A3A4").
Definition O_chS (b v : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Vb;Z0M0Z8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vv;A4S5G2A1A3A4").
Definition O_hh (h ms : sv) : sobj := ltac2:(tb__ "0|4|
Sf5Vh;Z0M0Z10S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8M3A4Vh;A4S1G2S3G1S16S3S14S0Z8G3A4Vms;A4S5G2A1A3A3A4").
Definition O_hidx (h v : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Vh;Z18M0Z20S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vv;A4S5G2A1A3A4").
Definition BSHS (h : sv) : sv := ltac2:(tb__ "0|0|
Sf9S1dS110Vh;S19Z3A1A3S19Z7fff8000A1A2").
Definition LENS (ms : sv) : sv := SAlu ALU_SRL ms (SLit 3).
Definition O_csh (h ms : sv) : sobj := ltac2:(tb__ "0|0|
S2eS8bVh;A1S19Z0A1S68Vms;A1S5S2dA1S2bA5").
Definition O_cidx (h : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Sf9S60S1dS111S5fS19Z3A1A3A2Z0M0Z8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vh;A4S5G2A1A3A4").
Definition O_clast (v : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Sf9S1dS111S3fS19Z3A1A3S60A2N8M0Z0S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vv;A4S5G2A1A3A4").
Definition O_lidx : sobj := ltac2:(tb__ "0|3|
Sf5S7eZ18M0Z20S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4SefA4S5G2A1A3A4").
Definition rtiS : list sobj := map carve_obj N_rti.
Definition OBJ1 : list sobj := ltac2:(tb__ "0|0|
S7S17SedS1S17SdcS1S17S70S1S17S71S1S17S6fS1S17S6eS1S17Sd9S1S17Sd8S1S17SdbS1S17S72S1S17S6cS5S17A1A3A3A3A3A3A3A3A3A3A3A3").
Definition OBJ2 (l : bool) (h : sv) : list sobj := ltac2:(tb__ "0|1|
S7S17S1S17S6aVh;S3cA2S1S17S6bVh;S3cA2S5S17A1M0A3A3S2S6S17A1Ll;Vl;S1S17S51Vh;Sf9S3fS19N1A1A2A2S1S17S50Vh;A1G0A3A3S1S17S51Vh;S5fA2S1S17S69Vh;A1S1S17S50S7eA1S1S17S6dG0A3A3A3A3X2x2A3").
Definition addos (X : axst) (os : list sobj) : axst := fold_left addo os X.
Definition setpc (X : axst) (pc : Z) (ru : list (nat * sv)) : axst := ltac2:(tb__ "0|0|
S10VX;A1S34S12VX;S2fVpc;S121S32R1A1Vru;A2S31R1A1S30R1A1S33R1A1S24R1A1S20R1A1S1aR1A1S1eR1A1A9A2TS;").
Definition dropk (X : axst) (k : nat) : axst := ltac2:(tb__ "0|2|
S12VX;S123S10VX;A1M0S115S17S11fS9S17S24G0A1M1A2Vk;A2G1A3A2A2").

Definition same_rngS (o o' : sobj) : bool := ltac2:(tb__ "0|0|
SdSdS25S27Vo;A1S27Vo';A1A2S25S29Vo;A1S29Vo';A1A2A2S25S28Vo;A1S28Vo';A1A2A2").
Definition isin (D : list sobj) (o : sobj) : bool := existsb (same_rngS o) D.
Fixpoint idxs_of (p : sobj -> bool) (l : list sobj) (i : nat) : list nat :=
  match l with [] => [] | o :: r => (if p o then [i] else []) ++ idxs_of p r (S i) end.
Definition sel_last (X : axst) (D : list sobj) : list nat := ltac2:(tb__ "0|2|
S7S0S54S17SeS55VD;R1A2A1Lo;S24S10VX;A1A1M0U0M1A3S54S55VD;A1G0G1A3A3").
Definition selX (X : axst) (D : list sobj) : axst := ltac2:(tb__ "0|0|
SbSfA1SfLx;S107VX;S1S105S106S5dVX;VD;A2A1S5S105A1A3A2SfR1LY;VX;Xbx2").
Definition cntD (X : axst) (D : list sobj) : nat := ltac2:(tb__ "0|0|
S9S0S54S55VD;A1S24S10VX;A1A1U0A3A2").
Definition dropD (X : axst) (D : list sobj) : axst := ltac2:(tb__ "0|0|
S4eS5cVX;VD;A2S53VX;VD;A2A2").

Definition F_m (f : nat) : list sprop := ltac2:(tb__ "0|3|
S0S6S18A1M0Lf;Vf;S1S18S22S109SfcA2S5S18A1M1A3M2S0S0G0Ln;R1G2S0S1S18S1bSf9SfcS19S10cZ2Z25A2A1A2S109A2G1A3Ln0;X0x2Ln;X0x2").
Definition F1 (f : nat) : list sprop := ltac2:(tb__ "0|2|
S7S18Sc7Vf;A1S1S18S1bS19S11cA1SfcA2S1S18S1bSfcS19S10dS10dS73S10cZ2M0Z25A2A2Z1000A2A1A2S1S18S21S1fS10eS3fS19Z0A1M1A3A1S1S18S1bS3fS19S10cG0Z14A2A1A2S1S18S21S1fS10eS126G1A3A1S1S18S21S1fS10eS125G1A3A1S5S18A1A3A3A3A3A3A3A3").

Definition F_h (f : nat) : list sprop := ltac2:(tb__ "0|6|
S0S6S18A1M0Lf;Vf;S1S18S1bSf9S3aS3cA2S19Z7fff7000A1M1A2S1S18S1bSf9S3cS3aA2G1A2S1S18S22Sf9S3aS19Z1000A1A2M2SfcA2S5S18A1M3A3M4A3A3S0S0G0Ln;R1S1S18S1bS19Z10007fff8000A1S3aA2M5G4A3S0S1S18G5S1S18S1bSf9SfcS19S10cZ2Z25A2A1A2G2A2G3A3A3Ln0;X0x2Ln;X0x2").

Definition F_len : sprop := ltac2:(tb__ "0|1|
S1fS113S1dS112S1dS10fS1dS110S1dS10fS1dS10fS3aS3cA3S19N8A1A3S19Z3A1M0A3S19Z1A1A3S1dS110S3aG0A3A3S19ZffffffffffffffffA1A3").
Definition F2 (f : nat) (l : bool) : list sprop := ltac2:(tb__ "0|4|
S7S18S1S18Sc6S1S18S21S1fS10eS3aS19Z0A1A3A1S1S18S1bS3aS109A2S1S18S22S109Sf9S3aS3cA2M0A2S1S18S26PcaZcM1A2S1S18S26PcbG1A2S1S18S1bS19Z12000A1S3cA2S1S18S1bS3cS19S73A1M2A2S1S18S1bS19Z643000A1S3aA2S1S18S1bG0G2A2S1S18S1bSf9S3cS3aA2G2A2S5S18A1M3A3A3A3A3A3A3A3A3A3A3A3S7S18Sc5Vf;A1S2S6S18A1Ll;Vl;G3S1S18S22S5fSf9S3fS19N1A1A2A2G3A3X2x2A3A3").
Definition jregs : list (nat * sv) := ltac2:(tb__ "0|1|
S1S4S0S16A2M0S3S0S16UfS23Pc0A1A4S1G0S3S0S16U10S23Pc1A1A4S1G0S3S0S16U11S23Pc2A1A4S1G0S3S0S16U5S23PacA1A4S5G0A1A3A3A3A3").

Definition S0 (f : nat) : axst := ltac2:(tb__ "0|0|
S11dS7aS127Sd6A2Sc3Vf;A1A2").
Definition runPA (f : nat) : list leafA := ltac2:(tb__ "0|0|
SfaU12cS1S14S45S1S14S44S5S14A1A3A3S46Vf;A1A3").
Lemma runPA_eq : ltac2:(tb__ "0|0|
S0S38S6S11A1SfaU12cS1S14S45S1S14S44S5S14A1A3A3S46R1A1A3S56R1A1A3Ff;"). Proof. intros f. unfold runPA. reflexivity. Qed.
Definition LA_0 : axst := Eval vm_compute in (leaf 0 (runPA 0)).
Definition LA_1 : axst := Eval vm_compute in (leaf 0 (runPA 1)).
Definition LA_2 : axst := Eval vm_compute in (leaf 0 (runPA 2)).
Definition LA (f : nat) : axst := ltac2:(tb__ "0|0|
S0SfLf;Vf;Sc8S0S0SfLn;R1Sc9S0ScaLn0;X0x2Ln;X0x2").
Definition VS0 : list positive := ltac2:(tb__ "0|0|
S1S15Pa0S1S15Pa1S1S15Pa2S1S15Pa3S1S15Pa4S1S15Pa5S1S15Pa6S1S15Pb8S1S15Pb9S1S15PbaS1S15PbbS1S15Pd0S1S15Pc8S1S15Pc9S1S15PcfS1S15Pd1S5S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition TsPA (f : nat) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35S67Vf;A1S108S52A1A4S5G0A1A3").

Definition SCof (f : nat) : axst := ltac2:(tb__ "0|1|
S11eS5eS67Vf;A1S45S7S4S0S16A2M0S1G0S3S0S16UcS61A4S1G0S3S0S16UdSf0A4S1G0S3S0S16UeS7dA4S5G0A1A3A3A3S7cA3A3SdaS61SeeA2A2").
Definition SC_0 : axst := Eval vm_compute in (SCof 0).
Definition SC_1 : axst := Eval vm_compute in (SCof 1).
Definition SC_2 : axst := Eval vm_compute in (SCof 2).
Definition SC (f : nat) : axst := ltac2:(tb__ "0|0|
S0SfLf;Vf;SddS0S0SfLn;R1SdeS0SdfLn0;X0x2Ln;X0x2").
Definition runPL (f : nat) : list leafA := ltac2:(tb__ "0|0|
SfaU64S1S14S45S1S14S44S5S14A1A3A3S3eVf;A1A3").
Lemma runPL_eq : ltac2:(tb__ "0|0|
S0S38S6S11A1SfaU64S1S14S45S1S14S44S5S14A1A3A3S3eR1A1A3S5bR1A1A3Ff;"). Proof. intros f. unfold runPL. reflexivity. Qed.
Definition LL_0 : list axst := Eval vm_compute in (map la_state (runPL 0)).
Definition LL_1 : list axst := Eval vm_compute in (map la_state (runPL 1)).
Definition LL_2 : list axst := Eval vm_compute in (map la_state (runPL 2)).
Definition LL (f : nat) : list axst := ltac2:(tb__ "0|1|
S0S6SfA1M0Lf;Vf;SccS0S0G0Ln;R1ScdS0SceLn0;X0x2Ln;X0x2").
Definition VSC : list positive := ltac2:(tb__ "0|0|
S7S15S52S1S15Pd2S1S15Pd3S1S15Pd4S1S15Pd5S1S15Pc0S1S15Pc1S1S15Pc2S1S15PacS5S15A1A3A3A3A3A3A3A3A3A3").
Definition TsPL (f : nat) : list (axst * vmap) := ltac2:(tb__ "0|0|
S114SfS4SfS35A2SfS3SfS35R1S108SecA1A4LT;ScbVf;A1A4").

Definition SXof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S11dS7aS4eS5eS3eVf;A1S44S7S4S0S16A2M0S1G0S3S0S16UcS61A4S1G0S3S0S16UdS3aA4S1G0S3S0S16UeS7dA4S5G0A1A3A3A3S7cA3A3U1A2Sd7Vl;S3aA2A2Sc4Vf;Vl;A2A2").
Definition SX_0_L : axst := Eval vm_compute in (SXof 0 true).
Definition SX_0_M : axst := Eval vm_compute in (SXof 0 false).
Definition SX_1_L : axst := Eval vm_compute in (SXof 1 true).
Definition SX_1_M : axst := Eval vm_compute in (SXof 1 false).
Definition SX_2_L : axst := Eval vm_compute in (SXof 2 true).
Definition SX_2_M : axst := Eval vm_compute in (SXof 2 false).
Definition SX (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Se0Se1X2x2S0S0SfLn;R1G0Vl;Se2Se3X2x2S0G0Vl;Se4Se5X2x2Ln0;X0x2Ln;X0x2").
Definition runPB (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S1S14S4fS5S14A1A3S47Vf;Vl;A2A3").
Lemma runPB_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S1S14S4fS5S14A1A3S47R2R1A2A3S57R2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPB. reflexivity. Qed.
Definition E5_0_L : axst := Eval vm_compute in (leaf 0 (runPB 0 true)).
Definition E5_0_M : axst := Eval vm_compute in (leaf 0 (runPB 0 false)).
Definition E5_1_L : axst := Eval vm_compute in (leaf 0 (runPB 1 true)).
Definition E5_1_M : axst := Eval vm_compute in (leaf 0 (runPB 1 false)).
Definition E5_2_L : axst := Eval vm_compute in (leaf 0 (runPB 2 true)).
Definition E5_2_M : axst := Eval vm_compute in (leaf 0 (runPB 2 false)).
Definition E5 (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S92S93X2x2S0S0SfLn;R1G0Vl;S94S95X2x2S0G0Vl;S96S97X2x2Ln0;X0x2Ln;X0x2").
Definition VSX (l : bool) : list positive := ltac2:(tb__ "0|1|
S7S15S52S7S15S1S15PcaS1S15PcbS1S15Pd2S1S15Pd5S1S15Pc0S1S15Pc1S1S15Pc2S1S15PacS5S15A1M0A3A3A3A3A3A3A3A3S2S6S15A1Ll;Vl;G0S1S15PccS1S15PcdS1S15PceG0A3A3A3X2x2A3A3").
Definition TsPB (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35S62Vf;Vl;A2S108S4dVl;A1A1A4S5G0A1A3").

Definition C5of (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S5eS62Vf;Vl;A2S4fS1S4S0S16A2M0S3S0S16UcS68S3cA1A4S5G0A1A3A3").
Definition C5_0_L : axst := Eval vm_compute in (C5of 0 true).
Definition C5_0_M : axst := Eval vm_compute in (C5of 0 false).
Definition C5_1_L : axst := Eval vm_compute in (C5of 1 true).
Definition C5_1_M : axst := Eval vm_compute in (C5of 1 false).
Definition C5_2_L : axst := Eval vm_compute in (C5of 2 true).
Definition C5_2_M : axst := Eval vm_compute in (C5of 2 false).
Definition C5 (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S8cS8dX2x2S0S0SfLn;R1G0Vl;S8eS8fX2x2S0G0Vl;S90S91X2x2Ln0;X0x2Ln;X0x2").
Definition s5 (f : nat) (l : bool) : wsub := ltac2:(tb__ "0|0|
S122P1S10S3bVf;Vl;A2A1S10S102A1A3").
Definition R5 (f : nat) (l : bool) : list sobj := ltac2:(tb__ "0|0|
S128S117S3bVf;Vl;A2S102S48Vf;Vl;A2A3A1").
Definition T5of (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S118S48Vf;Vl;A2S102S120S124S104A1A1S3bVf;Vl;A2S4bVf;Vl;A2A5").
Definition T5fof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S116S4cVf;Vl;A2S20S10S3bVf;Vl;A2A1A1A2").
Definition T5f_0_L : axst := Eval vm_compute in (T5fof 0 true).
Definition T5f_0_M : axst := Eval vm_compute in (T5fof 0 false).
Definition T5f_1_L : axst := Eval vm_compute in (T5fof 1 true).
Definition T5f_1_M : axst := Eval vm_compute in (T5fof 1 false).
Definition T5f_2_L : axst := Eval vm_compute in (T5fof 2 true).
Definition T5f_2_M : axst := Eval vm_compute in (T5fof 2 false).
Definition T5f (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Se6Se7X2x2S0S0SfLn;R1G0Vl;Se8Se9X2x2S0G0Vl;SeaSebX2x2Ln0;X0x2Ln;X0x2").

Definition runPC (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S5S14A1S3dVf;Vl;A2A3").
Lemma runPC_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S5S14A1S3dR2R1A2A3S58R2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPC. reflexivity. Qed.
Definition EUs_0_L : axst := Eval vm_compute in (leaf 0 (runPC 0 true)).
Definition EM_0_L : axst := Eval vm_compute in (leaf 1 (runPC 0 true)).
Definition EUs_0_M : axst := Eval vm_compute in (leaf 0 (runPC 0 false)).
Definition EM_0_M : axst := Eval vm_compute in (leaf 1 (runPC 0 false)).
Definition EUs_1_L : axst := Eval vm_compute in (leaf 0 (runPC 1 true)).
Definition EM_1_L : axst := Eval vm_compute in (leaf 1 (runPC 1 true)).
Definition EUs_1_M : axst := Eval vm_compute in (leaf 0 (runPC 1 false)).
Definition EM_1_M : axst := Eval vm_compute in (leaf 1 (runPC 1 false)).
Definition EUs_2_L : axst := Eval vm_compute in (leaf 0 (runPC 2 true)).
Definition EM_2_L : axst := Eval vm_compute in (leaf 1 (runPC 2 true)).
Definition EUs_2_M : axst := Eval vm_compute in (leaf 0 (runPC 2 false)).
Definition EM_2_M : axst := Eval vm_compute in (leaf 1 (runPC 2 false)).
Definition EUs (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sb7Sb8X2x2S0S0SfLn;R1G0Vl;Sb9SbaX2x2S0G0Vl;SbbSbcX2x2Ln0;X0x2Ln;X0x2").
Definition EM (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S98S99X2x2S0S0SfLn;R1G0Vl;S9aS9bX2x2S0G0Vl;S9cS9dX2x2Ln0;X0x2Ln;X0x2").
Definition TsPC (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|2|
S1S4SfS35A2M0S3SfS35Sb6Vf;Vl;A2S108S4dVl;A1A1M1A4S1G0S3SfS35S42Vf;Vl;A2G1A4S5G0A1A3A3").

Definition D_M : list sobj := ltac2:(tb__ "0|0|
S1S17S6aS3aS3cA2S5S17A1A3").
Definition EMxof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S5cS42Vf;Vl;A2S49A2").
Definition EMdof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S7bS42Vf;Vl;A2S49A2").
Definition EMx_0_L : axst := Eval vm_compute in (EMxof 0 true).
Definition EMd_0_L : axst := Eval vm_compute in (EMdof 0 true).
Definition EMx_0_M : axst := Eval vm_compute in (EMxof 0 false).
Definition EMd_0_M : axst := Eval vm_compute in (EMdof 0 false).
Definition EMx_1_L : axst := Eval vm_compute in (EMxof 1 true).
Definition EMd_1_L : axst := Eval vm_compute in (EMdof 1 true).
Definition EMx_1_M : axst := Eval vm_compute in (EMxof 1 false).
Definition EMd_1_M : axst := Eval vm_compute in (EMdof 1 false).
Definition EMx_2_L : axst := Eval vm_compute in (EMxof 2 true).
Definition EMd_2_L : axst := Eval vm_compute in (EMdof 2 true).
Definition EMx_2_M : axst := Eval vm_compute in (EMxof 2 false).
Definition EMd_2_M : axst := Eval vm_compute in (EMdof 2 false).
Definition EMx (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sa4Sa5X2x2S0S0SfLn;R1G0Vl;Sa6Sa7X2x2S0G0Vl;Sa8Sa9X2x2Ln0;X0x2Ln;X0x2").
Definition EMd (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S9eS9fX2x2S0S0SfLn;R1G0Vl;Sa0Sa1X2x2S0G0Vl;Sa2Sa3X2x2Ln0;X0x2Ln;X0x2").

Definition AMof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S11aS63Vf;Vl;A2S19Z0A1A2").
Definition AM_0_L : axst := Eval vm_compute in (AMof 0 true).
Definition AM_0_M : axst := Eval vm_compute in (AMof 0 false).
Definition AM_1_L : axst := Eval vm_compute in (AMof 1 true).
Definition AM_1_M : axst := Eval vm_compute in (AMof 1 false).
Definition AM_2_L : axst := Eval vm_compute in (AMof 2 true).
Definition AM_2_M : axst := Eval vm_compute in (AMof 2 false).
Definition AM (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S7fS80X2x2S0S0SfLn;R1G0Vl;S81S82X2x2S0G0Vl;S83S84X2x2Ln0;X0x2Ln;X0x2").
Definition runPD (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S5S14A1S40Vf;Vl;A2A3").
Lemma runPD_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S5S14A1S40R2R1A2A3S59R2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPD. reflexivity. Qed.
Definition EU_0_L : axst := Eval vm_compute in (leaf 0 (runPD 0 true)).
Definition EU_0_M : axst := Eval vm_compute in (leaf 0 (runPD 0 false)).
Definition EU_1_L : axst := Eval vm_compute in (leaf 0 (runPD 1 true)).
Definition EU_1_M : axst := Eval vm_compute in (leaf 0 (runPD 1 false)).
Definition EU_2_L : axst := Eval vm_compute in (leaf 0 (runPD 2 true)).
Definition EU_2_M : axst := Eval vm_compute in (leaf 0 (runPD 2 false)).
Definition EU (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;SaaSabX2x2S0S0SfLn;R1G0Vl;SacSadX2x2S0G0Vl;SaeSafX2x2Ln0;X0x2Ln;X0x2").
Definition TsPD (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35S43Vf;Vl;A2S108S4dVl;A1A1A4S5G0A1A3").

Definition D_U (l : bool) : list sobj := ltac2:(tb__ "0|2|
S7S17S1S17S70S1S17S71S1S17S6fS1S17S6eS1S17S72S1S17S6cS1S17S6bS3aS3cA2S1S17S51S3aS19Z0A1M0A2S1S17S50G0A1S5S17A1M1A3A3A3A3A3A3A3A3A3S2S6S17A1Ll;Vl;G1S1S17S69G0A1S1S17S6dG1A3A3X2x2A3").
Definition EUxof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S5cS43Vf;Vl;A2S4aVl;A1A2").
Definition EUdof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S7bS43Vf;Vl;A2S4aVl;A1A2").
Definition EUx_0_L : axst := Eval vm_compute in (EUxof 0 true).
Definition EUd_0_L : axst := Eval vm_compute in (EUdof 0 true).
Definition EUx_0_M : axst := Eval vm_compute in (EUxof 0 false).
Definition EUd_0_M : axst := Eval vm_compute in (EUdof 0 false).
Definition EUx_1_L : axst := Eval vm_compute in (EUxof 1 true).
Definition EUd_1_L : axst := Eval vm_compute in (EUdof 1 true).
Definition EUx_1_M : axst := Eval vm_compute in (EUxof 1 false).
Definition EUd_1_M : axst := Eval vm_compute in (EUdof 1 false).
Definition EUx_2_L : axst := Eval vm_compute in (EUxof 2 true).
Definition EUd_2_L : axst := Eval vm_compute in (EUdof 2 true).
Definition EUx_2_M : axst := Eval vm_compute in (EUxof 2 false).
Definition EUd_2_M : axst := Eval vm_compute in (EUdof 2 false).
Definition EUx (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;SbdSbeX2x2S0S0SfLn;R1G0Vl;SbfSc0X2x2S0G0Vl;Sc1Sc2X2x2Ln0;X0x2Ln;X0x2").
Definition EUd (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sb0Sb1X2x2S0S0SfLn;R1G0Vl;Sb2Sb3X2x2S0G0Vl;Sb4Sb5X2x2Ln0;X0x2Ln;X0x2").

Definition AUof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S11aS65Vf;Vl;A2S19Z0A1A2").
Definition AU_0_L : axst := Eval vm_compute in (AUof 0 true).
Definition AU_0_M : axst := Eval vm_compute in (AUof 0 false).
Definition AU_1_L : axst := Eval vm_compute in (AUof 1 true).
Definition AU_1_M : axst := Eval vm_compute in (AUof 1 false).
Definition AU_2_L : axst := Eval vm_compute in (AUof 2 true).
Definition AU_2_M : axst := Eval vm_compute in (AUof 2 false).
Definition AU (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S85S86X2x2S0S0SfLn;R1G0Vl;S87S88X2x2S0G0Vl;S89S8aX2x2Ln0;X0x2Ln;X0x2").
Definition runPE (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S1S14S10aS5S14A1A3S41Vf;Vl;A2A3").
Lemma runPE_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S1S14S10aS5S14A1A3S41R2R1A2A3S5aR2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPE. reflexivity. Qed.
Definition LR_0_L : axst := Eval vm_compute in (leaf 0 (runPE 0 true)).
Definition LR_0_M : axst := Eval vm_compute in (leaf 0 (runPE 0 false)).
Definition LR_1_L : axst := Eval vm_compute in (leaf 0 (runPE 1 true)).
Definition LR_1_M : axst := Eval vm_compute in (leaf 0 (runPE 1 false)).
Definition LR_2_L : axst := Eval vm_compute in (leaf 0 (runPE 2 true)).
Definition LR_2_M : axst := Eval vm_compute in (leaf 0 (runPE 2 false)).
Definition LR (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sd0Sd1X2x2S0S0SfLn;R1G0Vl;Sd2Sd3X2x2S0G0Vl;Sd4Sd5X2x2Ln0;X0x2Ln;X0x2").
Definition TsPE (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35ScfVf;Vl;A2S108S4dVl;A1A1A4S5G0A1A3").

Ltac fam3 := let f := fresh "f" in intros f; destruct f as [|[|[|f]]].
Ltac fam6 := let f := fresh "f" in let l := fresh "l" in intros f l; destruct f as [|[|[|f]]]; destruct l.
Definition famok (f : nat) : bool := Nat.leb f 2.
Lemma chkPA : ltac2:(tb__ "0|0|
S0S38S2S36S1aS10S46R1A1A1A1S56R1A1S74R1A1A3S8A3Ff;"). Proof. fam3; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPL : ltac2:(tb__ "0|0|
S0S38S2S36S1aS10S3eR1A1A1A1S5bR1A1S79R1A1A3S8A3Ff;"). Proof. fam3; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPB : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S47R2R1A2A1A1S57R2R1A2S75R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPC : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S3dR2R1A2A1A1S58R2R1A2S76R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPD : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S40R2R1A2A1A1S59R2R1A2S77R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPE : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S41R2R1A2A1A1S5aR2R1A2S78R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.

Lemma EMx_eq : ltac2:(tb__ "0|1|
S0S2S38SbSfA1S107S42R2R1A2M0S1S105S106S5dG0S49A2A1S5S105A1A3A2ScSfS64R2R1A2A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma EUx_eq : ltac2:(tb__ "0|1|
S0S2S38SbSfA1S107S43R2R1A2M0S1S105S106S5dG0S4aR1A1A2A1S5S105A1A3A2ScSfS66R2R1A2A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma EMd_eq : ltac2:(tb__ "0|0|
S0S2S38SfS63R2R1A2S4eS64R2R1A2U1A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma EUd_eq : ltac2:(tb__ "0|0|
S0S2S38SfS65R2R1A2S4eS66R2R1A2S2S0Ll;R1U9UbX2x2A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.

Lemma runs_shape : ltac2:(tb__ "0|7|
S0S2S38S4S4S4S4S4S4S4S0S0A2M0S0A2M1S0A2M2S0A2M3S0A2M4S0A2M5S0A2S3G5S0S3G4S0S3G3S0S3G2S0S3G1S0S3G0S0S3S0S0S9S11S56R2A1A2S9S11S5bR2A1A2A4S9S11S57R2R1A2A2A4S9S11S58R2R1A2A2A4S9S11S59R2R1A2A2A4S9S11S5aR2R1A2A2A4S53S42R2R1A2S49A2A4S53S43R2R1A2S4aR1A1A2A4S3G5S0S3G4S0S3G3S0S3G2S0S3G1S0S3G0S0S3S0S0U1M6U8A4G6A4U2A4G6A4G6A4G6A4S2S0Ll;R1U9UbX2x2A4A3Fl;Ff;").
Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.

Lemma He5 : ltac2:(tb__ "0|1|
S0S2S38SbS6S17A1M0A1S117S3bR2R1A2S102S48R2R1A2A3ScG0S4bR2R1A2A2A3Fl;Ff;").
Proof. fam6; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk5 : ltac2:(tb__ "0|0|
S0S2S38S2S119S3bR2R1A2S102S48R2R1A2S4bR2R1A2S114S11SfS13S103A4A5S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.

Lemma HT5 : ltac2:(tb__ "0|0|
S0S2S11SfeS11R1S103A3S38SfS118S48R4R3A2S102S13R2A1S3bR4R3A2S4bR4R3A2A5S4cR4R3A2A3F_;FP;Fl;Ff;").
Proof. intros f l P [<-|[]]. reflexivity. Qed.
Lemma T5f_eq : ltac2:(tb__ "0|0|
S0S2S38SfS116S4cR2R1A2S20S10S3bR2R1A2A1A1A2S3dR2R1A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma FBC5 : ltac2:(tb__ "0|1|
S0S2S38S2SffS18S2aS1aS10S3bR2R1A2A1M0A1A1S20G0A1A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma FBT5 : ltac2:(tb__ "0|0|
S0S2S38S2SffS18S2aS1aS10S4cR2R1A2A1A1A1S20S10S3bR2R1A2A1A1A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma NXC5 : ltac2:(tb__ "0|0|
S0S2S100SfbS1aS10S3bR2R1A2A1A1A2Fl;Ff;"). Proof. fam6; apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxS : ltac2:(tb__ "0|6|
S39S0S39S38S2S1eS10S46R1A1A1M0A1SaA3S100SfbS1aG0A1A2A2Ff;S39S0S39S38S2S1eS10S3eR1A1A1M1A1SaA3S100SfbS1aG1A1A2A2Ff;S39S0S2S39S38S2S1eS10S47R2R1A2A1M2A1SaA3S100SfbS1aG2A1A2A2Fl;Ff;S39S0S2S39S38S2S1eS10S3dR2R1A2A1M3A1SaA3S100SfbS1aG3A1A2A2Fl;Ff;S39S0S2S39S38S2S1eS10S40R2R1A2A1M4A1SaA3S100SfbS1aG4A1A2A2Fl;Ff;S0S2S39S38S2S1eS10S41R2R1A2A1M5A1SaA3S100SfbS1aG5A1A2A2Fl;Ff;A2A2A2A2A2").
Proof.
  split; [fam3; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam3; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]).
Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_PA : ltac2:(tb__ "0|0|
S0Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S74R8A1A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S46R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Ff;").
Proof. intros f J rho tp HJ HC. exact (tr_piece X 300%nat _ (S0 f) (runPA f) (TsPA f) (runPA_eq f) (chkPA f) (proj1 (proj1 nxS f)) (proj2 (proj1 nxS f)) J rho tp HJ HC). Qed.
Theorem seg_PL : ltac2:(tb__ "0|0|
S0Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S79R8A1A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S3eR6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Ff;").
Proof. intros f J rho tp HJ HC. exact (tr_piece X 100%nat _ (SC f) (runPL f) (TsPL f) (runPL_eq f) (chkPL f) (proj1 (proj1 (proj2 nxS) f)) (proj2 (proj1 (proj2 nxS) f)) J rho tp HJ HC). Qed.
Theorem seg_PB : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S75R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S47R7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (SX f l) (runPB f l) (TsPB f l) (runPB_eq f l) (chkPB f l) (proj1 (proj1 (proj2 (proj2 nxS)) f l)) (proj2 (proj1 (proj2 (proj2 nxS)) f l)) J rho tp HJ HC). Qed.
Theorem seg_PC : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S76R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S3dR7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (T5f f l) (runPC f l) (TsPC f l) (runPC_eq f l) (chkPC f l) (proj1 (proj1 (proj2 (proj2 (proj2 nxS))) f l)) (proj2 (proj1 (proj2 (proj2 (proj2 nxS))) f l)) J rho tp HJ HC). Qed.
Theorem seg_PD : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S77R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S40R7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (AM f l) (runPD f l) (TsPD f l) (runPD_eq f l) (chkPD f l) (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) J rho tp HJ HC). Qed.
Theorem seg_PE : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S78R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S41R7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (AU f l) (runPE f l) (TsPE f l) (runPE_eq f l) (chkPE f l) (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) J rho tp HJ HC). Qed.

Theorem qs_memset : ltac2:(tb__ "0|1|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3S1cS2cS1aS10S3bR7R6A2M0A1A1R4R1A3Sf7VQ;VX;Sf3Sf6R6S3dR8R7A2R2R4A5A3F_;Frho';Sf7VQ;VX;Sf3Sf6R5G0R4R3A5A3F_;F_;Ftp;FrhoE;FJ;Fl;Ff;").
Proof.
  intros f l J rhoE tp HJ HC.
  apply (tr_call X (C5 f l) Pre_memsetA Posts_memsetA (s5 f l) (R5 f l) (T5of f l)
           (fun ok Jx rho tp0 Hok Hst => memset_sumA ok Jx rho tp0 Hok Hst) (fun Jx rho tp0 Hst => memset_sumA_ex Jx rho tp0 Hst)
           (He5 f l) (Hchk5 f l) (HT5 f l) (FBC5 f l) (FBT5 f l) (NXC5 f l) J rhoE tp HJ).
  intros rho' Hag. rewrite (T5f_eq f l). exact (HC rho' Hag).
Qed.
End TR.

End SegQS_states.

(* [comment removed for export] *)
Module F0T_minst.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "FcsrFrm0"; "mkSS"; "valuation"; "SVar"; "rw"; "sprop"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "agree_below"; "cell"; "holds"; "mkObj"; "obj_range"; "smatch"; "soff"; "sprop_below"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "app"; "nil"; "cons"; "None"; "false"; "list"; "bool"; "prod"; "true"; "Some"; "fst"; "option"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@Stdlib.ZArith.BinInt.Z"; "le"; "div"; "add"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "MIDPC"; "regs_mid"; "stack_win_mid"; "Pre_mid"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NFS"; "O_pad"; "XI"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ustop"; "A_globals"; "mkA"; "unwind_objs"; "F_sp_high"; "KcA"; "base_sv"; "free_depth"; "pre_facts"; "stack_win"; "ulink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "O_sh"; "RT_f"; "VOBJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst"; "PMID_fc"; "sa_m"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "tol_facts"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst.StatesM"; "sd_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@Stdlib.Lists.List"; "In"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma stack_winm_range : ltac2:(tb__ "0|3|
S1cS56A1S4S14S1eS1cS58A1S57A2S11R4R3R2R1A4S63S0S2fS9R3A1A3SeR5S3fA2S25S27Z7fff7f800000S21S15S15S10R6S44A2M0A3M1A2S25S24S15S23S15S15G0A3M2S54Q40S6R6PaA2A2A3S27G1G2A2A2A2F_;F_;F_;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w Hsm Hin Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of, stack_win_mid in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Section StatesM.
Variable khi : bool.
Variables (W : list ulink) (st : ustop) (q : qvar).
Let PREOBJS : list sobj := ltac2:(tb__ "0|0|
S19S0S2fS17S0S3eVW;A1S17S0S19S0SfS5PcA1SbZ0A1S5PdA1S18SdA1SaA5S18S0A1A3S3cA3A3A3").
Let PREFACTS : list sprop := ltac2:(tb__ "0|0|
S17S7S3bS1cS7A1Lst;Vst;S51S51X3bx2S43S42A1A3").
Definition sa_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1VPREOBJS;VPREFACTS;S26S1bA9").
Definition sb_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1S17S0VPREOBJS;S31S36S0S35S37Vq;A1A4A3VPREFACTS;S26S1bA9").
Definition sc_m : sstate := ltac2:(tb__ "0|0|
S3S2dS2eS2cS2S1aS1A1S17S0S17S0VPREOBJS;S31S36S0S35S37Vq;A1A4A3S19S0S48S18S0A1A3A3VPREFACTS;S26S1bA9").
Definition sd_m : sstate := ltac2:(tb__ "0|1|
S3S2dS2eS2cS2S1aS1A1S17S0S17S0S17S0VPREOBJS;S31S36S0S35S37Vq;A1A4A3S19S0S48S18S0A1M0A3A3S19S0S38G0A3A3VPREFACTS;S26S1bA9").
Definition se_m : axst := ltac2:(tb__ "0|0|
S3dS5aS5dS46Vkhi;Vq;A2A2S18S1eS1S1A2A1A2").
End StatesM.

Definition PMID_fc (khi : bool) (W : list ulink) (st : ustop) (q : qvar) : axst := ltac2:(tb__ "0|0|
S3dS3S2dS2eS2cS2S1aS1A1S17S0S17S0S19S0S2fS17S0S3eVW;A1S3cA3A3S49A3S4aVq;A1A3S46Vkhi;Vq;A2S26S1bA9S18S1eS1S1A2A1A2").
Lemma Pre_mid_sa : ltac2:(tb__ "0|0|
S1cS45A1S3bS24S32S30R2R1A2S34S4cR2R1A2S18S1eS1S1A2A1S41A3A3Fst;FW;").
Proof. reflexivity. Qed.

Section INSTM.
Let segs : list Segment := segsA.
Variable khi : bool.
Let nW : nat := 0%nat. Let st : ustop := UStopLe. Variable q : qvar.
Let W : list ulink := Wcan nW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (A : AA) (Kc : KcA) : jpredA := J_free_tol_preT A Kc.

Hypothesis Wb : ltac2:(tb__ "0|0|
S24S1dS8S4dVW;Vst;Vq;A3A1S1fA3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S24S1dS8S4eVW;Vst;Vq;A3A1S1fA3").
Hypothesis Wd : ltac2:(tb__ "0|0|
S24S1dS8S4fVW;Vst;Vq;A3A1S1fA3").
Hypothesis Fe : ltac2:(tb__ "0|0|
S24S1dS64S7S13S26A1S46Vkhi;Vq;A2A3S1fA3").
Hypothesis AXI : ltac2:(tb__ "0|0|
S24S22S32A1S5bS50Vkhi;VW;Vst;Vq;A4S39VnW;Vq;A2A2S20S32S4bVkhi;VW;Vst;Vq;A4A2A3").

Lemma bv_signed_small : ltac2:(tb__ "0|1|
S15S25S27Z0R1A2S2aR1S2bZ2Z3fA2A2A2S24S15S55Q40M0S52G0R2A2A2R2A3F_;Fz;").
Proof.
  intros z Hz. rewrite bv_signed_U, u64_lit by lia. unfold Zsigned, H63v, M64v. destruct (Z.ltb_spec z 9223372036854775808); lia.
Qed.
Lemma div8_sum_le : ltac2:(tb__ "0|2|
S15S15S27Z0R2A2M0G0S27S29S28R4Z8M1A2S28R3G1A2A2S28S29R4R3A2G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
  apply Z.div_le_lower_bound; lia.
Qed.
Lemma soff_var : ltac2:(tb__ "0|1|
S4S16S15S24S53Q40M0A1S6R3R2A2S52G0R1A2A3S25S27Z0R2A2S2aR2S2bZ2Z3fA2A2A2S24S15S12R5S5R4A1A2R3A3F_;F_;Fz;Fi;Frho;").
Proof. intros rho i z E Hz. unfold soff. cbn [eval]. rewrite E. apply bv_signed_small. exact Hz. Qed.

Theorem f_instantiate_mid : ltac2:(tb__ "0|2|
S5eS40S4S4S1cS53Q40M0A1A1S59S15S15S15ScS26R7R6A3S3aVkhi;VW;Vst;Vq;R7R4R3R2S60S5fRaA1A1A9S47Vsegs;VJ;RbRaA2S30VW;Vst;A2R9R7R6A6S25S5cRaR9A2S25S47Vsegs;S61RcRbR9A3S4bVkhi;VW;Vst;Vq;A4M1R9R8R7A6S62R9S54G0S6R9PaA2A2S9S33G1A1A1A3A2A2F_;F_;F_;Fn8;Fn;Fp;Fw;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp w p n n8 Hag2 IFF H.
  assert (Hag : agree_below NF rho rho1) by (eapply agree_below_le; [|exact Hag2]; cbv; discriminate).
  destruct IFF as [E12 E13 E105 E106 Hpn Hcarve Hzone Hpd Hsh Hpadm Hfacts Hrig].
  split; [exact (Hrig rho (agree_below_vals _ _ _ Hag))|]. unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hpn.
  pose proof H as [HsmA HJ]. destruct HJ as ((HA & HU & HL & HK & Htp & HB & Htop) & HKM & HPRES).
  pose proof HA as (HG & _).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.

  assert (H1 : SPA segs (J A Kc) (Pre_mid W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|exact Hag2]; cbv; discriminate | apply (JTr_agree A Kc rho rho1); exact Hag]. }
  clear H HsmA.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by (symmetry; apply (proj1 Hag); unfold NF; lia).

  pose proof (proj2 H1) as ((_ & _ & _ & _ & _ & _ & Htop1) & _).
  assert (TOPlo : TOP <= fst (obj_range rho1 stack_win)) by exact Htop1.

  assert (H2 : SPA segs (J A Kc) (mkAX (sa_m W st) [] base_sv) rho1 tp w) by exact H1.
  clear H1.

  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_m]; apply in_or_app; right; cbn; tauto).
  destruct (stack_winm_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { constructor. }

  pose proof (urange (rw rho1 12%positive)) as U12. pose proof (urange (rw rho1 13%positive)) as U13.
  assert (Ep : bv_unsigned (rw rho1 12%positive) = p) by (rewrite E12; apply u64_lit; lia).
  assert (En : bv_unsigned (rw rho1 13%positive) = n) by (rewrite E13; apply u64_lit; lia).

  assert (H3 : SPA segs (J A Kc) (mkAX (sb_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sb_m W st q) [] base_sv) with
      (ax_setS (mkAX (sa_m W st) [] base_sv) (let S := ax_S (mkAX (sa_m W st) [] base_sv) in
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
      cbn [ss_objs ax_S sa_m]. unfold A_globals, O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI, IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
      apply Forall_cons.
      { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; lia. }
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
  assert (H4 : SPA segs (J A Kc) (mkAX (sc_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sc_m W st q) [] base_sv) with
      (ax_setS (mkAX (sb_m W st q) [] base_sv) (let S := ax_S (mkAX (sb_m W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj shb (SLit 0) vN8g [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SLit 0) = 0) by (apply soff_lit_small; lia).
    assert (Ehi : soff rho1 vN8g = n8 / 8).
    { unfold vN8g. apply (soff_var rho1 106%positive (n8 / 8) E106). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w shb (SLit 0) vN8g NW2 H3 Wc (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Hshb; try lia.
    -
      cbn [ss_objs ax_S sb_f]. apply Forall_app. split.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
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

  assert (H5 : SPA segs (J A Kc) (mkAX (sd_m W st q) [] base_sv) rho1 tp w).
  { change (mkAX (sd_m W st q) [] base_sv) with
      (ax_setS (mkAX (sc_m W st q) [] base_sv) (let S := ax_S (mkAX (sc_m W st q) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SVar 12) (SVar 13) vN8 [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SVar 13) = n) by (apply (soff_var rho1 13%positive n E13); lia).
    assert (Ehi : soff rho1 vN8 = n8) by (unfold vN8; apply (soff_var rho1 105%positive n8 E105); lia).
    assert (Eb : bv_unsigned (eval rho1 (SVar 12)) = p) by (cbn [eval]; exact Ep).
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w (SVar 12) (SVar 13) vN8 NW2 H4 Wd (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Eb; try lia.
    -
      cbn [ss_objs ax_S sc_f sb_f]. apply Forall_app. split; [apply Forall_app; split|].
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
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

  assert (H6 : SPA segs (J A Kc) (se_m khi W st q) rho1 tp w).
  { unfold se_m. change (mkA (with_facts (sd_m W st q) (FACTS_Tc khi q)) []) with (ax_with_facts (mkAX (sd_m W st q) [] base_sv) (FACTS_Tc khi q)).
    eapply SPA_refacts; [exact H5 | exact Fe |].
    intros Hold. unfold FACTS_Tc, FACTS_Tg.
    assert (HP : Forall (holds rho1) (tol_facts ++ pre_facts free_depth)).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) Hold). cbn [ss_facts ax_S sd_m]. exact Hp. }
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

  pose proof (SPA_axforms segs (J A Kc) (XI nW q) rho1 (se_m khi W st q) (PMID_fc khi W st q) tp w AXI H6) as H7.

  split; [exact (SPA_JT_intro A Kc (PMID_fc khi W st q) rho1 tp w H7)|].
  clear H6 H7. unfold objs_le, PMID_fc, mkA. cbn [ss_objs ax_S]. rewrite <- NRT_ok, <- (NV_ok q).
  assert (CARVE : forall l, incl l (NFS q) -> Forall (fun o => snd (obj_range rho1 o) <= bv_unsigned (rw rho1 10%positive)) (map carve_obj l)).
  { intros l Hl. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk0). pose proof (Hl k Hk0) as Hk.
    pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
    destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
    destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia. cbn [fst snd].
    unfold IMG_HI in *. lia. }
  repeat rewrite <- app_assoc. cbn [app]. apply Forall_cons; [change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win); lia|].
  unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
  apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia; lia|].
  apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia; lia|].
  apply Forall_app. split; [apply CARVE; unfold NFS; apply incl_appl; apply incl_refl|].
  apply Forall_cons.
  { unfold O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
    rewrite Hshb. unfold vN8g. rewrite (soff_var rho1 106%positive (n8 / 8) E106) by (split; [lia | apply Z.div_lt_upper_bound; lia]). lia. }
  apply Forall_cons.
  { unfold O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
    unfold vN8. rewrite (soff_var rho1 105%positive n8 E105) by lia. cbn [eval]. rewrite Ep. lia. }
  apply CARVE. unfold NFS. apply incl_appr. apply incl_refl.
Qed.
End INSTM.
End F0T_minst.

(* [comment removed for export] *)
Module SpineCallocS8.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "nil"; "true"; "cons"; "list"; "pair"; "prod"; "nat"; "Some"; "option"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "ss_facts"; "valuation"; "ss_next"; "SPBranch"; "SLit"; "rw"; "swf"; "SPNot"; "sobj"; "SAlu"; "eval"; "SPUle"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_CLS"; "E7c1"; "E7c2"; "F_gen"; "C7p"; "E7q1"; "E7q2"; "E7p"; "V_ND"; "n8e"; "upd"; "C8"; "C8p"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "BP"; "C7"; "LPe"; "ube"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "add"; "mul"; "le"; "lt"; "of_nat"; "sub"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "ALU_ADD"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.S8.B11S"; "E7c1'"; "E7c2'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.S8.B12S"; "E7q1'"; "E7q2'"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "needed8"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8"; "a0e7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "pvals_ok"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition a0e7 : sv := ltac2:(tb__ "0|0|
S1eS59S1eS5aS1eS59S3bS30A3S19Z3A1A3S40A3").

Section PSVals7.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S6bVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S45S45VSB;S46Vc;S4bZ2Z20A2A2A2S46Z10Vx;A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_a0e7 : ltac2:(tb__ "0|0|
S0S4cQ40A1S1fVrho;S6aA2S1fVrho;S38A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ub rho _ _ _ _ _ _ PV) as EUB. cbn zeta in EUB. fold ab in EUB.
  pose proof (pv_bp rho _ _ _ _ _ _ PV) as EBP. cbn zeta in EBP. fold ab in EBP.
  apply bv_eq. rewrite EBP. unfold a0e7, shb. cbn [eval]. fold ube. fold n8e.
  assert (EN8 : bv_unsigned (eval rho n8e) = n - n mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). apply land_M48. lia. }
  rewrite add_val, srl_val, add_val, EUB, EN8, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (B1 : 17594333495296 <= ab + rzv /\ ab + rzv + n <= 140737479966720) by (unfold ab; lia).
  rewrite (Z.mod_small (ab + rzv + _)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small rho _ _ _ _ _ _ PV (ab + rzv + (n - n mod 8)) ltac:(lia)) as (_ & E & _). rewrite E.
  unfold Sh. pose proof (Z.div_mod rzv 16 ltac:(lia)). pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)).
  replace (ab + rzv + (n - n mod 8)) with (ab + rzv + (n / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma pv_lp1 : ltac2:(tb__ "0|0|
S2S0S22S44Vn;Z8A2Z0A3A1S0S22S4dQ40S1fVrho;S3aA2A2Z1A3F_;").
Proof. intros Hn. rewrite (pv_lp rho _ _ _ _ _ _ PV). destruct (Z.eq_dec (n mod 8) 0); [contradiction | reflexivity]. Qed.
End PSVals7.

Section S8.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S55VAInv;VW;Vst;VA;VKc;S14PcA1A6").

Lemma class_restate_gen : ltac2:(tb__ "0|7|
S4S21S13S22SeS56S53S16SbS4cQ40M0A1A1S42S16S0S7S5dP9dM1R9A2S9A3S0S7S5eG1RaS5cR9R8A5S9A3S0S7S1bRcA1S9A3S0S10SdSbSdS13S13A2M2A1M3SbS12A1M4A2M5A1S52S3ReA1RdA2SfG5ScG3G4SaG2ScS13S13RcS14S27A1A4S8G2A1A3S8S12A1A4A2A3S0S23S17ReA1S17S3RfA1A1A3S68S4dG0S1aR9PcA2A2A1S22S1S1S47ReR1A2S48R1S45ReS46Z8M6S49RdA1A2A2A2A2S0S22S44S4aR1ReA2G6A2Z0A3A2Tnd;S24Vsegs;S3cVW;Vst;RcRbRaA5R11R7R9R8A6S24Vsegs;S3cVW;Vst;RdRcRbA5S6R12R11A2R8RaR9A6F_;F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fcnt;Flo;Fcreg;FES;FE;").
Proof.
  intros E ES creg lo cnt A Kc rho tp w rhoE OV TAB WS DS NX [Hr Hm] Hw.
  destruct w as [tr [ms md]]. pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _).
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  eapply SPA_restate; [exact WS | exact DS | exact NX | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_CLS. cbn [eval]. rewrite E158.
  exact (tab_ok_sound 157 _ ClassID lo cnt rhoE _ TAB OV E157 Hr Hm).
Qed.

Lemma needed_range : ltac2:(tb__ "0|6|
S56S53S16S16SbS4cQ40M0A1A1S42S4S7S24Vsegs;S3cVW;Vst;R8R7R6A5R2R5R4R3A6S3eS12S2aS15S3R3A1A1A3S3dS12S7S12Lb;R3S18S57S19Z200A1S14S2fA1A3M1S1cG1A1X7x2S15S3R4A1A1A3S68S4dG0S1aR9PcA2A2A1S22S7OLb;R5S1S1S47Z208M2R1A2S48R1S45G2S46Z8M3S49S63S64S4eS4fS50S4eS51A1A1A1A1A1A1A1A2A2A2A2S0S22S44S4aR1G2A2G3A2Z0M4A3A2S1S1S47Z18M5R1A2S48R1S45G5S46G3S49U3eA1A2A2A2A2S0S22S44S4aR1G5A2G3A2G4A3A2X7x2Tnd;F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *. cbn zeta.
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia. change (2 ^ 3) with 8 in G3.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F1.
  destruct b; cbn [holds eval] in F1; unfold V_ND in F1; rewrite E157 in F1; rewrite bt_ltu_lit in F1 by lia.
  - apply Z.ltb_lt in F1. split; [cbn; lia|]. replace (needed8 nv - 520) with (needed8 nv + (- 65) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
  - assert (needed8 nv <= 512) by (destruct (Z.ltb_spec 512 (needed8 nv)); [exfalso; apply F1; reflexivity | lia]).
    split; [cbn; lia|]. replace (needed8 nv - 24) with (needed8 nv + (- 3) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.

Section B11S.
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S7S65S66Ufa0SaS22Z3c8bcSaS22Z3ca04S8S22A1A3A3S3fSaS4S39VW;Vst;Vtmax;A3S8S4A1M0A3SaS4S28VW;Vst;Vtmax;A3SaS4S29VW;Vst;Vtmax;A3SaS4S2eVW;Vst;Vtmax;A3G0A3A3A3A6S9A3").
Definition E7c1' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S28VW;Vst;Vtmax;A3Z3ca04SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Definition E7c2' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S29VW;Vst;Vtmax;A3Z3ca04SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Hypothesis OV7a : ltac2:(tb__ "0|0|
S0S7S5dP9dS34VW;Vst;Vtmax;A3A2S9A3").
Hypothesis OV7b : ltac2:(tb__ "0|0|
S0S7S5dP9dS35VW;Vst;Vtmax;A3A2S9A3").
Hypothesis TAB7a : ltac2:(tb__ "0|0|
S0S7S5eP9dS34VW;Vst;Vtmax;A3S5cZ208S63S64S4eS4fS50S4eS51A1A1A1A1A1A1A5S9A3").
Hypothesis TAB7b : ltac2:(tb__ "0|0|
S0S7S5eP9dS35VW;Vst;Vtmax;A3S5cZ18U3eA5S9A3").
Hypothesis W7a : ltac2:(tb__ "0|0|
S0S7S1bS3S5fA1A1S9A3").
Hypothesis W7b : ltac2:(tb__ "0|0|
S0S7S1bS3S60A1A1S9A3").
Hypothesis D7a : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S28VW;Vst;Vtmax;A3A1S3S5fA1A2SfG3ScG1G2SaG0ScS13S13S34VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis D7b : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S29VW;Vst;Vtmax;A3A1S3S60A1A2SfG3ScG1G2SaG0ScS13S13S35VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis NX7a : ltac2:(tb__ "0|0|
S0S23S17S3S5fA1A1S17S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7b : ltac2:(tb__ "0|0|
S0S23S17S3S60A1A1S17S3S29VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7a : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7b : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S29VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7a : ltac2:(tb__ "0|0|
S3dS12S18S57S19Z200A1S14S2fA1A3S15S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7b : ltac2:(tb__ "0|0|
S3dS12S1cS18S57S19Z200A1S14S2fA1A3A1S15S3S29VW;Vst;Vtmax;A3A1A1A3").
Variables s8a s8b : wsub.
Hypothesis ENT8a : ltac2:(tb__ "0|0|
S0S7S5S5fS32VW;Vst;Vtmax;A3Vs8a;A3S9A3").
Hypothesis ENT8b : ltac2:(tb__ "0|0|
S0S7S5S60S32VW;Vst;Vtmax;A3Vs8b;A3S9A3").
Hypothesis SID8a : ltac2:(tb__ "0|0|
S0S7S5bVs8a;S3fA2S9A3").
Hypothesis SID8b : ltac2:(tb__ "0|0|
S0S7S5bVs8b;S3fA2S9A3").

Hypothesis G7p : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7p : ltac2:(tb__ "0|0|
S3dS12S1cS18S58S14PcA1S30A3A1S15S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W7p : ltac2:(tb__ "0|0|
S0S7S1bS3S2bVW;Vst;Vtmax;A3A1A1S9A3").
Hypothesis D7p : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S2eVW;Vst;Vtmax;A3A1S3S2bVW;Vst;Vtmax;A3A1A2SfG3ScG1G2SaG0ScS13S13S6aS38A4S8G0A1A3SaS12S20S19Z1A1S3aA2S8S12A1A3A4A2A3").
Hypothesis NX7p : ltac2:(tb__ "0|0|
S0S23S17S3S2bVW;Vst;Vtmax;A3A1A1S17S3S2eVW;Vst;Vtmax;A3A1A1A3").

Hypothesis F7an : ltac2:(tb__ "0|0|
S3dS12S18S58S14PcA1S30A3S15S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7bn : ltac2:(tb__ "0|0|
S3dS12S18S58S14PcA1S30A3S15S3S29VW;Vst;Vtmax;A3A1A1A3").

Lemma nmod8_of_fact : ltac2:(tb__ "0|4|
S56S53S16S16SbS4cQ40M0A1A1S42S4S7S24Vsegs;S3cVW;Vst;R8R7R6A5R2R5R4R3A6S3eS12S2aS15S3R3A1A1A3S3dS12S7S12Lb;R3S18S58S14PcM1A1S30A3M2S1cG2A1X7x2S15S3R4A1A1A3S7OLb;R4S0S22S44S4dG0S1aR9G1A2A2Z8A2Z0A3M3S2G3A1X7x2F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (JGb_rigid nW st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & _).
  destruct (JGb_model nW st A Kc rho rhoE tp tr md (proj2 Hw)) as [_ HN]. cbn zeta in HN.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F.
  assert (EV : bv_unsigned (eval rhoE n8e) = bv_unsigned (rw rho 12%positive) - bv_unsigned (rw rho 12%positive) mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, u64_lit by (unfold M48; lia). apply land_M48. pose proof (urange (rw rho 12%positive)). lia. }
  destruct b; cbn [holds eval] in F; fold n8e in F; cbn [branch_taken] in F; unfold bv_eqb in F; rewrite E12, EV in F.
  - apply Z.eqb_eq in F. lia.
  - intros E0. apply F. apply Z.eqb_eq. lia.
Qed.

Theorem spine_s7 : ltac2:(tb__ "0|5|
S42OF_;S56S53S16SbS4cQ40M0A1A1S43S67VW;Vst;A2S54R5A1S26Vsegs;R8S25R6A1A3S47Z1S69R8S4dG0S1aR6PcM1A2A2A2A2S0S22S44S4dG0S1aR7G1A2A2Z8M2A2Z0M3A3S16S41Vsegs;RcS24Vsegs;S3cVW;Vst;RbRaR9A5S32VW;Vst;Vtmax;A3R1R8A5R7A4FrhoX;F_;S2S0S22S44S4dG0S1aR8G1A2A2G2A2G3A3A1S16S41Vsegs;RdS24Vsegs;S3cVW;Vst;RcRbRaA5M4S2bVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;S16S41Vsegs;RdS24Vsegs;G4S39VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC8 HC7p rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c8bc; 0x3ca04] GW [C7 W st tmax] [E7c1 W st tmax; E7c2 W st tmax; E7p W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7a F7an)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8a))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c1' (C8 W st tmax) s8a rhoX tp w ENT8a SID8a); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c1', upd. lazy zeta.
      apply (class_restate_gen (E7c1 W st tmax) _ (creg7a W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7a TAB7a W7a D7a NX7a); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7a F7a).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7b F7bn)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8b))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c2' (C8 W st tmax) s8b rhoX tp w ENT8b SID8b); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c2', upd. lazy zeta.
      apply (class_restate_gen (E7c2 W st tmax) _ (creg7b W st tmax) 24 62%nat A Kc rho tp w rhoX OV7b TAB7b W7b D7b NX7b); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7b F7b).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 <> 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ false Hw G7p F7p)|]. intros Hm8.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7p Hm8 rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G7p Hcnt) as PV. cbn zeta in PV.
      destruct w as [tr [ms md]].
      unfold C7p, upd. lazy zeta. eapply SPA_restate; [exact W7p | exact D7p | exact NX7p | | | exact Hw].
      * unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_a0e7 rhoX _ _ _ _ _ _ PV).
      * apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. fold LPe. rewrite (pv_lp1 rhoX _ _ _ _ _ _ PV Hm8). rewrite u64_lit by lia. lia.
  - left. reflexivity.
Qed.
End B11S.

Section B12S.
Hypothesis Cert7p : ltac2:(tb__ "0|1|
S0S7S65S66Ufa0SaS22Z3ca04S8S22A1A3S3fSaS4S2bVW;Vst;Vtmax;A3S8S4A1M0A3SaS4S2cVW;Vst;Vtmax;A3SaS4S2dVW;Vst;Vtmax;A3G0A3A3A6S9A3").
Definition E7q1' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S2cVW;Vst;Vtmax;A3Z3ca04SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Definition E7q2' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S2dVW;Vst;Vtmax;A3Z3ca04SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Hypothesis OV7c : ltac2:(tb__ "0|0|
S0S7S5dP9dS36VW;Vst;Vtmax;A3A2S9A3").
Hypothesis OV7d : ltac2:(tb__ "0|0|
S0S7S5dP9dS37VW;Vst;Vtmax;A3A2S9A3").
Hypothesis TAB7c : ltac2:(tb__ "0|0|
S0S7S5eP9dS36VW;Vst;Vtmax;A3S5cZ208S63S64S4eS4fS50S4eS51A1A1A1A1A1A1A5S9A3").
Hypothesis TAB7d : ltac2:(tb__ "0|0|
S0S7S5eP9dS37VW;Vst;Vtmax;A3S5cZ18U3eA5S9A3").
Hypothesis W7c : ltac2:(tb__ "0|0|
S0S7S1bS3S61A1A1S9A3").
Hypothesis W7d : ltac2:(tb__ "0|0|
S0S7S1bS3S62A1A1S9A3").
Hypothesis D7c : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S2cVW;Vst;Vtmax;A3A1S3S61A1A2SfG3ScG1G2SaG0ScS13S13S36VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis D7d : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S2dVW;Vst;Vtmax;A3A1S3S62A1A2SfG3ScG1G2SaG0ScS13S13S37VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis NX7c : ltac2:(tb__ "0|0|
S0S23S17S3S61A1A1S17S3S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7d : ltac2:(tb__ "0|0|
S0S23S17S3S62A1A1S17S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7c : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7d : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7c : ltac2:(tb__ "0|0|
S3dS12S18S57S19Z200A1S14S2fA1A3S15S3S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7d : ltac2:(tb__ "0|0|
S3dS12S1cS18S57S19Z200A1S14S2fA1A3A1S15S3S2dVW;Vst;Vtmax;A3A1A1A3").
Variables s8c s8d : wsub.
Hypothesis ENT8c : ltac2:(tb__ "0|0|
S0S7S5S61S33VW;Vst;Vtmax;A3Vs8c;A3S9A3").
Hypothesis ENT8d : ltac2:(tb__ "0|0|
S0S7S5S62S33VW;Vst;Vtmax;A3Vs8d;A3S9A3").
Hypothesis SID8c : ltac2:(tb__ "0|0|
S0S7S5bVs8c;S3fA2S9A3").
Hypothesis SID8d : ltac2:(tb__ "0|0|
S0S7S5bVs8d;S3fA2S9A3").

Theorem spine_s7p : ltac2:(tb__ "0|0|
S42OF_;S56S53S16SbS4cQ40A1A1S43S67VW;Vst;A2S54R5A1S26Vsegs;R8S25R6A1A3S16S41Vsegs;RaS24Vsegs;S3cVW;Vst;R9R8R7A5S33VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S16S41Vsegs;RbS24Vsegs;S3cVW;Vst;RaR9R8A5S2bVW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC8 rhoE.
  apply (cfg_soundA segs 4000%nat [0x3ca04] GW [C7p W st tmax] [E7q1 W st tmax; E7q2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7p.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8c))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q1' (C8p W st tmax) s8c rhoX tp w ENT8c SID8c); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q1', upd. lazy zeta.
      apply (class_restate_gen (E7q1 W st tmax) _ (creg7c W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7c TAB7c W7c D7c NX7c); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7c F7c).
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8d))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q2' (C8p W st tmax) s8d rhoX tp w ENT8d SID8d); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q2', upd. lazy zeta.
      apply (class_restate_gen (E7q2 W st tmax) _ (creg7d W st tmax) 24 62%nat A Kc rho tp w rhoX OV7d TAB7d W7d D7d NX7d); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7d F7d).
  - left. reflexivity.
Qed.
End B12S.

Section B13C.

Variables (CC8 CC9 EE8n : axst).
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S7S65S66Ufa0SaS22Zdb004SaS22Z3ca54S8S22A1A3A3S3fSaS4VCC8;S8S4A1M0A3SaS4VEE8n;G0A3A6S9A3").
Variable s9e : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S7S5VEE8n;VCC9;Vs9e;A3S9A3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0S7S5bVs9e;S3fA2S9A3").

Theorem spine_s8c : ltac2:(tb__ "0|2|
S42OF_;S56S53S16SbS4cQ40A1A1M0S43S67VW;Vst;A2S54R5A1S26Vsegs;R8S25R6A1A3S16G0S41Vsegs;RbS24Vsegs;S3cVW;Vst;RaR9R8A5M1VCC9;R2R1A5R6A4FtpX;FrhoX;S16S41Vsegs;RbS24Vsegs;G1VCC8;R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC9 rhoE.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [0xdb004; 0x3ca54] GW [CC8] [EE8n] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - exact HST.
  - exact Cert8.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC9 (rho_sub rhoX s9e) tp)].
    exact (SPA_entails0 segs (JGb W st A Kc rho) GW EE8n CC9 s9e rhoX tp w ENT9 SID9 HST Hw).
  - left. reflexivity.
Qed.
End B13C.
End S8.
End SpineCallocS8.

(* [comment removed for export] *)
Module InvQC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_geom"; "ageom"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "pair"; "Some"; "option"; "prod"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "add"; "le"; "div"; "lt"; "modulo"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "live_block_reprC"; "K0C"; "rest_invQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "mkACell"; "maskv"; "view"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "live_block_repr"; "AInvA"; "QG"; "alloc_magic_ok"; "bandtp_inv"; "depot_wf"; "fs_inv"; "geom_ok"; "ia_inv"; "inv3"; "live_sep"; "misc_inv"; "model_inv"; "primary_repr"; "secondary_repr"; "shadow_unpoisoned"; "thread_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "K0"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "kQuarantineMin"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QNPRE"; "q_pure"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition live_block_reprC (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|7|
S0S0S1dS10S0S0A2SdS0S0R2R1A4S6VA;A1A3S2SfS9Q8M0A1M1A1M2Vm;S11R3Z10M3A2A1SeG1SaG0Z2M4A2A2M5A3S1S2G2Vm;S11R4G3A2A1G5A3S1S23Vm;S24S11R4ZcA2U4S16R3S17G4Z20A2M6A2A3A2S1S23Vm;S24S11R4ZeA2U2S14R3G6A2A3A2S1S3dVm;R4R3A3S1S31Vm;R4R3A3S3G1G1S1S2G2Vm;S11R5ZfA2A1SeG1R1A2A3S2S0S16SbG0R1A2Z4A2Z1A3A2Lt;A2A2A2A2A2A2F_;F_;Fn;Fb;").

Definition rest_invQC (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S1S38VA;A1S1S1fVm;VA;A2S1S3bVm;VA;A2S1S3cVm;VA;A2S1S1S47VA;A1S23Vm;S24S12S30Z48A2U8S44A3A2A2S1S33Vm;VA;A2S1S36Vm;VA;A2S1S3eVm;S7VA;A1A2S39Vm;A1A2A2A2A2A2A2A2A2").

Definition AInvQC (A : AA) (rho : valuation) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|1|
S26S1cS1bVrho;A1A2S22S7VA;A1S8S1S35R1A1S1S28R2R1A2S1S34S27S2dR1A1M0R2A2VA;A2S1S21S25G0R2A2VA;A2S1S3aS1cVA;Vtp;Vmd;A4S1S37VA;A1S32R2Vtp;A2A2A2A2A2A2A2TG;Tm;").

Lemma live_block_repr_C : ltac2:(tb__ "0|0|
S22S5S2eR2R1A2S1fR3R2A2F_;FA;Fm;").
Proof. intros m A H b n Hin _. exact (H b n Hin). Qed.
Lemma live_block_reprC_back : ltac2:(tb__ "0|3|
S0SfS9Q8M0A1M1A1M2Fx;S5S0S0S1dS10S0S0A2SdS0S0R2R1A4S6R3A1A3S2G2R5S11R3Z10A2A1SeG1SaG0Z2A2A2A3F_;Fn;Fb;S1fR3R2A2S2eR4R3A2F_;F_;FA;Fm;").
Proof. intros m A H2 H b n Hin. exact (H b n Hin (H2 b n Hin)). Qed.

Theorem AInvQ_C : ltac2:(tb__ "0|0|
S5S1aScS9Q40A1A1S18S3fR4R3R2R1A4S1eR5R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQC. cbn zeta.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  destruct HRest as (R1 & R2 & R3). split; [exact R1|]. split; [exact (live_block_repr_C _ A R2) | exact R3].
Qed.
Theorem AInvA_QC : ltac2:(tb__ "0|0|
S5S1aScS9Q40A1A1S18S2fS1cR4R3R2R1A5S1eR5R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md H. exact (AInvQ_C A rho tp md (AInvA_Q A rho tp md H)). Qed.
Theorem AInvQC_back : ltac2:(tb__ "0|2|
S5S1aScS9Q40A1A1S18S0S0S1dS10S0S0A2SdS0S0R2R1A4S6R6A1A3S2SfS9Q8M0A1M1A1S25S2dS7R7A1A1S26S1cS1bR6A1A2S11R3Z10A2A3SeG1SaG0Z2A2A2A3F_;Fn;Fb;S1eR5R4R3R2A4S3fR6R5R4R3A4F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md H2 (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  destruct HRest as (R1 & R2 & R3). split; [exact R1|]. split; [exact (live_block_reprC_back _ A H2 R2) | exact R3].
Qed.

Lemma live_block_reprC_agree : ltac2:(tb__ "0|4|
S22S22S5S5S2ScS10S0S0A2M0A1S6R1A1S6R2A1A3S0S0S0S1dG0SdS0S0R3R2A4S6R6A1M1A3S4S1S13S11R4S45R3A1A2R2A2S15R2S12R4R3A2A2A2S1S13S43R4A1M2R2A2S15R2S12G2S14S12R3Z7A2Z8A2A2A2A2A2S2SfS9Q8A1A1R9R3A1RaR3A1A3F_;F_;Fz;Fn;Fb;S0S0S1dG0SdS0S0R2R1A4G1A3S13Z1R2A2F_;Fn;Fb;S1fR7R5A2M3G3F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EL AG HN HL b n Hin H2'. rewrite EL in Hin.
  pose proof (HN b n Hin) as Hn1. pose proof (rz_bound n) as RZ.
  assert (AGb : forall z, b - rz n <= z < b + n -> m' z = m z) by (intros z Hz; apply (AG b n z Hin); left; exact Hz).
  assert (H2 : m (b - 16) = Some (Z_to_bv 8 2)) by (rewrite <- AGb by lia; exact H2').

  set (A1 := mkAA (aa_geom A) (aa_cls A) (aa_cache_inited A) (aa_sec A) (aa_ptr_committed A) [(b, n)]
                  (aa_q_thread A) (aa_q_global A) (aa_depot A) (aa_fs_hint A) (aa_fs_busy A) (aa_internal_inited A) (aa_V A) (aa_Km A) (aa_Kf A)).
  assert (L1 : live_block_repr m A1).
  { intros b0 n0 [E|[]]. injection E as <- <-. exact (HL b n Hin H2). }
  assert (L1' : live_block_repr m' A1).
  { apply (live_block_repr_agree m m' A1 A1 eq_refl); [| |exact L1].
    - intros b0 n0 z [E|[]] Hz. injection E as <- <-. exact (AG b n z Hin Hz).
    - intros b0 n0 [E|[]]. injection E as <- <-. exact Hn1. }
  exact (L1' b n (or_introl eq_refl)).
Qed.

Definition K0C (Kc : KcA) (A : AA) : jpredA := ltac2:(tb__ "0|0|
S1aScS9Q40A1A1ScS19A1S18S1S1eVA;R4R3R1A4S1VKc;R2R1A2S1S2cVA;R4A2S1S2bVA;R4A2S41VA;R4A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Lemma K0_C : ltac2:(tb__ "0|0|
S29S5S1aScS9Q40A1A1ScS19A1S18S40R6R5R4R3R2R1A6S20R7R6R5R4R3R2A6F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof. intros Kc A rho tp tr md (HA & HR). exact (conj (AInvQ_C A rho tp md HA) HR). Qed.

Theorem K0C_stable : ltac2:(tb__ "0|0|
S29S5S2aR2A1S42S1cS46S20R3R2A2A3F_;FA;FKc;").
Proof.
  intros Kc A HKc rho rho' tp tr md md' Hag Hme (HA & HK & Htp & Htop & HRG). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [|split; [|split; [|split]]].
  - destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQC. cbn zeta. rewrite Erm.
    split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [exact (model_inv_mat A tp md md' HM Hme) | exact (conj HI3 HB)].
  - destruct Hme as ((mat' & ->) & _). rewrite <- (with_vm_backing_id md) in HK. exact (Kc_ok_mat Kc tr md _ _ _ _ HKc HK).
  - unfold tp_ok in *. rewrite <- (Hw 24%positive) by (unfold QNPRE; lia). exact Htp.
  - unfold top_high in *. rewrite <- (Hw 10%positive), <- (Hw V_DEPTH) by (unfold QNPRE, V_DEPTH; lia). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite <- (Hw 151%positive), <- (Hw 152%positive), <- (Hw 155%positive), <- (Hw 156%positive) by (unfold QNPRE; lia).
    exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
End InvQC.

(* [comment removed for export] *)
Module InvQ7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "topG"; "AA"; "ag_thread"; "cs_allocated_user"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "q_mem"; "QRD"; "cls_of"; "q_pure"; "@Corelib.Init.Datatypes"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "QG"; "q_foot"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3"; "QT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ5.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma q_mem_frame : ltac2:(tb__ "0|4|
S6SbSbSfR3A1S0S12R5R1A2SaS10S13Q8A1A1M0R4R2A1R5R2A1M1A3F_;Fz;S0S9S1S3S7S4R6A1A1M2Z50A2R1A2S2R1S3G2Z70A2A2A2SaG0G1R6R2A1M3A3F_;Fz;S0S9S1S3S11Z98A2R1A2S2R1S3S11Zc0A2A2A2SaG0G3R7R2A1A3F_;Fz;ScR6R7A2ScR6R8A2F_;F_;F_;F_;F_;Fm';Fm;FA;").
Proof.
  intros A m m' [QP _] AGF AGT AGQ (QB & QL1 & QL2 & QH1 & QH2 & QMX). unfold q_mem.
  assert (EXT : forall b z, In b (qall A) -> qb_addr b <= z < qb_addr b + kQuarantineBatchSize -> m' z = m z).
  { intros b z Hb Hz. apply AGF. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact Hb | left; exact Hz]. }
  split.
  { apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) QP b Hb) as BP. pose proof (proj1 (Forall_forall _ _) QB b Hb) as BM.
    apply (batch_mem_frame A m m' b BP); [|exact BM]. intros z Hz. apply AGF. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact Hb|].
    destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right].
    apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it. split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz. }
  split; [apply (qlinks_agree m m'); [|exact QL1]; intros b z Hb Hz; apply (EXT b z); [unfold qall; apply in_or_app; left; exact Hb | unfold kQuarantineBatchSize; lia]|].
  split; [apply (qlinks_agree m m'); [|exact QL2]; intros b z Hb Hz; apply (EXT b z); [unfold qall; apply in_or_app; right; exact Hb | unfold kQuarantineBatchSize; lia]|].
  split; [apply (qhdr_repr_agree m m'); [|exact QH1]; intros z Hz; apply AGT; lia|].
  split; [apply (qhdr_repr_agree m m'); [|exact QH2]; intros z Hz; apply AGQ; lia|].
  eapply cell_ok_agree; [|exact QMX]. cbn [c_addr c_w]. intros k Hk. apply AGQ. lia.
Qed.

Section Top.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HI3 : inv3 A.
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S0S9S1Z1R1A2S1R1Z1eA2A2S9S1Z0S8SeVA;R2A2A1M0A2S1G0S14A2A2F_;Fc;").
Variable mq : bview.
Hypothesis HSR : secondary_repr mq A.
Local Abbreviation Gq := (aa_geom A).

Lemma QT_lt_top : ltac2:(tb__ "0|0|
S0S15VA;R1A2S2R2S5S4VA;A1A1A2F_;Fz;").
Proof.
  intros z HQ. pose proof HI3 as (H3 & _). pose proof (QT_num A HG H3 HQP HAU z HQ) as W.
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG). unfold QG in W.
  destruct W as [W|[[_ W]|[W|[W|W]]]]; clear -W T2 S2 TG; lia.
Qed.

Lemma q_foot_lt_top : ltac2:(tb__ "0|0|
S0S12VA;R1A2S2R2S5S4VA;A1A1A2F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _ & SEC3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  unfold q_foot in Hz. fold (qall A) in Hz. apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A z -> z < topG Gq) by (intros QZ; exact (QT_lt_top z (or_introl (or_introl QZ)))).
  destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + destruct HQP as [QP _]. pose proof (proj1 (Forall_forall _ _) QP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz]; [clear -Hz RZ Eu Esz D8 R8 IP2 D12; lia|].
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (fst it + snd it + 8) ltac:(clear -Eu Esz D8 R8 IP2 D12 TG D10; destruct D10 as (E1 & _); lia)) as SL. unfold HIGH_SHADOW_END in SL.
      assert (M : Sh (fst it) + (snd it + 7) / 8 <= Sh (fst it + snd it + 8)).
      { unfold Sh. pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
        pose proof (Z.div_le_mono (fst it + (snd it + 7) / 8 * 8) (fst it + snd it + 8) 8 ltac:(lia) ltac:(lia)) as X. rewrite Z.div_add in X by lia. lia. }
      clear -Hz SL M TG. lia.
Qed.

Lemma QRD_lt_top : ltac2:(tb__ "0|0|
S0SdVA;R1A2S2R2S5S4VA;A1A1A2F_;Fz;").
Proof.
  intros z HQ. pose proof HI3 as (H3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  pose proof (geom_old _ HG) as (_ & _ & _ & _ & _ & _ & _ & C1 & C2 & _).
  destruct HQ as [[HQ|[HQ|[(c & Hc & HQ)|HS]]]|[HQ|HQ]].
  - exact (QT_lt_top z (or_introl HQ)).
  - clear -HQ T2. lia.
  - unfold region_info, free_array, region_beg, kRegionInfoStride, kFreeArraySize in HQ. rewrite kSpaceSize_val, kUserSpaceSize_val in HQ. unfold kRegionSize in HQ.
    destruct HQ as [HQ|[HQ|HQ]]; [clear -HQ Hc S2; lia | clear -HQ Hc S2; lia |].
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (ag_spacebeg Gq + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + 2 ^ 29) ltac:(clear -Hc S1 S2 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL. clear -HQ SL TG. lia.
  -
    destruct HSR as (HS1 & _ & _ & _ & (_ & PD) & _). destruct PD as (_ & _ & PD3 & _).
    destruct HS as [HS|[HS|[HS|HS]]].
    + unfold SEC_INST in HS. clear -HS TG. lia.
    + clear -HS PD3. lia.
    + apply Exists_exists in HS as (ch & Hch & HS). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in *. clear -HS D8 D9 D12. lia.
    + apply Exists_exists in HS as (ch & Hch & _ & HS). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      destruct HS as [HS|HS]; [clear -HS D12; lia|].
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (sc_map_beg ch + sc_map_size ch) ltac:(destruct D10 as (E1 & E2 & _); clear -E1 E2 D12 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL.
      clear -HS SL TG. lia.
  - unfold qrtc_zone, QG in HQ. clear -HQ C2 TG. lia.
  - unfold qrtc2_zone in HQ. clear -HQ TG. lia.
Qed.

Lemma q_mem_frame_top : ltac2:(tb__ "0|1|
SbSbS0S2R1S5S4VA;A1A1A2SaS10S13Q8A1A1R3R2A1R4R2A1A3F_;Fz;ScR3VA;A2M0G0F_;F_;Fm';Fm;").
Proof.
  intros m m' AV HQM. pose proof HI3 as (H3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  apply (q_mem_frame A m m' HQP); [| | | exact HQM].
  - intros z Hz. apply AV. exact (q_foot_lt_top z Hz).
  - intros z Hz. apply AV. clear -Hz T2. lia.
  - intros z Hz. apply AV. unfold QG in Hz. clear -Hz TG. lia.
Qed.
End Top.
End InvQ7.

