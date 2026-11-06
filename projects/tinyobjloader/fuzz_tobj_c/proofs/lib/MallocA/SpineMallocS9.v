(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "cell"; "valuation"; "SVar"; "sprop"; "rw"; "SAlu"; "mkCell"; "DUnknown"; "ss_facts"; "ss_objs"; "mkObj"; "rm"; "ss_next"; "SPUle"; "eval"; "c_width"; "ob_dflt"; "sstate"; "c_off"; "dflt_writable"; "enc_bytes"; "ob_cells"; "odefault"; "smatch"; "soff"; "swf"; "DZero"; "c_val"; "covered"; "holds"; "mkSS"; "ob_base"; "obj_hi_of"; "obj_lo_of"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sv_eqb"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "False"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "list"; "cons"; "nil"; "nat"; "true"; "prod"; "pair"; "app"; "Some"; "option"; "length"; "None"; "andb"; "fst"; "snd"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "mulop"; "ALU_AND"; "ALU_OR"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "land"; "add"; "pow"; "lor"; "lt"; "to_nat"; "eqb"; "leb"; "ltb"; "of_nat"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_wrap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "xr_below"; "ax_X"; "ax_base"; "cell_eqb"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "prim_room"; "ag_spacebeg"; "ag_ctx"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "AE_A"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "client_addrA"; "client_shadowA"; "ustop"; "L_malloc_ok"; "JL_malloc_ok"; "Posts_malloc"; "V_RES"; "base_sv"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "J_alloc_preT"; "O_got"; "O_rtc"; "V_DEPTH"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_RZ"; "ube"; "F_gen"; "ab_e"; "BP"; "LPe"; "O_L"; "O_R"; "O_T"; "O_UB"; "O_Uz"; "O_pck"; "O_pcs"; "V_CNT"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "N_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9"; "idxs9"; "S2_of"; "R9"; "X9_of"; "hc_cptr"; "hc_magic"; "hc_type"; "pcell"; "tya_okb"; "tyv"; "KEPT9"; "O_Hf"; "O_Pf"; "O_pccf"; "O_stf"; "hc_size"; "hc_sizehi"; "hc_state"; "sw9"; "ty_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9.S9"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of";
"cells_in_view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub"; "wsub_get"; "wsub_id_below"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "in_rangesZ"; "mkACell"; "view"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "kAllocBegMagic"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv ReprGlue Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition sw9 (swc : list cell) : sobj := ltac2:(tb__ "0|0|
SdS5PaA1S5S82A1S2Z0A1Vswc;SaA5").
Definition O_pccf : sobj := ltac2:(tb__ "0|2|
SdS92S2Z0A1M0S2Z4M1A1S38S3S9G0G1S8S47S5S91A1S2N1A1A3A3S39S3A1A3SaA5").
Definition O_stf (scells : list cell) : sobj := ltac2:(tb__ "0|0|
SdSd1S2Zad0A1S2Zc60A1Vscells;SaA5").
Definition O_Hf (hcells : list cell) : sobj := ltac2:(tb__ "0|0|
SdS87S2Z0A1S5S84A1Vhcells;SaA5").
Definition O_Pf (pcells : list cell) : sobj := ltac2:(tb__ "0|0|
SdS88S2Z0A1S89Vpcells;SaA5").
Definition pcell : cell := ltac2:(tb__ "0|0|
S9S2Z0A1Z1S8S49S5PcA1S2Z7A1A3A3").
Definition hc_state : cell := ltac2:(tb__ "0|0|
S9S8S47S5S84A1S2N10A1A3Z1S2Z2A1A3").
Definition hc_size : cell := ltac2:(tb__ "0|0|
S9S8S47S5S84A1S2NcA1A3Z4S5PcA1A3").
Definition hc_sizehi : cell := ltac2:(tb__ "0|0|
S9S8S47S5S84A1S2NeA1A3Z2S2Z0A1A3").

Definition hc_magic : cell := ltac2:(tb__ "0|0|
S9S2Z0A1Z8S2SddA1A3").
Definition hc_cptr : cell := ltac2:(tb__ "0|1|
S9S2Z8M0A1G0S8S47S8S47S87S5S84A1A3S2N10A1A3A3").
Definition KEPT9 (W : list ulink) (swc : list cell) : list sobj := ltac2:(tb__ "0|0|
S3eS1S38S1SbbVswc;A1S83VW;A1A3S38S1S8dS38S1S80S38S1S81S39S1A1A3A3A3A3").
Definition R9 (scells hcells pcells : list cell) : list sobj := ltac2:(tb__ "0|0|
S3eS1SdaS38S1Sb6S38S1S90S38S1S8fS38S1Sb7Vscells;A1S38S1Sb4Vhcells;A1S38S1S8cS38S1S8aS38S1S8eS38S1Sb5Vpcells;A1S38S1S8bS39S1A1A3A3A3A3A3A3A3A3A3A3A3").

Definition S2_of (F : axst) (K : list sobj) : sstate := ltac2:(tb__ "0|1|
S60VF;A1S14S21S29R1A1S94S2aR1A1S38S3cS3aS0A2M0S3dS3aS0U4S5P18A1A4S39G0A1A3A2S27R1A1S26R1A1S2bR1A1VK;SbR1A1SfR1A1S28R1A1A9TS;").
Definition X9_of (F : axst) (K : list sobj) : axst := ltac2:(tb__ "0|1|
S66SaaVF;VK;A2S38S3cS0S0A2M0S3dS0S0S85S5PcA1A4S39G0A1A3S7bA3").

Definition idxs9 (nW : nat) : list nat := ltac2:(tb__ "0|1|
S3eS3aS38S3aU0Sa4U1M0VnW;A2A3S3eS3aS38S3aSa3VnW;U26A2S38S3aSa3VnW;G0A2S38S3aSa3VnW;U2A2S39S3aA1A3A3A3S3eS3aSa4Sa3VnW;U3A2U23A2Sa4Sa3VnW;U27A2U5A2A3A3A3").

Section Absorb.
Let segs : list Segment := segsA.
Lemma absorb_obj : ltac2:(tb__ "0|e|
S4S14S37Sa8A1M0Sc4Sa7S37S1A1M1G1S1S1aVsegs;R8R7S3dG0Sc5R6Sc6R5R4A2A4A4S2dG1ScR8A1S3eS1R4R3A3A3S57S1R3R4A3S5bQ40M2S11RbS22R4A1A2A2S33S24RcR5A2S33S23RdR6A2S33ScaReR8RbA3S4S2eS2eS4bZ0M3S4eR4R3A2A2S2eS4bS4eR4R2A2S4fZ2Z40A2A2S4bR3R2A2A2A2S2eS3S57S3R1S18R9A1A3S2eS4bR5S1bR11S15R2A1A2M4A2S2eS4bS4eG4S12R2A1A2R4A2S3aSd9R1S52S12R3A1A1A2S2dS40S5cQ8M5A1M6A1M7Sc0Vsegs;SeR5A1M8S5dG2S4eS4eR8S1bR13S15R4A1A2A2S56R2A1A2A2A3S3fG6Sa6G6R2S17S52S12R4A1A1S11R13S1eR4A1A2A2S5dG5G3A2M9A4A2A3F_;Fj;A2A2F_;Fc;S2eS2fS2dS19S13R8A1MaSaA3S2dS19GaS1dA3MbA2S33S2eS4bR5R1A2S51R1R4A2A2McS32G6G6S2dG7Sc0Vsegs;G8S5dG2S4eR8R3A2A2A3MdS3fG6R1A2A3Lx;A2F_;Foff;F_;GbS33GcS30S1fR12S18RbA1R2A3A1S2dG7GdS3fG6G9A2A3F_;F_;Foff;F_;A2A2A2Trho';Thi;Tlo;Tb;F_;F_;F_;Fo;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using.
  intros rho S tr ms md objs R o Hsm Ho Hin b lo hi rho'.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  pose proof (proj1 (Forall_forall _ _) HallR _ Hin) as Hoh.
  unfold obj_holds in Hoh. fold b lo hi in Hoh. cbn zeta in Hoh.
  destruct Hoh as (Hbnd & Hwv & Hcl & Hdf & _).
  assert (RNG : forall off, lo <= off < hi -> in_ranges rho R (Z_to_bv 64 (b + off))).
  { intros off Hoff. exists o. split; [exact Hin|]. unfold obj_range. fold b lo hi. cbn [fst snd]. rewrite u64_of_sum by lia. lia. }
  assert (CB : forall c, In c (ob_cells o) -> lo <= soff rho (c_off c) /\ soff rho (c_off c) + c_width c <= hi
            /\ forall j, (j < Z.to_nat (c_width c))%nat ->
                 rd ms (Z_to_bv 64 (b + soff rho (c_off c) + Z.of_nat j)) = Some (nth j (enc_bytes (Z.to_nat (c_width c)) (eval rho (SymState.c_val c))) (Z_to_bv 8 0))).
  { intros c Hcin. pose proof (proj1 (Forall_forall _ _) Hcl _ Hcin) as Hch. unfold cell_holds in Hch.
    destruct Hch as (Hc1 & Hc2 & Hrb). split; [exact Hc1|]. split; [exact Hc2|]. intros j Hj.
    pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) (oaddr rho (ob_base o) (soff rho (c_off c))) _ j Hrb Hj) as X.
    rewrite oaddr_unsigned in X by lia. fold b in X. apply X. lia. }
  split; [lia|]. split.
  - intros c Hcin. destruct (CB c Hcin) as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. intros j Hj.
    unfold rho'. rewrite (rd_of_absorb_in segs rho R ms _ Hrom) by (replace (b + soff rho (c_off c) + Z.of_nat j) with (b + (soff rho (c_off c) + Z.of_nat j)) by lia; apply RNG; lia).
    exact (C3 j Hj).
  - split.
    + intros Hd off Hoff. unfold rho'. rewrite (rd_of_absorb_in segs rho R ms _ Hrom (RNG off Hoff)).
      destruct (covered_dec rho (ob_cells o) off) as [Hcov|Hncov].
      * unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hcin & Hic). unfold in_cell in Hic.
        destruct (CB c Hcin) as (C1 & C2 & C3).
        specialize (C3 (Z.to_nat (off - soff rho (c_off c))) ltac:(lia)).
        replace (b + soff rho (c_off c) + Z.of_nat (Z.to_nat (off - soff rho (c_off c)))) with (b + off) in C3 by lia.
        eexists. exact C3.
      * specialize (Hdf off Hoff Hncov). unfold dflt_holds in Hdf. destruct Hd as [Hd|Hd]; rewrite Hd in Hdf; [exact Hdf | eexists; exact Hdf].
    + intros Hd off Hoff Hncov. unfold rho'. rewrite (rd_of_absorb_in segs rho R ms _ Hrom (RNG off Hoff)).
      specialize (Hdf off Hoff Hncov). unfold dflt_holds in Hdf. rewrite Hd in Hdf. exact Hdf.
Qed.

Lemma absorb_defined : ltac2:(tb__ "0|4|
S4S14S37Sa8A1M0Sc4Sa7S37S1A1M1G1S5cQ40M2A1S1aVsegs;R8R7S3dG0Sc5R6Sc6R5R4A2A4A4S2dG1ScR8A1S3eS1R4R3A3A3Sa5S1S1S2dS36S16S13R1A1A1S3bA3Lo;R4A3SceRbR5R4A3S4bSdbS5bG2R5A2A2S30S2dS40S5cQ8A1M3A1SeScaRdR7RaA3R6A2S42G3A1A3A1F_;F_;F_;F_;F_;Fa;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using.
  intros rho S tr ms md objs R a Hsm Ho HW Hin Ha.
  rewrite (rm_absorb_in rho R ms a Hin).
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  destruct Hin as (o & Hoin & Hr'). pose proof (proj1 (Forall_forall _ _) HallR _ Hoin) as Hoh.
  pose proof (proj1 (Forall_forall _ _) HW _ Hoin) as Wo. cbn beta in Wo.
  unfold obj_holds in Hoh. cbn zeta in Hoh. destruct Hoh as (Hbnd & Hwv & _).
  unfold obj_range in Hr'. cbn [fst snd] in Hr'.
  specialize (Hwv (bv_unsigned a - bv_unsigned (eval rho (ob_base o))) ltac:(unfold obj_lo_of, obj_hi_of in *; lia) Wo).
  replace (bv_unsigned (eval rho (ob_base o)) + (bv_unsigned a - bv_unsigned (eval rho (ob_base o)))) with (bv_unsigned a) in Hwv by lia.
  rewrite Z_to_bv_bv_unsigned in Hwv. unfold wview in Hwv.
  destruct (ms_mem ms a) as [bt|] eqn:Em; [discriminate|].
  pose proof (urange a). unfold segs in Hwv. rewrite (find_segment_A_off (bv_unsigned a)) in Hwv by (unfold IMG_HI in Ha; lia). exfalso. apply Hwv. reflexivity.
Qed.
End Absorb.

Section Civ.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_die : ltac2:(tb__ "0|0|
S67S4S37S5cQ40A1A1Sa7VAInv;R4R3R2R1A4Sd3Sd6Vsegs;SeR4A1A2Sd5Z182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Lemma N_m1_civ : ltac2:(tb__ "0|5|
S67S4S37S5cQ40M0A1M1A1Sa7VAInv;R4R3R2R1A4S2dG1S7R4P97A2S5dG0S6eS68R5A1A1A2A3S2dG1S7R5P98A2S5dG0S6bS68R6A1A1A2A3S2dG1S7R6P99A2S5dG0S6dS68R7A1A1A2A3S2dG1S7R7P9aA2S5dG0S6cS68R8A1A1A2A3S2dG1S7R8P9bA2S5dG0S6aS68R9A1A1A2A3S2dG1S7R9P9cA2S5dG0S4eS6aS68RaA1A1SdcA2A2A3Sa5Sd2Sd2S3cS3cS3cS0S33A2M2S33A2M3S37S3cS3cS33S3aA2S0A2A1M4A2OLk;R1G3G4G3OLp;R2G2S33G2OLp0;R2S0S33Sc1R11Sc0Vsegs;SeR11A1A2S5bG0S11R11R2A2A2R5A4Llo;Lbase;X3cx1Lhi;Lp0;X3cx1Lcs;Lp;X3cx1Lk;S9fA3F_;F_;F_;F_;F_;F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA E151 E152 E153 E154 E155 E156.
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (topG_range (aa_geom A)) as ACV.
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G19 G20 G21.
  destruct HRest as (Hsep & _ & _ & _ & _ & _ & _ & HTH & HMI). unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG0 | lia]).
  destruct HMI as [HMIc _]. pose proof (Forall_inv (Forall_inv_tail HMIc)) as HPP.
  assert (HPP' : cell_ok (view segs (rm rho)) (mkACell (0 + 0xeec4d) 1 1)).
  { intros j Hj. specialize (HPP j Hj). cbn [c_addr c_w c_val] in HPP, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HPP; [exact HPP | apply fs_footb_img; [exact HG0 | lia]]. }
  pose proof (law_die A rho tp _ HA) as HDIE.
  assert (HDIE' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x182f1c) 4 0)) by (rewrite Z.add_0_l; exact HDIE).
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HMIc))) as HCSD.
  assert (HCSD' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x183018) 4 0)).
  { intros j Hj. specialize (HCSD j Hj). cbn [c_addr c_w c_val] in HCSD, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HCSD; [exact HCSD | apply fs_footb_img; [exact HG0 | lia]]. }
  unfold N_m1, N_rest, N_fn, N_m5. cbn [tl app]. unfold vT, vCTX, vTOP, vBOT, vSB, vRIS.
  repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E153, ?E154, ?E155, ?E156, ?u64_lit by lia.

  all: first [ exact (civ_cell rho (rm rho) 0 0xeec4d 1 1 (SLit 1) HPP' eq_refl ltac:(lia) ltac:(lia))
             | exact (civ_cell rho (rm rho) 0 0x182f1c 4 0 (SLit 0) HDIE' eq_refl ltac:(lia) ltac:(lia))
             | exact (civ_cell rho (rm rho) 0 0x183018 4 0 (SLit 0) HCSD' eq_refl ltac:(lia) ltac:(lia))
             | (intros j Hj; replace j with 0%nat by lia; rewrite nth0_enc1_zero'; cbn [Z.of_nat]; rewrite Z.add_0_r; rewrite <- view_in by lia; exact HTH)
             | civ_any2 HR ].
Qed.
End Civ.

Lemma In_of_cellb : ltac2:(tb__ "0|0|
S3S37S3A1S2dS36S5aS3S65R2A1R1A3S3bA3S57S3R3R2A3F_;Fl;Fc;").
Proof. intros c l H. apply existsb_exists in H as (c' & Hin & E). apply cell_eqb_sound in E. subst c'. exact Hin. Qed.

Lemma nth0_enc1_two' : ltac2:(tb__ "0|3|
S2dS5cQ8M0A1M1Sa6G1U0S17U1S5dQ40Z2M2A2A2S5dG0Z0A2A4S5dG0G2A2A3").
Proof. reflexivity. Qed.

Definition tyv (x : sv) (a : Z) : sv := ltac2:(tb__ "0|0|
S8S49S8S4aS8S49S8S47S8S49Vx;S2ZfffffffffffffffcA1A3S2Z1A1A3S2Z8fA1A3S2Va;A1A3S2Zf3A1A3").
Definition hc_type (x : sv) (a : Z) : cell := ltac2:(tb__ "0|0|
S9S8S47S5S84A1S2NfA1A3Z1Sb2Vx;Va;A2A3").

Definition ty_of_cell (c : cell) : option (sv * Z) := ltac2:(tb__ "0|19|
S3S40S3cS0S33A2M0A1M1Lc;Vc;S0S33S0S33G1Lc_width;R2S42G0A1M2S34S34G1Lp;R1S34G2Lp0;M3G3S0G1Lc_val;R2S33G2Lz;M4S34G2Li;M5S46S0S0S46G1Lop;R3G2G2G2G2G2G2G2G2G2S0G1La0;R2G4G5S46S0S0S46G1Lop0;R3G2G2G2G2G2G2G2G2S0G1La1;R2G4G5S46S0S0S46G1Lop1;R3G2G2G2G2G2G2G2G2G2S0G1La2;R2G4G5S46S0S0S46G1Lop2;R3S0G1La3;R2G4G5S46S0S0S46G1Lop3;R3G2G2G2G2G2G2G2G2G2S0G1Lb3;R1S33S0G1Lb2;R5S33S0G1Lb1;R9S33S0G1Lb0;RdS33S0G1Lb;R11S33S36G1L_;S2cR18S8S47S5S84A1S2NfA1A3A2S3fG0S3dS0S33R7R2A4A2G2X36x2Lz2;G5S46S0S0G2Lb4;M6La4;M7Lop4;M8G8S48G7Lop4;M9G9S36S35S0G2La4;Lw;Lsgn;S34S0S33G2Lk;Li;Ll;MaX0x8La;G5S46S0G6La;MbLop4;McGcS48GbLop4;MdGdS36S35S0G2La;Lw;Lsgn;MeGaX0x8Lz1;G5GcGcGdGdGeGaX0x8Lz0;G5GcGcGdGdGeGaX0x8Lz;G5GcGcGdGdGeGaX0x8X46xaLb3;Lx;Lop3;S46S0S0G2Lb3;La;MfLop3;S48GfLop3;M10G10GeGaX0x8G2G2G2G2G2G2G2G2G2X46xaLb2;La3;Lop2;S46S0S0G2Lb2;La;M11Lop2;S48G11Lop2;M12G12GeGaX0x8X46xaLb1;La2;Lop1;S46S0S0G2Lb1;La;M13Lop1;S48G13Lop1;M14G14GeGaX0x8G2X46xaLb0;La1;Lop0;S46S0S0G2Lb0;La;M15Lop0;S48G15Lop0;M16G16GeGaX0x8X46xaLb;La0;Lop;S46S0S0G2Lb;La;M17Lop;S48G17Lop;M18G18GeGaX0x8X34x3Lp;S34G2Lp;X33x3Lc_val;Lc_width;Loff;X3x1").
Fixpoint ty_of (l : list cell) : sv * Z :=
  match l with [] => (SLit 0, 0) | c :: r => match ty_of_cell c with Some p => p | None => ty_of r end end.
Lemma land_mod4 : ltac2:(tb__ "0|2|
S33S33S4bZ0R2A2M0G0S2dS33S4cS4dR4R3A2Z4M1A2S4dS4cR4G1A2S4cR3G1A2A2A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. change 4 with (2 ^ 2). rewrite <- !Z.land_ones by (try apply Z.land_nonneg; lia).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 2) n); reflexivity.
Qed.
Lemma lor_mod4 : ltac2:(tb__ "0|2|
S33S33S4bZ0R2A2M0G0S2dS33S4cS50R4R3A2Z4M1A2S50S4cR4G1A2S4cR3G1A2A2A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. change 4 with (2 ^ 2). rewrite <- !Z.land_ones by (try apply Z.lor_nonneg; lia).
  apply Z.bits_inj'. intros n Hn. rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 2) n); reflexivity.
Qed.
Lemma tyZ_mod4 : ltac2:(tb__ "0|3|
S33S33S4bZ0M0R2A2M1G1S2dS33S4dR3Z3A2G0A3S2dS33S4cS4dS50S4dS5eQ40S4eS4dR5ZfffffffffffffffcA2Z1M2A2A2Z8fA2R4A2Zf3A2Z4A2G2A3F_;F_;F_;Fa;Fx;").
Proof.
  intros x a Hx Ha Ha3.
  assert (L0 : 0 <= Z.land x 18446744073709551612) by (apply Z.land_nonneg; lia).
  assert (M0 : (Z.land x 18446744073709551612) mod 4 = 0).
  { rewrite land_mod4 by lia. change (18446744073709551612 mod 4) with 0. apply Z.land_0_r. }
  set (y := Z.land x 18446744073709551612) in *.
  assert (M1 : (bv_wrap 64 (y + 1)) mod 4 = 1 /\ 0 <= bv_wrap 64 (y + 1)).
  { unfold bv_wrap. change (bv_modulus 64%N) with (4 * 2 ^ 62).
    pose proof (Z.div_mod (y + 1) (4 * 2 ^ 62) ltac:(lia)) as D. pose proof (Z.mod_pos_bound (y + 1) (4 * 2 ^ 62) ltac:(lia)) as B.
    pose proof (Z.div_mod y 4 ltac:(lia)) as D4. rewrite M0 in D4.
    set (r := (y + 1) mod (4 * 2 ^ 62)) in *. set (q := (y + 1) / (4 * 2 ^ 62)) in *.
    split; [|lia]. symmetry. apply Z.mod_unique with (q := y / 4 - q * 2 ^ 62); lia. }
  destruct M1 as [M1 W].
  rewrite land_mod4 by (try apply Z.lor_nonneg; try split; try apply Z.land_nonneg; lia).
  rewrite lor_mod4 by (try apply Z.land_nonneg; lia).
  rewrite land_mod4 by lia. rewrite M1.
  change (143 mod 4) with 3. change (243 mod 4) with 3.
  replace (a mod 4) with 0.
  2: { change 4 with (2 ^ 2). rewrite <- Z.land_ones by lia. change (Z.ones 2) with 3. symmetry. exact Ha3. }
  reflexivity.
Qed.
Lemma tyv_sound : ltac2:(tb__ "0|1|
S4S0S33S2eS4bZ0M0R1A2S51R1S4fZ2Z40A2A2A2S2dS33S4dR2Z3A2G0A3S2dS33S4cS5bQ40S11R5Sb2R4R3A2A2A2Z4A2Z1A3F_;F_;Fa;Fx;Frho;").
Proof.
  intros rho x a Ha Ha3. unfold tyv. cbn [eval]. unfold alu64, alu.
  rewrite bv_and_unsigned, bv_or_unsigned, bv_and_unsigned, bv_add_unsigned, bv_and_unsigned.
  rewrite !Z_to_bv_unsigned. change (bv_wrap 64 18446744073709551612) with 18446744073709551612.
  change (bv_wrap 64 1) with 1. change (bv_wrap 64 143) with 143. change (bv_wrap 64 243) with 243.
  replace (bv_wrap 64 a) with a by (unfold bv_wrap; rewrite Z.mod_small; [reflexivity | exact Ha]).
  apply tyZ_mod4; [pose proof (bv_unsigned_in_range 64 (eval rho x)); lia | lia | exact Ha3].
Qed.
Definition tya_okb (a : Z) : bool := ltac2:(tb__ "0|1|
S43S43S54Z0M0Va;A2S55Va;S4fZ2Z40A2A2A2S53S4dVa;Z3A2G0A2A2").
Lemma tya_okb_sound : ltac2:(tb__ "0|1|
S33S2dS36Sb1R1A1S3bA3S2eS2eS4bZ0M0R2A2S51R2S4fZ2Z40A2A2A2S2dS33S4dR2Z3A2G0A3A2F_;Fa;").
Proof. intros a H. unfold tya_okb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia. Qed.
Lemma R9_writable : ltac2:(tb__ "0|1|
S37S3A1M0G0G0Sa5S1S1S2dS36S16S13R1A1A1S3bA3Lo;SabR3R2R1A3A3Fpc;Fhc;Fsc;").
Proof. intros. unfold R9, RT_m1. cbn. repeat (apply Forall_cons; [reflexivity|]). apply Forall_nil. Qed.

Section S9.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S33Sd4VCST;R1A2Sd4SdeR2A2S31F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S7fVAInv;VW;Vst;VA;VKc;S5PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S67S4S37S5cQ40A1A1Sa7VAInv;R4R3R2R1A4Sd3Sd6Vsegs;SeR4A1A2Sd5Z182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section B14.

Variable F : axst.
Variables swc scells hcells : list cell.
Variable partial : bool.
Let pcells : list cell := ltac2:(tb__ "0|1|
S36S37S3A1Lpartial;Vpartial;S38S3Sb0S39S3A1M0A3G0X36x2").
Let K : list sobj := KEPT9 W swc.
Let R : list sobj := ltac2:(tb__ "0|0|
SabVscells;Vhcells;Vpcells;A3").
Hypothesis SEL9 : ltac2:(tb__ "0|0|
S2dS37S1A1Sc9ScS60VF;A1A1Sa9VnW;A1A2S3eS1VK;VR;A3A3").
Hypothesis ND9 : ltac2:(tb__ "0|0|
S2dS36Sc8Sa9VnW;A1A1S3bA3").
Hypothesis BND9 : ltac2:(tb__ "0|0|
S2dS36S58S3aS3aSd8R1S41S1ScS60VF;A1A1A2A2Li;Sa9VnW;A1A3S3bA3").
Hypothesis COV9 : ltac2:(tb__ "0|0|
S2dS36S58S3aS3aS5aS3aSd7R1A1Sa9VnW;A1A3Li;Sa4U0S41S1ScS60VF;A1A1A2A2A3S3bA3").
Hypothesis XF : ax_X F = [].
Hypothesis BF9 : ax_base F = base_sv.
Hypothesis HCs : In hc_state hcells.
Hypothesis HCn : In hc_size hcells.
Hypothesis HC0 : In hc_sizehi hcells.
Variables (tyx : sv) (tya : Z).
Hypothesis HCt : ltac2:(tb__ "0|0|
S57S3SafVtyx;Vtya;A2Vhcells;A3").
Hypothesis HTA : tya_okb tya = true.
Hypothesis HMG : ltac2:(tb__ "0|0|
S2fS57S6S10S5S84A1S2Z10A1A2SbS60VF;A1A1A3S2eS57S3SaeVhcells;A3S57S3SadVhcells;A3A2A2").
Hypothesis FG9 : ltac2:(tb__ "0|0|
S59S6S86SbS60VF;A1A1A3").
Hypothesis FP9 : ltac2:(tb__ "0|0|
S59S6S3eS6S7eVW;Vst;A2S7dS7cA1A3SbS60VF;A1A1A3").
Hypothesis W9 : ltac2:(tb__ "0|0|
S2dS36S1cSaaVF;VK;A2A1S3bA3").
Hypothesis D9 : ltac2:(tb__ "0|4|
S2dS40S3cS37S3cS0S0A2M0A1M1S37S6A1M2A2M3A1Sc7ScfS60VF;A1VK;A2SaaVF;VK;A2A2S3fG3S3dG1G2S38G0S3dS0S0S2Sd0A1S5P18A1A4S39G0A1A3S39S6A1A4A2A3").
Hypothesis XB9 : ltac2:(tb__ "0|0|
S2dS36S62SfS60VF;A1A1S3dS0S0S85S5PcA1A4A2S3bA3").
Variable s9 : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S2dS36S61SacVF;VK;A2S77S70VW;Vst;A3Vs9;A3S3bA3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S2dS36ScdVs9;S93A2S3bA3").
Hypothesis G110 : ltac2:(tb__ "0|0|
S2dS0SccVs9;S7aA2S85A3").

Theorem malloc_finish_P : ltac2:(tb__ "0|5|
S67S67S71S4S4S33OF_;S4S37S5cQ40M0A1A1M1G1S99S37S3cS5fS9cA2M2A1S57G2S3dS5fS9cS77S70VW;Vst;A3S78VAInv;VCST;VXGL;RbR9A5A4R1A3S2dS76Vst;S73A3S2dS37S6fA1VW;S39S6fA1A3F_;S72RbA1Sa1ReRdA2Sa2RaRcRbA3S33S2fS74VCST;R11R1A3S75VCST;VXGL;R11R1A4A2RdR2A1F_;Fa;S4bZ1S9dR10S5bG0S7RdPcM3A2A2A2A2S69R11A1S36OLpartial;Vpartial;S30S2dS33S4cS5bG0S7RfG3A2A2Z8A2Z0A3M4A1G4X36x2S95Vsegs;Sa0VW;Vst;R13R12R10A5VF;ReRcRbA6S9bVsegs;S93R12ReRbRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Proof.
  intros A0 A Kc rho0 rho keep rhoE tp0 tp w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar H.
  destruct w as [tr [ms md]].
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [w_tr w_cfg cfg_model fst snd] in HA, HK, Htp, HU, HB, HN.
  pose proof (JGb_pvals nW st A Kc rho rhoE tp _ F H FG9 Hcnt) as PV. cbn zeta in PV.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  set (SB := ag_spacebeg (aa_geom A)) in *. set (c := cls_of nv) in *. set (x := chk_of A nv) in *. set (sz := Size c) in *.
  set (ab := SB + c * 2 ^ 32 + 16 * x). set (ub := ab + rz nv). set (ue := ub + nv).
  set (G := aa_geom A) in *. set (T := ag_thread G). set (pce := T + 0xd0 + 80 * c). set (cnt := cnt_of A nv) in *.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 T). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx G)). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E153 : rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top G)). { rewrite <- (Hagw 153%positive) by (unfold GW; lia). reflexivity. }
  assert (E154 : rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom G)). { rewrite <- (Hagw 154%positive) by (unfold GW; lia). reflexivity. }
  assert (E156 : rw rhoE 156%positive = Z_to_bv 64 (SB + kSpaceSize)). { rewrite <- (Hagw 156%positive) by (unfold GW; lia). reflexivity. }
  assert (E149 : rw rhoE 149%positive = Z_to_bv 64 cnt). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }
  assert (Erm : rm rhoE = rm rho). { apply functional_extensionality. intros a. symmetry. exact (Hagm a). }
  pose proof HA as (HG & HR & _). pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & _). fold G in G3, G5. fold G T in G4, G5. pose proof (topG_range G) as ACV.
  pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & C4). fold c in C1, C4.
  assert (GS2 : SB + 2 ^ 37 + 4096 <= 140737479966720).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold SB, G in *. clear -X ACV.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X14 & _). lia. }
  assert (CNT16 : cnt <= 16) by exact (proj1 (proj2 (proj2 (proj2 (proj2 (pc_entry_facts segs A rhoE tp md nv HA ltac:(lia) Hcnt)))))).

  pose proof (pv_ab rhoE _ _ _ _ _ _ PV) as Eab. pose proof (pv_ub rhoE _ _ _ _ _ _ PV) as Eub. pose proof (pv_ue rhoE _ _ _ _ _ _ PV) as Eue.
  pose proof (pv_bsh rhoE _ _ _ _ _ _ PV) as Ebsh. pose proof (pv_bu rhoE _ _ _ _ _ _ PV) as Ebu. pose proof (pv_lu rhoE _ _ _ _ _ _ PV) as Elu.
  pose proof (pv_lp rhoE _ _ _ _ _ _ PV) as Elp. pose proof (pv_lt rhoE _ _ _ _ _ _ PV) as Elt. pose proof (pv_bp rhoE _ _ _ _ _ _ PV) as Ebp.
  pose proof (pv_br rhoE _ _ _ _ _ _ PV) as Ebr. pose proof (pv_lr rhoE _ _ _ _ _ _ PV) as [Elr Blr]. pose proof (r8_facts rhoE _ _ _ _ _ _ PV) as R8F.
  cbn zeta in Eab, Eub, Eue, Ebsh, Ebu, Elu, Elp, Elt, Ebp, Ebr, Elr, Blr, R8F. fold ab in Eab, Eub, Eue, Ebsh, Ebu, Ebp, Ebr. fold ub in Eub, Eue, Ebu, Ebp, Ebr.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *. set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  assert (EB : bv_unsigned (eval rhoE pc_base) = pce).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (c * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. unfold pce. lia. }
  assert (ET : bv_unsigned (eval rhoE vT) = T). { unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia. }
  assert (ECH : soff rhoE choff = 16 + 4 * (cnt - 1)).
  { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by lia.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace ((cnt + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
    change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
    unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
  assert (ERZ : soff rhoE (SVar V_RZ) = rz nv). { apply soff_of_val; [|lia]. cbn [eval]. unfold V_RZ. rewrite E150. apply u64_lit. lia. }
  idtac "mf:1".

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (Ha : SPA segs KJ F rhoE tp (tr, {| cfg_ms := ms; cfg_model := md |})) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_select segs KJ rhoE F (idxs9 nW) tp _ Ha ND9
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BND9 i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COV9 i ltac:(apply in_seq; lia)) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsel.
  rewrite SEL9 in Hsel. clear Ha.

  pose proof (SPA_unobj segs KJ rhoE (ax_setS F (set_objs (ax_S F) (K ++ R))) K R tp tr ms md eq_refl Hsel (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE R (vms md tp ms)) in *.
  pose proof (proj1 (proj1 Hsel)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S ax_setS] in Hsm1.
  idtac "mf:2".

  destruct (proj1 (Z.mod_divide (rz nv) 16 ltac:(clear -ACV; lia)) ltac:(clear -Brz; tauto)) as [qr Hqr].
  destruct (proj1 (Z.mod_divide sz 16 ltac:(clear -ACV; lia)) ltac:(clear -Bsz; tauto)) as [qs Hqs].
  assert (AB8 : ab mod 8 = 0).
  { apply Z.mod_divide; [clear -ACV; lia|]. destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(clear -ACV; lia)) ltac:(clear -BSB; tauto)) as [q Hq].
    exists (q * 2 ^ 13 + c * 2 ^ 29 + 2 * x). unfold ab. clear -Hq. lia. }
  assert (EShub : Sh ub = Sh ab + 2 * qr).
  { unfold ub. rewrite (Sh_SB ab (rz nv) AB8). rewrite Hqr. replace (qr * 16 / 8) with (2 * qr) by (clear -ACV; apply Z.div_unique with 0; lia). reflexivity. }
  pose proof (Z.div_mod nv 8 ltac:(clear -ACV; lia)) as DMn. pose proof (Z.mod_pos_bound nv 8 ltac:(clear -ACV; lia)) as MBn.
  set (qn := nv / 8) in *.
  assert (Er8 : r8 / 8 = qn + lp /\ (sz - rz nv - r8) / 8 = 2 * qs - 2 * qr - qn - lp /\ sz / 8 = 2 * qs /\ rz nv / 8 = 2 * qr /\ 0 <= lp <= 1
               /\ nv <= 8 * qn + 8 * lp /\ 8 * qn + 8 * lp + rz nv <= sz).
  { destruct R8F as (R1 & R2 & R3 & R4). unfold lp in *.
    destruct (Z.eq_dec (nv mod 8) 0) as [Ez|Nz].
    - rewrite R4. rewrite Hqs, Hqr. repeat split.
      1-4: symmetry; apply Z.div_unique with 0; clear -ACV; lia.
      + clear -ACV; lia. + clear -ACV; lia.
      + clear -DMn Ez. lia.
      + rewrite R4, Hqs, Hqr in Blr. clear -Blr DMn Ez Bfit Hqs Hqr. lia.
    - rewrite R4. rewrite Hqs, Hqr. repeat split.
      1-4: symmetry; apply Z.div_unique with 0; clear -ACV; lia.
      + clear -ACV; lia. + clear -ACV; lia.
      + clear -DMn MBn. lia.
      + rewrite R4, Hqs, Hqr in Blr. clear -Blr DMn MBn Bfit Hqs Hqr. lia. }
  destruct Er8 as (Er8a & Er8b & Esz8 & Erz8 & Blp & Bn8 & Bfit8).
  idtac "mf:3".

  set (P10 := [O_pccf; O_pcs; O_pck; O_stf scells; O_Hf hcells; O_T; O_L; O_Uz; O_Pf pcells; O_R]).
  assert (ER : R = RT_m1 ++ P10) by reflexivity.
  assert (RG1 : obj_range rhoE O_pccf = (pce, pce + 4)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_pccf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite EB. apply f_equal2; clear; lia. }
  assert (RG2 : obj_range rhoE O_pcs = (pce + 8, pce + 16)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_pcs]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite EB. reflexivity. }
  assert (RG3 : obj_range rhoE O_pck = (pce + 16 + 4 * (cnt - 1), pce + 80)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_pck]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite EB, ECH. apply f_equal2; clear; lia. }
  assert (RG4 : obj_range rhoE (O_stf scells) = (T + 2768, T + 3168)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_stf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite ET. reflexivity. }
  assert (RG5 : obj_range rhoE (O_Hf hcells) = (ab, ub)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_Hf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Eab, ERZ. apply f_equal2; [clear; lia | unfold ub; clear; lia]. }
  assert (RG6 : obj_range rhoE O_T = (ue, ab + sz)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_T]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Eue.
    rewrite (soff_of_val rhoE LTe _ Elt) by (clear -Bfit Bsz Bn Brz; lia). fold ue. apply f_equal2; [clear; lia | unfold ue, ub; clear; lia]. }
  assert (ELL : bv_unsigned (eval rhoE LLe) = 2 * qr).
  { unfold LLe. cbn [eval]. unfold V_RZ. rewrite E150, srl_val, !u64_lit by (clear -Brz; lia). change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by (clear; lia). exact Erz8. }
  assert (RG7 : obj_range rhoE O_L = (Sh ab, Sh ab + 2 * qr)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_L]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebsh.
    rewrite (soff_of_val rhoE LLe (2 * qr) ELL) by (clear -Brz Hqr; lia). apply f_equal2; clear; lia. }
  assert (RG8 : obj_range rhoE O_Uz = (Sh ub, Sh ub + qn)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_Uz]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebu.
    rewrite (soff_of_val rhoE LUe qn Elu) by (clear -Bn DMn MBn; lia). apply f_equal2; clear; lia. }
  assert (RG9 : obj_range rhoE (O_Pf pcells) = (Sh ub + qn, Sh ub + qn + lp)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_Pf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebp.
    rewrite (soff_of_val rhoE LPe lp Elp) by (clear -Blp; lia). fold qn. apply f_equal2; clear; lia. }
  assert (RG10 : obj_range rhoE O_R = (Sh ub + qn + lp, Sh ab + 2 * qs)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_R]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebr.
    rewrite (soff_of_val rhoE LRe _ Elr) by (rewrite Er8b; clear -Blp Bfit8 Hqs Hqr Bsz Brz DMn MBn Bn; lia). rewrite Er8a, Er8b, EShub. apply f_equal2; clear; lia. }
  assert (PIN : forall o z, In o P10 -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> chg_m G pce ab ub ue sz cnt z).
  { intros o z Ho Hz. unfold chg_m. fold T. rewrite Esz8. unfold P10 in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
      first [rewrite RG1 in Hz | rewrite RG2 in Hz | rewrite RG3 in Hz | rewrite RG4 in Hz | rewrite RG5 in Hz
            | rewrite RG6 in Hz | rewrite RG7 in Hz | rewrite RG8 in Hz | rewrite RG9 in Hz | rewrite RG10 in Hz];
      cbn [fst snd] in Hz; rewrite ?EShub in Hz;
      clear -Hz Blp Bn8 Bfit8 Hqr Hqs Hcnt CNT16 DMn MBn Bn Brz Bsz Bfit; unfold ub, ue in *; lia. }
  idtac "mf:4".

  set (v3 := view segs (rm rho3)). set (vE := view segs (rm rhoE)).
  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoE _ tr (vms md tp ms) (vmd md) K R o Hsm1 eq_refl Ho)).
  assert (INP : forall o, In o P10 -> In o R) by (intros o Ho; rewrite ER; apply in_or_app; right; exact Ho).
  assert (P1 : In O_pccf P10) by (unfold P10; cbn; tauto).
  assert (P2 : In O_pcs P10) by (unfold P10; cbn; tauto).
  assert (P5 : In (O_Hf hcells) P10) by (unfold P10; cbn; tauto).
  assert (P8 : In O_Uz P10) by (unfold P10; cbn; tauto).
  assert (P9 : In (O_Pf pcells) P10) by (unfold P10; cbn; tauto).
assert (PCEB : 4096 <= pce /\ pce + 80 <= 140737479966720) by (unfold pce; clear -G4 G5 C1 ACV; lia).
  assert (ABB : 17594333495296 <= ab /\ ab + sz <= 140737479966720 /\ 16 <= rz nv /\ nv + rz nv <= sz) by (unfold ab; clear -BSB Bc Bx Btop Brz Bfit; lia).
  assert (VC : cell_ok v3 (mkACell pce 4 (cnt - 1))).
  { destruct (AO _ (INP _ P1)) as (_ & CO & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_pccf] in CO. specialize (CO _ (or_introl eq_refl)). cbn [c_off c_width SymState.c_val] in CO.
    destruct CO as (_ & _ & CO). rewrite soff_lit_small in CO by (clear; lia). rewrite EB in CO.
    assert (EV : eval rhoE (SAlu ALU_ADD (SVar V_CNT) (SLit (-1))) = Z_to_bv 64 (cnt - 1)).
    { apply bv_eq. cbn [eval]. unfold V_CNT. rewrite E149, add_val, u64_lit by (clear -Hcnt CNT16; lia).
      replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity. rewrite u64_lit by (clear -Hcnt CNT16; lia).
      rewrite <- (Z.mod_add _ (-1)) by (clear; lia). rewrite Z.mod_small; clear -Hcnt CNT16; lia. }
    rewrite EV in CO. intros k Hk. cbn [c_addr c_w RtCells.c_val]. unfold v3. rewrite view_in by (clear -PCEB Hk ACV; cbn in Hk; lia).
    replace (pce + Z.of_nat k) with (pce + 0 + Z.of_nat k) by (clear; lia). exact (CO k Hk). }
  assert (VS : cell_ok v3 (mkACell (pce + 8) 8 sz)).
  { destruct (AO _ (INP _ P2)) as (_ & CO & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_pcs] in CO. specialize (CO _ (or_introl eq_refl)). cbn [c_off c_width SymState.c_val] in CO.
    destruct CO as (_ & _ & CO). rewrite soff_lit_small in CO by (clear; lia). rewrite EB in CO. cbn [eval] in CO. unfold V_SIZE in CO. rewrite E148 in CO.
    intros k Hk. cbn [c_addr c_w RtCells.c_val]. unfold v3. rewrite view_in by (clear -PCEB Hk ACV; cbn in Hk; lia). exact (CO k Hk). }
  assert (SOFFH : forall d, -16 <= d < 0 -> soff rhoE (SAlu ALU_ADD (SVar V_RZ) (SLit d)) = rz nv + d).
  { intros d Hd. apply soff_of_val; [|clear -Hd Brz; lia]. cbn [eval]. unfold V_RZ. rewrite E150, add_val, u64_lit by (clear -Brz; lia).
    replace (bv_unsigned (Z_to_bv 64 d)) with (d + 1 * 2 ^ 64).
    2: { rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. rewrite <- (Z.mod_add d 1 (2 ^ 64)) by (clear; lia). symmetry. apply Z.mod_small. clear -Hd. lia. }
    rewrite Z.add_assoc. rewrite Z.mod_add by (clear; lia). rewrite Z.mod_small; clear -Brz Hd; lia. }
  destruct (AO _ (INP _ P5)) as (_ & COH & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_Hf] in COH.
  assert (VH2 : v3 (ub - 16) = Some (Z_to_bv 8 2)).
  { destruct (COH _ HCs) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_state] in CO. rewrite (SOFFH (-16)) in CO by (clear; lia).
    rewrite Eab in CO. specialize (CO 0%nat ltac:(clear; cbn; lia)). cbn [eval Z.of_nat Z.to_nat Pos.to_nat Pos.iter_op nth] in CO.
    unfold v3. rewrite view_in by (clear -ABB ACV Bn; unfold ub; lia). replace (ub - 16) with (ab + (rz nv + -16) + 0) by (unfold ub; clear; lia).
    etransitivity; [exact CO|]. f_equal; exact nth0_enc1_two'. }
  assert (VHN : cell_ok v3 (mkACell (ub - 12) 4 nv)).
  { destruct (COH _ HCn) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_size] in CO. rewrite (SOFFH (-12)) in CO by (clear; lia).
    rewrite Eab in CO. cbn [eval] in CO. rewrite E12 in CO.
    intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn; unfold ub; lia).
    replace (ub - 12 + Z.of_nat k) with (ab + (rz nv + -12) + Z.of_nat k) by (unfold ub; clear; lia). exact (CO k Hk). }
  assert (VH0 : cell_ok v3 (mkACell (ub - 14) 2 0)).
  { destruct (COH _ HC0) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_sizehi] in CO. rewrite (SOFFH (-14)) in CO by (clear; lia).
    rewrite Eab in CO. cbn [eval] in CO.
    intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn; unfold ub; lia).
    replace (ub - 14 + Z.of_nat k) with (ab + (rz nv + -14) + Z.of_nat k) by (unfold ub; clear; lia). exact (CO k Hk). }

  assert (VH1 : exists t, v3 (ub - 15) = Some t /\ bv_unsigned t mod 4 = 1).
  { destruct (COH _ HCt) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_type] in CO. rewrite (SOFFH (-15)) in CO by (clear; lia).
    rewrite Eab in CO. specialize (CO 0%nat ltac:(clear; cbn; lia)). cbn [Z.of_nat nth enc_bytes Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op] in CO.
    exists (Z_to_bv 8 (bv_unsigned (eval rhoE (tyv tyx tya)))). split.
    - unfold v3. rewrite view_in by (clear -ABB ACV Bn; unfold ub; lia). replace (ub - 15) with (ab + (rz nv + -15) + 0) by (unfold ub; clear; lia). exact CO.
    - destruct (tya_okb_sound tya HTA) as [TA1 TA2]. pose proof (tyv_sound rhoE tyx tya TA1 TA2) as M4.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8%N) with (4 * 64).
      set (u := bv_unsigned (eval rhoE (tyv tyx tya))) in *. pose proof (bv_unsigned_in_range 64 (eval rhoE (tyv tyx tya))) as UR. fold u in UR.
      pose proof (Z.div_mod u (4 * 64) ltac:(clear; lia)) as D1. pose proof (Z.mod_pos_bound u (4 * 64) ltac:(clear; lia)) as B1.
      pose proof (Z.div_mod u 4 ltac:(clear; lia)) as D2. rewrite M4 in D2.
      symmetry. apply Z.mod_unique with (q := u / 4 - (u / (4 * 64)) * 64); clear -D1 B1 D2 UR; lia. }
  assert (SHB : 2147450880 <= Sh ab /\ Sh ab + 2 * qs < 17594333495296).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos ab 8 ltac:(clear -ABB; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_le_mono (ab + sz) 140737479966720 8 ltac:(clear; lia) ltac:(clear -ABB; lia)) as D1.
    replace (ab + sz) with (ab + 2 * qs * 8) in D1 by (clear -Hqs; lia). rewrite Z.div_add in D1 by (clear; lia).
    change (140737479966720 / 8) with 17592184995840 in D1. clear -D0 D1. lia. }
  assert (VZ : forall g, 0 <= g < nv / 8 -> v3 (Sh ub + g) = Some (Z_to_bv 8 0)).
  { intros g Hg. destruct (AO _ (INP _ P8)) as (_ & _ & _ & ZO). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_Uz] in ZO. specialize (ZO eq_refl g).
    unfold obj_lo_of, obj_hi_of in ZO. cbn [ob_lo ob_hi ob_cells ob_base O_Uz] in ZO. rewrite soff_lit_small in ZO by (clear; lia).
    rewrite (soff_of_val rhoE LUe qn Elu) in ZO by (clear -Bn DMn MBn; lia). rewrite Ebu in ZO.
    unfold v3. rewrite view_in by (rewrite EShub; clear -SHB Hg Bfit8 Hqr Hqs Blp DMn MBn Bn Brz; unfold qn in *; lia).
    apply ZO; [clear -Hg; unfold qn; lia|]. intros HC. unfold covered in HC. apply Exists_exists in HC as (cc & Hcc & _). exact Hcc. }
  assert (VP : nv mod 8 <> 0 -> v3 (Sh ub + nv / 8) = Some (Z_to_bv 8 (nv mod 8))).
  { intros Hm. destruct partial eqn:EP; [|exfalso; exact (Hm Hpar)].
    destruct (AO _ (INP _ P9)) as (_ & CO & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_Pf] in CO. specialize (CO pcell ltac:(unfold pcells; left; reflexivity)).
    cbn [c_off c_width SymState.c_val pcell] in CO. destruct CO as (_ & _ & CO). rewrite soff_lit_small in CO by (clear; lia). rewrite Ebp in CO.
    specialize (CO 0%nat ltac:(clear; cbn; lia)). cbn [Z.of_nat] in CO. rewrite Z.add_0_r in CO.
    assert (EV : eval rhoE (SAlu ALU_AND (SVar 12) (SLit 7)) = Z_to_bv 64 (nv mod 8)).
    { apply bv_eq. cbn [eval]. rewrite E12, and_val, !u64_lit by (clear -Bn MBn; lia). apply land_7. clear -Bn; lia. }
    rewrite EV in CO. change (Z.to_nat 1) with 1%nat in CO. rewrite (nth_enc_bytes 1 0 (nv mod 8) ltac:(clear; lia) ltac:(clear; lia)) in CO.
    unfold le_byte in CO. rewrite Z.shiftr_0_r in CO. change (2 ^ (8 * Z.of_nat 1)) with 256 in CO. rewrite !Z.mod_small in CO by (clear -MBn; lia).
    unfold v3. rewrite view_in by (rewrite EShub; clear -SHB Bfit8 Hqr Hqs Blp DMn MBn Bn Brz Hm; unfold qn, lp in *; destruct (Z.eq_dec (nv mod 8) 0); lia).
    replace (Sh ub + nv / 8) with (Sh ub + nv / 8 + 0) by (clear; lia). exact CO. }
  idtac "mf:5".
  assert (PRESo : forall o z, In o P10 -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb).
  { intros o z Ho Hz. destruct (AO _ (INP _ Ho)) as (Bo & _ & Po & _). unfold obj_range in Hz. cbn [fst snd] in Hz.
    assert (DD : ob_dflt o = DUnknown \/ ob_dflt o = DZero).
    { unfold P10 in Ho. clear -Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn; tauto. }
    destruct (Po DD (z - bv_unsigned (eval rhoE (ob_base o))) ltac:(clear -Hz; lia)) as [bb Hbb]. exists bb.
    unfold v3. rewrite view_in by (clear -Hz Bo; lia).
    replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) at 1 by (clear; lia). exact Hbb. }
  assert (PRES : forall z, chg_m G pce ab ub ue sz cnt z -> exists bb, v3 z = Some bb).
  { intros z Hz. unfold chg_m in Hz. fold T in Hz. rewrite Esz8 in Hz.
    destruct Hz as [Hz|[Hz|[Hz|[Hz|[Hz|[Hz|Hz]]]]]].
    - apply (PRESo O_pccf); [exact P1 | rewrite RG1; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo O_pcs); [exact P2 | rewrite RG2; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo O_pck); [unfold P10; cbn; tauto | rewrite RG3; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo (O_stf scells)); [unfold P10; cbn; tauto | rewrite RG4; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo (O_Hf hcells)); [exact P5 | rewrite RG5; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo O_T); [unfold P10; cbn; tauto | rewrite RG6; cbn [fst snd]; clear -Hz; lia].
    - destruct (Z_lt_dec z (Sh ub)); [|destruct (Z_lt_dec z (Sh ub + qn)); [|destruct (Z_lt_dec z (Sh ub + qn + lp))]].
      + apply (PRESo O_L); [unfold P10; cbn; tauto | rewrite RG7; cbn [fst snd]; rewrite EShub in *; clear -Hz l; lia].
      + apply (PRESo O_Uz); [exact P8 | rewrite RG8; cbn [fst snd]; clear -Hz n l; lia].
      + apply (PRESo (O_Pf pcells)); [exact P9 | rewrite RG9; cbn [fst snd]; clear -Hz n0 l; lia].
      + apply (PRESo O_R); [unfold P10; cbn; tauto | rewrite RG10; cbn [fst snd]; clear -Hz n1; lia]. }
  idtac "mf:6".
  assert (NK : forall k, In k N_m1 -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoE (rd_of segs (rm rhoE)) (fst (spec_range rhoE k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk. split; [rewrite ER; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
    split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
    split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
    pose proof (proj1 (Forall_forall _ _) (N_m1_civ law_die A rhoE tp md HA E151 E152 E153 E154 E155 E156) k Hk) as CV. cbn beta in CV.
    destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by (clear; lia). exact CV. }
  assert (INR : forall a, in_ranges rhoE R a ->
            (exists k, In k N_m1 /\ fst (spec_range rhoE k) <= bv_unsigned a < snd (spec_range rhoE k)) \/ chg_m G pce ab ub ue sz cnt (bv_unsigned a)).
  { intros a (o & HoR & Hr). rewrite ER in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [exact Hk|].
      pose proof (proj1 (Forall_forall _ _) N_m1_small k Hk) as Sk. destruct k as [[[base lo] hi] cs]. destruct Sk as (S1 & S2 & S3 & _).
      cbn [carve_obj] in Hr. unfold carved in Hr. rewrite obj_range_mk in Hr by (clear -S1 S2 S3; lia). cbn [spec_range fst snd] in Hr |- *. exact Hr.
    - right. exact (PIN o _ HoR Hr). }
  assert (VO : forall z, ~ chg_m G pce ab ub ue sz cnt z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoE R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|Hc]; [|rewrite u64_lit in Hc by (clear -l l0; lia); exfalso; exact (Hz Hc)].
      rewrite u64_lit in Hr by (clear -l l0; lia). unfold rho3.
      exact (absorb_specs_view rhoE _ tr (vms md tp ms) (vmd md) K R N_m1 (rd_of segs (rm rhoE)) Hsm1 eq_refl NK z k Hk Hr).
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ chg_m G pce ab ub ue sz cnt a -> ~ rt_zoneM G a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ha Hc Hrt. unfold rho3. apply rm_absorb_out. intros Hin.
    destruct (INR _ Hin) as [(k & Hk & Hr)|Hc']; rewrite u64_lit in * by (clear -Ha; lia).
    - apply Hrt. exact (N_m1_zone G rhoE k a HG E151 E152 Hk Hr).
    - exact (Hc Hc'). }
  assert (DEFM : forall a, IMG_HI <= a < 2 ^ 64 -> rm rhoE (Z_to_bv 64 a) <> None -> rm rho3 (Z_to_bv 64 a) <> None).
  { intros a Ha Hd. destruct (in_ranges_dec rhoE R (Z_to_bv 64 a)) as [Hin|Hout].
    - unfold rho3. apply (absorb_defined rhoE _ tr (vms md tp ms) (vmd md) K R _ Hsm1 eq_refl (R9_writable scells hcells pcells) Hin).
      rewrite u64_lit by (unfold IMG_HI in Ha; clear -Ha; lia). clear -Ha; lia.
    - unfold rho3. rewrite rm_absorb_out by exact Hout. exact Hd. }
  assert (VMG : alloc_magic_ok v3 ub nv).
  { destruct HMG as [HF16|[HM1 HM2]].
    - left. pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ F _ H HF16) as X. cbn [holds eval] in X. unfold V_RZ in X.
      rewrite E150, !u64_lit in X by (clear -Brz; lia). clear -X Brz. lia.
    - right. split.
      + destruct (COH _ HM1) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_magic] in CO. rewrite soff_lit in CO. cbn [snorm Z.ltb] in CO.
        rewrite Eab in CO. cbn [eval] in CO.
        intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn Brz; unfold ub; lia).
        replace (ub - rz nv + Z.of_nat k) with (ab + 0 + Z.of_nat k) by (unfold ub; clear; lia). unfold kAllocBegMagic. exact (CO k Hk).
      + destruct (COH _ HM2) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_cptr] in CO. rewrite soff_lit in CO. cbn [snorm Z.ltb] in CO.
        rewrite Eab in CO.
        assert (EV : eval rhoE (SAlu ALU_ADD (SAlu ALU_ADD ab_e (SVar V_RZ)) (SLit (-16))) = Z_to_bv 64 (ub - 16)).
        { apply bv_eq. change (eval rhoE (SAlu ALU_ADD (SAlu ALU_ADD ab_e (SVar V_RZ)) (SLit (-16)))) with (alu64 ALU_ADD (eval rhoE ube) (Z_to_bv 64 (-16))).
          rewrite add_val, Eub. rewrite (u64_lit (ub - 16)) by (clear -ABB ACV Bn; unfold ub; lia).
          replace (bv_unsigned (Z_to_bv 64 (-16))) with (2 ^ 64 - 16) by (rewrite Z_to_bv_unsigned; reflexivity).
          replace (ub + (2 ^ 64 - 16)) with ((ub - 16) + 1 * 2 ^ 64) by (clear; lia). rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear -ABB ACV Bn; unfold ub; lia. }
        rewrite EV in CO.
        intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn Brz; unfold ub; lia).
        replace (ub - rz nv + 8 + Z.of_nat k) with (ab + 8 + Z.of_nat k) by (unfold ub; clear; lia). exact (CO k Hk). }
  idtac "mf:7".
  destruct (malloc_rebuild CST XGL HCST HXGL HCSTM A rhoE rho3 tp md nv (aa_Km A) ltac:(clear; lia) HA ltac:(clear -Bn; lia) Hcnt HPRM
              VC VS VH2 VHN VH0 VH1 VZ VP VMG PRES VO RMO DEFM) as (A2 & HA2 & HL2 & HFR2 & HV2 & HKm2 & HKf2 & HGe2 & KEPT2 & CK2).
  idtac "mf:8".

  set (A1 := ax_setS (ax_setS F (set_objs (ax_S F) (K ++ R))) (set_objs (ax_S (ax_setS F (set_objs (ax_S F) (K ++ R)))) K)) in Hb.
  assert (Hc : SPA segs KJ (ax_setS A1 (S2_of F K)) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { eapply SPA_restate; [exact W9 | exact D9 | reflexivity | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. pose proof (geom_old _ HG) as HGt. destruct HGt as (_ & _ & _ & G4' & _). unfold G in G4'. rewrite G4'. reflexivity. }
  clear Hb.

  assert (Eub3 : bv_unsigned (eval rho3 ube) = ub) by (unfold rho3; rewrite eval_absorb; exact Eub).
  assert (E12_3 : bv_unsigned (eval rho3 (SVar 12)) = nv) by (unfold rho3; rewrite eval_absorb; cbn [eval]; rewrite E12; apply u64_lit; clear -Bn; lia).

  pose proof (proj1 (proj1 Hc)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S ax_setS] in Hsm2.
  assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rho3 p).
  { intros p Hp. unfold rho3. apply (proj2 (holds_absorb rhoE R (vms md tp ms) p)). exact (fact_of_stateB nW st A Kc rho rhoE tp _ F p H (FP9 p Hp)). }
  assert (Hhigh : holds rho3 F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
  destruct (sw_range_gen segs rho3 (S2_of F K) _ (sw9 swc) Hsm2 ltac:(cbn; left; reflexivity) eq_refl Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => 140735332483072 + 16 <= bv_unsigned (eval rho3 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ 140735332483072); [|clear -SW1 SW2 SW3; lia|clear; lia]. apply Forall_forall. intros p Hp. apply HFX. apply in_or_app. left. exact (chain_pre_factsS W st p HW Hp). }
  assert (OUTK : forall z, SHADOW_OFF <= z < 17594333495296 -> outside_all rho3 K (Z_to_bv 64 z)).
  { intros z Hz. unfold K, KEPT9, outside_all. rewrite u64_lit by (unfold SHADOW_OFF in Hz; clear -Hz; lia). cbn [app]. constructor.
    - cbn zeta. clear -SW1 SW3 Hz ACV. unfold SHADOW_OFF in Hz. lia.
    - apply Forall_app. split.
      + eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
        cbn zeta. rewrite obj_range_mk by (clear; lia). cbn [fst snd]. clear -B1 Hz ACV. unfold SHADOW_OFF in Hz. lia.
      + unfold O_UB, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil; cbn zeta.
        * unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
          rewrite (soff_of_val rho3 (SVar 12) nv E12_3) by (clear -Bn; lia). rewrite Eub3. cbn [fst snd]. clear -Hz ABB. unfold ub, SHADOW_OFF in *. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd eval]. rewrite u64_lit by (clear; lia). unfold SHADOW_OFF in Hz. clear -Hz. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd eval]. rewrite u64_lit by (clear; lia). unfold SHADOW_OFF in Hz. clear -Hz. lia. }

  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (PC c C1) as PCc. fold G in PCc. unfold class_repr in PCc.
  destruct PCc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & N7 & _ & PSH & _).
  assert (Hxin : In x (cs_free_array (nthZ (aa_cls A) c cs_empty) ++ cs_cache (nthZ (aa_cls A) c cs_empty))).
  { apply in_or_app. right. unfold x, chk_of, cst_of. fold c. apply nth_In.
    unfold cnt, cnt_of, cst_of in Hcnt. fold c in Hcnt. clear -Hcnt. lia. }
  destruct (N7 x Hxin) as (_ & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by (clear; lia). change (2 ^ 4) with 16 in X3. fold sz in X3.
  set (mu := cs_mapped_user (nthZ (aa_cls A) c cs_empty)) in *. set (au := cs_allocated_user (nthZ (aa_cls A) c cs_empty)) in *.
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in N1, N2, N3. fold SB in PSH.
  assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in PSH.
  destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(clear; lia)) ltac:(clear -BSB; tauto)) as [qb Hqb].
  destruct (proj1 (Z.mod_divide mu (2 ^ 18) ltac:(clear; lia)) N1) as [qm Hqm].
  assert (ESHrb : Sh (SB + c * 2 ^ 32) = qb * 2 ^ 13 + c * 2 ^ 29 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHre : Sh (SB + c * 2 ^ 32 + mu) = qb * 2 ^ 13 + c * 2 ^ 29 + qm * 2 ^ 15 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb, Hqm. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHab : Sh ab = qb * 2 ^ 13 + c * 2 ^ 29 + 2 * x + SHADOW_OFF).
  { unfold Sh, ab. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHsp : Sh SB = qb * 2 ^ 13 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHtop : Sh (SB + 2 ^ 37 + 4096) = qb * 2 ^ 13 + 2 ^ 34 + 512 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (CHGD : forall z, chg_m G pce ab ub ue sz cnt z \/ ~ chg_m G pce ab ub ue sz cnt z) by (intros z; unfold chg_m; clear; lia).
  assert (WDEF : forall w, Sh (SB + c * 2 ^ 32) <= w < Sh (SB + c * 2 ^ 32 + mu) -> rm rho3 (Z_to_bv 64 w) <> None).
  { intros w Hw.
    assert (Bw : 0x646000 <= w < 2 ^ 64).
    { rewrite ESHrb, ESHre in Hw. unfold SHADOW_OFF in Hw. clear -Hw Hqb Hqm BSB Bc N2 N3 Btop Bx Bsz ACV. lia. }
    assert (VW : exists bb, v3 w = Some bb).
    { destruct (CHGD w) as [Hcw|Hnw]; [exact (PRES w Hcw)|]. rewrite (VO w Hnw).
      destruct (PSH w Hw) as [bb Hbb]. exists bb. unfold vE. rewrite <- (maskv_out (fs_footb G) _ w); [exact Hbb|].
      apply fs_footb_space_sh; [exact HG|]. fold SB. rewrite kSpaceSize_val, ESHsp, ESHtop. rewrite ESHrb, ESHre in Hw.
      clear -Hw Bc N2 N3 Hqm. lia. }
    destruct VW as [bb Hbb]. unfold v3 in Hbb. rewrite view_in in Hbb by (clear -Bw; lia).
    rewrite (rd_off_image _ _ _ Bw Hbb). discriminate. }
  idtac "mf:9".
  destruct (proj1 (Z.mod_divide ab 8 ltac:(clear; lia)) AB8) as [qa Hqa].
  assert (Hd : SPA segs KJ (ax_setX (ax_setS A1 (S2_of F K)) ((ube, SVar 12) :: ax_X (ax_setS A1 (S2_of F K)))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { apply SPA_x_publish; [exact XB9 | | exact Hc].
    change (ax_base (ax_setS A1 (S2_of F K))) with (ax_base F). rewrite BF9. change (ss_objs (ax_S (ax_setS A1 (S2_of F K)))) with K.
    unfold xr_ok. cbn [fst snd]. rewrite Eub3, E12_3. unfold base_sv. cbn [eval]. rewrite u64_lit by (unfold SHADOW_OFF; clear; lia).
    split; [unfold ub; rewrite Hqr, Hqa; apply Z.mod_divide; [clear; lia|]; exists (qa + 2 * qr); clear; lia|].
    split; [clear -ABB ACV Bn; unfold ub; lia|].
    intros a Ha.
    pose proof (Z.div_mod a 8 ltac:(clear; lia)) as DMa. pose proof (Z.mod_pos_bound a 8 ltac:(clear; lia)) as MBa.
    set (pa := a / 8) in *.
    assert (PA : qa + 2 * qr <= pa /\ 8 * pa <= a /\ a < qa * 8 + 16 * qs /\ 8 * (qa + 2 * qr) = ub).
    { unfold ub, ue in Ha. rewrite Hqa, Hqr in Ha. clear -Ha DMa MBa Hqa Hqr Hqs Bfit Bn. unfold ub. split; [|lia]. nia. }
    assert (PA2 : pa < qa + 2 * qs) by (clear -PA DMa MBa; nia).
    assert (SHA : SHADOW_OFF + pa = Sh ub + (pa - qa - 2 * qr)).
    { unfold Sh, ub. rewrite Hqa, Hqr. replace (qa * 8 + qr * 16) with ((qa + 2 * qr) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
    assert (RB : Sh (SB + c * 2 ^ 32) <= (SHADOW_OFF + pa) / 8 * 8 /\ (SHADOW_OFF + pa) / 8 * 8 + 8 <= Sh (SB + c * 2 ^ 32 + mu)).
    { rewrite ESHrb, ESHre. unfold SHADOW_OFF.
      pose proof (Z.div_mod (2147450880 + pa) 8 ltac:(clear; lia)) as DMs. pose proof (Z.mod_pos_bound (2147450880 + pa) 8 ltac:(clear; lia)) as MBs.
      assert (LO : qb * 2 ^ 13 + c * 2 ^ 29 + 2147450880 <= 2147450880 + pa).
      { unfold ab in Hqa. rewrite Hqb in Hqa. clear -Hqa PA Bx Brz Hqr. lia. }
      assert (HI : 2147450880 + pa < qb * 2 ^ 13 + c * 2 ^ 29 + qm * 2 ^ 15 + 2147450880).
      { unfold ab in Hqa. rewrite Hqb in Hqa. rewrite Hqm, Hqs in *. clear -Hqa PA2 X3 N2 Bx. lia. }
      pose proof (Z.div_le_mono _ _ 8 ltac:(clear; lia) LO) as D1.
      replace ((qb * 2 ^ 13 + c * 2 ^ 29 + 2147450880) / 8) with (qb * 2 ^ 10 + c * 2 ^ 26 + 268431360) in D1 by (apply Z.div_unique with 0; clear; lia).
      pose proof (Z.div_lt_upper_bound (2147450880 + pa) 8 (qb * 2 ^ 10 + c * 2 ^ 26 + qm * 2 ^ 12 + 268431360) ltac:(clear; lia) ltac:(clear -HI; lia)) as D2.
      clear -D1 D2 DMs MBs. lia. }
    split; [clear -PA PA2 Hqa Hqs Hqr Bsz Brz ABB ACV; unfold ub in *; unfold SHADOW_OFF; lia|].
    split; [unfold shadow_addr; fold pa; apply OUTK; clear -PA PA2 Hqa Hqs Bsz Brz Hqr ABB ACV; unfold ub in *; unfold SHADOW_OFF; lia|].
    split.
    { intros j Hj. unfold word_byte. fold pa. split.
      - apply OUTK. rewrite ESHrb, ESHre in RB. unfold SHADOW_OFF in *. clear -RB Hj BSB Hqb Bc N2 N3 Hqm GS2 ACV. lia.
      - apply WDEF. clear -RB Hj. lia. }
    destruct (Z_lt_dec (pa - qa - 2 * qr) qn) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      unfold shadow_addr. fold pa. rewrite SHA. pose proof (VZ (pa - qa - 2 * qr) ltac:(clear -LT PA; unfold qn; lia)) as X. unfold v3 in X.
      rewrite view_in in X by (rewrite <- SHA; clear -PA PA2 Hqa Hqs Hqr Bsz Brz ABB ACV; unfold ub in *; unfold SHADOW_OFF; lia).
      refine (rd_off_image _ _ _ _ X). rewrite <- SHA. clear -PA PA2 Hqa Hqs Hqr Bsz Brz ABB ACV. unfold ub in *. unfold SHADOW_OFF. lia.
    - assert (EQ : pa - qa - 2 * qr = qn /\ nv mod 8 <> 0).
      { clear -GE PA DMa MBa DMn MBn Bn Ha Hqa Hqr. unfold ub in *. unfold qn in *. lia. }
      destruct EQ as [EQ NZ]. exists (Z_to_bv 8 (nv mod 8)). split.
      + unfold shadow_addr. fold pa. rewrite SHA, EQ. pose proof (VP NZ) as X. unfold v3 in X. fold qn in X.
        rewrite view_in in X by (rewrite EShub; clear -SHB Bfit8 Hqr Hqs Blp DMn MBn Bn Brz; unfold qn in *; lia).
        refine (rd_off_image _ _ _ _ X). rewrite EShub. clear -SHB Bfit8 Hqr Hqs Blp DMn MBn Bn Brz. unfold qn in *. lia.
      + right. split.
        * rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by (clear -MBn; lia).
          rewrite <- (proj2 (proj2 (proj2 PA))). rewrite Z.add_comm, Z.mul_comm, Z.mod_add by (clear; lia). reflexivity.
        * rewrite <- (proj2 (proj2 (proj2 PA))). fold pa. rewrite Z.add_comm, Z.mul_comm, Z.div_add by (clear; lia). clear -EQ DMn MBn. unfold qn in *. lia. }
  clear Hc.
  idtac "mf:10".

  change (ax_setX (ax_setS A1 (S2_of F K)) ((ube, SVar 12) :: ax_X (ax_setS A1 (S2_of F K))))
    with (mkAX (S2_of F K) ((ube, SVar 12) :: ax_X F) (ax_base F)) in Hd.
  rewrite XF, BF9 in Hd. change (mkAX (S2_of F K) [(ube, SVar 12)] base_sv) with (X9_of F K) in Hd.
  pose proof (smatchA_entails segs (X9_of F K) (L_malloc_ok AE_A W st) s9 rho3 tp _ ENT9 (proj1 Hd)) as Hsm4.
  set (rho4 := rho_sub rho3 s9) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ SID9 Hk). cbn [eval]. unfold rho3. cbn [rho_absorb rw]. reflexivity. }
  assert (E110 : bv_unsigned (rw rho4 V_RES) = ub). { unfold rho4. cbn [rho_sub rw]. rewrite G110. exact Eub3. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 s9).
  destruct HL as (HLw & HLl & HLm & HLd).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).
  assert (LOWE : forall k, (k < NF)%positive -> rw rhoE k = rw rho0 k).
  { intros k Hk. rewrite <- (Hagw k) by (unfold GW, NF in *; clear -Hk; lia). rewrite <- (RMw k Hk). exact (HLw k). }
  destruct HDO as (Dgeom & Dcls & Dci & Dsec & Dpc & Dlive & Dqt & Dqg & Dii & Dbusy & Dhint & DV & DKm & DKf).
  assert (CLE : forall a, client_addrA CST A0 a <-> client_addrA CST A a).
  { intros a. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag. rewrite Dlive, Dbusy, Dgeom. split; intros X; exact X. }
  assert (CSE : forall a, client_shadowA CST XGL A0 a <-> client_shadowA CST XGL A a).
  { intros a. unfold client_shadowA. split; intros [(y & Y1 & Y2)|Y]; [left; exists y; split; [apply (proj1 (CLE y)); exact Y1 | exact Y2] | right; exact Y
      | left; exists y; split; [apply (proj2 (CLE y)); exact Y1 | exact Y2] | right; exact Y]. }
  apply (LQPA_intro segs NF rho0 tp0 _ (L_malloc_ok AE_A W st) (JL_malloc_ok AInv CST XGL A0 Kc) rho4 tp _ KJ).
  - exact HPin.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi), (LOWE i Hi). reflexivity.
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite <- (Hagl l). rewrite <- (RMl l). symmetry. exact (HLl l).
  - intros _. unfold JL_malloc_ok. cbn [w_tr w_cfg cfg_model].
    exists A2, [], (aa_live A0). cbn [app].
    split; [unfold AInv, AInvA in HA2 |- *; rewrite Erm4; exact HA2|].
    split; [rewrite HL2, E110, <- (HLw 12%positive), Dlive; reflexivity|].
    split; [reflexivity|].
    split; [rewrite HFR2; unfold aa_frames; rewrite Dbusy; reflexivity|].
    split; [rewrite HV2, DV, <- (HLw 12%positive); reflexivity|].
    split; [rewrite HKm2, DKm; reflexivity|]. split; [rewrite HKf2, DKf; reflexivity|]. split; [rewrite HGe2, Dgeom; reflexivity|].
    split.
    { split.
      - intros a Ha Hcl. rewrite Erm4.

        assert (EQ0 : rm rho (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { apply HLm. rewrite u64_lit by exact Ha. apply HKEEP. destruct Hcl as [(X & _)|(X & _)]; [left | right]; exact X. }
        assert (Hcl' : (client_addrA CST A a /\ client_addrA CST A2 a /\ ~ errno_addrA a)
                       \/ (client_shadowA CST XGL A a /\ client_shadowA CST XGL A2 a /\ rm rhoE (Z_to_bv 64 a) <> None)).
        { destruct Hcl as [(X & Y & NE)|(X & Y & DEF)]; [left; split; [apply (proj1 (CLE a)); exact X | exact (conj Y NE)]
                                                         | right; split; [apply (proj1 (CSE a)); exact X | split; [exact Y | rewrite Erm, EQ0; exact DEF]]]. }
        rewrite (proj1 KEPT2 a Ha Hcl'). rewrite Erm. exact EQ0.
      - intros xx jj Hx Hj Hdef. rewrite Erm4. apply (proj2 KEPT2 xx jj); [| exact Hj |].
        + destruct Hx as [[X Y]|X]; [left; split; [apply (proj1 (CLE xx)); exact X | exact Y] | right; exact X].
        + rewrite Erm. apply HLd; [|exact Hdef].

          assert (BX : 0 <= xx < 2 ^ 47).
          { destruct Hx as [[X _]|X]; [apply (proj1 (CLE xx)) in X; exact (proj1 (client_addr_bounds CST HCST A xx _ HG (proj1 (proj2 (proj2 HA))) (proj1 (proj1 (proj2 (proj2 (proj2 HA))))) X))|].
            destruct (HXGL xx X). unfold IMG_HI in *. clear -H0 H1. lia. }
          pose proof (Sh_in_band xx BX) as SBX. unfold word_byte. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
          rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64).
          pose proof (Z.div_mod (Sh xx) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Sh xx) 8 ltac:(lia)). rewrite Z.mod_small by (clear -SBX Hj H0 H1; lia). clear -SBX Hj H0 H1. lia. }
    split; [exact HK|].
    rewrite <- (HLw 12%positive). fold nv. intros c0 Hc0 Hor Hfr. apply (CK2 c0 Hc0 Hor). unfold class_fresh in Hfr |- *. rewrite Dcls. exact Hfr.
Qed.

Theorem malloc_finish : ltac2:(tb__ "0|4|
S67S67S71S4S4S33OF_;S4S37S5cQ40M0A1A1M1G1S99S2dS76Vst;S73A3S2dS37S6fA1VW;S39S6fA1A3F_;S72R9A1Sa1RcRbA2Sa2R8RaR9A3S33S2fS74VCST;RfR1A3S75VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S4bZ1S9dReS5bG0S7RbPcM2A2A2A2A2S69RfA1S36OLpartial;Vpartial;S30S2dS33S4cS5bG0S7RdG2A2A2Z8A2Z0A3M3A1G3X36x2S95Vsegs;Sa0VW;Vst;R11R10ReA5VF;RcRaR9A6S9bVsegs;S93R10RcS79S70VAInv;VCST;VXGL;VW;Vst;R13R11A8RaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;FrhoE;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Proof.
  intros A0 A Kc rho0 rho keep rhoE tp0 tp w. apply malloc_finish_P. unfold Posts_malloc. right. left. reflexivity.
Qed.

End B14.

Definition fin_hyps (F : axst) (swc scells hcells : list cell) (partial : bool) (s9 : wsub) : Prop := ltac2:(tb__ "0|e|
Sb3VW;Vswc;A2S37S1A1M0SbcVhcells;A1S3cS0S33A2S2eS2dG0Sc9ScS60VF;A1M1A1M2Sa9VnW;A1M3A2S3eS1R2SabVscells;Vhcells;S36S37S3A1Lpartial;Vpartial;S38S3Sb0S39S3A1M4A3G4X36x2A3A3A3S2eS2dS36Sc8G3A1S3bA3S2eS2dS36S58S3aS3aSd8R1S41S1G2A2M5A2Li;G3A3S3bA3S2eS2dS36S58S3aS3aS5aS3aSd7R1A1G3A3Li;Sa4U0G5A2A3S3bA3S2eS2dS37S3cS0S0A2M6A1M7S63VF;A1S39G6A1M8A3S2eS2dS0S64VF;A1S7bA3S2eS57S3SbaVhcells;A3S2eS57S3Sb8Vhcells;A3S2eS57S3Sb9Vhcells;A3S2eS57S3SafS44S0S33R1A3S45S0S33R1A3M9A2Vhcells;A3S2eS2dS36Sb1G9A1S3bA3S2eS2fS57S6S10S5S84A1S2Z10A1A2SbG1A1MaA3S2eS57S3SaeVhcells;A3S57S3SadVhcells;A3A2A2S2eS59S6S86GaA3S2eS59S6S3eS6S7eVW;Vst;A2S7dS7cA1A3GaA3S2eS2dS36S1cSaaVF;R2A2MbA1S3bA3S2eS2dS40S3cG7S37S6A1McA2MdA1Sc7ScfG1R2A2GbA2S3fGdS3dG7GcS38G6S3dS0S0S2Sd0A1S5P18A1A4G8A3S39S6A1A4A2A3S2eS2dS36S62SfG1A1S3dS0S0S85S5PcA1A4A2S3bA3S2eS2dS36S61SacVF;R2A2S77S70VW;Vst;A3Vs9;A3S3bA3S2eS2dS36ScdVs9;S93A2S3bA3S2dS0SccVs9;S7aA2S85A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tty;TK;").

Lemma malloc_finish'_P : ltac2:(tb__ "0|6|
S5fS37S3A1M0G0G0S36ScbSbdR6R5R4R3R2R1A6S67S67S71S4S4S33OF_;S4S37S5cQ40M1A1A1M2G2S99S37S3cS5fS9cA2M3A1S57G3S3dS5fS9cS77S70VW;Vst;A3S78VAInv;VCST;VXGL;RbR9A5A4R1A3S2dS76Vst;S73A3S2dS37S6fA1VW;S39S6fA1A3F_;S72RbA1Sa1ReRdA2Sa2RaRcRbA3S33S2fS74VCST;R11R1A3S75VCST;VXGL;R11R1A4A2RdR2A1F_;Fa;S4bZ1S9dR10S5bG1S7RdPcM4A2A2A2A2S69R11A1S36OLpartial;R16S30S2dS33S4cS5bG1S7RfG4A2A2Z8A2Z0A3M5A1G5X36x2S95Vsegs;Sa0VW;Vst;R13R12R10A5R1bReRcRbA6S9bVsegs;S93R12ReRbRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fkeep;Frho;Frho0;FKc;FA;FA0;F_;Fs9;Fpartial;Fhcells;Fscells;Fswc;FF;").
Proof.
  intros F swc scells hcells partial s9 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H9t & H9a & H9m & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
  exact (malloc_finish_P F swc scells hcells partial H1 H2 H3 H4 H5 H6 H7 H8 H9 _ _ H9t H9a H9m H10 H11 H12 H13 H14 s9 H15 H16 H17).
Qed.
Lemma malloc_finish' : ltac2:(tb__ "0|5|
S5fS37S3A1M0G0G0S36ScbSbdR6R5R4R3R2R1A6S67S67S71S4S4S33OF_;S4S37S5cQ40M1A1A1M2G2S99S2dS76Vst;S73A3S2dS37S6fA1VW;S39S6fA1A3F_;S72R9A1Sa1RcRbA2Sa2R8RaR9A3S33S2fS74VCST;RfR1A3S75VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S4bZ1S9dReS5bG1S7RbPcM3A2A2A2A2S69RfA1S36OLpartial;R14S30S2dS33S4cS5bG1S7RdG3A2A2Z8A2Z0A3M4A1G4X36x2S95Vsegs;Sa0VW;Vst;R11R10ReA5R19RcRaR9A6S9bVsegs;S93R10RcS79S70VAInv;VCST;VXGL;VW;Vst;R13R11A8RaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;FrhoE;Fkeep;Frho;Frho0;FKc;FA;FA0;F_;Fs9;Fpartial;Fhcells;Fscells;Fswc;FF;").
Proof.
  intros F swc scells hcells partial s9 FH A0 A Kc rho0 rho keep rhoE tp0 tp w. apply (malloc_finish'_P F swc scells hcells partial s9 FH). unfold Posts_malloc. right. left. reflexivity.
Qed.

Lemma SPA_add_facts : ltac2:(tb__ "0|0|
S98S4S5fS37S6A1S37S5cQ40A1A1S99Sa5S6S20R5A1R3A3S2dS36S58S6S25SfS60R5A1A1A1R4A3S3bA3S95Vsegs;R8R6R7R4R3A6S95Vsegs;R9SbeR6R7A2R8R5R4A6F_;F_;F_;Fw;Ftp;FFs;FA;Frho;FJx;").
Proof. intros Jx rho A Fs tp w HF HB [Hsm HJ]. split; [exact (smatchA_add_facts segs rho tp Fs A w Hsm HF HB) | exact HJ]. Qed.

Section B15.
Variable partial : bool.
Variables (CC9 Fa Fb : axst).
Hypothesis Cert9a : ltac2:(tb__ "0|1|
S2dS36SbfSc3Ufa0S39S33A1Sc2S38S5fSbeS38S6S10S2Z20A1S5S84A1A2S39S6A1A3VCC9;A2S39S5fA1M0A3S38S5fVFa;G0A3A6S3bA3").
Hypothesis Cert9b : ltac2:(tb__ "0|1|
S2dS36SbfSc3Ufa0S39S33A1Sc2S38S5fSbeS38S6S10S5S84A1S2Z10A1A2S39S6A1A3VCC9;A2S39S5fA1M0A3S38S5fVFb;G0A3A6S3bA3").
Hypothesis NX9 : ltac2:(tb__ "0|0|
SdfSc2SfS60VCC9;A1A1A2").
Hypothesis FGC : ltac2:(tb__ "0|0|
S59S6S86SbS60VCC9;A1A1A3").
Variables (swca scellsa hcellsa swcb scellsb hcellsb : list cell) (sa sb : wsub).
Hypothesis FHa : ltac2:(tb__ "0|0|
SbdVFa;Vswca;Vscellsa;Vhcellsa;Vpartial;Vsa;A6").
Hypothesis FHb : ltac2:(tb__ "0|0|
SbdVFb;Vswcb;Vscellsb;Vhcellsb;Vpartial;Vsb;A6").

Theorem spine_s9_P : ltac2:(tb__ "0|5|
S99OF_;S67S67S71S4S4S33OF_;S37S5cQ40M0A1A1M1S37S3cS5fS9cA2M2A1S57G2S3dS5fS9cS77S70VW;Vst;A3S78VAInv;VCST;VXGL;R8R6A5A4R1A3S2dS76Vst;S73A3S2dS37S6fA1VW;S39S6fA1A3F_;S9eVW;Vst;A2S72R9A1S97Vsegs;RdS96RaA1A3Sa1RdRcA2Sa2R9RbRaA3S33S2fS74VCST;R10R1A3S75VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S4bZ1S9dRfS5bG0S7RcPcM3A2A2A2A2S69R10A1S36OLpartial;Vpartial;S30S2dS33S4cS5bG0S7ReG3A2A2Z8A2Z0A3M4A1G4X36x2S4G1S9aVsegs;R16S95Vsegs;Sa0VW;Vst;R14R13R11A5VCC9;R2R1A5S9bVsegs;S93R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;").
Proof.
  intros ok A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc Hokf HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  apply (triple_pre_pure segs ok _ _ (rw rhoX V_RZ = Z_to_bv 64 (rz nv) /\ (16 <= rz nv <= 1024 /\ rz nv mod 16 = 0))).
  { intros w Hw. pose proof (JGb_pvals nW st A Kc rho rhoX tpX w CC9 Hw FGC Hcnt) as PV. cbn zeta in PV.
    destruct PV as (_ & _ & E150 & _ & _ & _ & _ & _ & Brz & _). split; [exact E150 | exact Brz]. }
  intros [E150 RZF].
  destruct (Z.eq_dec (rz nv) 16) as [E16|N16].
  - eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw |].
    { apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SVar V_RZ) (SLit 16)] tpX w); [| |exact Hw].
      - constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
      - cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia. }
    apply (cfg_soundA segs 4000%nat [] GW [ax_add_facts [SPUle (SVar V_RZ) (SLit 16)] CC9] [Fb] (JGb W st A Kc rho) ok _ tpX).
    + intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
    + exact HST.
    + exact Cert9b.
    + intros E rhoY HinE. destruct HinE as [<-|[]].
      eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
      eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
      intros w Hw. exact (malloc_finish'_P Fb swcb scellsb hcellsb partial sb FHb A0 A Kc rho0 rho keep rhoY tp0 tpX w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar Hw).
    + left. reflexivity.
  - eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw |].
    { apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SLit 32) (SVar V_RZ)] tpX w); [| |exact Hw].
      - constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
      - cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia. }
    apply (cfg_soundA segs 4000%nat [] GW [ax_add_facts [SPUle (SLit 32) (SVar V_RZ)] CC9] [Fa] (JGb W st A Kc rho) ok _ tpX).
    + intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
    + exact HST.
    + exact Cert9a.
    + intros E rhoY HinE. destruct HinE as [<-|[]].
      eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
      eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
      intros w Hw. exact (malloc_finish'_P Fa swca scellsa hcellsa partial sa FHa A0 A Kc rho0 rho keep rhoY tp0 tpX w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar Hw).
    + left. reflexivity.
Qed.
Theorem spine_s9 : ltac2:(tb__ "0|4|
S99OF_;S67S67S71S4S4S33OF_;S37S5cQ40M0A1A1M1S2dS76Vst;S73A3S2dS37S6fA1VW;S39S6fA1A3F_;S9eVW;Vst;A2S72R7A1S97Vsegs;RbS96R8A1A3Sa1RbRaA2Sa2R7R9R8A3S33S2fS74VCST;ReR1A3S75VCST;VXGL;ReR1A4A2RaR2A1F_;Fa;S4bZ1S9dRdS5bG0S7RaPcM2A2A2A2A2S69ReA1S36OLpartial;Vpartial;S30S2dS33S4cS5bG0S7RcG2A2A2Z8A2Z0A3M3A1G3X36x2S4G1S9aVsegs;R14S95Vsegs;Sa0VW;Vst;R12R11RfA5VCC9;R2R1A5S9bVsegs;S93R10RdS79S70VAInv;VCST;VXGL;VW;Vst;R13R11A8A5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;").
Proof.
  intros ok A0 A Kc rho0 rho keep tp0. apply spine_s9_P. unfold Posts_malloc. right. left. reflexivity.
Qed.
End B15.
End S9.
