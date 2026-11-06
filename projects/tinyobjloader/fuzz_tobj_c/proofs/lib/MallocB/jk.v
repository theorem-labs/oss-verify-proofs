(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib jn jg.

(* [comment removed for export] *)
Module SpineCallocEc.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "app"; "list"; "nil"; "prod"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_next"; "ss_facts"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E2a"; "E2b"; "C1g"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section EC.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2fS59VCST;R1A2S59S66R2A2S1F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S55VAInv;VW;Vst;VA;VKc;S16PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S58S17SaS60Q40A1A1S64VAInv;R4R3R2R1A4S5aS5cVsegs;S1dR4A1A2S5bZ17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section E_spine_s2C.
Let Xa : axst := ltac2:(tb__ "0|0|
S5S1fVW;Vst;Vtmax;A3S2S37VnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S5S20VW;Vst;Vtmax;A3S2S38VnW;Vst;Vtmax;A3A1A2").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S6S35S2eUfa0S8S2fZ40d40SbS2fA1A3S2dS8S3S21VW;Vst;Vtmax;A3SbS3A1M0A3S8S3S1fVW;Vst;Vtmax;A3S8S3S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Hypothesis OVa : ltac2:(tb__ "0|0|
S0S6S5eP9dS25VW;Vst;Vtmax;A3A2S7A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S6S5eP9dS26VW;Vst;Vtmax;A3A2S7A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S6S5fP9dS25VW;Vst;Vtmax;A3S4fZ208S62S63S46S47S48S46S49A1A1A1A1A1A1A5S7A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S6S5fP9dS26VW;Vst;Vtmax;A3S4fZ18U3eA5S7A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S6S12S2S37VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S6S12S2S38VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4bS2S1fVW;Vst;Vtmax;A3A1S2S37VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S25VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4bS2S20VW;Vst;Vtmax;A3A1S2S38VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S26VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S30S14S2S37VnW;Vst;Vtmax;A3A1A1S14S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S30S14S2S38VnW;Vst;Vtmax;A3A1A1S14S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S41S10S19S4aS18Z200A1S16S29A1A3S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S41S10S1cS19S4aS18Z200A1S16S29A1A3A1S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S40S10S22S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S40S10S22S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis SKa : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3bS1bS2VXa;A1A1A4S31S13G0S3bS9S13S8S13S4dS9S13S54VW;A1S50A3A3S4eA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3bS1bS2VXb;A1A1A4S31S13G0S3bS9S13S8S13S4dS9S13S54VW;A1S50A3A3S4eA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S40S10S9S10S9S10S9S10S53VW;Vst;A2S52S51A1A3S4cA3S22A3S15S2VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S40S10S9S10S9S10S9S10S53VW;Vst;A2S52S51A1A3S4cA3S22A3S15S2VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXa;A1A1A1S7A3").
Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S6S12S2S3dVXa;A1A1A1S7A3").
Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXa;A1A1A1S7A3").
Hypothesis W2a : ltac2:(tb__ "0|0|
S0S6S12S2S39VXa;A1A1A1S7A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXa;A1A1A1S7A3").
Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S6S12S2S3aVXa;A1A1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXb;A1A1A1S7A3").
Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S6S12S2S3dVXb;A1A1A1S7A3").
Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXb;A1A1A1S7A3").
Hypothesis W2b : ltac2:(tb__ "0|0|
S0S6S12S2S39VXb;A1A1A1S7A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXb;A1A1A1S7A3").
Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S6S12S2S3aVXb;A1A1A1S7A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S6S4S39VXa;A1S23VW;Vst;Vtmax;A3Vsa;A3S7A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S6S4S3aVXa;A1S24VW;Vst;Vtmax;A3Vsra;A3S7A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S6S4S39VXb;A1S23VW;Vst;Vtmax;A3Vsb;A3S7A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S6S4S3aVXb;A1S24VW;Vst;Vtmax;A3Vsrb;A3S7A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S6S32Vsa;S2dA2S7A3").
Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S6S32Vsra;S2dA2S7A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S6S32Vsb;S2dA2S7A3").
Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S6S32Vsrb;S2dA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S42S10S1aS14S2S23VW;Vst;Vtmax;A3A1A1A1S9S10S27S2cA3A3S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S42S10S1aS14S2S24VW;Vst;Vtmax;A3A1A1A1S27A3S7A3").

Hypothesis NXC1g : ltac2:(tb__ "0|0|
S69S2dS14S2S21VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0S6S36S2eUfa0S8S2fZ40d40SbS2fA1A3S2dS8S33S34S21VW;Vst;Vtmax;A3Z1S18Z0M0A1M1A3SbS33A1M2A3S8S33S34S1fVW;Vst;Vtmax;A3G0G1A3S8S33S34S20VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S7A3").
Theorem espine_s2c : ltac2:(tb__ "0|2|
S58S56S17SaS60Q40M0A1A1S44OF_;S65VW;Vst;A2S68VW;Vst;A2S57R6A1S17S43Vsegs;S45Vsegs;S5dVW;Vst;R9R8R7A5S2aVW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;S0S2fS67R9S61G0S1eR7PcA2A2A2Z0A3S17S43Vsegs;S45Vsegs;S5dVW;Vst;RbRaR9A5M1S2bVW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;S17S43Vsegs;S45Vsegs;G1S21VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HW HUS HKc HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (ecfg_cut 4000%nat [0x40d40] GW [mkVNA (C1g W st tmax) 1 (SLit 0)] [mkVNA (E2a W st tmax) 0 (SLit 0); mkVNA (E2b W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C1g W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC1g].
  - exact ECert2.
  - intros E rhoX HinE. clear NXC1g ECert2. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End E_spine_s2C.
End EC.
End SpineCallocEc.

(* [comment removed for export] *)
Module SegQS_loop.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "pair"; "prod"; "bool"; "list"; "nil"; "true"; "app"; "fst"; "length"; "option"; "Some"; "S"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "sprop"; "eval"; "SLit"; "SAlu"; "SVar"; "rw"; "holds"; "rm"; "SPUle"; "ss_objs"; "SPBranch"; "SPNot"; "rl"; "SPUlt"; "SPAlign"; "agree_below"; "soff"; "sprop_below"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "aa_sec"; "sc_map_beg"; "topG"; "AA"; "aa_geom"; "ag_spacebeg"; "sc_map_size"; "ag_ctx"; "ag_thread"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "pow"; "div"; "modulo"; "sub"; "opp"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "Forall2"; "nth_error"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "nth"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "qsenv"; "zloS"; "fam_ok"; "N1"; "ZD_fixS"; "ZD_rtiS"; "ZD_sec1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "NPRE"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop"; "KEEPV"; "lfL"; "ZD_ref"; "zhiX"; "REF1"; "a3_of"; "ENVQ"; "F2X"; "LF"; "NSC"; "NX"; "UX"; "ZUL"; "EQF"; "F_lenX"; "LT1"; "LT2"; "T_exit"; "T_first"; "T_loop"; "ZDNX"; "ZDU"; "hv_of"; "r16_of"; "zbX"; "BSX"; "F_hX"; "M_exit"; "M_first"; "M_loop"; "zbL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vCHV"; "vMS"; "VS0"; "vPTR"; "SC"; "VSC"; "vPAB"; "vEND"; "vIDX"; "vNCH"; "vNEAR"; "LA"; "SX"; "vLAST"; "BSHS"; "LENS"; "LL"; "vH"; "vLIDX"; "F2"; "OBJ2"; "O_chS"; "TOPMAX"; "TsPL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "cell_ok"; "mkACell"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "vIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_ADD"; "ALU_SRL"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "forallb2"; "same_rng"; "dspec"; "keepN"; "dobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop.Loop"; "SCANI"; "XVALS"; "ZUXl"; "zbE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world";
"@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayReserve"; "Sh"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "LOW_SHADOW_BEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "carve_okq"; "DQI0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "mkST"; "s_Cd"; "s_ok"; "uobj"; "ro_cond"; "s_okU"; "unk_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop.Env"; "zbL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan"; "best"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "sec_foot"; "@Stdlib.Arith.PeanoNat.Nat"; "even"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "FRM"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition zbX (T CTX TOP h SHH C6 C7 LST C9 : Z) (z : nat) : Z := ltac2:(tb__ "0|0|
S0SfLz;Vz;Z0S0S0SfLn;R1VT;S0S0SfLn0;R1VCTX;S0S0SfLn1;R1VTOP;S0S0SfLn2;R1VSHH;S0S0SfLn3;R1Vh;S0S0SfLn4;R1VC6;S0S0SfLn5;R1VC7;S0S0SfLn6;R1VLST;S0VC9;Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition zhiX (ms : Z) (z : nat) : Z :=
  match z with 0%nat => 0x643000 | 1%nat => 4096 | 2%nat => 4096 | 3%nat => 2 ^ 64 | 4%nat => 17592186048512 | 5%nat => ms | 6%nat => 8 | 7%nat => 8 | 8%nat => 32 | _ => 8 end.

Lemma in_zone_ext : ltac2:(tb__ "0|7|
S18S0SfF_;M0G0G0S5S0A1M1S0SfFx;M2G2G2G1S19S4bS4cRbRaR9R8R7R2R1A7S45S0S9S0SfS9S3S0SfA2M3SfR2A3A3R4A3S11SfR8S9S0SfS9G3SfR3A3A3M4A1RcG4A1A3S11SfR8S9S0SfS9G3SfR4A3A3M5A1RcG5A1A3S11SfR8S9S0SfS9G3SfR5A3A3M6A1RcG6A1A3S4cR10RbRaR9R8R7R6A7F_;F_;F_;F_;F_;Fd;Fo;FZU';Fzhi';Fzlo';Fzb';FZU;Fzhi;Fzlo;Fzb;Frho;").
Proof. intros rho zb zlo zhi ZU zb' zlo' zhi' ZU' o [[z lo] hi] (U & L1 & L2 & R) HU E1 E2 E3. cbn [fst] in *. unfold in_zone. rewrite E1, E2, E3. tauto. Qed.
Lemma in_zone_ext_list : ltac2:(tb__ "0|4|
S18S0SfF_;M0G0G0S5S0A1M1S0SfFx;M2G2G2G1S5S19A1S5S4bA1S46S19S4bS4cRbRaR9R8R7A5R2R1A5S4dS4bS4bS12S45S0S9S0SfS9S3S0SfA2SfR1A3A3M3R5A3S12S11SfR8G3A1RcG3A1A3S12S11SfR7G3A1RbG3A1A3S11SfR6G3A1RaG3A1A3A2A2A2Ld;R2A3S46S19S4bS4cRdR8R7R6R5A5R4R3A5F_;F_;Fds;Fobjs;FZU';Fzhi';Fzlo';Fzb';FZU;Fzhi;Fzlo;Fzb;Frho;").
Proof.
  intros rho zb zlo zhi ZU zb' zlo' zhi' ZU' objs ds HF. induction HF as [|o d objs' ds' Ho HF IH]; intros HD; [constructor|].
  apply Forall_cons_iff in HD as [(D1 & D2 & D3 & D4) HD]. constructor; [exact (in_zone_ext _ _ _ _ _ _ _ _ _ _ _ Ho D1 D2 D3 D4) | exact (IH HD)].
Qed.

Lemma in_zone_same : ltac2:(tb__ "0|2|
S18S0SfF_;M0G0G0S5S0A1S5S19A1M1G1S5S4bA1S11S4Sa4S19S19Sa5R3R2A5S7A3S46S19S4bS4cR9R8R7R6R5A5R3R2A5S46S19S4bS4cRaR9R8R7R6A5R5R3A5F_;F_;Fds;Frefs;Fobjs;FZU;Fzhi;Fzlo;Fzb;Frho;").
Proof.
  intros rho zb zlo zhi ZU objs refs ds HB HF. revert objs HB. induction HF as [|r d refs' ds' Hr HF IH]; intros objs HB; destruct objs as [|o objs']; cbn [forallb2] in HB; try discriminate; [constructor|].
  apply andb_prop in HB as [H1 H2]. constructor; [|exact (IH objs' H2)].
  destruct d as [[z lo] hi]. unfold in_zone in *. rewrite (same_rng_range rho o r H1). exact Hr.
Qed.

Definition ZD_ref : list zdesc := ltac2:(tb__ "0|0|
S8S4bS57S8S4bS58S59A3A3").
Definition REF1 : list sobj := ltac2:(tb__ "0|0|
S8S19S23SaaSbeA1A1S4eSaeS19SafS56A4A3").
Definition NSC (b v : sv) : list carve_spec := ltac2:(tb__ "0|7|
S1S3S3S3S17SfA2M0SfA2M1S5S3S3SfS0A2M2S17A2M3A1M4A2M5S2G1G4S2G0SfS2S17SfVb;Z0M6A4Z8A4S1G3S2G2S17S2SfS0G6U8A4Vv;A4S6G3A1A3A4S6G5A1A3").

Definition M_first : vmap := ltac2:(tb__ "0|5|
S8S3S10S17A2M0S9aS7fA1S1G0S2S10S17Pd2S83A4S1G0S2S10S17Pd3M1S1eG1A1A4S1G0S2S10S17Pd4S1cZ0A1M2A4S1G0S2S10S17Pd5S5aS83S1dS9dS86S1cZ3A1A3A2A4S1G0S2S10S17Pc0G2A4S1G0S2S10S17Pc1G2A4S1G0S2S10S17Pc2M3S1eG3A1A4S1G0S2S10S17PacM4S1eG4A1A4S6G0A1A3A3A3A3A3A3A3A3A3").
Definition T_first (f : nat) : strans := ltac2:(tb__ "0|3|
SbfS88Vf;A1U0S66S83S1ePd3M0A1A2S1S10G0S6S10A1A3S6S1aA1S81Vf;A1S79S5fS1S3S3S0SfA2M1SfA2M2S2G1SfS2S0SfU9Z0A4Z8A4S6G2A1A3A9").

Definition a3_of (k : nat) : sv := match k with 2%nat | 3%nat => vCHV | _ => vNEAR end.
Definition r16_of (k : nat) : sv := match k with 0%nat | 1%nat | 2%nat | 3%nat => vCHV | _ => vNEAR end.
Definition M_loop (k : nat) : vmap := ltac2:(tb__ "0|1|
S8S3S10S17A2M0S9aS7fA1S1G0S2S10S17Pd2S5aS80S1cZ8A1A2A4S1G0S2S10S17Pd3S1ePd6A1A4S1G0S2S10S17Pd4S62Vk;A1A4S1G0S2S10S17Pd5S84A4S1G0S2S10S17Pc0S7dA4S1G0S2S10S17Pc1S74Vk;A1A4S1G0S2S10S17Pc2S1dS9cS99S7dA3A4S1G0S2S10S17PacS1dS9cS99S87A3A4S6G0A1A3A3A3A3A3A3A3A3A3").
Definition lfL (f k : nat) : axst := ltac2:(tb__ "0|0|
S50SabVk;S8dVf;A1S81Vf;A1A4").
Definition T_loop (f k : nat) : strans := ltac2:(tb__ "0|4|
SbfS5eVf;Vk;A2U1S66S5aS80S1cZ8M0A1A2S1ePd6M1A1A2S1S10G1S6S10A1A3S6S1aA1S81Vf;A1S7aVk;A1S5fS1S3S3S0SfA2M2SfA2M3S2G2SfS2S0SfU9Z0A4G0A4S6G3A1A3A9").

Lemma T_first_ok : ltac2:(tb__ "0|0|
S0S51R1U2A2S11S4Sc1S6fR2A1A1S7A3F_;Ff;").
Proof. intros [|[|[|f]]] Hf; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl true) | lia]. Qed.
Lemma T_loop_ok : ltac2:(tb__ "0|0|
S0S0S51R2U2A2S45S0R2S1S0U1S1S0U3S1S0U5S1S0U7S6S0A1A3A3A3A3A3S11S4Sc1S70R4R3A2A1S7A3F_;F_;Fk;Ff;").
Proof.
  intros [|[|[|f]]] k Hf Hk; [| | | lia]; cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [vm_cast_no_check (eq_refl true)|]); destruct Hk.
Qed.
Lemma T_first_ref : ltac2:(tb__ "0|0|
S0S51R1U2A2S11S4Sa4S19S19Sa5S23SaaSc0S6fR2A1A1A1A1S61A5S7A3F_;Ff;").
Proof. intros [|[|[|f]]] Hf; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl true) | lia]. Qed.
Lemma T_loop_ref : ltac2:(tb__ "0|0|
S0S0S51R2U2A2S45S0R2S1S0U1S1S0U3S1S0U5S1S0U7S6S0A1A3A3A3A3A3S11S4Sa4S19S19Sa5S23SaaSc0S70R4R3A2A1A1A1S61A5S7A3F_;F_;Fk;Ff;").
Proof.
  intros [|[|[|f]]] k Hf Hk; [| | | lia]; cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [vm_cast_no_check (eq_refl true)|]); destruct Hk.
Qed.

Definition KEEPV (rS r : valuation) : Prop := ltac2:(tb__ "0|0|
S12S10S13Sd4R1S5bA2S45S10R1S7fA3A2S11S43Q40A1S1fVr;R2A2S1fVrS;R2A2A3F_;Fv;S12S10S11S5S43Q8A1A1S26Vr;R1A2S26VrS;R1A2A3Fl;S11S98S95S4aS21Vr;A1A2S95S4aS21VrS;A1A2A3A2A2").
Lemma KEEPV_refl : ltac2:(tb__ "0|0|
S18S5dR1R1A2Fr;"). Proof. intros r. split; [intros v _; reflexivity | split; [intros l; reflexivity | reflexivity]]. Qed.
Lemma KEEPV_trans : ltac2:(tb__ "0|1|
S18S18S18S5dR3R2A2M0G0S5dR5R3A2F_;F_;Fr3;Fr2;Fr1;").
Proof. intros r1 r2 r3 (A1 & L1 & B1) (A2 & L2 & B2). split; [intros v Hv; rewrite (A2 v Hv); exact (A1 v Hv) | split; [intros l; rewrite L2; apply L1 | rewrite B2; exact B1]]. Qed.
Lemma KEEPV_keepsM : ltac2:(tb__ "0|0|
SacS18S18SadR3R2R1A3S10S45S10R1S7fA3S45S3S10S17A2S2S10S17R2S1eR2A1A4R6A3F_;Fv;S5dR4R3A2F_;F_;Fr';Fr;FM;").
Proof.
  intros M r r' [HA HM] HIN. split; [|split].
  - intros v [Hv|Hv]; [symmetry; exact (proj1 HA v Hv) | rewrite (HM v (SVar v) (HIN v Hv)); reflexivity].
  - intros l. symmetry. exact (proj1 (proj2 HA) l).
  - f_equal. apply functional_extensionality. intros x. symmetry. exact (proj2 (proj2 HA) x).
Qed.

Lemma KEEPV_step : ltac2:(tb__ "0|4|
S18S18S18S18S5S3S10S43Q40A1M0A2M1A1SacS5dR6R5A2S10S11G0S1fR6R1A2S1fR7R1A2A3Fv;S10S11S5S43Q8A1M2A1S26R7R1A2S26R8R1A2A3Fl;S11S98S95S4aS21R7A1A2S95S4aS21R8A1A2A3S10S45S10R1S4eG1S10S9S10G0A2R7A4A3S12Sd3S5bR2A2S15S45S10R2S7fA3A1A2F_;Fv;S29S5bSc8R9R7A2R8A3S11G0SbG2A1F_;S21R9A1S21RaA1A3S10S17S45S3S10S17A2M3S2S10S17R2R1A4RaA3S11G0S1fRdR3A2S1bSc8ReRcA2R2A2A3F_;Fe;Fv;S10S45S10R1S7fA3S45G3S2S10S17R2S1eR2A1A4RbA3F_;Fv;S5dRfRcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FM;Fbs;Fr5;Fr3;Fr;FrS;").
Proof.
  intros rS r r3 r5 bs M (KV & KL & KM) RW RL EV HB AG RM HM HIN.
  assert (OT : forall v, (v < NPRE)%positive \/ In v VS0 -> rw (rho_sets r3 bs) v = rw rS v).
  { intros v Hv. rewrite rho_sets_other; [rewrite RW; exact (KV v Hv)|]. intros Hin. destruct (HB v Hin) as [B1 B2]. destruct Hv as [Hv|Hv]; [lia | exact (B2 Hv)]. }
  split; [|split].
  - intros v Hv. destruct Hv as [Hv|Hv]; [rewrite <- (proj1 AG v Hv); exact (OT v (or_introl Hv)) | rewrite (HM v (SVar v) (HIN v Hv)); cbn [eval]; exact (OT v (or_intror Hv))].
  - intros l. rewrite <- (proj1 (proj2 AG) l). rewrite (proj1 (rho_sets_rl_rm bs r3)), RL. apply KL.
  - rewrite RM, EV. exact KM.
Qed.

Lemma qsenv_keep : ltac2:(tb__ "0|0|
S32S3SfSfA2S0S2eS18S18S53R6R5R4R3R2A5S5dR3R2A2S53R8R7R6R5R3A5F_;F_;Fr;FrS;Fch;Fi;Fit;FA;").
Proof.
  intros A it i ch rS r [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV] (KV & _ & KM).
  assert (E : forall v, In v [151; 152; 155; 156; 165; 200; 201; 207; 209]%positive -> rw r v = rw rS v).
  { intros v Hv. apply KV. cbn [In] in Hv. unfold NPRE, VS0. repeat (destruct Hv as [<-|Hv]; [first [left; reflexivity | right; cbn; tauto]|]). destruct Hv. }
  constructor; rewrite ?KM; try assumption.
  - rewrite !E by (cbn; tauto). exact HRIG.
  - rewrite !E by (cbn; tauto). exact HV.
Qed.
Lemma top_high_keep : ltac2:(tb__ "0|0|
S32S18S18Sa3R3R2A2S5dR3R2A2Sa3R5R3A2F_;F_;Fr;FrS;FA;").
Proof. intros A rS r H (KV & _). unfold top_high in *. rewrite !KV by (left; unfold NPRE, V_DEPTH; reflexivity). exact H. Qed.
Lemma pre_facts_below : ltac2:(tb__ "0|0|
S11S4S48S1aS2bS5bA1Sa2Sa9A1A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pre_facts_keep : ltac2:(tb__ "0|1|
S18S18S4dS1aS20R2A1Sa2Sa9A1M0A3S5dR3R2A2S4dS1aS20R3A1G0A3F_;F_;Fr;FrS;").
Proof.
  intros rS r H (KV & KL & _). apply Forall_forall. intros f Hf.
  apply (holds_agree_vals NPRE rS r f); [split; [intros v Hv; symmetry; exact (KV v (or_introl Hv)) | intros l; symmetry; apply KL] | exact (proj1 (forallb_forall _ _) pre_facts_below f Hf) | exact (proj1 (Forall_forall _ _) H f Hf)].
Qed.

Definition ENVQ (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk) (rS r : valuation) : Prop := ltac2:(tb__ "0|0|
S12S53VA;Vit;Vi;Vch;VrS;A5S12Sa3VA;VrS;A2S12S4dS1aS20VrS;A1Sa2Sa9A1A3S5dVrS;Vr;A2A2A2A2").
Lemma ENVQ_at : ltac2:(tb__ "0|0|
S32S3SfSfA2S0S2eS18S18S63R6R5R4R3R2R1A6S12S53R7R6R5R4R2A5S12Sa3R7R2A2S4dS1aS20R2A1Sa2Sa9A1A3A2A2F_;Fr;FrS;Fch;Fi;Fit;FA;").
Proof. intros A it i ch rS r (QS & HT & HF & KV). split; [exact (qsenv_keep _ _ _ _ _ _ QS KV) | split; [exact (top_high_keep _ _ _ HT KV) | exact (pre_facts_keep _ _ HF KV)]]. Qed.

Definition EQF : sprop := ltac2:(tb__ "0|0|
S24Sa1S5aS80S1cZ8A1A2S84A3").
Definition LT1 : sprop := ltac2:(tb__ "0|0|
S24Sa0S99S7dA3").
Definition LT2 : sprop := ltac2:(tb__ "0|0|
S24Sa0S1dS9cS99S7dA3S1dS9cS99S87A3A3").
Definition LF (k : nat) : list sprop := ltac2:(tb__ "0|2|
S1S1aS4S1aL_;M0ScdVk;A1S6aS25S6aA1X4x2S1S1aG0SceScfVk;U4M1A2U2A2S6cS25S6cA1X4x2S1S1aG0SceVk;G1A2S6dS25S6dA1X4x2S6S1aA1A3A3A3").
Lemma leaf_facts_ok : ltac2:(tb__ "0|0|
S0S0S51R2U2A2S52R2U8A2S11S4S48S1aS1aS49S1aS2cR1A1S2dSaaS5eR5R4A2A1A1A3LF;S65R3A1A3S7A3F_;F_;Fk;Ff;").
Proof.
  intros [|[|[|f]]] k Hf Hk; [| | | lia]; (destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [vm_cast_no_check (eq_refl true) .. | lia]).
Qed.
Lemma leaf_objs_ok : ltac2:(tb__ "0|1|
S0S0S51R2U2A2S52R2U8A2S11S5S19A1S23SaaS5eR4R3A2M0A1A1S8S19Sa7G0U1A2S1S19S92S80S7dA2S6S19A1A3A3A3F_;F_;Fk;Ff;").
Proof.
  intros [|[|[|f]]] k Hf Hk; [| | | lia]; (destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end .. | lia]).
Qed.
Lemma LL_len : ltac2:(tb__ "0|0|
S0S51R1U2A2S11S0SaSabS8dR2A1A2U8A3F_;Ff;"). Proof. intros [|[|[|f]]] Hf; [reflexivity | reflexivity | reflexivity | lia]. Qed.

Lemma U_sub : ltac2:(tb__ "0|5|
S18S17S17SfSfS11S43Q40M0A1M1S1bR5R4A2S42G0R2A2M2A3S11G1S1bR6R4A2G2A3S12S38Z0R4A2S3aR4S3dZ2Z40A2M3A2A2M4G4S11SfS44G0S1bR9S1dS9cR8R7A3A2A2S3fS40R6R5A2G3A2A3F_;F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof. intros rho a b x y Ea Eb Hx Hy. cbn [eval]. rewrite sub_val, Ea, Eb, !u64_lit by lia. reflexivity. Qed.

Lemma upd_of_leaf : ltac2:(tb__ "0|4|
S18S0SfSfSfS52R4U8A2S11S43Q40M0A1M1S1bR6S99A2S42G0R4A2A3S11G1S1bR7S7dA2S42G0R3A2A3S11G1S1bR8S87A2S42G0R5A2A3S12S38Z0M2R6A2S38R6R7A2A2S3aR8S3dZ2Z40A2M3A2S12S38G2R7A2S3aR7G3A2A2S4dS1aS20RcA1S65RbA1A3S11G1S1bRdS62RcA1A2S42G0ScaRbRaR9A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;Fc;Fnr;Fpp;Fk;Frho;").
Proof.
  intros rho k pp nr c Hk Ep Ec En Hn Hp Hc HF. unfold LF in HF.
  apply Forall_cons_iff in HF as [_ HF]. apply Forall_cons_iff in HF as [F1 HF]. apply Forall_cons_iff in HF as [F2 _].
  assert (S1 : bv_unsigned (eval rho (SAlu ALU_SUB vIT vCHV)) = (pp - c) mod 2 ^ 64) by (apply U_sub; [exact Ep | exact Ec | lia | lia]).
  assert (S2 : bv_unsigned (eval rho (SAlu ALU_SUB vIT vNEAR)) = (pp - nr) mod 2 ^ 64) by (apply U_sub; [exact Ep | exact En | lia | lia]).
  assert (L1 : holds rho LT1 <-> pp < c).
  { unfold LT1. cbn [holds branch_taken]. unfold bv_ltu. rewrite Ep, Ec, !u64_lit by lia. apply Z.ltb_lt. }
  assert (L2 : holds rho LT2 <-> (pp - c) mod 2 ^ 64 < (pp - nr) mod 2 ^ 64).
  { unfold LT2. cbn [holds branch_taken]. unfold bv_ltu. rewrite S1, S2. apply Z.ltb_lt. }
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | | exfalso; lia]; cbn [Nat.ltb Nat.leb Nat.modulo Nat.divmod fst snd Nat.sub] in F1, F2; cbn [a3_of].
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite Ec, (upd_yes pp nr c Hn Hp Hc (proj1 L2 F2) (fun H => F1 (proj2 L1 H))). reflexivity.
  - rewrite Ec, (upd_yes pp nr c Hn Hp Hc (proj1 L2 F2) (fun H => F1 (proj2 L1 H))). reflexivity.
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite En, (upd_no_ge pp nr c Hn Hp Hc (fun H => F2 (proj2 L2 H))). reflexivity.
  - rewrite En, (upd_no_ge pp nr c Hn Hp Hc (fun H => F2 (proj2 L2 H))). reflexivity.
Qed.

Definition ZUL : list nat := ltac2:(tb__ "0|0|
S1S0U0S1S0U1S1S0U2S1S0U3S1S0U5S1S0U9S6S0A1A3A3A3A3A3A3").
Lemma ZD_ref_zones : ltac2:(tb__ "0|0|
S4dS4bS4bS45S0S9S0SfS9S3S0SfA2SfR1A3A3S1S0U0S1S0U1S1S0U2S1S0U3S1S0U5S6S0A1A3A3A3A3A3A3Ld;S5fA3").
Proof. apply Forall_forall. intros d Hd. apply (proj1 (forallb_forall (fun d : zdesc => existsb (Nat.eqb (fst (fst d))) [0; 1; 2; 3; 5]%nat) ZD_ref) eq_refl) in Hd.
  apply existsb_exists in Hd as (z & Hz & E). apply Nat.eqb_eq in E. rewrite E. exact Hz. Qed.

Section Env.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let CTX : Z := ag_ctx G.
Let PAB : Z := ag_pab G.
Let h : Z := sc_map_beg ch.
Let ms : Z := sc_map_size ch.
Let NC : Z := Z.of_nat (length (aa_sec A)).
Definition zbL (c9 : Z) : nat -> Z := ltac2:(tb__ "0|1|
S75VT;VCTX;S31VG;A1Vh;Z0M0G0G0G0Vc9;A9").

Lemma tbl_nums : ltac2:(tb__ "0|2|
S18S53VA;Vit;Vi;Vch;R1A5S12S38Sb9VPAB;A2S12S38S39VPAB;Sb7A2M0S31VG;A1A2S12S38S3bZ8VNC;A2Sb7A2S12S13S38G0SbbA2S38SbaVPAB;A2A2S12S13S38G0VT;A2S38S39VT;Z1000M1A2VPAB;A2A2S12S13S38G0VCTX;A2S38S39VCTX;G1A2VPAB;A2A2S13S38S39Vh;Vms;A2VPAB;A2S38G0Vh;A2A2A2A2A2A2A2A2F_;Frho;").
Proof.
  intros rho [HG HSEP3 _ _ HSR _ _ _ HSEP _ _ _ _].
  destruct HSR as (_ & _ & (B1 & B2) & _ & PD & _). pose proof (dyn_ok_big _ _ _ PD ltac:(unfold kPtrArrayReserve; lia)) as BIG.
  destruct PD as (_ & _ & _ & P3 & _ & P5). destruct HSEP3 as (_ & _ & _ & _ & ST & _ & SC & _). destruct HSEP as (_ & _ & HP & _).
  clear HG. unfold NC, PAB, T, CTX, G, h, ms in *.
  split; [exact BIG|]. split; [exact P3|]. split; [clear -B1 B2; lia|]. split; [exact P5|]. split; [exact ST|]. split; [exact SC | exact HP].
Qed.

Lemma zsepL : ltac2:(tb__ "0|3|
S18SfS53VA;Vit;Vi;Vch;R2A5S38VPAB;R2A2S38S39R3Z8A2S39VPAB;Sb7A2A2S0S0S45S0R2S69A3M0G0S15S11S0R4R3A3A1S13S38S39Sc6R9R5A2M1S60Vms;R5A2A2S39Sc6R9R4A2M2S54R4A1A2A2S38S39G2S60Vms;R4A2A2S39G1S54R5A1A2A2A2F_;F_;F_;Fz';Fz;F_;F_;F_;Fc9;Frho;").
Proof.
  intros rho c9 QS C1 C2. pose proof (tbl_nums rho QS) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & TC). pose proof (qs_chunk A it i ch rho QS) as (_ & _ & MS & IH & HT & _).
  destruct QS as [_ _ _ _ _ _ _ _ HSEP _ _ _ _]. destruct HSEP as (_ & HT' & _ & HC' & _).
  intros z z' Hz Hz' NE. unfold ZUL in Hz, Hz'. cbn [In] in Hz, Hz'. unfold zbL, zbX, zloS, zhiX, IMG_HI, kPtrArrayReserve, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  repeat (destruct Hz as [<-|Hz]); try (exfalso; exact Hz); repeat (destruct Hz' as [<-|Hz']); try (exfalso; exact Hz'); try (exfalso; apply NE; reflexivity);
    unfold NC, ms, h, PAB, CTX, T, G in *; clear -C1 C2 P1 P2 P3 P5 P6 P7 T0 T1 C0 C1' TG TI CI TC MS IH HT HT' HC'; lia.
Qed.

Lemma inz_refL : ltac2:(tb__ "0|0|
S18SfS5S19A1S53VA;Vit;Vi;Vch;R3A5Sa3VA;R4A2S4dS1aS20R5A1Sa2Sa9A1A3S11S4Sa4S19S19Sa5R4S61A5S7A3S46S19S4bS4cR7Sc6R6A1S54S60Vms;A1S69A5R5S5fA5F_;F_;F_;F_;Fobjs;Fc9;Frho;").
Proof.
  intros rho c9 objs QS HT HF HB. apply (in_zone_same rho _ _ _ _ objs REF1 ZD_ref HB).
  apply (in_zone_ext_list rho (zbS T CTX (topG G) h) zloS (zhiS ms) ZUS).
  - unfold REF1, ZD_ref. apply Forall2_app; [exact (inz_fixS A it i ch rho HT HF) | exact (inz_N1 A it i ch rho QS)].
  - eapply Forall_impl; [|exact ZD_ref_zones]. intros [[z lo] hi] Hz. cbn [fst] in *. cbn [In] in Hz.
    repeat (destruct Hz as [<-|Hz]; [split; [unfold ZUL; cbn; tauto | split; [reflexivity | split; reflexivity]]|]). destruct Hz.
Qed.
End Env.

Definition hv_of (k : nat) : positive := match k with 2%nat | 3%nat => 211%positive | _ => 212%positive end.
Lemma a3_hv : ltac2:(tb__ "0|0|
S0S11S17S62R1A1S1eS73R1A1A1A3Fk;"). Proof. intros [|[|[|[|k]]]]; reflexivity. Qed.
Definition F_hX (f : nat) (hT : sv) : list sprop := ltac2:(tb__ "0|6|
S0S5S1aA1M0Lf;Vf;S1S1aS22S5aVhT;S7eA2S1cZ7fff7000A1M1A2S1S1aS22S5aS7eVhT;A2G1A2S1S1aS27S5aVhT;S1cZ1000A1A2M2S5cA2S6S1aA1M3A3M4A3A3S0S0G0Ln;R1S1S1aS22S1cZ10007fff8000A1VhT;A2M5G4A3S0S1S1aG5S1S1aS22S5aS5cS1cS3dZ2Z25A2A1A2G2A2G3A3A3Ln0;X0x2Ln;X0x2").
Definition F_lenX (hT : sv) : sprop := ltac2:(tb__ "0|1|
S24Sa0S1dS9cS1dS9eS1dS9fS1dS9eS1dS9eVhT;S7eA3S1cN8A1A3S1cZ3A1M0A3S1cZ1A1A3S1dS9fVhT;G0A3A3S1cZffffffffffffffffA1A3").
Definition F2X (f : nat) (l : bool) (hv : positive) : list sprop := ltac2:(tb__ "0|4|
S1eVhv;A1S17S8S1aS1S1aS6bR1A1S1S1aS25S24Sa1R1S1cZ0A1A3A1S1S1aS22R1S99A2S1S1aS27S99S5aR1S7eA2M0A2S1S1aS28Vhv;ZcM1A2S1S1aS28PcbG1A2S1S1aS22S1cZ12000A1S7eA2S1S1aS22S7eS1cS93A1M2A2S1S1aS22S1cZ643000A1R1A2S1S1aS22G0G2A2S1S1aS22S5aS7eR1A2G2A2S6S1aA1M3A3A3A3A3A3A3A3A3A3A3A3S8S1aS77Vf;R1A2S4S5S1aA1Ll;Vl;G3S1S1aS27S85S5aS86S1cN1A1A2A2G3A3X4x2A3A3ThT;").
Lemma F2X_F2 : ltac2:(tb__ "0|0|
S0S4S11S5S1aA1S64R2R1PcaA3S90R2R1A2A3Fl;Ff;"). Proof. intros [|[|f]] [|]; reflexivity. Qed.
Definition NX (l : bool) (hT : sv) : list carve_spec := ltac2:(tb__ "0|14|
S8S3S3S3S17SfA2M0SfA2M1S5S3S3SfS0A2M2S17A2M3A1M4A2M5S1G5S2G1G4S2G0SfS2S17SfVhT;Z0M6A4Z10A4S1G3S2G2S17S2SfS0G6U8M7A4VhT;A4M8S1G3S2G2S17S2SfS0Z8M9G7A4S7eA4S6G3A1MaA3A3A4S6G5A1MbA3S4S5G5A1Ll;Vl;S1G5S2G1G4S2G0SfS2S17SfVhT;Z18McA4Z20MdA4MeS1G3S2G2S17S2SfS0GcG7A4MfS5aS86S1cN1A1A2A4GaA3A4S1G5S2G1G4S2G0SfS2S17SfS5aS1dS9dS86S1cZ3A1M10A3S83A2N8M11A4G6A4M12S1G3S2G2S17S2SfS0G11G7A4M13VhT;A4GaA3A4GbA3A3S1G5S2G1G4GeS1G3S2G2S17GfS85A4GaA3A4S1G5S2G1G4S2G0SfS2S17SfS5aS83S1dS9dS85G10A3A2G6A4G9A4S1G3G8GaA3A4S1G5S2G1G4G12S1G3S2G2S17G13S8aA4GaA3A4S1G5S2G1G4S2G0SfS2S17SfS8aGcA4GdA4S1G3S2G2S17GfS8fA4GaA3A4GbA3A3A3A3X4x2A3").
Definition UX (hT : sv) : sv * sv * sv := ltac2:(tb__ "0|0|
S2S3S17S17A2S17S2S17S17S8bVhT;A1S1cZ0A1A4S8cS7eA1A4").
Lemma NX_OBJ2 : ltac2:(tb__ "0|0|
S4S17S11S5S19A1S1S19Sc2S68R1A1A1S4eSaeS19SafS67R2R1A2A4A3S91R2R1A2A3FhT;Fl;"). Proof. intros [|] hT; reflexivity. Qed.
Definition ZDNX (l : bool) : list zdesc := ltac2:(tb__ "0|a|
S8S3S3S0SfA2M0SfA2M1S1G1S2G0SfS2S0SfU5M2Z0M3A4Z10A4S6G1A1M4A3S4S5G1A1Ll;Vl;S1G1S2G0SfS2S0SfG2Z18M5A4Z20M6A4M7S1G1S2G0SfS2S0SfU7G3A4Z8M8A4M9G4A3A3S1G1G7S1G1S2G0SfS2S0SfU6G3A4G8A4S1G1G9S1G1S2G0SfS2S0SfU8G5A4G6A4G4A3A3A3A3X4x2A3").
Definition ZDU : zdesc := ltac2:(tb__ "0|0|
S2S3S0SfA2SfS2S0SfU4Z0A4Z100000001000A4").
Definition M_exit (k : nat) (l : bool) : vmap := ltac2:(tb__ "0|2|
S8S3S10S17A2M0S9aS7fA1S8G0S1G0S2S10S17PcaS62Vk;A1A4S1G0S2S10S17PcbS7eA4S1G0S2S10S17Pd2S5aS80S1cZ8A1A2A4S1G0S2S10S17Pd5S84A4S1G0S2S10S17Pc0S7dA4S1G0S2S10S17Pc1S74Vk;A1A4S1G0S2S10S17Pc2S1dS9cS99S7dA3A4S1G0S2S10S17PacS1dS9cS99S87A3A4S6G0A1M1A3A3A3A3A3A3A3A3S4S5G0A1Ll;Vl;G1S1G0S2S10S17PccS85A4S1G0S2S10S17PcdS8aA4S1G0S2S10S17PceS8fA4G1A3A3A3X4x2A3A3").
Definition BSX (l : bool) : list positive := ltac2:(tb__ "0|1|
S8S10S1S10PcbS6S10A1M0A3S4S5S10A1Ll;Vl;G0S1S10PccS1S10PcdS1S10PceG0A3A3A3X4x2A3").
Definition T_exit (f k : nat) (l : bool) : strans := ltac2:(tb__ "0|0|
SbfS5eVf;Vk;A2U1S67Vl;S62Vk;A1A2S76Vl;A1S64Vf;Vl;S73Vk;A1A3S89Vf;Vl;A2S78Vk;Vl;A2S5fS71Vl;A1A9").
Lemma T_exit_ok : ltac2:(tb__ "0|1|
S0S0S4S51R3U2M0A2S45S0R3S1S0U0S1S0G0S1S0U4S1S0U6S6S0A1A3A3A3A3A3S11S4Sc4S6eR5R4R3A3S68S62R4A1A1S72A3S7A3F_;F_;Fl;Fk;Ff;").
Proof.
  intros [|[|[|f]]] k l Hf Hk; [| | | lia]; cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [destruct l; vm_cast_no_check (eq_refl true)|]); destruct Hk.
Qed.
Lemma T_exit_ref : ltac2:(tb__ "0|1|
S0S0S4S51R3U2M0A2S45S0R3S1S0U0S1S0G0S1S0U4S1S0U6S6S0A1A3A3A3A3A3S11S4Sa4S19S19Sa5S23SaaSc0S6eR5R4R3A3A1A1A1S61A5S7A3F_;F_;Fl;Fk;Ff;").
Proof.
  intros [|[|[|f]]] k l Hf Hk; [| | | lia]; cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [destruct l; vm_cast_no_check (eq_refl true)|]); destruct Hk.
Qed.

Lemma eval_srl3 : ltac2:(tb__ "0|2|
S18S17SfS11S43Q40M0A1M1S1bR3R2A2S42G0R1A2A3S12S38Z0R2A2S3aR2S3dZ2Z40A2A2A2S11G1S1bR5S1dS9fR4S1cZ3A1A3A2S42G0S3eR3Z8A2A2A3F_;F_;Fx;Fa;Frho;").
Proof.
  intros rho a x Ea Hx. apply bv_eq. rewrite U_srl_lit, Ea, !u64_lit; [reflexivity | | lia].
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma eval_BSHS : ltac2:(tb__ "0|2|
S18S17SfS11S43Q40M0A1M1S1bR3R2A2S42G0R1A2A3S12S38Z0R2A2S3aR2S3dZ2Z2fA2A2A2S11G1S1bR5S8bR4A1A2S42G0Sb8R3A1A2A3F_;F_;Fx;FhT;Frho;").
Proof.
  intros rho hT x Eh Hx. unfold BSHS. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  rewrite (ev_add_lit rho _ (x / 8) 2147450880 (eval_srl3 rho hT x Eh ltac:(lia))) by lia. reflexivity.
Qed.
Lemma soff_LENS : ltac2:(tb__ "0|1|
S18S17SfS11S43Q40M0A1S1bR3R2A2S42G0R1A2A3S12S38Z0R2A2S3aR2S3dZ2Z3fA2A2A2S11SfS2aR5S8cR4A1A2S3eR3Z8A2A3F_;F_;Fx;FmT;Frho;").
Proof.
  intros rho mT x Em Hx. unfold LENS, soff. rewrite signed_of_unsigned, (eval_srl3 rho mT x Em ltac:(lia)).
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
  rewrite u64_lit by lia. apply snorm_small. lia.
Qed.
Lemma Sh_add8 : ltac2:(tb__ "0|2|
SfSfS11SfS3fR2Z8M0A2Z0A3M1G1S11SfSb8S39R4R3A2A1S39Sb8R4A1S3eR3G0A2A2A3F_;F_;Fy;Fx;").
Proof. intros x y Hx Hy. unfold Sh. destruct (proj1 (Z.mod_divide y 8 ltac:(lia)) Hy) as [k ->]. rewrite Z.div_add, Z.div_mul by lia. lia. Qed.

Lemma F_lenX_holds : ltac2:(tb__ "0|6|
S18S17SfSfS11S43Q40M0A1M1S1bR4R3A2S42G0R2A2M2A3S11G1S1bR5S7eA2G2A3S38Z0M3R4A2S38Z8M4R4A2S3aS39R6R5A2S3dZ2Z2fA2A2S11SfS3fR7G4A2G3A3M5G5S20RbS6bRaA1A2F_;F_;F_;F_;F_;F_;F_;Fmx;Fhx;FhT;Frho;").
Proof.
  intros rho hT hx mx Eh Em H0 H8 HT Hh Hm. unfold F_lenX. cbn [holds branch_taken]. unfold bv_ltu. apply Z.ltb_lt.
  destruct (proj1 (Z.mod_divide hx 8 ltac:(lia)) Hh) as [kh Ekh]. destruct (proj1 (Z.mod_divide mx 8 ltac:(lia)) Hm) as [km Ekm].
  assert (E1 : eval rho (SAlu ALU_ADD (SAlu ALU_ADD hT vMS) (SLit (-8))) = Z_to_bv 64 (hx + mx - 8)).
  { replace (hx + mx - 8) with (hx + mx + -8) by lia. apply ev_add_lit; [apply (eval_add_z rho hT vMS hx mx Eh Em); lia | lia | lia | lia]. }
  assert (E2 : eval rho (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_ADD hT vMS) (SLit (-8))) (SLit 3)) = Z_to_bv 64 (kh + km - 1)).
  { rewrite (eval_srl3 rho _ (hx + mx - 8) E1 ltac:(lia)). f_equal. subst hx mx. replace (kh * 8 + km * 8 - 8) with ((kh + km - 1) * 8) by lia. apply Z.div_mul. lia. }
  assert (E3 : eval rho (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_ADD hT vMS) (SLit (-8))) (SLit 3)) (SLit 1)) = Z_to_bv 64 (kh + km)).
  { replace (kh + km) with (kh + km - 1 + 1) by lia. apply ev_add_lit; [exact E2 | lia | lia | lia]. }
  assert (E4 : eval rho (SAlu ALU_SRL hT (SLit 3)) = Z_to_bv 64 kh) by (rewrite (eval_srl3 rho hT hx Eh ltac:(lia)); f_equal; subst hx; apply Z.div_mul; lia).
  rewrite (U_sub rho _ _ (kh + km) kh E3 E4 ltac:(lia) ltac:(lia)). cbn [eval]. rewrite u64_lit by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma eval_sll3 : ltac2:(tb__ "0|2|
S18S17SfS11S43Q40M0A1M1S1bR3R2A2S42G0R1A2A3S12S38Z0R2A2S3aR2S3dZ2Z3cA2A2A2S11G1S1bR5S1dS9dR4S1cZ3A1A3A2S42G0S3bZ8R3A2A2A3F_;F_;Fx;Fa;Frho;").
Proof. intros rho a x Ea Hx. apply bv_eq. rewrite U_sllk by lia. rewrite Ea, !u64_lit by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma firstn_S_nth_Z : ltac2:(tb__ "0|1|
S5SfA1M0S0S52R1SaSfR2A2A2S11G0S4fSfSdR2A1R3A3S8SfS4fSfR2R3A3S1SfS50SfR2R3Z0A4S6SfA1A3A3A3F_;Fj;Fl;").
Proof. induction l as [|x l IH]; intros j Hj; [cbn in Hj; lia|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. cbn in Hj. lia. Qed.

Section Loop.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk).
Variables (a n0 : Z) (nd : nat) (its : list (Z * Z)) (tmp' rest : list qbatch).
Hypothesis HQW : ltac2:(tb__ "0|0|
SfScbVA;R1A2ScbVA0;R2A2F_;Fz;").
Hypothesis HSF : ltac2:(tb__ "0|0|
SfSccVA;R1A2SccVA0;R2A2F_;Fz;").
Let J : jpredA := ltac2:(tb__ "0|0|
Sd1VK;VA0;Vrho0;VA;Va;Vn0;Vnd;S1S3SfSfA2Vit;Vits;A3Vtmp';Vrest;Aa").
Let PAB : Z := ag_pab (aa_geom A).
Let NC : Z := Z.of_nat (length (aa_sec A)).
Let maps : list Z := map sc_map_beg (aa_sec A).
Let pp : Z := fst it - 16.

Definition SCANI (j : nat) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S12S11S43Q40M0A1M1S1fVr;Pd2A2S42G0S39VPAB;S3bZ8M2S3cVj;A1A2A2A2A3S12S11G1S1fVr;Pd5A2S42G0S39VPAB;S3bG2VNC;A2A2A2A3S12S11G1S1fVr;Pd4A2S42G0Sc9S4fSfVj;Vmaps;A3Vpp;A2A2A3S11G1S1fVr;Pd3A2S42G0S50SfVj;Vmaps;Z0A4A2A3A2A2A2").

Lemma J_ro : ltac2:(tb__ "0|0|
S18S18S5S43Q40A1A1S5Sb6A1Sb5S11S98S95S4aS21R4A1A2S95S4aS21R5A1A2A3VK;VA;R5R4R3R2A5Sd2VA0;Vrho0;R6A3VJ;R8R6R5R4A4VJ;R8R7R6R5A4F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr3;Fr;").
Proof. intros r r3 tp tr md EV HK3 HF3 (_ & HC & HR & _). unfold J, JRI. rewrite EV. tauto. Qed.

Lemma maps_nth : ltac2:(tb__ "0|0|
S0S2eS11SbS2eA1S47S2eS2fVA;A1R2A3ScS2eR1A2A3S11SfS50SfR3Vmaps;Z0A4S30R2A1A3F_;Fchj;Fj;").
Proof. intros j chj Hj. unfold maps. apply nth_error_nth. apply map_nth_error. exact Hj. Qed.

Lemma tbl_cell : ltac2:(tb__ "0|2|
S18S0S2eS53VA;Vit;Vi;Vch;R3A5S11SbS2eA1S47S2eS2fVA;A1R3A3ScS2eR2A2A3S12S96S95S4aS21R5A1A2S97S39VPAB;S3bZ8S3cR4A1M0A2A2U8S30R3A1M1A3A2S12S3aG0VNC;A2S12S3aZ0G1A2S3aG1S3dZ2Z2fA2A2A2A2A2F_;F_;Fchj;Fj;Fr;").
Proof.
  intros r j chj QS Hj. pose proof QS as [HG _ _ _ HSR _ _ _ _ _ _ _ _]. destruct HSR as (SC1 & _).
  destruct (SC1 j chj Hj) as (_ & _ & _ & _ & CP & _ & _ & _ & _ & D10 & _ & D12 & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) j) ltac:(rewrite Hj; discriminate)) as LT.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  destruct D10 as (E1 & E2 & _). split; [exact CP|]. unfold NC. split; [lia|]. clear -E1 E2 D12 TG. lia.
Qed.

Lemma cell_carve : ltac2:(tb__ "0|7|
S18S17S17S0S2eS5S19A1S53VA;Vit;Vi;Vch;R6A5Sa3VA;R7A2S4dS1aS20R8A1Sa2Sa9A1A3S11SbS2eA1S47S2eS2fVA;A1R6A3ScS2eR5A2A3S11S43Q40M0A1M1S1bRaR9A2S42G0S39VPAB;S3bZ8M2S3cR7A1A2A2A2A3S11G1S1bRbR9A2S42G0S30R7A1A2A3S11S4Sa4S19S19Sa5R7S61A5S7A3S12S4dSaeSbdRdA1S66RcRbA2M3A3S12S46S19S4bS4cRdS7bVA;Vch;S39VPAB;S3bG2S3cRaA1A2A2A3S54S60S35Vch;A1A1S69A5M4S4eSaeS19SafG3A4S1S3S3S0SfA2M5SfA2M6S2G5SfS2S0SfU9Z0A4G2A4S6G6A1A3A5S46S19S4bG4R8S5fA5A2A2F_;F_;F_;F_;F_;F_;F_;Fobjs;Fchj;Fj;Fv;Fb;Fr4;").
Proof.
  intros r4 b v j chj objs QS HT HF Hj Eb Ev HB.
  destruct (tbl_cell r4 j chj QS Hj) as (CP & LT & MB). pose proof (tbl_nums A it i ch r4 QS) as (P1 & P2 & P3 & _).
  fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in *.
  pose proof (geom_nums _ (qs_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  assert (R : 0x643000 <= PAB + 8 * Z.of_nat j /\ PAB + 8 * Z.of_nat j + 8 <= 2 ^ 47) by (clear -P1 P2 P3 LT TG; lia).
  split; [|split].
  - unfold NSC. apply Forall_cons; [|apply Forall_nil]. unfold carve_okq. lazy beta iota zeta. rewrite Eb, u64_lit by (clear -R; lia).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [clear -R; lia|]. split; [clear -R; lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
    + intros off Hoff. apply (cell_wok_rd (rm r4) (PAB + 8 * Z.of_nat j) 8 (sc_map_beg chj) (PAB + 8 * Z.of_nat j + off) CP); [cbn [Z.of_nat]; lia | clear -R; lia | cbn [Z.of_nat]; clear -R; lia].
    + unfold cells_in_view. apply Forall_cons; [|apply Forall_nil]. intros jj Hjj.
      apply (civ_cell r4 (rm r4) (PAB + 8 * Z.of_nat j) 0 8 (sc_map_beg chj) v); [rewrite Z.add_0_r; exact CP | exact Ev | clear -R; lia | cbn [Z.of_nat]; clear -R; lia | exact Hjj].
  - unfold NSC. cbn [map carve_obj]. apply Forall2_cons; [|apply Forall2_nil]. unfold in_zone. split; [unfold ZUL; cbn; tauto|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
    unfold carved. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite Eb, u64_lit by (clear -R; lia). unfold zbL, zbX. lia.
  - exact (inz_refL A it i ch r4 (PAB + 8 * Z.of_nat j) objs QS HT HF HB).
Qed.

Lemma keepN0 : ltac2:(tb__ "0|0|
SabS11S5S19A1S23SaaR1A1A1S8S19Sa7R1U0A2S4eSa6S19Sa8S6Sa6A1A4A3A3FC;"). Proof. intros C. unfold keepN. rewrite Nat.sub_0_r, firstn_all. cbn [map]. rewrite app_nil_r. reflexivity. Qed.
Lemma VS0_idm : ltac2:(tb__ "0|1|
SacS10S45S10R1S7fA3S45S3S10S17A2M0S2S10S17R2S1eR2A1A4S8G0S9aS7fA1R3A3A3F_;Fv;FMx;").
Proof. intros Mx v Hv. apply in_or_app. left. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. Qed.

Lemma first_glue : ltac2:(tb__ "0|0|
S0S18S18S5S43Q40A1A1Sb4S51R5U2A2S63VA;Vit;Vi;Vch;R5R4A6S7cS4aVJ;S88R7A1R5R4R3A6S14S18S18S12S7cS4aVJ;S81R9A1R1R6R5A6S12S5dR8R1A2Sb0U0R1A2A2A2Lrho2;A2F_;F_;F_;Fw;Ftp;Frho;FrS;Ff;").
Proof.
  intros f rS rho tp [tr [ms md]] Hf EN H. pose proof EN as (QS0 & HT0 & HF0 & KV). destruct (ENVQ_at _ _ _ _ _ _ EN) as (QS & HT & HFp).
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  assert (HJ : J rho tp tr md) by exact (proj2 H).

  destruct (nth_error (aa_sec A) 0) as [ch0|] eqn:E0.
  2:{ exfalso. pose proof (qs_hi _ _ _ _ _ QS) as HI. apply nth_error_None in E0. pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)). lia. }
  destruct (tbl_cell rho 0 ch0 QS E0) as (CP0 & LT0 & MB0).
  pose proof (qs_hv _ _ _ _ _ QS) as (E165 & E200 & E201 & _).
  pose proof (tbl_nums A it i ch rho QS) as (P1 & P2 & P3 & _). fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3.
  pose proof (geom_nums _ (qs_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  assert (HT0' : SPA segsA TJ (LA f) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  destruct (s_step K HL A0 rho0 (zbL A ch (PAB + 8 * Z.of_nat 0)) zloS (zhiX (sc_map_size ch)) ZUL
              (zsepL A it i ch rho (PAB + 8 * Z.of_nat 0) QS ltac:(cbn; lia) ltac:(fold PAB; unfold kPtrArrayReserve; cbn [Z.of_nat]; clear -P3 LT0; lia))
              (T_first f) J [] [Z_to_bv 64 (sc_map_beg ch0)] A rho tp tr ms md (T_first_ok f Hf) (JRI_stable K HL A0 rho0 A a n0 nd (it :: its) tmp' rest) HQW
              (keepN0 (LA f)) eq_refl HT0' HK HFRM (Forall_nil _)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros HK3 HF3 EV3. set (rho3 := rho_absorb rho (map dobj []) (vms md tp ms)) in *.
    set (rho4 := rho_sets rho3 (combine (s_bs (T_first f)) [Z_to_bv 64 (sc_map_beg ch0)])).
    assert (KV4 : KEEPV rS rho4).
    { destruct KV as (KVa & KVl & KVm). split; [|split].
      - intros v Hv. unfold rho4. rewrite rho_sets_other; [exact (KVa v Hv)|]. cbn. intros [<-|[]]. destruct Hv as [Hv|Hv]; [unfold NPRE in Hv; lia | unfold VS0 in Hv; cbn in Hv; intuition discriminate].
      - intros l. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). exact (KVl l).
      - unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). rewrite EV3. exact KVm. }
    destruct (ENVQ_at A it i ch rS rho4 (conj QS0 (conj HT0 (conj HF0 KV4)))) as (QS4 & HT4 & HF4).
    split; [exact (J_ro rho rho3 tp tr md EV3 HK3 HF3 HJ)|].
    pose proof (qs_hv _ _ _ _ _ QS4) as (_ & E200' & _).
    assert (E211 : rw rho4 211%positive = Z_to_bv 64 (sc_map_beg ch0)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
    destruct (cell_carve rho4 vPAB (SVar 211) 0 ch0 (ss_objs (ax_S (s_Cd (T_first f)))) QS4 HT4 HF4 E0
                ltac:(unfold vPAB; cbn [eval Z.of_nat]; rewrite E200'; f_equal; fold PAB; lia) ltac:(cbn [eval]; exact E211) (T_first_ref f Hf)) as (C1 & C2 & C3).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros _. apply Forall_nil. }
  exists rho5. split; [exact H5|]. split.
  - apply (KEEPV_step rS rho (rho_absorb rho (map dobj []) (vms md tp ms)) rho5 (combine (s_bs (T_first f)) [Z_to_bv 64 (sc_map_beg ch0)]) (s_M (T_first f)) KV
             ltac:(intros v; reflexivity) ltac:(intros l; reflexivity) EV); [| exact AG5 | exact RM5 | exact V5 | intros v Hv; exact (VS0_idm _ v Hv)].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[]]. split; [unfold NPRE; lia | unfold VS0; cbn; intuition discriminate].
  - set (rho4 := rho_sets (rho_absorb rho (map dobj []) (vms md tp ms)) (combine (s_bs (T_first f)) [Z_to_bv 64 (sc_map_beg ch0)])) in *.
    assert (OT : forall v, v <> 211%positive -> rw rho4 v = rw rho v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
    assert (E211 : rw rho4 211%positive = Z_to_bv 64 (sc_map_beg ch0)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
    unfold SCANI.
    rewrite (V5 210%positive vPAB ltac:(unfold T_first, M_first; cbn; tauto)), (V5 213%positive (add vPAB (SAlu ALU_SLL vNCH (SLit 3))) ltac:(unfold T_first, M_first; cbn; tauto)),
            (V5 212%positive (SLit 0) ltac:(unfold T_first, M_first; cbn; tauto)), (V5 211%positive (SVar 211) ltac:(unfold T_first, M_first; cbn; tauto)).
    assert (EP : eval rho4 vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; rewrite OT by discriminate; exact E200).
    assert (ENc : eval rho4 vNCH = Z_to_bv 64 NC) by (unfold vNCH; cbn [eval]; rewrite OT by discriminate; exact E201).
    split; [rewrite EP; f_equal; cbn [Z.of_nat]; lia|]. split; [|split; [reflexivity | cbn [eval]; rewrite E211, (maps_nth 0 ch0 E0); reflexivity]].
    apply (eval_add_z rho4 vPAB _ PAB (8 * NC) EP (eval_sll3 rho4 vNCH NC ENc ltac:(clear -P3 LT0; lia))); [clear -P1; lia | clear -LT0; lia | clear -P1 P2 P3 TG; lia].
Qed.

Lemma leaf_facts : ltac2:(tb__ "0|0|
S0S0S18S5S43Q40A1A1Sb4S51R5U2A2S52R5U8A2S7cS4aVJ;S5eR7R6A2R5R4R3A6S4dS1aS20R6A1S65R7A1A3F_;F_;F_;Fw;Ftp;Fr;Fk;Ff;").
Proof.
  intros f k r tp w Hf Hk H. pose proof (SPA_facts_hold segsA _ r (lfL f k) tp w H) as HFa. apply Forall_forall. intros F HF.
  pose proof (proj1 (forallb_forall _ _) (leaf_facts_ok f k Hf Hk) F HF) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
  exact (proj1 (Forall_forall _ _) HFa F Hg).
Qed.

Lemma leaf_vals : ltac2:(tb__ "0|7|
S0S0S0S18S18S5S43Q40M0A1M1A1Sb4S2eS51R8U2A2S52R8U8A2S53VA;Vit;Vi;Vch;R7A5Sb0R9R8A2S11SbS2eA1S47S2eS2fVA;A1M2RaA3ScS2eR5A2A3SadS9aS82A1RaR9A3S7cS4aVJ;S5eReRdA2RaR9R8A6S12S11G1S1bRbS80A2S42G0S39VPAB;S3bZ8M3S3cRdA1A2A2A2A3S12S11G1S1bRbS84A2S42G0S39VPAB;S3bG3VNC;A2A2A2A3S12S11G1S1bRbS7dA2S42G0S30R8A1A2A3S12S11G1S1bRbS62ReA1A2S42G0Sc9S4fSfSdRdA1Vmaps;A3Vpp;A2A2A3S12S11S4ScdReA1M4S7A3S11S0SdReA1M5SaS2eG2A2M6A3F_;S11S4G4SeA3S52G5G6A2F_;A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fchj;Fw;Ftp;Frho';Frho;Fj;Fk;Ff;").
Proof.
  intros f k j rho rho' tp w chj Hf Hk QS (E210 & E213 & E212 & E211) Hj HKp H.
  pose proof (leaf_facts f k rho' tp w Hf Hk H) as HLF.
  assert (KV : forall v, In v VSC -> rw rho' v = rw rho v) by (intros v Hv; rewrite (proj2 HKp v (SVar v) ltac:(unfold idm; apply in_map_iff; exists v; split; [reflexivity | exact Hv])); reflexivity).
  destruct (tbl_cell rho j chj QS Hj) as (CP & LT & MB). pose proof (tbl_nums A it i ch rho QS) as (P1 & P2 & P3 & _).
  fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3.
  pose proof (geom_nums _ (qs_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (qs_hv _ _ _ _ _ QS) as (E165 & _). pose proof (qs_chunk A it i ch rho QS) as (_ & _ & MS & IH & HTG & _). pose proof (qs_hu _ _ _ _ _ QS) as HU.
  assert (EP : eval rho' vPTR = Z_to_bv 64 (PAB + 8 * Z.of_nat j)) by (unfold vPTR; cbn [eval]; rewrite KV by (unfold VSC, VS0; cbn; tauto); exact E210).
  assert (EE : eval rho' vEND = Z_to_bv 64 (PAB + 8 * NC)) by (unfold vEND; cbn [eval]; rewrite KV by (unfold VSC, VS0; cbn; tauto); exact E213).
  assert (EC : eval rho' vCHV = Z_to_bv 64 (sc_map_beg chj)) by (unfold vCHV; cbn [eval]; rewrite KV by (unfold VSC, VS0; cbn; tauto); rewrite E211, (maps_nth j chj Hj); reflexivity).
  assert (ENr : eval rho' vNEAR = Z_to_bv 64 (best (firstn j maps) pp)) by (unfold vNEAR; cbn [eval]; rewrite KV by (unfold VSC, VS0; cbn; tauto); exact E212).
  assert (EI : eval rho' vIT = Z_to_bv 64 pp) by (unfold vIT; cbn [eval]; rewrite KV by (unfold VSC, VS0; cbn; tauto); exact E165).
  assert (PP : 0 <= pp < 2 ^ 47) by (unfold pp; rewrite HU; unfold PG, IMG_HI in *; clear -MS IH HTG TG; lia).
  pose proof (best_range (firstn j maps) pp (proj1 PP)) as BR.
  split; [exact EP|]. split; [exact EE|]. split; [exact EC|]. split.
  - rewrite (upd_of_leaf rho' k pp (best (firstn j maps) pp) (sc_map_beg chj) Hk EI EC ENr BR ltac:(clear -PP; lia) ltac:(clear -MB; lia) HLF).
    f_equal. rewrite <- best_snoc. f_equal. rewrite <- (maps_nth j chj Hj). symmetry. apply firstn_S_nth_Z. unfold maps. rewrite length_map. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
  - unfold LF in HLF. apply Forall_cons_iff in HLF as [F0 _].
    assert (EA : eval rho' (add vPTR (SLit 8)) = Z_to_bv 64 (PAB + 8 * Z.of_nat j + 8)) by (apply ev_add_lit; [exact EP | clear -P1 P2 P3 LT TG; lia | lia | clear -P1 P2 P3 LT TG; lia]).
    assert (EQ : holds rho' EQF <-> S j = length (aa_sec A)).
    { unfold EQF. cbn [holds branch_taken]. unfold bv_eqb. rewrite EA, EE, !u64_lit by (clear -P1 P2 P3 LT TG; lia). rewrite Z.eqb_eq. unfold NC. lia. }
    split; intros EV; rewrite EV in F0.
    + exact (proj1 EQ F0).
    + unfold NC in LT. assert (S j <> length (aa_sec A)) by (intros X; apply F0; exact (proj2 EQ X)). lia.
Qed.

Lemma VSC_VS0 : ltac2:(tb__ "0|0|
S10S45S10R1S7fA3S45S3S10S17A2S2S10S17R2S1eR2A1A4S9aS82A1A3F_;Fv;").
Proof. intros v Hv. unfold idm, VSC. apply in_map_iff. exists v. split; [reflexivity | apply in_or_app; left; exact Hv]. Qed.

Lemma cell_ro : ltac2:(tb__ "0|b|
S18S0S2eS53VA;Vit;Vi;Vch;R3A5S11SbS2eA1S47S2eS2fVA;A1R3A3ScS2eR2A2A3S11S43Q40M0A1M1S1bR5S80A2S42G0S39VPAB;S3bZ8M2S3cR4A1A2A2A2A3S11G1S1bR6S7dA2S42G0S30R4A1A2A3S4dSa6Sc3VA0;R7A2S1S3S3S3S3S17SfA2M3SfA2M4S5S3S3SfS0A2M5S17A2M6A1M7A2M8SfA2M9S2G8SfS2G4G7S2G3SfS2S17SfS80Z0MaA4G2A4S1G6S2G5S17S2SfS0GaU8A4S7dA4S6G6A1A3A4S39VPAB;S3bG2S3cR6A1A2A2A4S6G9A1A3A3F_;F_;F_;F_;Fchj;Fj;Fr;").
Proof.
  intros r j chj QS Hj EP EC. destruct (tbl_cell r j chj QS Hj) as (CP & LT & MB). pose proof (tbl_nums A it i ch r QS) as (P1 & P2 & P3 & P4 & _).
  fold PAB in P1, P2, P4. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3, P4.
  pose proof (geom_nums _ (qs_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  apply Forall_cons; [|apply Forall_nil]. unfold ro_cond.
  split; [exact EP|]. split; [clear -P1 P2 P3 LT TG; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [clear -P1; lia|].
  split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
  - intros z Hz. split; [|clear -Hz P4 P3 LT; lia].
    left. right. right. right. apply HSF. right. left. fold PAB. unfold kPtrArrayReserve. clear -Hz P3 LT. lia.
  - intros z Hz. exists 0, 8%nat, vCHV, (sc_map_beg chj). split; [left; reflexivity|]. split; [cbn [Z.of_nat]; lia|]. split; [exact EC|]. rewrite Z.add_0_r. exact CP.
Qed.

Lemma loop_glue : ltac2:(tb__ "0|2|
S0S0S0S18S18S18S5S43Q40A1A1Sb4S51R8U2A2S45S0R8S1S0U1S1S0U3S1S0U5S1S0U7S6S0A1A3A3A3A3A3S63VA;Vit;Vi;Vch;R7R6A6Sb0R9R7A2S52RaSaS2eS2fVA;A1A2M0A2SadS9aS82A1R9R8A3S7cS4aVJ;S5eReRdA2R9R8R7A6S14S18S18S12S7cS4aVJ;S81R10A1R1RaR9A6S12S5dRdR1A2S12Sb0SdReA1M1R1A2S52G1G0A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FrS;Fj;Fk;Ff;").
Proof.
  intros f k j rS rho rho' tp [tr [ms md]] Hf Hk EN HSC Hj HKp H. pose proof EN as (QS0 & HT0 & HF0 & KV).
  assert (Hk8 : (k < 8)%nat) by (cbn [In] in Hk; lia). assert (Hodd : Nat.even k = false) by (cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [reflexivity|]); destruct Hk).
  pose proof (KEEPV_trans rS rho rho' KV (KEEPV_keepsM _ rho rho' HKp VSC_VS0)) as KV'.
  destruct (ENVQ_at _ _ _ _ _ _ EN) as (QS & _). destruct (ENVQ_at A it i ch rS rho' (conj QS0 (conj HT0 (conj HF0 KV')))) as (QS' & HT' & HFp').
  destruct (nth_error (aa_sec A) j) as [chj|] eqn:Ej; [|exfalso; apply nth_error_None in Ej; lia].
  destruct (leaf_vals f k j rho rho' tp _ chj Hf Hk8 QS HSC Ej HKp H) as (EP & EE & EC & EA3 & _ & HLT). specialize (HLT Hodd).
  destruct (nth_error (aa_sec A) (S j)) as [chn|] eqn:En; [|exfalso; apply nth_error_None in En; lia].
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  assert (HJ : J rho' tp tr md) by exact (proj2 H).
  assert (HT0' : SPA segsA TJ (lfL f k) rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  destruct (tbl_cell rho' (S j) chn QS' En) as (CPn & LTn & MBn).
  pose proof (tbl_nums A it i ch rho' QS') as (P1 & P2 & P3 & _). fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3.
  pose proof (geom_nums _ (qs_hg _ _ _ _ _ QS')) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  set (dsD := [(vPTR, 0, 8, [(0, 8%nat, vCHV)], PAB + 8 * Z.of_nat j)] : list dspec).
  destruct (s_step K HL A0 rho0 (zbL A ch (PAB + 8 * Z.of_nat (S j))) zloS (zhiX (sc_map_size ch)) ZUL
              (zsepL A it i ch rho' (PAB + 8 * Z.of_nat (S j)) QS' ltac:(clear; lia) ltac:(fold PAB; unfold kPtrArrayReserve; clear -P3 LTn; lia))
              (T_loop f k) J dsD [Z_to_bv 64 (sc_map_beg chn)] A rho' tp tr ms md (T_loop_ok f k Hf Hk) (JRI_stable K HL A0 rho0 A a n0 nd (it :: its) tmp' rest) HQW
              (leaf_objs_ok f k Hf Hk8) eq_refl HT0' HK HFRM (cell_ro rho' j chj QS' Ej EP EC)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros HK3 HF3 EV3. set (rho3 := rho_absorb rho' (map dobj dsD) (vms md tp ms)) in *.
    set (rho4 := rho_sets rho3 (combine (s_bs (T_loop f k)) [Z_to_bv 64 (sc_map_beg chn)])).
    assert (KV4 : KEEPV rS rho4).
    { destruct KV' as (KVa & KVl & KVm). split; [|split].
      - intros v Hv. unfold rho4. rewrite rho_sets_other; [exact (KVa v Hv)|]. cbn. intros [<-|[]]. destruct Hv as [Hv|Hv]; [unfold NPRE in Hv; lia | unfold VS0 in Hv; cbn in Hv; intuition discriminate].
      - intros l. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). exact (KVl l).
      - unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). rewrite EV3. exact KVm. }
    destruct (ENVQ_at A it i ch rS rho4 (conj QS0 (conj HT0 (conj HF0 KV4)))) as (QS4 & HT4 & HF4).
    split; [exact (J_ro rho' rho3 tp tr md EV3 HK3 HF3 HJ)|].
    assert (E214 : rw rho4 214%positive = Z_to_bv 64 (sc_map_beg chn)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
    assert (EP4 : eval rho4 vPTR = Z_to_bv 64 (PAB + 8 * Z.of_nat j)) by (rewrite <- EP; unfold vPTR; cbn [eval]; unfold rho4; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; discriminate]).
    destruct (cell_carve rho4 (add vPTR (SLit 8)) (SVar 214) (S j) chn (ss_objs (ax_S (s_Cd (T_loop f k)))) QS4 HT4 HF4 En
                ltac:(replace (PAB + 8 * Z.of_nat (S j)) with (PAB + 8 * Z.of_nat j + 8) by lia; apply ev_add_lit; [exact EP4 | clear -P1 P2 P3 LTn TG; lia | lia | clear -P1 P2 P3 LTn TG; lia])
                ltac:(cbn [eval]; exact E214) (T_loop_ref f k Hf Hk)) as (C1 & C2 & C3).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros _. apply Forall_nil. }
  exists rho5. split; [exact H5|]. split; [|split; [|exact HLT]].
  - apply (KEEPV_step rS rho' (rho_absorb rho' (map dobj dsD) (vms md tp ms)) rho5 (combine (s_bs (T_loop f k)) [Z_to_bv 64 (sc_map_beg chn)]) (s_M (T_loop f k)) KV'
             ltac:(intros v; reflexivity) ltac:(intros l; reflexivity) EV); [| exact AG5 | exact RM5 | exact V5 | intros v Hv; exact (VS0_idm _ v Hv)].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[]]. split; [unfold NPRE; lia | unfold VS0; cbn; intuition discriminate].
  - set (rho4 := rho_sets (rho_absorb rho' (map dobj dsD) (vms md tp ms)) (combine (s_bs (T_loop f k)) [Z_to_bv 64 (sc_map_beg chn)])) in *.
    assert (OT : forall v, v <> 214%positive -> rw rho4 v = rw rho' v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
    assert (E214 : rw rho4 214%positive = Z_to_bv 64 (sc_map_beg chn)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
    assert (EP4 : eval rho4 vPTR = Z_to_bv 64 (PAB + 8 * Z.of_nat j)) by (rewrite <- EP; unfold vPTR; cbn [eval]; apply OT; discriminate).
    assert (EE4 : eval rho4 vEND = Z_to_bv 64 (PAB + 8 * NC)) by (rewrite <- EE; unfold vEND; cbn [eval]; apply OT; discriminate).
    assert (EA4 : eval rho4 (a3_of k) = Z_to_bv 64 (best (firstn (S j) maps) pp)).
    { rewrite <- EA3. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [a3_of]; unfold vCHV, vNEAR; cbn [eval]; apply OT; discriminate|]). destruct Hk. }
    unfold SCANI.
    rewrite (V5 210%positive (add vPTR (SLit 8)) ltac:(unfold T_loop, M_loop; cbn; tauto)), (V5 213%positive vEND ltac:(unfold T_loop, M_loop; cbn; tauto)),
            (V5 212%positive (a3_of k) ltac:(unfold T_loop, M_loop; cbn; tauto)), (V5 211%positive (SVar 214) ltac:(unfold T_loop, M_loop; cbn; tauto)).
    split; [replace (PAB + 8 * Z.of_nat (S j)) with (PAB + 8 * Z.of_nat j + 8) by lia; apply ev_add_lit; [exact EP4 | clear -P1 P2 P3 LTn TG; lia | lia | clear -P1 P2 P3 LTn TG; lia]|].
    split; [exact EE4|]. split; [exact EA4|]. cbn [eval]. rewrite E214, (maps_nth (S j) chn En). reflexivity.
Qed.

Hypothesis HKS : KQ_sec segsA K.
Let G : ageom := aa_geom A.
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Definition ZUXl (l : bool) : list nat := ltac2:(tb__ "0|8|
S4S5S0A1Ll;Vl;S1S0U0M0S1S0U1M1S1S0U2M2S1S0U3M3S1S0U4M4S1S0U5M5S1S0U7M6S6S0A1M7A3A3A3A3A3A3A3S1S0G0S1S0G1S1S0G2S1S0G3S1S0G4S1S0G5S1S0U6S1S0G6S1S0U8G7A3A3A3A3A3A3A3A3A3X4x2").
Definition zbE (lst : sec_chunk) : nat -> Z := ltac2:(tb__ "0|1|
S75S37VG;A1S36VG;A1S31VG;A1Vh;SbcS39VPAB;S3bZ8M0S3cVi;A1A2A2S39VPAB;S3bG0S40VNC;Z1A2A2A2S30Vlst;A1Z0A9").

Lemma lst_facts : ltac2:(tb__ "0|9|
S18S5S43Q40A1A1S5Sb6A1Sb5S2eVK;VA;R5R4R3R2A5S53VA;Vit;Vi;Vch;R6A5S11SbS2eA1S47S2eS2fVA;A1M0S9bSaS2eG0A2U1A2M1A3ScS2eR3A2A3S12S38Sb9S30R4A1M2A2S12S38S39G2S35R4A1M3A2M4S31VG;A1A2S12S38Z12000G3A2S12S13S38G4SbbA2S38SbaG2A2A2S12S13S38G4S37VG;A1M5A2S38S39G5Z1000M6A2G2A2A2S12S13S38G4S36VG;A1M7A2S38S39G7G6A2G2A2A2S12S13S38G4VPAB;A2S38S39VPAB;Sb7A2G2A2A2S12S15S11S0Vi;G1A3A1S13S38S39Vh;Vmsz;A2S30R5A1M8A2S38S39G8S35R5A1A2Vh;A2A2F_;S96S95S4aS21R8A1A2S97S39G2Z18A2U8S3cG1A1A3A2A2A2A2A2A2A2A2A2F_;F_;F_;Flst;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md lst HK QS Hl. pose proof (ks_sep segsA K HKS A r tp tr md HK _ lst Hl) as SEP. cbv zeta in SEP. destruct SEP as (_ & S2 & S3 & S4 & _).
  pose proof QS as [_ _ _ _ HSR HI _ _ HSEP _ _ _ _]. destruct HSR as (SC1 & _).
  destruct (SC1 _ lst Hl) as (_ & _ & _ & C24 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in *; clear -D8 D9; lia)) as BIG. destruct D10 as (_ & _ & _ & _ & DB).
  assert (MS : 73728 <= sc_map_size lst).
  { rewrite D11. unfold round_up, PG in *. pose proof (Z.div_mod (sc_size lst + (4096 - 1)) 4096 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (sc_size lst + (4096 - 1)) 4096 ltac:(lia)). clear -D9 DM H. nia. }
  destruct HSEP as (_ & _ & _ & _ & HJ).
  split; [exact BIG|]. split; [exact D12|]. split; [exact MS|]. split; [exact DB|]. split; [exact S2|]. split; [exact S4|]. split; [exact S3|]. split; [|exact C24].
  intros NE. exact (HJ _ lst Hl NE).
Qed.

Lemma zsepE : ltac2:(tb__ "0|4|
S18S5S43Q40A1A1S5Sb6A1Sb5S4S2eVK;VA;R6R5R4R3A5S53VA;Vit;Vi;Vch;R7A5S11SbS2eA1S47S2eS2fVA;A1M0S9bSaS2eG0A2U1A2M1A3ScS2eR3A2A3S11S4R5SeA3S52Vi;G1A2F_;S0S0S45S0R2Sb2R8A1A3S45S0R2Sb2R9A1A3S15S11S0R4R3A3A1S13S38S39Sb3RaR5A2M2S60Vmsz;R5A2A2S39Sb3RaR4A2M3S54R4A1A2A2S38S39G3S60Vmsz;R4A2A2S39G2S54R5A1A2A2A2F_;F_;F_;Fz';Fz;F_;F_;F_;F_;Flst;Fl;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md l lst HK QS Hl HLT. destruct (lst_facts r tp tr md lst HK QS Hl) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _).
  pose proof (tbl_nums A it i ch r QS) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (qs_nums A it i ch r QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & TC). pose proof (qs_chunk A it i ch r QS) as (_ & _ & MS & IH & HT & HB & _).
  pose proof (geom_bands _ (qs_hg _ _ _ _ _ QS)) as (_ & TB & CB & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (qs_hi _ _ _ _ _ QS); discriminate)) as LTi.
  pose proof QS as [_ _ _ _ _ _ _ _ HSEP _ _ _ _]. destruct HSEP as (_ & HT' & _ & HC' & _).
  assert (Zi : 0 <= Z.of_nat i < NC) by (unfold NC; clear -LTi; lia).
  assert (Zl : l = false -> Z.of_nat i < NC - 1) by (intros E; specialize (HLT E); unfold NC; clear -HLT; lia).
  assert (L8' : l = false -> h + msz <= sc_map_beg lst \/ sc_map_beg lst + sc_map_size lst <= h) by (intros E; specialize (HLT E); apply L8; clear -HLT; lia).
  clear L8 HLT LTi.
  intros z z' Hz Hz' NE. unfold zbE, zbX, zloS, zhiX, IMG_HI, kPtrArrayReserve, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct l; unfold ZUXl in Hz, Hz'; cbn [In] in Hz, Hz'; [clear Zl L8' | specialize (Zl eq_refl); specialize (L8' eq_refl)];
    (repeat (destruct Hz as [<-|Hz]); try (exfalso; exact Hz); repeat (destruct Hz' as [<-|Hz']); try (exfalso; exact Hz'); try (exfalso; apply NE; reflexivity);
     unfold msz, h, G in *;
     first [ solve [clear -T0 T1 C0 C1' TG TI CI TC; lia]
           | solve [clear -TG TB CB T0 C0; lia]
           | solve [clear -MS IH HT HT' HC' HB TG; lia]
           | solve [clear -P1 P2 P3 P4 P5 P6 P7 Zi TG MS; lia]
           | solve [clear -P1 P2 P3 P4 P5 P6 P7 Zi Zl TG MS; lia]
           | solve [clear -L1 L2 L3 L4 L5 L6 L7 P3 Zi TG MS; lia]
           | solve [clear -L1 L2 L3 L4 L5 L6 L7 L8' P3 Zi Zl TG MS; lia] ]).
Qed.

Lemma inz_refE : ltac2:(tb__ "0|0|
S18S4S2eS5S19A1S53VA;Vit;Vi;Vch;R4A5Sa3VA;R5A2S4dS1aS20R6A1Sa2Sa9A1A3S11S4Sa4S19S19Sa5R4S61A5S7A3S46S19S4bS4cR8Sb3R6A1S54S60Vmsz;A1Sb2R7A1A5R5S5fA5F_;F_;F_;F_;Fobjs;Flst;Fl;Fr;").
Proof.
  intros r l lst objs QS HT HF HB. apply (in_zone_same r _ _ _ _ objs REF1 ZD_ref HB).
  apply (in_zone_ext_list r (zbS (ag_thread G) (ag_ctx G) (topG G) h) zloS (zhiS msz) ZUS).
  - unfold REF1, ZD_ref. apply Forall2_app; [exact (inz_fixS A it i ch r HT HF) | exact (inz_N1 A it i ch r QS)].
  - eapply Forall_impl; [|exact ZD_ref_zones]. intros [[z lo] hi] Hz. cbn [fst] in *. cbn [In] in Hz.
    repeat (destruct Hz as [<-|Hz]; [split; [destruct l; unfold ZUXl; cbn; tauto | split; [reflexivity | split; reflexivity]]|]). destruct Hz.
Qed.

Lemma carve1_ok : ltac2:(tb__ "0|b|
S18S17SfSfS5S3S3SfS0A2M0S17A2M1A1M2SfS11S43Q40M3A1M4S1bR6R5A2S42G3R1A2M5A3S12S38Z0R2A2S3aR2S3dZ2Z3eA2M6A2A2S38S41G6A1R6A2S38R7R6A2S3aR7G6A2S38Z643000M7S39R6R9A2A2Sd0RaR9R8A3SfS12S38S39R9RcA2R1A2S3aR1S39R9RbA2A2A2S14SfSfS14S0S0S14SfSfS12S12S12S38S39RdR3A2M8R5A2S3aR5S39G8S3cR2A1A2M9A2A2S12S38G7G8A2S38G9G6A2A2A2S96S95S4aS21R12A1A2S97G8R2R1A3A2A2Lval;A2Lk;A2Loff;A2F_;Fz;S4dG1G1G1OLc;R1G0S17G0OLp;R2SfS0S14SfSfS12S11G4S1bR14R4A2G5A3S96S95S4aS21R14A1A2S97S39RfR3A2R2R1A3A2A2Lval;A2Lk;Loff;X3x1Le;Lp;X3x1Lc;RaA3SbdRfS2S3S3S17SfA2MaSfA2G2S2GaSfS2S17SfReRdA4RcA4RbA4A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbz;Fcs;Fhi;Flo;Fb;Fr;").
Proof.
  intros r b lo hi cs bz Eb Hb L1 L2 L3 L4 CI COV CV. unfold carve_okq. lazy beta iota zeta. rewrite Eb, u64_lit by lia.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CI|]. split.
  - intros off Hoff. destruct (COV (bz + off) ltac:(lia)) as (o & k & val & (Hz & Ho & Hk) & Cc).
    apply (cell_wok_rd (rm r) (bz + o) k val (bz + off) Cc Hz Ho). lia.
  - unfold cells_in_view. apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) CV c Hc) as Z1. pose proof (proj1 (Forall_forall _ _) CI c Hc) as Z2.
    destruct c as [[off k] e]. destruct Z1 as (val & Ee & Cc). destruct Z2 as (B1 & B2 & B3). exact (civ_cell r (rm r) bz off k val e Cc Ee ltac:(lia) ltac:(lia)).
Qed.

Definition XVALS (l : bool) (lst : sec_chunk) (r : valuation) (hT : sv) : Prop := ltac2:(tb__ "0|3|
S12S11S43Q40M0A1M1S1bVr;VhT;A2S42G0Vh;A2A3S12S11G1S1fVr;PcbA2S42G0Vmsz;A2A3S12S11S4Vl;S7A3S11S0Vi;S9bSaS2eS2fVA;A1A2U1A2M2A3F_;S11S4Vl;SeA3S12S52Vi;G2A2S12S11G1S1fVr;PccA2S42G0S3cVi;A1A2A3S12S11G1S1fVr;PcdA2S42G0S30Vlst;A1A2A3S11G1S1fVr;PceA2S42G0S40VNC;Z1A2A2A3A2A2A2F_;A2A2A2").

Lemma exit_carve : ltac2:(tb__ "0|7|
S18S5S43Q40A1A1S5Sb6A1Sb5S4S2eS17S5S19A1VK;VA;R8R7R6R5A5S53VA;Vit;Vi;Vch;R9A5Sa3VA;RaA2S4dS1aS20RbA1Sa2Sa9A1A3S11SbS2eA1S47S2eS2fVA;A1M0S9bSaS2eG0A2U1A2A3ScS2eR7A2A3Sb1R9R8RdR7A4S11S4Sa4S19S19Sa5R7S61A5S7A3S12Sc5RfS68R9A1M1A2S12S4dSaeSbdRfA1S67RbR9A2M2A3S12S4cRfSb3RaA1M3S54S60Vmsz;A1M4Sb2RbA1M5Sc2G1A1S72A7S12S46S19S4bS4cRfG3S54G4G5A5M6S4eSaeS19SafG2A4S71RbA1A5S46S19S4bG6R8S5fA5A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fobjs;FhT;Flst;Fl;Fmd;Ftr;Ftp;Fr4;").
Proof.
  intros r4 tp tr md l lst hT objs HK QS HT HF Hl (EH & E203 & XT & XF) HB.
  destruct (lst_facts r4 tp tr md lst HK QS Hl) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & LC24).
  pose proof (tbl_nums A it i ch r4 QS) as (P1 & P2 & P3 & P4 & _). fold PAB in P1, P2, P4. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3, P4.
  pose proof (qs_chunk A it i ch r4 QS) as (HP & MP & MS & IH & HTG & HBD & _ & _ & C0 & C8 & C24 & CPi & PSH). fold h msz in HP, MP, MS, IH, HTG, HBD, C0, C8, C24, PSH.
  pose proof (geom_nums _ (qs_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (qs_hv _ _ _ _ _ QS) as (_ & E200 & E201 & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (qs_hi _ _ _ _ _ QS); discriminate)) as LTi.
  destruct (tbl_cell r4 _ lst QS Hl) as (CPl & _ & _).
  assert (EM : eval r4 vMS = Z_to_bv 64 msz) by (unfold vMS; cbn [eval]; exact E203).
  assert (EPb : eval r4 vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; exact E200).
  assert (ENc : eval r4 vNCH = Z_to_bv 64 NC) by (unfold vNCH; cbn [eval]; exact E201).
  assert (NCb : 1 <= NC /\ 8 * NC <= 2 ^ 23) by (unfold NC; clear -LTi P3; fold NC in P3; lia).
  assert (M8 : h mod 8 = 0 /\ msz mod 8 = 0).
  { unfold PG in HP, MP. destruct (proj1 (Z.mod_divide h 4096 ltac:(clear; lia)) HP) as [k1 E1]. destruct (proj1 (Z.mod_divide msz 4096 ltac:(clear; lia)) MP) as [k2 E2].
    rewrite E1, E2. replace (k1 * 4096) with (k1 * 512 * 8) by (clear; lia). replace (k2 * 4096) with (k2 * 512 * 8) by (clear; lia). split; apply Z_mod_mult. }
  assert (ELast : eval r4 (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB) = Z_to_bv 64 (8 * NC + PAB)).
  { apply (eval_add_z r4 _ vPAB (8 * NC) PAB (eval_sll3 r4 vNCH NC ENc ltac:(clear -NCb; lia)) EPb); clear -NCb P1 P2 TG; lia. }
  unfold G in L2, L5, L6. unfold IMG_HI, PG, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  assert (HR : 0x643000 <= h /\ h + msz < 2 ^ 47) by (clear -IH HTG TG; lia).
  split; [|split; [|split; [|split]]].
  -
    unfold UX, unk_ok. rewrite soff_lit_small by (clear; lia). rewrite (soff_LENS r4 vMS msz EM ltac:(clear -MS HR; lia)), (eval_BSHS r4 hT h EH ltac:(clear -HR MS; lia)).
    pose proof (Sh_in_band h ltac:(clear -HR MS; lia)) as B1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
    pose proof (Z.div_pos msz 8 ltac:(clear -MS; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -HR IH MS; lia)).
    rewrite u64_lit by (clear -B1; lia).
    split; [clear -H; lia|]. split; [clear -H H0; lia|]. split; [clear -B1; lia|]. split; [clear -B1 H0; lia|].
    intros x Hx. rewrite <- (Sh_add8 h msz (proj1 M8) (proj2 M8)) in Hx. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (h + msz) ltac:(clear -HR IH MS; lia)) as B2. unfold HIGH_SHADOW_END in B2.
    apply (wr_present (rm r4) (Sh h) (Sh (h + msz)) x PSH); [clear -Hx; lia | clear -B1; lia | clear -B2; lia | right; clear -B1; lia].
  -
    unfold NX. apply Forall_app. split.
    + apply Forall_cons; [|apply Forall_nil].
      apply (carve1_ok r4 hT 0 16 _ h EH ltac:(clear -HR MS; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -HR MS; lia)).
      * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
      * intros z Hz. destruct (Z_lt_dec z (h + 8)) as [l0|n]; [exists 0, 8%nat, h; split; [cbn [Z.of_nat]; clear -Hz HR MS l0; lia | rewrite Z.add_0_r; exact C0] | exists 8, 8%nat, msz; split; [cbn [Z.of_nat]; clear -Hz HR MS n; lia | exact C8]].
      * repeat apply Forall_cons; try apply Forall_nil; [exists h; rewrite Z.add_0_r; split; [exact EH | exact C0] | exists msz; split; [exact EM | exact C8]].
    + destruct l.
      * specialize (XT eq_refl). assert (Ei : Z.of_nat i = NC - 1) by (unfold NC; clear -XT LTi; lia).
        assert (Elst : lst = ch) by (rewrite <- XT in Hl; rewrite (qs_hi _ _ _ _ _ QS) in Hl; injection Hl as <-; reflexivity).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (carve1_ok r4 hT 24 32 _ h EH ltac:(clear -HR MS; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -HR MS; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 24, 8%nat, (Z.of_nat i). split; [cbn [Z.of_nat]; clear -Hz HR MS; lia | exact C24].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (Z.of_nat i). split; [|exact C24]. rewrite Ei. apply ev_add_lit; [exact ENc | clear -NCb; lia | lia | clear -NCb; lia].
        -- apply (carve1_ok r4 _ (-8) 0 _ (8 * NC + PAB) ELast ltac:(clear -NCb P1 P2 TG; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -NCb P1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists (-8), 8%nat, h. split; [cbn [Z.of_nat]; clear -Hz NCb P1 P2 TG; lia|]. replace (8 * NC + PAB + -8) with (PAB + 8 * Z.of_nat i) by (clear -Ei; lia). exact CPi.
           ++ repeat apply Forall_cons; try apply Forall_nil. exists h. split; [exact EH|]. replace (8 * NC + PAB + -8) with (PAB + 8 * Z.of_nat i) by (clear -Ei; lia). exact CPi.
      * destruct (XF eq_refl) as (XLT & E204 & E205 & E206). assert (Ei : Z.of_nat i < NC - 1) by (unfold NC; clear -XLT; lia).
        assert (ELn : Z.of_nat (length (aa_sec A) - 1) = NC - 1) by (unfold NC; clear -LTi; lia). rewrite ELn in LC24, CPl.
        assert (EIdx : eval r4 (add vPAB (SAlu ALU_SLL vIDX (SLit 3))) = Z_to_bv 64 (PAB + 8 * Z.of_nat i)).
        { apply (eval_add_z r4 vPAB _ PAB (8 * Z.of_nat i) EPb (eval_sll3 r4 vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(clear -NCb Ei; lia))); clear -NCb P1 P2 TG Ei; lia. }
        assert (ELa : eval r4 vLAST = Z_to_bv 64 (sc_map_beg lst)) by (unfold vLAST; cbn [eval]; exact E205).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (carve1_ok r4 hT 24 32 _ h EH ltac:(clear -HR MS; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -HR MS; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 24, 8%nat, (Z.of_nat i). split; [cbn [Z.of_nat]; clear -Hz HR MS; lia | exact C24].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (Z.of_nat i). split; [unfold vIDX; cbn [eval]; exact E204 | exact C24].
        -- apply (carve1_ok r4 _ 0 8 _ (PAB + 8 * Z.of_nat i) EIdx ltac:(clear -NCb P1 P2 TG Ei; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -P1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 0, 8%nat, h. split; [cbn [Z.of_nat]; clear -Hz NCb P1 P2 TG Ei; lia | rewrite Z.add_0_r; exact CPi].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists h. rewrite Z.add_0_r. split; [exact EH | exact CPi].
        -- apply (carve1_ok r4 _ (-8) 0 _ (8 * NC + PAB) ELast ltac:(clear -NCb P1 P2 TG; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -NCb P1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists (-8), 8%nat, (sc_map_beg lst). split; [cbn [Z.of_nat]; clear -Hz NCb P1 P2 TG; lia|]. replace (8 * NC + PAB + -8) with (PAB + 8 * (NC - 1)) by (clear; lia). exact CPl.
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (sc_map_beg lst). split; [exact ELa|]. replace (8 * NC + PAB + -8) with (PAB + 8 * (NC - 1)) by (clear; lia). exact CPl.
        -- apply (carve1_ok r4 vLAST 24 32 _ (sc_map_beg lst) ELa ltac:(clear -L1 L2 L3 TG; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -L1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 24, 8%nat, (NC - 1). split; [cbn [Z.of_nat]; clear -Hz L1 L2 L3 TG; lia | exact LC24].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (NC - 1). split; [unfold vLIDX; cbn [eval]; exact E206 | exact LC24].
  -
    unfold UX, uobj, ZDU, in_zone. split; [destruct l; unfold ZUXl; cbn [In]; clear; tauto|]. split; [cbn; clear; lia|]. split; [cbn; clear; lia|]. right.
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_LENS r4 vMS msz EM ltac:(clear -MS HR; lia)), (eval_BSHS r4 hT h EH ltac:(clear -HR MS; lia)).
    pose proof (Sh_in_band h ltac:(clear -HR MS; lia)) as B1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (h + msz) ltac:(clear -HR IH MS; lia)) as B2. unfold HIGH_SHADOW_END in B2. rewrite (Sh_add8 h msz (proj1 M8) (proj2 M8)) in B2.
    rewrite u64_lit by (clear -B1; lia). unfold zbE, zbX, LOW_SHADOW_BEG. clear -B1 B2. lia.
  -
    unfold NX, ZDNX. cbn [map carve_obj app]. destruct l; cbn [map carve_obj app].
    + specialize (XT eq_refl). assert (Ei : Z.of_nat i = NC - 1) by (unfold NC; clear -XT LTi; lia).
      repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone; (split; [unfold ZUXl; cbn [In]; clear; tauto|]); (split; [cbn; clear -MS; lia|]); (split; [cbn; fold msz; clear -MS; lia|]); right;
        unfold carved; rewrite obj_range_mk by (clear; lia); cbn [fst snd]; rewrite ?EH, ?ELast, ?u64_lit by (clear -HR MS NCb P1 P2 TG; lia); unfold zbE, zbX; clear -Ei; lia.
    + destruct (XF eq_refl) as (XLT & E204 & E205 & E206). assert (Ei : Z.of_nat i < NC - 1) by (unfold NC; clear -XLT; lia).
      assert (EIdx : eval r4 (add vPAB (SAlu ALU_SLL vIDX (SLit 3))) = Z_to_bv 64 (PAB + 8 * Z.of_nat i)).
      { apply (eval_add_z r4 vPAB _ PAB (8 * Z.of_nat i) EPb (eval_sll3 r4 vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(clear -NCb Ei; lia))); clear -NCb P1 P2 TG Ei; lia. }
      assert (ELa : eval r4 vLAST = Z_to_bv 64 (sc_map_beg lst)) by (unfold vLAST; cbn [eval]; exact E205).
      repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone; (split; [unfold ZUXl; cbn [In]; clear; tauto|]); (split; [cbn; clear -MS; lia|]); (split; [cbn; fold msz; clear -MS; lia|]); right;
        unfold carved; rewrite obj_range_mk by (clear; lia); cbn [fst snd]; rewrite ?EH, ?ELast, ?EIdx, ?ELa, ?u64_lit by (clear -HR MS NCb P1 P2 TG Ei L1 L2 L3; lia); unfold zbE, zbX; clear; lia.
  - exact (inz_refE r4 l lst objs QS HT HF HB).
Qed.

Lemma exit_facts : ltac2:(tb__ "0|0|
S18S0S4S2eS10S51R4U2A2S53VA;Vit;Vi;Vch;R6A5S55R6S34S33VA;A1A1Vh;Vmsz;A4Sb1R6R5R8S1eR4A1A4S4dS1aS20R9A1S64R8R7R5A3A3F_;F_;F_;F_;Fhv;Flst;Fl;Ff;Fr4;").
Proof.
  intros r4 f l lst hv Hf QS HFAM (EH & E203 & XT & XF).
  pose proof (qs_chunk A it i ch r4 QS) as (HP & MP & MS & IH & HTG & _). fold h msz in HP, MP, MS, IH, HTG.
  pose proof (geom_nums _ (qs_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  pose proof (qs_hv _ _ _ _ _ QS) as (E165 & _ & E201 & _). pose proof (qs_hrig _ _ _ _ _ QS) as (_ & _ & E155 & _). pose proof (qs_hu _ _ _ _ _ QS) as HU. fold h in HU.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (qs_hi _ _ _ _ _ QS); discriminate)) as LTi.
  pose proof (tbl_nums A it i ch r4 QS) as (_ & _ & P3 & _). fold NC in P3. unfold kPtrArrayReserve in P3.
  unfold IMG_HI, PG, HIGH_SHADOW_END, TOPMAX in *.
  assert (EM : eval r4 vMS = Z_to_bv 64 msz) by (unfold vMS; cbn [eval]; exact E203).
  assert (EI : eval r4 vIT = Z_to_bv 64 (h + 6128)) by (unfold vIT; cbn [eval]; rewrite E165, HU; f_equal; clear; lia).
  assert (ES : eval r4 vSB = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by (unfold vSB; cbn [eval]; exact E155).
  assert (HR : 0x643000 <= h /\ h + msz <= 140737479966720 /\ 73728 <= msz) by (clear -IH HTG TG MS; lia).
  assert (EA1 : eval r4 (add (SVar hv) vMS) = Z_to_bv 64 (h + msz)) by (apply (eval_add_z r4 _ vMS h msz EH EM); clear -HR; lia).
  assert (EA2 : eval r4 (add vMS (SVar hv)) = Z_to_bv 64 (msz + h)) by (apply (eval_add_z r4 vMS _ msz h EM EH); clear -HR; lia).
  assert (EA3 : eval r4 (add (SVar hv) (SLit 4096)) = Z_to_bv 64 (h + 4096)) by (apply ev_add_lit; [exact EH | clear -HR; lia | clear; lia | clear -HR; lia]).
  assert (M8 : h mod 8 = 0 /\ msz mod 8 = 0).
  { destruct (proj1 (Z.mod_divide h 4096 ltac:(clear; lia)) HP) as [k1 E1]. destruct (proj1 (Z.mod_divide msz 4096 ltac:(clear; lia)) MP) as [k2 E2].
    rewrite E1, E2. replace (k1 * 4096) with (k1 * 512 * 8) by (clear; lia). replace (k2 * 4096) with (k2 * 512 * 8) by (clear; lia). split; apply Z_mod_mult. }
  unfold F2X. cbv zeta. apply Forall_app. split; [|apply Forall_app; split].
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (F_lenX_holds r4 (SVar hv) h msz EH EM); [clear -HR; lia | clear -HR; lia | clear -HR; lia | exact (proj1 M8) | exact (proj2 M8)].
    + apply (hne0 r4 _ h EH). clear -HR. lia.
    + apply (hle r4 _ vIT h (h + 6128) EH EI); clear -HR; lia.
    + apply (hlt r4 vIT _ (h + 6128) (h + msz) EI EA1); clear -HR; lia.
    + cbn [holds]. split; [clear; lia|]. cbn [eval] in EH. rewrite EH, u64_lit by (clear -HR; lia). change (2 ^ 12) with 4096. exact HP.
    + cbn [holds]. split; [clear; lia|]. rewrite E203, u64_lit by (clear -HR; lia). change (2 ^ 12) with 4096. exact MP.
    + apply (hle r4 _ vMS 73728 msz (elit r4 _) EM); clear -HR; lia.
    + apply (hle r4 vMS _ msz 140737479966720 EM (elit r4 _)); clear -HR; lia.
    + apply (hle r4 _ (SVar hv) 0x643000 h (elit r4 _) EH); clear -HR; lia.
    + apply (hle r4 _ _ (h + msz) 140737479966720 EA1 (elit r4 _)); clear -HR; lia.
    + apply (hle r4 _ _ (msz + h) 140737479966720 EA2 (elit r4 _)); clear -HR; lia.
  - unfold F_hX. destruct f as [|[|[|f]]]; [| | | exfalso; clear -Hf; lia]; cbn [fam_ok] in HFAM; repeat apply Forall_cons; try apply Forall_nil.
    + apply (hle r4 _ _ (h + msz) 0x7fff7000 EA1 (elit r4 _)); clear -HR HFAM; lia.
    + apply (hle r4 _ _ (msz + h) 0x7fff7000 EA2 (elit r4 _)); clear -HR HFAM; lia.
    + apply (hlt r4 _ vSB (h + 4096) (ag_spacebeg (aa_geom A)) EA3 ES); clear -HR HFAM S1 S2 TG; lia.
    + apply (hle r4 _ (SVar hv) 0x10007fff8000 h (elit r4 _) EH); clear -HR HFAM; lia.
    + apply (hlt r4 _ vSB (h + 4096) (ag_spacebeg (aa_geom A)) EA3 ES); clear -HR HFAM S1 S2 TG; lia.
    + apply (hle r4 _ (SVar hv) 0x10007fff8000 h (elit r4 _) EH); clear -HR HFAM S1 S2; lia.
    + apply (hle r4 (add vSB (SLit (2 ^ 37))) _ (ag_spacebeg (aa_geom A) + 2 ^ 37) (h + 4096)); [apply ev_add_lit; [exact ES | clear -S1 S2 TG; lia | clear; lia | clear -S1 S2 TG; lia] | exact EA3 | clear -S1 S2 TG; lia | clear -HR; lia | clear -HFAM; lia].
  - destruct l; [apply Forall_nil|]. destruct (XF eq_refl) as (XLT & E204 & _). apply Forall_cons; [|apply Forall_nil].
    apply (hlt r4 vIDX _ (Z.of_nat i) (NC - 1)); [unfold vIDX; cbn [eval]; exact E204 | apply ev_add_lit; [unfold vNCH; cbn [eval]; exact E201 | | clear; lia |] | | |]; unfold NC in *; clear -XLT LTi P3; lia.
Qed.

Lemma exit_glue : ltac2:(tb__ "0|4|
S0S0S4S0S2eS18S18S18S5S43Q40A1A1Sb4S51RaU2M0A2S45S0RaS1S0U0S1S0G0S1S0U4S1S0U6S6S0A1A3A3A3A3A3S63VA;Vit;Vi;Vch;R7R6A6Sb0RaR7A2S52RbSaS2eS2fVA;A1M1A2M2A2SadS9aS82A1R9R8A3S7cS4aVJ;S5eR10RfA2R9R8R7A6S55R11S34S33VA;A1A1Vh;Vmsz;A4S11SbS2eA1S47S2eG1S9bG2U1A2M3A3ScS2eReA2A3S16S11S4R11S7A3S11S0Vi;G3A3A2S14S18S18S12S7cS4aVJ;S89R15R13A2R1RdRcA6S12S5dR10R1A2Sb1R13R11R1S8eA4A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FrS;Flst;Fj;Fl;Fk;Ff;").
Proof.
  intros f k l j lst rS rho rho' tp [tr [ms md]] Hf Hk EN HSC Hj HKp H HFAM Hl HLI. pose proof EN as (QS0 & HT0 & HF0 & KV).
  assert (Hk8 : (k < 8)%nat) by (cbn [In] in Hk; lia). assert (Hev : Nat.even k = true) by (cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [reflexivity|]); destruct Hk).
  pose proof (KEEPV_trans rS rho rho' KV (KEEPV_keepsM _ rho rho' HKp VSC_VS0)) as KV'.
  destruct (ENVQ_at _ _ _ _ _ _ EN) as (QS & _). destruct (ENVQ_at A it i ch rS rho' (conj QS0 (conj HT0 (conj HF0 KV')))) as (QS' & HT' & HFp').
  destruct (nth_error (aa_sec A) j) as [chj|] eqn:Ej; [|exfalso; apply nth_error_None in Ej; lia].
  destruct (leaf_vals f k j rho rho' tp _ chj Hf Hk8 QS HSC Ej HKp H) as (EP & EE & EC & EA3 & HEQ & _). specialize (HEQ Hev).

  pose proof (qs_chunk A it i ch rho' QS') as (_ & _ & MS & IH & HTG & _). fold h msz in MS, IH, HTG. pose proof (qs_hu _ _ _ _ _ QS') as HU. fold h in HU.
  assert (EH : eval rho' (a3_of k) = Z_to_bv 64 h).
  { rewrite EA3. f_equal. rewrite HEQ. unfold maps. rewrite <- (length_map sc_map_beg), firstn_all.
    apply (chunk_is_best (aa_sec A) i ch pp (qs_hi _ _ _ _ _ QS')); [unfold pp; fold h msz; rewrite HU; unfold PG; clear -MS; lia | fold h; unfold IMG_HI in IH; clear -IH; lia | |].
    - pose proof QS' as [_ _ _ _ _ _ _ _ HSEP _ _ _ _]. destruct HSEP as (_ & _ & _ & _ & HJx). exact HJx.
    - intros j' ch' Hj'. pose proof QS' as [_ _ _ _ HSR _ _ _ _ _ _ _ _]. destruct HSR as (SC1 & _).
      destruct (SC1 j' ch' Hj') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). destruct D10 as (_ & D & _). exact D. }
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  assert (HJ : J rho' tp tr md) by exact (proj2 H).
  assert (HT0' : SPA segsA TJ (lfL f k) rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (qs_hi _ _ _ _ _ QS'); discriminate)) as LTi.
  assert (HLF : l = false -> (i < length (aa_sec A) - 1)%nat).
  { intros ->. destruct (Nat.eq_dec i (length (aa_sec A) - 1)) as [E|NE]; [pose proof (proj2 HLI E); discriminate | clear -NE LTi; lia]. }
  set (dsD := [(vPTR, 0, 8, [(0, 8%nat, vCHV)], PAB + 8 * Z.of_nat j)] : list dspec).
  set (vals := [Z_to_bv 64 msz] ++ (if l then [] else [Z_to_bv 64 (Z.of_nat i); Z_to_bv 64 (sc_map_beg lst); Z_to_bv 64 (NC - 1)])).
  assert (LV : length vals = length (s_bs (T_exit f k l))) by (unfold vals, T_exit, BSX; destruct l; reflexivity).
  assert (NDB : List.NoDup (map fst (combine (s_bs (T_exit f k l)) vals))) by (unfold vals, T_exit, BSX; destruct l; cbn; repeat constructor; cbn; intuition discriminate).
  assert (INB : forall v, In v (map fst (combine (s_bs (T_exit f k l)) vals)) -> In v [203; 204; 205; 206]%positive) by (intros v; unfold vals, T_exit, BSX; destruct l; cbn; tauto).
  destruct (s_stepU K HL A0 rho0 (zbE lst) zloS (zhiX msz) (ZUXl l) (zsepE rho' tp tr md l lst HK QS' Hl HLF)
              (T_exit f k l) (UX (a3_of k)) ZDU J dsD vals A rho' tp tr ms md (T_exit_ok f k l Hf Hk) (JRI_stable K HL A0 rho0 A a n0 nd (it :: its) tmp' rest) HQW
              (leaf_objs_ok f k Hf Hk8) LV HT0' HK HFRM (cell_ro rho' j chj QS' Ej EP EC)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros HK3 HF3 EV3. set (rho3 := rho_absorb rho' (map dobj dsD) (vms md tp ms)) in *.
    set (rho4 := rho_sets rho3 (combine (s_bs (T_exit f k l)) vals)) in *.
    assert (OT : forall v, ~ In v [203; 204; 205; 206]%positive -> rw rho4 v = rw rho' v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [reflexivity | intros X; exact (Hv (INB v X))]).
    assert (KV4 : KEEPV rS rho4).
    { destruct KV' as (KVa & KVl & KVm). split; [|split].
      - intros v Hv. rewrite OT; [exact (KVa v Hv)|]. intros X. cbn [In] in X. destruct Hv as [Hv|Hv]; [unfold NPRE in Hv; clear -X Hv; lia | unfold VS0 in Hv; cbn in Hv; clear -X Hv; intuition (subst; discriminate)].
      - intros l0. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). exact (KVl l0).
      - unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). rewrite EV3. exact KVm. }
    destruct (ENVQ_at A it i ch rS rho4 (conj QS0 (conj HT0 (conj HF0 KV4)))) as (QS4 & HT4 & HF4).
    assert (HK4 : K A rho4 tp tr md).
    { apply (kq_stable segsA K HL A rho3 rho4 tp tr md md); [|apply mat_equiv_refl | exact HK3]. split; [|split].
      - intros v Hv. symmetry. unfold rho4. rewrite rho_sets_other; [reflexivity|]. intros X. pose proof (INB v X) as Y. cbn [In] in Y. unfold QNPRE in Hv. clear -Y Hv. lia.
      - intros l0. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). reflexivity.
      - intros x. unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). reflexivity. }
    assert (XV4 : XVALS l lst rho4 (a3_of k)).
    { split; [rewrite <- EH; rewrite a3_hv; cbn [eval]; apply OT; cbn [In]; destruct k as [|[|[|[|k]]]]; cbn [hv_of]; clear; intuition discriminate|].
      split; [unfold rho4; apply rho_sets_get; [exact NDB | unfold vals, T_exit, BSX; destruct l; cbn; tauto]|].
      split; [intros E; exact (proj1 HLI E)|]. intros E. split; [exact (HLF E)|]. subst l.
      split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]|]. split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto] | unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]]. }
    split; [exact (J_ro rho' rho3 tp tr md EV3 HK3 HF3 HJ)|].
    destruct (exit_carve rho4 tp tr md l lst (a3_of k) (ss_objs (ax_S (s_Cd (T_exit f k l)))) HK4 QS4 HT4 HF4 Hl XV4 (T_exit_ref f k l Hf Hk)) as (C1 & C2 & C3 & C4 & C5).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. intros _.
    rewrite a3_hv in XV4. exact (exit_facts rho4 f l lst (hv_of k) Hf QS4 HFAM XV4). }
  exists rho5. split; [exact H5|]. split.
  - apply (KEEPV_step rS rho' (rho_absorb rho' (map dobj dsD) (vms md tp ms)) rho5 (combine (s_bs (T_exit f k l)) vals) (s_M (T_exit f k l)) KV'
             ltac:(intros v; reflexivity) ltac:(intros l0; reflexivity) EV); [| exact AG5 | exact RM5 | exact V5 | intros v Hv; exact (VS0_idm _ v Hv)].
    intros v Hv. pose proof (INB v Hv) as Y. cbn [In] in Y. split; [unfold NPRE; clear -Y; lia | unfold VS0; cbn; clear -Y; intuition (subst; discriminate)].
  - set (rho4 := rho_sets (rho_absorb rho' (map dobj dsD) (vms md tp ms)) (combine (s_bs (T_exit f k l)) vals)) in *.
    assert (OT : forall v, ~ In v [203; 204; 205; 206]%positive -> rw rho4 v = rw rho' v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [reflexivity | intros X; exact (Hv (INB v X))]).
    unfold XVALS. unfold vH. cbn [eval].
    rewrite (V5 202%positive (a3_of k) ltac:(unfold T_exit, M_exit; cbn [s_M]; apply in_or_app; right; cbn; tauto)).
    rewrite (V5 203%positive vMS ltac:(unfold T_exit, M_exit; cbn [s_M]; apply in_or_app; right; cbn; tauto)).
    split; [rewrite <- EH; rewrite a3_hv; cbn [eval]; apply OT; cbn [In]; destruct k as [|[|[|[|k]]]]; cbn [hv_of]; clear; intuition discriminate|].
    split; [unfold vMS; cbn [eval]; unfold rho4; apply rho_sets_get; [exact NDB | unfold vals, T_exit, BSX; destruct l; cbn; tauto]|].
    split; [intros E; exact (proj1 HLI E)|]. intros E. split; [exact (HLF E)|]. subst l.
    rewrite (V5 204%positive vIDX ltac:(unfold T_exit, M_exit; cbn [s_M]; apply in_or_app; right; apply in_or_app; right; cbn; tauto)).
    rewrite (V5 205%positive vLAST ltac:(unfold T_exit, M_exit; cbn [s_M]; apply in_or_app; right; apply in_or_app; right; cbn; tauto)).
    rewrite (V5 206%positive vLIDX ltac:(unfold T_exit, M_exit; cbn [s_M]; apply in_or_app; right; apply in_or_app; right; cbn; tauto)).
    unfold vIDX, vLAST, vLIDX. cbn [eval].
    split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]|]. split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto] | unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]].
Qed.

Context {Q : assn} (X : trk Q).
Hypothesis HJX : JOK X J.

Lemma TsPL_In : ltac2:(tb__ "0|0|
S0SabSacS51R3U2A2S45S3SabSacA2S2SabSacR3R2A4S94R4A1A3S14S0S0S12S52R1U8A2S12S11SabR5S5eR6R1A2A3S11SacR4S9aS82A1A3A2A2Lk;A2F_;F_;FM;FT;Ff;").
Proof.
  intros f T M Hf HIN. unfold TsPL in HIN. apply in_map_iff in HIN as (T0 & E & HIN). injection E as <- <-.
  destruct (In_nth _ _ (SC f) HIN) as (k & Hk & Ek). rewrite (LL_len f Hf) in Hk. exists k. split; [exact Hk|]. split; [symmetry; exact Ek | reflexivity].
Qed.

Section Scan.
Variables (f : nat) (rS : valuation) (tp : list word).
Hypothesis Hf : (f <= 2)%nat.
Hypothesis HFAM : ltac2:(tb__ "0|0|
S55Vf;S34S33VA;A1A1Vh;Vmsz;A4").

Hypothesis HXC : ltac2:(tb__ "0|2|
S4S2eS18S11SbS2eA1S47S2eS2fVA;A1M0S9bSaS2eG0A2U1A2M1A3ScS2eR2A2A3S16S11S4R4S7A3S11S0Vi;G1A3A2S5dVrS;R3A2Sb1R6R5R4S8eA4Sc7VQ;VX;S7cS4aVJ;S89Vf;R7A2R5Vtp;A5A3F_;F_;F_;F_;Frho2;Flst;Fl;").

Lemma scan_loop : ltac2:(tb__ "0|1|
S0S0S18S11S0R3S9bS9bSaS2eS2fVA;A1A2M0U1A2R2A2A3S52R3G0A2S63VA;Vit;Vi;Vch;VrS;R3A6Sb0R5R4A2Sc7VQ;VX;S7cS4aVJ;S81Vf;A1R5Vtp;A5A3F_;F_;F_;F_;Frho;Fj;Fm;").
Proof.
  induction m as [|m IH]; intros j rho Hm Hj EN HSC; apply (seg_PL X f J rho tp HJX); intros T M rho' HIN HKp;
    destruct (TsPL_In f T M Hf HIN) as (k & Hk & -> & ->); pose proof EN as (QS0 & HT0 & HF0 & KV);
    (assert (EL : exists lst, nth_error (aa_sec A) (length (aa_sec A) - 1) = Some lst) by (destruct (nth_error (aa_sec A) (length (aa_sec A) - 1)) as [lst|] eqn:El; [exists lst; reflexivity | exfalso; apply nth_error_None in El; clear -El Hj; lia]));
    destruct EL as [lst El];
    destruct (Nat.even k) eqn:Ev.
  -
    assert (Hk' : In k [0; 2; 4; 6]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_glue X _ J (SX f (Nat.eqb i (length (aa_sec A) - 1))) tp (fun r => KEEPV rS r /\ XVALS (Nat.eqb i (length (aa_sec A) - 1)) lst r vH)).
    + intros w Hw. destruct (exit_glue f k (Nat.eqb i (length (aa_sec A) - 1)) j lst rS rho rho' tp w Hf Hk' EN HSC Hj HKp Hw HFAM El ltac:(apply Nat.eqb_eq)) as (rho2 & H2 & K2 & X2).
      exists rho2. split; [exact H2 | split; [exact K2 | exact X2]].
    + intros r [R1 R2]. exact (HXC _ lst r El ltac:(apply Nat.eqb_eq) R1 R2).
  -
    assert (Hk' : In k [1; 3; 5; 7]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_pure X _ False); [|intros []]. intros w Hw.
    destruct (loop_glue f k j rS rho rho' tp w Hf Hk' EN HSC Hj HKp Hw) as (_ & _ & _ & _ & LT). clear -LT Hm. lia.
  - assert (Hk' : In k [0; 2; 4; 6]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_glue X _ J (SX f (Nat.eqb i (length (aa_sec A) - 1))) tp (fun r => KEEPV rS r /\ XVALS (Nat.eqb i (length (aa_sec A) - 1)) lst r vH)).
    + intros w Hw. destruct (exit_glue f k (Nat.eqb i (length (aa_sec A) - 1)) j lst rS rho rho' tp w Hf Hk' EN HSC Hj HKp Hw HFAM El ltac:(apply Nat.eqb_eq)) as (rho2 & H2 & K2 & X2).
      exists rho2. split; [exact H2 | split; [exact K2 | exact X2]].
    + intros r [R1 R2]. exact (HXC _ lst r El ltac:(apply Nat.eqb_eq) R1 R2).
  -
    assert (Hk' : In k [1; 3; 5; 7]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_glue X _ J (SC f) tp (fun r => KEEPV rS r /\ SCANI (S j) r /\ (S j < length (aa_sec A))%nat)).
    + intros w Hw. destruct (loop_glue f k j rS rho rho' tp w Hf Hk' EN HSC Hj HKp Hw) as (rho2 & H2 & K2 & S2 & L2). exists rho2. tauto.
    + intros r (R1 & R2 & R3). apply (IH (S j) r); [clear -Hm R3; lia | exact R3 | exact (conj QS0 (conj HT0 (conj HF0 R1))) | exact R2].
Qed.

Theorem scan_all : ltac2:(tb__ "0|0|
S18S63VA;Vit;Vi;Vch;VrS;R1A6Sc7VQ;VX;S7cS4aVJ;S88Vf;A1R2Vtp;A5A3F_;Frho;").
Proof.
  intros rho EN. pose proof EN as (QS0 & HT0 & HF0 & KV).
  apply (tr_glue X _ J (SC f) tp (fun r => KEEPV rS r /\ SCANI 0 r)).
  - intros w Hw. destruct (first_glue f rS rho tp w Hf EN Hw) as (rho2 & H2 & K2 & S2). exists rho2. tauto.
  - intros r [R1 R2]. pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (qs_hi _ _ _ _ _ QS0); discriminate)) as LTi.
    apply (scan_loop (length (aa_sec A) - 1 - 0) 0 r eq_refl ltac:(clear -LTi; lia) (conj QS0 (conj HT0 (conj HF0 R1))) R2).
Qed.
End Scan.
End Loop.
End SegQS_loop.

(* [comment removed for export] *)
Module SpineMallocR12.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "div"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "length"; "list"; "nil"; "Some"; "option"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "eval"; "ss_next"; "sv"; "sprop"; "valuation"; "ss_facts"; "ss_lenient"; "SMd"; "SPNot"; "SVar"; "holds"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_free_array"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "gh_new"; "JR"; "entryR"; "ghosts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vNEW"; "GR"; "F_new"; "cD"; "vAU"; "vMFA"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12"; "F_geu"; "need_e"; "new_e"; "facap_okb"; "rup_e"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "CLS30"; "FACAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws PrimCredit PrimCreditLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition new_e : sv := ltac2:(tb__ "0|0|
S25S37S1cS36S1cS33S3fS1dZ40000A1A3S3dA3S27S4eA1A3").
Definition need_e : sv := ltac2:(tb__ "0|0|
S1cS35S1cS33S40S39A3S1dZ2A1A3").
Definition F_geu : sprop := SPBranch BC_GEU vMFA need_e.
Definition rup_e : sv := ltac2:(tb__ "0|0|
S1cS34S1cS33S42S1dZ3ffffA1A3S1dZfffffffffffc0000A1A3").

Definition facap_okb (c : Z) : bool := FACAP c <=? 536608768.
Lemma facap_okb_all : ltac2:(tb__ "0|0|
S2S11S49S0S44S50A3S13A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma facap_room : ltac2:(tb__ "0|0|
S0S1S5Z1R1A2S5R1Z1eA2A2S5S51R2A1Z1ffc0000A2F_;Fc;").
Proof. intros c Hc. pose proof (proj1 (forallb_forall _ _) facap_okb_all c (proj2 (In_CLS30 c) Hc)) as H. apply Z.leb_le in H. exact H. Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S53VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S32VA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma new_nums : ltac2:(tb__ "0|5|
S4fVc;A1S0S8S14S0S2bVcs;A1A2A1S0S2dVcs;A1S0S2eVcs;A1S0S2cVcs;A1S0S2fVA;Vrb;A2S0S1S1S5Z20R6A2S5R6Z10000A2A2S1S1S5Z0M0R4A2S5R4R3A2A2S1S5R3Zdffc0000A2S1S1S5Z4M1R1A2S5R1Z2001A2A2S1S5S52Vc;A1R1A2S1S5S6R4S7R1R6A2A2M2S6R3Z40000M3A2M4A2S1S9G4S6G2R6A2A2S1S5G0R5A2S1S5S7G1R5A2R2A2S1S5R2Z1ffc0000A2S1S2S0SbR2G3A2G0A3S2S0R1SaScG4R4A2R6A2A3A2A2A2A2A2A2A2A2A2A2A2Tnew;Tmfa;Tmu;Tau;Tnf;TS;").
Proof.
  intros S nf au mu mfa new.
  destruct (pop_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8. fold nv c cs in N1, N2, N3, N4, N5, N6, N7, N8. fold S nf au mu in N1, N2, N3, N4, N5, N6, N7, N8.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as ((_ & C1 & _) & (_ & _ & K3) & _ & (MF0 & MF1) & (_ & FC0 & _) & _). fold S in K3. fold nf mfa in MF0, MF1, FC0.
  pose proof (facap_room c C1) as FR.
  assert (EN : new = (mu + 262144 - au) / S) by (unfold new, gh_new, kUserMapSize; fold nv c cs; reflexivity).
  pose proof (Z.div_mod (mu + 262144 - au) S ltac:(clear -N1; lia)) as DM. pose proof (Z.mod_pos_bound (mu + 262144 - au) S ltac:(clear -N1; lia)) as MB.
  rewrite <- EN in DM. clearbody new.
  assert (Q1 : 262144 - S < new * S <= 262144 + S) by (clear -DM MB N4 N6 N1; nia).
  assert (Q2 : 4 <= new <= 8193) by (clear -Q1 N1; nia).
  assert (Q3 : kchunks c <= new) by (clear -Q1 N1 N2 K3; nia).
  split; [exact N1|]. split; [exact N4|]. split; [exact N5|]. split; [exact Q2|]. split; [exact Q3|].
  split; [clear -DM MB; nia|]. split; [clear -DM MB; nia|]. split; [clear -N3; lia|]. split; [clear -MF1; lia|]. split; [clear -FC0 FR; lia|]. split; [exact MF0 | exact EN].
Qed.

Lemma new_val : ltac2:(tb__ "0|0|
S2S46Q40A1S1eVr;S43A2S1eVr;S39A2A3").
Proof.
  destruct new_nums as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & _ & _ & EN). cbn zeta in N1, N2, N3, N4, EN. fold nv c cs in N1, N2, N3, N4, EN.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & _ & _ & Q223 & Q224 & _ & _ & _ & Q228 & _). fold nv c cs in Q223, Q224.
  unfold new_e, vMU, vAU, vNEW, V_SIZE. cbn [eval]. apply bv_eq. rewrite divu_val by (rewrite E148, u64_lit; clear -N1; lia).
  rewrite sub_val, add_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N3 N4; lia).
  rewrite (Z.mod_small (cs_mapped_user cs + 262144)) by (clear -N2 N3; lia). rewrite Z.mod_small by (clear -N2 N3; lia). symmetry. exact EN.
Qed.

Lemma F_new_hold : Forall (holds r) F_new.
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _ & _ & _ & _ & _ & Q228 & _). fold nv c cs in Q222.
  unfold F_new. repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; unfold vNEW, vMFA; cbn [eval]; rewrite ?Q222, ?Q228, ?u64_lit by (clear -N4 N8 N9 N10; lia).
  - clear -N4; lia.
  - clear -N4; lia.
  - exact N10.
  - split; [clear; lia | change (2 ^ 18) with 262144; exact N11].
Qed.

Lemma need_val : ltac2:(tb__ "0|0|
S2S0S47Q40S1eVr;S42A2A2S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A3").
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N4, N8, N9, N10. fold nv c cs in N4, N8, N9, N10.
  destruct GH as (_ & Q221 & _ & _ & _ & _ & _ & _ & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221.
  unfold need_e, vNF, vNEW. cbn [eval]. rewrite sll_val, add_val, Q221, Q228, !u64_lit by (clear -N4 N8 N9 N10; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ + _)) by (clear -N4 N8 N9 N10; lia).
  rewrite Z.mod_small by (clear -N4 N8 N9 N10; lia). clear; lia.
Qed.

Lemma geu_iff : ltac2:(tb__ "0|0|
S4S28Vr;S41A2S3S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2A1A2").
Proof.
  destruct new_nums as (_ & _ & _ & _ & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N8, N9, N10. fold nv c cs in N8, N9, N10.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  unfold F_geu. cbn [holds]. unfold branch_taken, bv_ltu. rewrite need_val. unfold vMFA. cbn [eval]. rewrite Q222, u64_lit by (clear -N8 N9 N10; lia).
  rewrite negb_true_iff, Z.ltb_ge. clear; lia.
Qed.

Lemma rup_val : ltac2:(tb__ "0|0|
S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2S2S46Q40A1S1eVr;S45A2S1eVr;S1cS33S3eS1dZ40000A1A3A2A3F_;").
Proof.
  intros HLT. pose proof need_val as NV.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  set (need := 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)) in *. set (mfa := cs_mapped_free_array cs) in *.
  unfold rup_e. cbn [eval]. apply bv_eq. rewrite and_val, !add_val, NV. unfold vMFA. cbn [eval]. rewrite Q222.
  replace (bv_unsigned (Z_to_bv 64 18446744073709289472)) with 18446744073709289472 by reflexivity. rewrite !u64_lit by (clear -N9 N10; lia).
  rewrite (Z.mod_small (need + 262143)) by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite land_m18_up by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite (Z.mod_small (mfa + 262144)) by (clear -N9 N10 N8; lia).
  destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) N11) as [q Hq].
  assert (E : (need + 262143) / 262144 = q + 1).
  { symmetry. apply Z.div_unique with (need + 262143 - (q + 1) * 262144); [left; unfold need in *; clear -HLT Hq N4 N9; lia | clear; lia]. }
  rewrite E, Hq. clear; lia.
Qed.
End VALS.

Section POPMID.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S31VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let cs : class_state := cst_of A nv.
Variable ph : phase.

Variable F : nat.
Variables (E3 RU : axst) (LD LF0 LFm : leafA).
Let FR : list sprop := factsR E3.
Let CD : axst := ltac2:(tb__ "0|0|
S3cVFR;SeVLD;A1A2").
Hypothesis R_d : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2aVF;S12S0Z41884S16S0A1A3VRU;S13A5S17G0S12SfVLD;S16SfA1A3A2A3").
Hypothesis LN_u : ltac2:(tb__ "0|0|
S2S11S24SdVRU;A1A1S19A3").
Hypothesis NX_u : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVRU;A1A1A2S13A3").
Hypothesis W_d : ltac2:(tb__ "0|0|
S2S11S29SdVCD;A1A1S13A3").
Hypothesis D_d : ltac2:(tb__ "0|4|
S2S18S1bS15S1bS20S20A2M0A1M1S15S21A1M2A2M3A1S4dSdSeVLD;A1A1SdVCD;A1A2S17G3S1aG1G2S12G0S1aS20S20S43S39A4S16G0A1A3S3bA4A2A3").
Hypothesis NX_d : ltac2:(tb__ "0|0|
S2S11S4bS1fSdVCD;A1A1S1fSdSeVLD;A1A1A1A2S13A3").
Hypothesis R_f : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2aVF;S12S0Z3f404S12S0Z418c0S16S0A1A3A3VCD;S13A5S17G0S12SfVLF0;S12SfVLFm;S16SfA1A3A3A2A3").
Hypothesis LN_d : ltac2:(tb__ "0|0|
S2S11S24SdVCD;A1A1S19A3").
Hypothesis NXr_d : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVCD;A1A1A2S13A3").
Hypothesis F0_in : ltac2:(tb__ "0|0|
S48S21S41S23SdSeVLF0;A1A1A1A3").
Hypothesis Fm_in : ltac2:(tb__ "0|0|
S48S21S26S41A1S23SdSeVLFm;A1A1A1A3").

Theorem populate_mid : ltac2:(tb__ "0|2|
S22S15S46Q40A1A1S4cS3S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2M0A1S22VTR;S38S2aS30VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6M1SeVLF0;A1R1R4A5R3A2Fr';F_;G0S22VTR;S38S2aG1SeVLFm;A1R1R5A5R4A2Fr';F_;VTR;S38S2aG1VRU;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q H0 Hm.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41884] RU [LD] ph r tp Q R_d LN_u NX_u).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LD) (ax_S CD) _ _ ph r1 tp Q W_d D_d NX_d).
  { intros tr md (HFz & HGh & _) _. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. split.
    - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (new_val A rb r1 CF PF RG HGh).
    - exact (F_new_hold A rb r1 CF PF HGh). }
  change (ax_setS (la_state LD) (ax_S CD)) with CD.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3f404; 0x418c0] CD [LF0; LFm] ph r1 tp Q R_f LN_d NXr_d).
  intros L r2 [<-|[<-|[]]] _.
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ F0_in) as BF.
    apply (tr_pure Kc TR KIT (~ (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)))).
    { intros w [_ (HFz & HGh & _)]. exact (proj1 (geu_iff A rb r2 CF PF HGh) BF). }
    intros X. exact (H0 X r2).
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ Fm_in) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))).
    { intros w [_ (HFz & HGh & _)].
      destruct (Z_lt_dec (cs_mapped_free_array cs) (4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))) as [X|X]; [exact X|].
      exfalso. apply BF. exact (proj2 (geu_iff A rb r2 CF PF HGh) X). }
    intros X. exact (Hm X r2).
Qed.
End POPMID.
End SpineMallocR12.

(* [comment removed for export] *)
Module SpineCallocEi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "ax_add_facts"; "check_cfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "sprop"; "SPUle"; "SVar"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "leaf"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C1g"; "C2p"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C6"; "C6b"; "C6l"; "C7"; "C7p"; "C8"; "C8p"; "E2a"; "E2b"; "E3p"; "E3r"; "E4d"; "E5f"; "E5j"; "E5m1"; "E5m2"; "E5n"; "E5s1"; "E5s2"; "E6j"; "E6l"; "E6m"; "E6s"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "E8n"; "E8pn"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "run9a"; "run9b"; "run9pa"; "run9pb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocEi"; "vn0"; "vn1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9i"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CallocMemoSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9i.
Import ListNotations.
Open Scope Z_scope.

Definition vn1 (a : axst) : vnodeA := mkVNA a 1 (SLit 0).
Definition vn0 (a : axst) : vnodeA := mkVNA a 0 (SLit 0).
Definition cert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S8SbUfa0Vcutpcs;SaS0S13Vc;S1S13A1A3Ves;A6").
Definition ecert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S6SbUfa0Vcutpcs;SaS0S4S4eVc;A1S1S4A1A3S4cS13S4S4dVes;A4A6").

Definition F9a (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S48VW;Vst;Vtmax;A3A2").
Definition F9b (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S49VW;Vst;Vtmax;A3A2").
Definition F9pa (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4aVW;Vst;Vtmax;A3A2").
Definition F9pb (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4bVW;Vst;Vtmax;A3A2").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma s2_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40d40S1S9A1A3SaS0S4S5S1dVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2dVW;Vst;Vtmax;A3G0G1A3S0S4S5S2eVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s3p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40e58S0S9Z3c614S1S9A1A3A3SaS0S4S5S1eVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2fVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s3r_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40e58S0S9Z3c614S1S9A1A3A3SaS0S4S5S1fVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S30VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s4_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z7e9e4S1S9A1A3SaS0S4S5S20VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S31VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c774S0S9Z3c80cS1S9A1A3A3SaS0S4S5S21VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S36VW;Vst;Vtmax;A3G0G1A3S0S4S5S32VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c7e0S1S9A1A3SaS0S4S5S22VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S37VW;Vst;Vtmax;A3G0G1A3S0S4S5S38VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5c_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S23VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S34VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5d_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S24VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S35VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s5e_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c80cS1S9A1A3SaS0S4S5S25VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S33VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s6_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z5f9f8S0S9Z3c82cS1S9A1A3A3SaS0S4S5S26VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3cVW;Vst;Vtmax;A3G0G1A3S0S4S5S3aVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s6l_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S28VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3bVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s6b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c82cS1S9A1A3SaS0S4S5S27VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S39VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s7_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c8bcS0S9Z3ca04S1S9A1A3A3SaS0S4S5S29VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3dVW;Vst;Vtmax;A3G0G1A3S0S4S5S3eVW;Vst;Vtmax;A3G0G1A3S0S4S5S3fVW;Vst;Vtmax;A3G0G1A3G2A3A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma s7p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3ca04S1S9A1A3SaS0S4S5S2aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S40VW;Vst;Vtmax;A3G0G1A3S0S4S5S41VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSP_all; MemoFast.vmc.
Lemma NXC1g_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2r_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC3_0 : ltac2:(tb__ "0|0|
S14SaSdS12S20VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5_0 : ltac2:(tb__ "0|0|
S14SaSdS12S21VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S22VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5c_0 : ltac2:(tb__ "0|0|
S14SaSdS12S23VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5d_0 : ltac2:(tb__ "0|0|
S14SaSdS12S24VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5e_0 : ltac2:(tb__ "0|0|
S14SaSdS12S25VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S14SaSdS12S26VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6l_0 : ltac2:(tb__ "0|0|
S14SaSdS12S28VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S27VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7_0 : ltac2:(tb__ "0|0|
S14SaSdS12S29VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXCC8_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S0S9Z3ca54S1S9A1A3A3SaS0S4S5S2bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S42VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NXCC8p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8p_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S0S9Z3ca54S1S9A1A3A3SaS0S4S5S2cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S43VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10a_0 : ltac2:(tb__ "0|0|
S14SaSdS12S19VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S44VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S19VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S4fG0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S45VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S50G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S46VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S51G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S47VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S52G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
End INST.
End SpineCallocEi.

(* [comment removed for export] *)
Module SpineCallocEiW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "ax_add_facts"; "check_cfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "sprop"; "SPUle"; "SVar"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "leaf"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C1g"; "C2p"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C6"; "C6b"; "C6l"; "C7"; "C7p"; "C8"; "C8p"; "E2a"; "E2b"; "E3p"; "E3r"; "E4d"; "E5f"; "E5j"; "E5m1"; "E5m2"; "E5n"; "E5s1"; "E5s2"; "E6j"; "E6l"; "E6m"; "E6s"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "E8n"; "E8pn"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "run9a"; "run9b"; "run9pa"; "run9pb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocEiW1"; "vn0"; "vn1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9iW1"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9iW1.
Import ListNotations.
Open Scope Z_scope.

Definition vn1 (a : axst) : vnodeA := mkVNA a 1 (SLit 0).
Definition vn0 (a : axst) : vnodeA := mkVNA a 0 (SLit 0).
Definition cert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S8SbUfa0Vcutpcs;SaS0S13Vc;S1S13A1A3Ves;A6").
Definition ecert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S6SbUfa0Vcutpcs;SaS0S4S4eVc;A1S1S4A1A3S4cS13S4S4dVes;A4A6").

Definition F9a (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S48VW;Vst;Vtmax;A3A2").
Definition F9b (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S49VW;Vst;Vtmax;A3A2").
Definition F9pa (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4aVW;Vst;Vtmax;A3A2").
Definition F9pb (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
S18U0S4bVW;Vst;Vtmax;A3A2").

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma s2_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40d40S1S9A1A3SaS0S4S5S1dVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2dVW;Vst;Vtmax;A3G0G1A3S0S4S5S2eVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s3p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40e58S0S9Z3c614S1S9A1A3A3SaS0S4S5S1eVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S2fVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s3r_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z40e58S0S9Z3c614S1S9A1A3A3SaS0S4S5S1fVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S30VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s4_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z7e9e4S1S9A1A3SaS0S4S5S20VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S31VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c774S0S9Z3c80cS1S9A1A3A3SaS0S4S5S21VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S36VW;Vst;Vtmax;A3G0G1A3S0S4S5S32VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c7e0S1S9A1A3SaS0S4S5S22VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S37VW;Vst;Vtmax;A3G0G1A3S0S4S5S38VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5c_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S23VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S34VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5d_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S24VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S35VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s5e_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c80cS1S9A1A3SaS0S4S5S25VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S33VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s6_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z5f9f8S0S9Z3c82cS1S9A1A3A3SaS0S4S5S26VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3cVW;Vst;Vtmax;A3G0G1A3S0S4S5S3aVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s6l_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S28VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3bVW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s6b_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c82cS1S9A1A3SaS0S4S5S27VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S39VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s7_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3c8bcS0S9Z3ca04S1S9A1A3A3SaS0S4S5S29VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S3dVW;Vst;Vtmax;A3G0G1A3S0S4S5S3eVW;Vst;Vtmax;A3G0G1A3S0S4S5S3fVW;Vst;Vtmax;A3G0G1A3G2A3A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma s7p_ecert_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Z3ca04S1S9A1A3SaS0S4S5S2aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S40VW;Vst;Vtmax;A3G0G1A3S0S4S5S41VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSPW1_all; MemoFast.vmc.
Lemma NXC1g_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC2r_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC3_0 : ltac2:(tb__ "0|0|
S14SaSdS12S20VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5_0 : ltac2:(tb__ "0|0|
S14SaSdS12S21VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S22VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5c_0 : ltac2:(tb__ "0|0|
S14SaSdS12S23VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5d_0 : ltac2:(tb__ "0|0|
S14SaSdS12S24VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC5e_0 : ltac2:(tb__ "0|0|
S14SaSdS12S25VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S14SaSdS12S26VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6l_0 : ltac2:(tb__ "0|0|
S14SaSdS12S28VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S27VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7_0 : ltac2:(tb__ "0|0|
S14SaSdS12S29VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXC7p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NXCC8_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S0S9Z3ca54S1S9A1A3A3SaS0S4S5S2bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S42VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NXCC8p_0 : ltac2:(tb__ "0|0|
S14SaSdS12S2cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert8p_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S0S9Z3ca54S1S9A1A3A3SaS0S4S5S2cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S43VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10a_0 : ltac2:(tb__ "0|0|
S14SaSdS12S19VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S44VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10a_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S19VW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S4fG0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10b_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1aVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S16VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S45VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10b_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1aVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S50G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pa_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1bVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfScZ20A1S10S15A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S46VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pa_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1bVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S51G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma NX9fpb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma NX10pb_0 : ltac2:(tb__ "0|0|
S14SaSdS12S1cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma ECert9pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S0S9Zdb004S1S9A1A3SaS0S4S5S7S0SeSfS10S15A1ScZ10A1A2S1SeA1A3S17VW;Vst;Vtmax;A3A2Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S47VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
Lemma ECert10pb_0 : ltac2:(tb__ "0|3|
S11S2S6SbUfa0S1S9A1SaS0S4S5S1cVW;Vst;Vtmax;A3Z1ScZ0M0A1M1A3S1S4A1M2A3S0S4S5S52G0G1A3G2A3A6S3A3"). Proof. mc. Qed.
End INST.
End SpineCallocEiW1.

(* [comment removed for export] *)
Module SpineCallocR10.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "sprop"; "SAlu"; "eval"; "ss_next"; "ss_facts"; "valuation"; "sprop_below"; "ss_objs"; "swf"; "smatch"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "sym_runA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "list"; "true"; "nat"; "prod"; "pair"; "Some"; "app"; "option"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "lt"; "pow"; "ge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "frozen"; "ghosts"; "mlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "rMS"; "sMS"; "GR"; "nxt"; "O_pcm"; "O_ri"; "addobjs"; "idx_rot"; "nobj"; "pcof"; "relM"; "updR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR9"; "O_piece"; "O_shp"; "sh_e"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocR10"; "a2_e"; "cMr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.CRebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition a2_e (eb : sv) : sv := ltac2:(tb__ "0|1|
S7S49S7S47S7S48S7S47Veb;S5Z3fff8A1A3S5Z3A1M0A3S5Z1A1A3S7S48Veb;G0A3A3").
Definition cMr (E : axst) : axst := ltac2:(tb__ "0|2|
S39S17S6A1M0VE;S37VE;A1S16S1cS1bS4A2M1S1dS1bS4UcS5Z8000A1A4S17G1A1A3S17S3A1S21G0S31VE;A1A8").
Definition cMc (E : axst) (eb : sv) : axst := ltac2:(tb__ "0|0|
S34S50VE;A1S16S3S43Veb;A1S17S3A1A3S31VE;A1A3").
Definition dMSf (C : axst) : axst := ltac2:(tb__ "0|0|
S5fS4eVC;S2fVC;A1S2eVC;A1A3SaS11VC;A1A1A2").

Lemma idx_rot_ok : ltac2:(tb__ "0|1|
S1bS55U1M0R1A2S1bS2S53S1bR1S1fS1bS3fG0S46R3G0A2A2S16S1bU0S17S1bA1A3A3A3S56R1R3A2A2Fi;F_;Fn;").
Proof.
  intros n Hn i. rewrite in_app_iff, in_seq. cbn [In]. lia.
Qed.

Section VALS.
Variables (r : valuation) (eb : sv) (B : Z).
Hypothesis EB : ltac2:(tb__ "0|0|
S0S22S3cQ40S8Vr;Veb;A2A2VB;A3").
Hypothesis HB : ltac2:(tb__ "0|1|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S0S22S25VB;Z10000A2G0A3A2A2").

Lemma a2_val : ltac2:(tb__ "0|0|
S0S3bQ40A1S8Vr;S4fVeb;A1A2S8Vr;S5Z8000A1A2A3").
Proof.
  destruct HB as (B0 & B1 & BM). destruct (proj1 (Z.mod_divide B 65536 ltac:(lia)) BM) as [q Hq].
  unfold a2_e. cbn [eval]. apply bv_eq. rewrite sub_val, add_val, !srl_val, add_val, EB, !u64_lit by lia.
  change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (Z.mod_small (B + 262136)) by lia. rewrite Hq.
  replace ((q * 65536 + 262136) / 8) with (q * 8192 + 32767) by (apply Z.div_unique with 0; lia).
  replace (q * 65536 / 8) with (q * 8192) by (apply Z.div_unique with 0; lia).
  rewrite (Z.mod_small (q * 8192 + 32767 + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sh_val : ltac2:(tb__ "0|0|
S0S22S3cQ40S8Vr;S44Veb;A1A2A2S4dVB;A1A3").
Proof.
  destruct HB as (B0 & B1 & BM). unfold sh_e, gsv, shb. cbn [eval]. rewrite add_val, srl_val, EB, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold Sh.
  pose proof (Z.div_le_upper_bound B 8 (2 ^ 59) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
Qed.
End VALS.

Section MEMSET.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S2aVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S0S1bS64Vp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S63VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SbS2bVrb;R1A2S2cVA;Vrb;R2A3S0S22S3cQ40S8R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S24S23S68S67VA;A1A1M0Z100000000A2VB;A2S1S24S23VB;Z40000A2S23G0Z2000000000A2A2S0S22S25VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S19S3bQ40A1A1S40S2dVA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S28S62R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable F : nat.
Variables (G1 : axst) (LM : leafA).
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM eb.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.
Hypothesis R_m : ltac2:(tb__ "0|1|
S0S20S19S12A1M0A1S15S3aVF;S16S22Zdb004S17S22A1A3VG1;S1aA5S1eG0S16S12VLM;S17S12A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S18S10S11VG1;A1A1S21A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S18S45S30S9S11VG1;A1A1A2S1aA3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S19S1cS1cS4S4A2S4A2M0A1S3dS3G0S51SdS11VEM;A1A1A4S3dS3G0S51S1fS3S6aVW;A1S16S3S65S16S3S66S16S3S32S16S3S33S16S3S42Veb;A1S17S3A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S54S6S69VW;Vst;A2SaS11VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S18SeS11VCMR;A1A1S1aA3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S20S1cS19S1cS4S4A2M0A1M1S19S6A1M2A2M3A1S5cS11VEM;A1S11VCMR;A1A2S1eG3S1dG1G2S16G0S1dS4S4S4fVeb;A1S5Z8000A1A4S17G0A1A3S17S6A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S18SeS11VCMC;A1A1S1aA3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S20S19S3A1M0A1S61VCMC;S4aS2fVCMC;A1A3S1eG0S2eVCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S18S60VCMC;S4aS2fVCMC;A1S2eVCMC;A1S3dS12S13S14S4bA4A5S1aA3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S18S45S5bS9S11VCMC;A1A1A2S1aA3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S18S45S30S9S11VCMC;A1A1A2S1aA3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S18S52S6ScS9S11VCMC;A1M0A1A1SaG0A1A3S1aA3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S18S52S6ScS9S11S4eVCMC;S2fVCMC;A1S2eVCMC;A1A3A1A1A1SaS11VCMC;A1A1A3S1aA3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S18S5dS35VDM;A1A1S1aA3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S19S3A1SdS11VRM;A1A1M0S1fS3S3eS3S46S36VDM;A1U2A2G0A3S16S3S42Veb;A1S16S3S43Veb;A1S17S3A1A3A3A3A3").

Let ph2 : phase := ph_set p 2 ph.
Let ph3 : phase := ph_set p 3 ph.

Lemma piece_nums : ltac2:(tb__ "0|2|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S1S0S22S25VB;Z10000A2G0A3S1S0S22S25S4dVB;A1M1Z1000A2G0A3S1S24Z2008fff7000G1A2S24S23G1Z8000A2Z10007fff8000A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _). destruct HBn as (HB1 & HB2 & HB3).
  destruct (sh_run_nums (ag_spacebeg (aa_geom A)) B ltac:(clear -G13; lia) HB1 HB2 ltac:(clear -G14 TG; lia) HB3) as (Q1 & Q2 & Q3 & _).
  split; [clear -HB1 G13; lia|]. split; [clear -HB2 G14 TG; lia|]. split; [exact HB3|]. split; [exact Q1|]. split; [exact Q2 | exact Q3].
Qed.

Lemma piece_release : ltac2:(tb__ "0|1|
SbS19S3bQ40A1A1S19S41A1M0S57S40S40SfS3aR6S11VRM;A1S1dG0S58R4S59R3R2A2A4A4S29VA;VKc;Vrb;Vtp0;Vmd0;Vph2;R7R6R5R2AaS29VA;VKc;Vrb;Vtp0;Vmd0;Vph3;S5eR8S16S3S42Veb;A1S16S3S43Veb;A1S17S3A1A3A3R5A3R7R6R3AaF_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr ms md mdJ Hsm (HFz & HGh & HK' & HM & HR & HRM).
  destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  set (R := [O_piece eb; O_shp eb]). set (r3 := rho_absorb r R ms).
  pose proof (HBv r HFz HGh) as EB.
  assert (RNp : obj_range r (O_piece eb) = (B, B + 262144)).
  { unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r (O_shp eb) = (Sh B, Sh B + 32768)).
  { unfold O_shp. rewrite obj_range_mk by (clear; lia). rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))). f_equal; clear; lia. }
  assert (G2 : ph_get p ph2 = 2%nat) by (unfold ph2; apply ph_get_set).
  assert (E3 : ph3 = ph_set p 3 ph2) by (unfold ph3, ph2; rewrite ph_set_set; reflexivity).
  assert (ZR : forall z, zoneR A rb ph3 z <-> (zoneR A rb ph2 z \/ B <= z < B + 262144)) by (intros z; rewrite E3; exact (zone_release A rb p ph2 z G2)).
  assert (ZS : forall z, Sh B <= z < Sh B + 32768 -> zoneR A rb ph2 z).
  { intros z Hz. unfold ph2. apply (zone_reveal A rb p ph z PH1). right. exact Hz. }
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  assert (MO : forall z, ~ (B <= z < B + 262144) -> ~ (Sh B <= z < Sh B + 32768) -> m3 z = m z).
  { intros z H1 H2. unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; assumption. }
  assert (MIN : forall z, (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) -> m3 z <> None).
  { intros z Hz.
    assert (Hz64 : 0 <= z < 2 ^ 64) by (clear -Hz B0 B1 Q2 Q3; lia).
    destruct Hz as [Hz|Hz].
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_piece eb) Hsm OB_r (or_introl eq_refl)) as (_ & _ & ASp & _).
      cbn [ob_base O_piece ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_piece] in ASp. rewrite !soff_lit_small in ASp by (clear; lia). rewrite EB in ASp.
      destruct (ASp (or_intror eq_refl) (z - B) ltac:(clear -Hz; lia)) as [x Hx]. replace (B + (z - B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate.
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_shp eb) Hsm OB_r (or_intror (or_introl eq_refl))) as (_ & _ & ASp & _).
      cbn [ob_base O_shp ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_shp] in ASp. rewrite !soff_lit_small in ASp by (clear; lia).
      rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))) in ASp.
      destruct (ASp (or_introl eq_refl) (z - Sh B) ltac:(clear -Hz; lia)) as [x Hx]. replace (Sh B + (z - Sh B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|].
  split; [rewrite E3; exact (mlink_release A rb tp0 md0 p ph2 tp mdJ HM G2)|].
  split.
  - apply (rlink_quiet_intro A rb ph2 ph3 _ m m3); [unfold ph3; apply ph_quiet_set; exact PQ | | exact HR | |].
    + intros z Hz. apply ZR. left. exact Hz.
    + intros z Hz. apply MO; intros X; apply Hz; apply ZR; [right; exact X | left; exact (ZS z X)].
    + intros z Hz. apply ZR in Hz.
      assert (D : (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) \/ ~ (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768)) by (clear; lia).
      destruct D as [D|D]; [exact (MIN z D)|]. rewrite MO by (clear -D; lia).
      destruct Hz as [Hz|Hz]; [exact (proj1 (proj2 HR) z Hz) | exfalso; apply D; left; exact Hz].
  - apply (rmlink_absorb _ r R ms HRM). intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; unfold IMG_LO, IMG_HI.
    + pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. destruct CF0 as (_ & _ & _ & _ & _ & (_ & G13 & _) & _).
      destruct HBn as (HB1 & _). right. clear -HB1 G13. lia.
    + right. clear -Q2. lia.
Qed.

Theorem piece_map : ltac2:(tb__ "0|1|
SbS19S3bQ40A1A1M0S5aSbG0VTR;S4cS3aS29VA;VKc;Vrb;Vtp0;Vmd0;Vph3;A6S38VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S4cS3aS29VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VG1;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC. destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0xdb004] G1 [LM] ph r tp Q R_m LN_g NX_g).
  intros L r1 [<-|[]] _. fold EM.

  apply (tr_cut Kc TR KIT (list word * valuation) _ (fun x => SPA segs (JRp ph2) EM (snd x) (fst x ++ tp)) Q).
  { intros w Hw. destruct (piece_reveal A Kc rb tp0 md0 W st rho HW HE p eb ph PH1 PQ HBv HBn HROOM EM SK_m XF_m r1 tp w Hw) as (tpn & r' & H').
    exists (tpn, r'). exact H'. }
  intros [tpn r2]. cbn [fst snd]. set (tp2 := tpn ++ tp).

  apply (tr_pure Kc TR KIT (Forall (fun o => ranges_disjoint (obj_range r2 o) (Sh B, Sh B + 32768)) (ss_objs (ax_S EM)))).
  { intros w Hw. assert (G2 : ph_get p ph2 = 1%nat -> False) by (unfold ph2; rewrite ph_get_set; discriminate).
    destruct Hw as [HsmA HJ]. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r2 CF0 RG HGh) as (EBx & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
    unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
    pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
    destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S EM) [O_pcc0; O_st; O_pcm; O_ri; O_piece eb] r2 _ HW HE HFz Hsm SK_m XF_m) as (ob & ox & EO & SKx & BZ).
    destruct ox as [|oc [|os [|om [|ori [|opc [|? ?]]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
    assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
    assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
    assert (SKp : skel opc = skel (O_piece eb)) by (clear -SKx; congruence).
    rewrite <- (obj_range_skel r2 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r2 os O_st SKs) in RNs.
    rewrite <- (obj_range_skel r2 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r2 ori O_ri SKr) in RNr.
    assert (RNp : obj_range r2 opc = (B, B + 262144)).
    { rewrite (obj_range_skel r2 opc (O_piece eb) SKp). unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite (HBv r2 HFz HGh). f_equal; clear; lia. }
    assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
    destruct HBn as (HB1 & HB2 & _).
    rewrite EO. apply Forall_app. split.
    - apply BZ. right; right. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear -Q2 Q3. lia.
    - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr, ?RNp; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -Q2 Q3 HB1 HB2 C1 T1 T2 TB G13; lia. }
  intros OBJD.

  apply (jr_restate A Kc rb tp0 md0 TR KIT EM (ax_S CMR) _ _ ph2 r2 tp2 Q W_mr D_mr ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    exact (a2_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))). }
  change (ax_setS EM (ax_S CMR)) with CMR.

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) CMC r2 tp2)).
  { intros w Hw. pose proof (proj2 Hw) as HJ. pose proof HJ as (HFz & HGh & _ & _ & HR & _).
    pose proof (sh_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))) as ESH.
    apply (SPA_carve_unk segs (JRp ph2) r2 CMR tp2 w (sh_e eb) (SLit 0) (SLit 32768) (nxt EM) Hw W_mc ltac:(apply Pos.le_refl)); rewrite ?ESH, ?soff_lit_small by (clear; lia).
    - clear; lia.
    - clear; lia.
    - clear -Q2; lia.
    - clear -Q3; lia.
    - replace (Sh B + 0) with (Sh B) by (clear; lia). change (ss_objs (ax_S CMR)) with (ss_objs (ax_S EM) ++ []). rewrite app_nil_r. exact OBJD.
    - intros a Ha. assert (Ha64 : 0x643000 <= a < 2 ^ 64) by (clear -Ha Q2 Q3; lia).
      assert (ZN : zoneR A rb ph2 a) by (unfold ph2; apply (zone_reveal A rb p ph a PH1); right; fold B; clear -Ha; lia).
      pose proof (proj1 (proj2 HR) a ZN) as D. rewrite view_in in D by (clear -Ha64; lia).
      pose proof (wok_rd_off_image (rm r2) a) as WK.
      destruct (rd_of segs (rm r2) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
    - unfold xwords_clear. change (ax_X CMR) with (ax_X EM). rewrite XX_m. intros rr y j []. }

  apply (tr_facts Kc TR KIT). intros HFC.
  apply (tr_memset Kc TR KIT (JRp ph2) CMC (sMS CMC) (rMS CMC) r2 tp2 Q (JR_K A Kc rb tp0 md0 ph2)
           (JR_stable A Kc rb tp0 md0 ph2 _ HKc ltac:(apply Pos.leb_le; exact NX_ms)) ltac:(apply Pos.leb_le; exact NF_ms) E_ms CHK_ms).
  intros r3 tp3 Hag.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) DM r3 tp3)).
  { intros w Hw. apply SPA_refacts; [exact Hw | exact FBT_ms |]. intros _. exact (Forall_holds_agree _ r2 r3 _ Hag FBC_ms HFC). }

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) RM r3 tp3)).
  { intros w Hw. apply (SPA_select segs (JRp ph2) r3 DM (idx_rot DM) tp3 w Hw ND_r).
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi.
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi. }
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JRp ph3) (relM DM) r4 tp3) Q); [|intros r4; exact (HC r4 tp3)].
  intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_piece eb; O_shp eb] (vms md tp3 ms)).
  apply (SPA_unobj_J (JRp ph2) (JRp ph3) r3 RM _ [O_piece eb; O_shp eb] tp3 tr ms md OB_r Hw).
  intros Hsm HJ. exact (piece_release r3 tp3 tr (vms md tp3 ms) (vmd md) md Hsm HJ).
Qed.
End MEMSET.
End SpineCallocR10.

