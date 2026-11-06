(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9 kf.

(* [comment removed for export] *)
Module SpineCallocSec6L.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "cons"; "prod"; "option"; "Some"; "app"; "pair"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "sobj"; "sv"; "ss_next"; "ss_facts"; "SLit"; "SPBranch"; "sprop_below"; "swf"; "SVar"; "rw"; "DUnknown"; "SAlu"; "SPUle"; "cell"; "eval"; "mkObj"; "obj_range"; "rm"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ageom"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L.SEC6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV"; "F_A"; "L3"; "B3"; "END8"; "RUE"; "UE9"; "a2e6"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "O_1"; "O_2"; "Pret_ms"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "SKEL0"; "range_noband"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SEC6L.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S41S67VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S4S5cS6cVnx;A2S5A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S6fVnW;Vst;Vnx;VBX;A4").

Definition F_low : sprop := ltac2:(tb__ "0|0|
S23S22S43S1fVnx;A1S1fS66A1A3S1bZ7fff7000A1A2").

Lemma low_FA : ltac2:(tb__ "0|1|
S2aS2aFx;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bS2aS0S2cS2bRaR1A1A1S2bR1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S16R6S35A2S39S14S16R7A1S4fVnx;A1A3F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ HL.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _ & _ & E155 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  destruct HJ as (_ & _ & HA & HP & _).
  pose proof (proj1 HA) as HG. rewrite BXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (RSB : 0 <= SB < 2 ^ 64) by (clear -S1 S2 TG; lia).
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  unfold F_low in HL. cbn [holds eval] in HL. rewrite Enx, E142, add_val in HL. fold ua L in HL.
  rewrite (u64_lit L RL) in HL. rewrite Z.mod_small in HL by (clear -IMG HTOP SMB; lia). rewrite u64_lit in HL by (clear; lia).
  unfold F_A. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E142, E155, add_val. fold ua L SB.
  rewrite (u64_lit L RL), (u64_lit SB RSB). rewrite Z.mod_small by (clear -IMG HTOP SMB; lia). clear -HL S1. lia.
Qed.

Definition F_g7L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS42S1bZ7fff7fffA1S53Vnx;A1A3S6S14A1A3").
Definition F_g8L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS42S1bZ7fff7fffA1S52Vnx;A1A3S6S14A1A3").
Definition F_g9L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS42S1bZ7fff7fffA1S54Vnx;A1A3S6S14A1A3").

Lemma low_end : ltac2:(tb__ "0|2|
S2aS2aF_;S2aS30S15S2dQ40M0A1M1S15S3G1A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S48S49S2eG0R7A2S5aS2eG0S20R8PcA2A2A1A2Z7fff7000A2F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  unfold F_low in HL. cbn [holds eval] in HL. rewrite Enx, E142, add_val in HL. fold ua L in HL.
  rewrite (u64_lit L RL) in HL. rewrite Z.mod_small in HL by (clear -IMG HTOP SMB; lia). rewrite u64_lit in HL by (clear; lia). exact HL.
Qed.

Lemma geu_intro : ltac2:(tb__ "0|0|
S15S40S18S1S48Z0R2A2S4aR2S4cZ2Z40A2A2A2S48S2eQ40S25R4R2A2A2R3A2S16R5S1cS42S1bR4A1R3A3A2F_;F_;Fe;Fc;Fr;").
Proof.
  intros r c e Hc H. cbn [holds eval branch_taken]. apply Bool.negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite u64_lit by exact Hc. exact H.
Qed.

Lemma F_g7L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1S36A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). unfold PG in *. lia. }
  unfold F_g7L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. unfold RUE. cbn [eval].
  rewrite and_val, !add_val, Enx, E12, !u64_lit by lia. fold ua nv.
  rewrite (Z.mod_small (ua + 6144)) by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (Z.mod_small (ua + 6144 + nv + 7)) by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (land_m8E nW st tmax nx Hnx) by (clear -Ra HTOP LB HN SMB; lia). pose proof (Z.mod_pos_bound (ua + 6144 + nv + 7) 8 ltac:(lia)) as MB. clear -MB LE LB. lia.
Qed.

Lemma F_g8L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1S37A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  destruct (site8_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & EE). cbn zeta in EE.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g8L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. rewrite EE. clear -LE LB MN. lia.
Qed.

Lemma F_g9L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1S38A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  destruct (site9_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (EU & _). cbn zeta in EU.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g9L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. rewrite EU. clear -LE LB MN. lia.
Qed.

Section HINT.
Variable BX : AA -> AA.
Variables (D D' : axst) (F : list sprop).
Hypothesis WD : ltac2:(tb__ "0|0|
S0S4S1eSeVD';A1A1S5A3").
Hypothesis DD : ltac2:(tb__ "0|4|
S0S9S8S3S8S18S18A2M0A1M1S3S14A1M2A2M3A1S59SeVD;A1SeVD';A1A2SaG3ScG1G2S6G0A1VF;A4A2A3").
Hypothesis NXD : ltac2:(tb__ "0|0|
S0S41S19SeVD';A1A1S19SeVD;A1A1A3").
Hypothesis HD : ltac2:(tb__ "0|0|
S0SfS10VD;SeVD';A1A2VD';A3").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S57S14S35S1aSeVD;A1A1A3").
Hypothesis FH : ltac2:(tb__ "0|1|
S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;VBX;R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1VF;A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").

Lemma hint_low : ltac2:(tb__ "0|1|
S2aS30S15S2dQ40A1M0S15S3G0A1S45S3dVsegs;VJG;VBX;R7R6R5R4A5VD;R3R2R1A6S3dVsegs;VJG;VBX;R8R7R6R5A5VD';R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw.
  pose proof (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rhoX D tp w Hw) _ FLOW) as HL.
  destruct w as [tr [ms md]]. rewrite <- HD.
  eapply SPA_restate; [exact WD | exact DD | exact NXD | constructor | | exact Hw].
  exact (FH A Kc rho a rhoX tp tr md (proj2 Hw) HL).
Qed.

Lemma hint_low_triple : ltac2:(tb__ "0|2|
S45OF_;S2aS30S15S2dQ40A1M0S46S15S3G0A1M1S44Vsegs;R8S3dVsegs;VJG;VBX;R7R6R5R4A5VD';R2R1A5R3A4FtY;FrY;S15G1S44Vsegs;R9S3dVsegs;VJG;VBX;R8R7R6R5A5VD;R2R1A5R4A4FtX;FrX;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HC rX tX.
  eapply triple_conseq; [intros w Hw; exact (hint_low A Kc rho a rX tX w Hw) | intros w Hw; exact Hw | exact (HC rX tX)].
Qed.
End HINT.

Section G43L.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2aS0S2cS2bVBX;R1A1A1S2bR1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;VBX;R8R7R6R5R4R3R2R1A9S39S14S16R5A1VFXP;A3S3S17A1S0S3S8S8S18S18A2S18A2M1A1S3aS17G1S47R1A4S3aS17G1S47VPX;A4A3S39S17S17S71S27R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A Y6A E6 CT6 CO6 T6 : axst) (sA s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S60VT6;S1aSeVCO6;A1A1A2").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S57S14S35S1aSeVC5;A1A1A3").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0SfS5eS4fVnx;A1VC5;A2VC5A;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S4S56S14S1dS19SeVC5;A1A1A1S4fVnx;A1A3S5A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S4S5fS6eUfa0S7S40S65S6S40A1A3VGS;S7SfVC5A;S6SfA1M0A3S7SfVY6A;G0A3A6S5A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S4S11VY6A;VE6;VsA;A3S5A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S4S5dVsA;VGS;A2S5A3").
Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S4S1eSeVCT6;A1A1S5A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0S9S8S3S8S18S18A2M0A1M1S3S14A1M2A2M3A1S59SeVE6;A1SeVCT6;A1A2SaG3ScG1G2S7G0ScS18S18S55Vnx;A1S50A4S6G0A1A3S6S14A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S41S19SeVCT6;A1A1S19SeVE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0SfS10VE6;SeVCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S3S8S8S18S18A2S18A2M0A1S3aS17G0S47S29SeVCT6;A1A1A4S3aS17G0S47SbS17S7S17S69Vnx;A1S7S17S68Vnx;A1S6S17A1A3A3SbS17S70VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S58S14SbS14S34VW;Vst;A2S33S32A1A3S1aSeVCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S58S14VFXP;S1aSeVCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0SfS6bVCT6;S26S51Vnx;A1S1bZ0A1S50S6S24A1S21A5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S4S1eSeVCO6;A1A1S5A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S9S3S17A1M0A1S62VCO6;S4dVs6;A3SaG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S4S61VCO6;S4dVs6;VR6;S3aS13SfS12S4eA4A5S5A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0SfS63Vs6;S4dS6aVCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S4S56S14S1dS19SeVCO6;A1M0A1A1S1aG0A1A3S5A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S4S56S14S1dS19SeVT6;A1A1A1S1aSeVCO6;A1A1A3S5A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S4S5cVGS;S19SeVCO6;A1A1A2S5A3").

Theorem sec_g43_low : ltac2:(tb__ "0|5|
S45OF_;S2aS30S15S2dQ40M0A1M1S46S64VW;Vst;A2S5bVW;Vst;A2S31R6A1S3fVsegs;R9S3eR7A1A3S40S1S48S6dS2eG0R7A2A1M2R1A2S4aR1S49G2S4bS5aS2eG0S20R8PcA2A2A1Z8A2A2A2A2S2S0S9S2dQ8A1M3A1S28R9S2fG0R2A2A2SdG3A1A3A1F_;Fz;S15S3G1A1M4S44Vsegs;RdS3dVsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A4FtpY;FrhoY;S15G4S44Vsegs;ReS3dVsegs;VJG;VBX;RdRcRbRaA5VC5;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (TAIL : forall rE tE, triple segs ok (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ms_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
             (RS6 nW st tmax nx Hnx BX E6 CT6 WC6 DF6 NX6 HC6) (HBL6 nW st tmax nx Hnx BX PX FXP PX_noband E6 CT6 NX6 FX6)
             SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             ok A Kc rho rho a tE Q HW HUS HKc Hokl SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }
  apply (triple_conseq (P:=SPA segs (JG BX A Kc rho a) C5A rX tX) (SPA segs (JG BX A Kc rho a) C5 rX tX) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { pose proof (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rX C5 tX w Hw) _ FLOW) as HL.
    destruct w as [tr [ms md]]. rewrite <- HC5A.
    split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) (low_FA BX A Kc rho a rX tX tr md BXg (proj2 Hw) HL) FBA). }
  apply (cfg_soundA segs 4000%nat [MSENT] GS [C5A] [Y6A] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6A); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | intros w Hw; right; exact Hw |].
  apply TAIL.
Qed.
End G43L.
End SEC6L.
End SpineCallocSec6L.

(* [comment removed for export] *)
Module CallocGlueZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "soff"; "ss_objs"; "sstate"; "DZero"; "cell"; "eval"; "mkObj"; "mkSS"; "obj_range"; "ranges_disjoint"; "rm"; "smatch"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "valuation"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "nil"; "pair"; "true"; "Some"; "app"; "cons"; "list"; "option"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "xwords_clear"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma smatch_carve_zero_sym : ltac2:(tb__ "0|8|
S1dSbS28S36A1M0S34S35S8S8S8S1S14Vsegs;R9R8S23G0S2eR7S2fR6R5A2A4A4S10S19R9A1S1aR9A1S17R9A1S16R9A1S1bR9A1S26S7SaR9A1S27S7SfR5R4R3S22SdA1ScA5S22S7A1A3A3S15R9A1R2S18R9A1A9SbS1fS21S1cR1A1S24A3S2cQ40M1SeRcR7A2A2S0S9RdR7A2S0S9ReR7A2S0S3R2R1A2S4S6R2R3A2S5Z2M2Z3fA2A2S3Z0M3S2R5R4A2A2S3S2R6R4A2S5G2Z40A2A2S2dS7S7S12S11R14R1A2S23S0S0S2R8R7A2S2R8R6A2A4A2Lo';SaR12A1A3S0S20S3S2R9R8A2R1A2S4R1S2R9R7A2A2A2S20S1fS21S33Vsegs;S13R16A1M4S2aG1R2A2M5A3S24A3S1fS29S2bQ8M6A1M7A1S32Vsegs;G4G5A3S25G7S2aG6G3A2A2A3A2F_;Fa;S14Vsegs;R15RbS23G0S2eR13S2fR12R11A2A4A4F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;TS';F_;Fnx;Fehi;Felo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md base elo ehi nx Hsm S' Hwf' b lo hi Hs1 Hs2 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base elo ehi [] DZero).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)) by reflexivity.
  assert (Hout : forall a, b + lo <= a < b + hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. apply Forall_forall. intros o Ho. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite u64_lit by lia. lia. }
  assert (MEM : forall a, b + lo <= a < b + hi -> ms_mem ms (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)).
  { intros a Ha. exact (Hfr _ (Hout a Ha)). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    subst newo. unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. fold lo. fold hi.
    split; [lia|]. split.
    { intros off Hoff _. destruct (Hbytes (b + off) ltac:(lia)) as [Hw Hb].
      unfold wview. rewrite (MEM (b + off)) by lia.
      pose proof (wview_of_views segs (rm rho) (Z_to_bv 64 (b + off)) Hw (ex_intro _ _ Hb)) as X. unfold wview in X. exact X. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEM (b + off)) by lia.
    destruct (Hbytes (b + off) ltac:(lia)) as [_ Hb]. unfold rd_of in Hb.
    destruct (rm rho (Z_to_bv 64 (b + off))) as [x|]; [exact Hb|]. rewrite <- Hb. first [apply Hrom | symmetry; apply Hrom].
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. first [rewrite Hnr | subst newo; rewrite Hnr]. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_zero_sym : ltac2:(tb__ "0|9|
S31S1dS3aS28S2bQ40M0A1A1S37S8S8S8S1S30Vsegs;R9R7R8R6R5A6S38R8A1SbS10S19R1A1S1aR1A1S17R1A1S16R1A1S1bR1A1S26S7SaR1A1S27S7SfR6R5R4S22SdA1ScA5S22S7A1A3A3S15R1A1R3S18R1A1A9SbS1fS21S1cR1A1S24A3S3cS1eR3A1R5A2S2cG0SeRdR9A2A2S0S9ReR9A2S0S9RfR9A2S0S3R2R1A2S4S6R2R3A2S5Z2M1Z3fA2A2S3Z0M2S2R5R4A2A2S3S2R6R4A2S5G1Z40A2A2S2dS7S7S12S11R15R1A2S23S0S0S2R8R7A2S2R8R6A2A4A2Lo';SaRbA1A3S0S20S3S2R9R8A2M3R1A2S4R1S2R9R7A2M4A2A2S20S1fS21S33Vsegs;S13R17A1M5S2aG0R2A2M6A3S24A3S1fS29S2bQ8M7A1M8A1S32Vsegs;G5G6A3S25G8S2aG7G2A2A2A3A2F_;Fa;S3bR16R15G3G4A4S30Vsegs;R18S39R16RdA2R17R15R14A6F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;F_;TS';TS;F_;Fnx;Fehi;Felo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp [tr [ms md]] base elo ehi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hnx b lo hi Hs1 Hs2 Hlo Hhi Hdisj Hbytes Hxs.
  subst S' S. split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_zero_sym rho (ax_S A) tr (vms md tp ms) (vmd md) base elo ehi nx Hsm Hwf' Hs1 Hs2 Hlo Hhi Hdisj Hbytes).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    change (obj_range rho (mkObj base elo ehi [] DZero)) with (b + lo, b + hi). cbn [fst snd].
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.
End WithSegs.
End CallocGlueZ.

(* [comment removed for export] *)
Module SpineCallocSec7.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "or"; "@Corelib.Init.Datatypes"; "nat"; "cons"; "list"; "bool"; "app"; "nil"; "true"; "length"; "pair"; "prod"; "andb"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "valuation"; "cell"; "sprop"; "sv"; "SVar"; "rl"; "rm"; "ss_facts"; "eval"; "holds"; "ss_objs"; "SLit"; "SPBranch"; "SPNot"; "odefault"; "ss_next"; "swf"; "DUnknown"; "DZero"; "SAlu"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_geom"; "aa_ptr_committed"; "aa_depot"; "ageom"; "aa_Kf"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_q_global"; "aa_q_thread"; "class_state"; "qbatch"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "add"; "div"; "mul"; "eqb"; "leb"; "ltb"; "modulo"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "mkAX"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "A_globals"; "unwind_objs"; "V_RES"; "base_sv"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV"; "O_UBs"; "UBs"; "F_par"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7.SEC7.FIN"; "idxsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7"; "idxsF"; "S2F"; "KUB"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_ok"; "JLc_ok"; "PFc"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NCH"; "V_NRES"; "nxS";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9"; "sw9"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayCommit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "GS"; "JGs"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require MallocInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.CRebuildS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.CallocGlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition idxsF (nW : nat) (partial : bool) : list nat := ltac2:(tb__ "0|3|
S8S4S5S4U5S8S4S66U6M0VnW;A2S5S4S55G0VnW;A2S5S4S55U7VnW;A2S9S4A1M1A3A3A3A3S8S4S66S55U8M2VnW;A2U1eA2S8S4S5S4U0S5S4U1S5S4U2S5S4U3S5S4U4G1A3A3A3A3A3S8S4S66S55U26VnW;A2G2A2S8S4S5S4S55U2eVnW;A2S5S4S55U2fVnW;A2S5S4S55U30VnW;A2G1A3A3A3S7S6S4A1Lpartial;Vpartial;S5S4S55U31VnW;A2G1A3G1X7x2A3A3A3A3A3").
Definition KEPTF (W : list ulink) (swc : list cell) : list sobj := ltac2:(tb__ "0|0|
S5S13S9dVswc;A1S8S13S60VW;A1S5fA3A3").

Definition KUB (W : list ulink) (swc : list cell) (nx : positive) : list sobj := ltac2:(tb__ "0|0|
S8S13S5S13S9dVswc;A1S60VW;A1A3S8S13S5S13S68Vnx;A1S9S13A1A3S5fA3A3").
Definition S2F (F : axst) (K : list sobj) : sstate := ltac2:(tb__ "0|1|
S56VF;A1S30S29S2dR1A1S7fS2eR1A1S5SdS4S18A2M0ScS4S18U4S19P18A1A4S9G0A1A3A2S2bR1A1S2aR1A1S2fR1A1VK;S1cR1A1S24R1A1S2cR1A1A9TS;").
Definition XF_of (F : axst) (K : list sobj) (nx : positive) : axst := ltac2:(tb__ "0|1|
S59S8bVF;VK;A2S5SdS18S18A2M0ScS18S18S69Vnx;A1S19PcA1A4S9G0A1A3S62A3").

Definition bx_ok (BX : AA -> AA) : Prop := ltac2:(tb__ "0|3|
S35S1S0S3cS39VBX;R1A1M0A1S39R1A1A3S1S0S6S47A1S40G0A1S40R1A1A3S1S0S7S3fG0A1S3fR1A1A3S1S0S6S37A1S36G0A1S36R1A1A3S1S0S6SdS11S11A2A1M1S44G0A1S44R1A1A3S1S0S6S48A1M2S46G0A1S46R1A1A3S1S0G2S45G0A1S45R1A1A3S1S0S6S11A1S42G0A1S42R1A1A3S1S0S6G1A1S41G0A1S41R1A1A3S1S0S7S43G0A1S43R1A1A3S1S0S11S3eG0A1S3eR1A1A3S1S0S11S38G0A1S4eS38R1A1Z1A2A3S0S11S3dG0A1S3dR1A1A3A2A2A2A2A2A2A2A2A2A2A2A2FX;").

Section SEC7.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S12S9cVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S7SabSa3Vnx;A2SaA3").
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S11S87VCST;R1A2S87Sa7R2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S11S87VCST;R1A2S87Sa8R2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
SaaVnW;Vst;Vnx;VBX;A4").

Section FIN.
Variable BX : AA -> AA.
Hypothesis BXok : bx_ok BX.
Variables (blk : Z) (dpx : odefault) (NRESe : sv) (FXP : list sprop).
Hypothesis Hdpx : ltac2:(tb__ "0|0|
S3S0S23Vdpx;S26A3S0S23Vdpx;S27A3A2").

Hypothesis HPATH : ltac2:(tb__ "0|4|
S35S5cS15S4aQ40M0A1M1S15S6G1A1S6S91A1S90VJG;VBX;R8R7R6R5R4R3R2R1A9S67S17S1eR5A1VFXP;A3VBX;S5bRaS49G0S14R8PcA2A2A2A1S35S1S1S4cZ8M2Vblk;A2S4cVblk;Z20000A2A2S1S4cS4eS50G2S4dSbS37S36RbA1A2A1A2Vblk;A2S3aR1A1M3A2S0G1S1dR7VNRESe;A2S4bG0S4fG3G2A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variable partial : bool.
Variable F : axst.
Variables swc c1 c2 c4 c5 mc xc : list cell.
Variable tyb : Z.
Let K : list sobj := KEPTF W swc.
Let RS : list sobj := ltac2:(tb__ "0|0|
S6bVnx;Vc1;Vc2;Vc4;Vc5;Vmc;Vxc;Vblk;Vdpx;Vpartial;Aa").
Let R : list sobj := RT_m1 ++ RS.
Hypothesis SELF : ltac2:(tb__ "0|0|
S0S6S13A1S98S1fS56VF;A1A1S8aVnW;Vpartial;A2A2S8S13VK;VR;A3A3").
Hypothesis NDF : ltac2:(tb__ "0|0|
S0S7S97S8aVnW;Vpartial;A2A1SaA3").
Hypothesis BNDF : ltac2:(tb__ "0|0|
S0S7S32S4S4S9fR1SbS13S1fS56VF;A1A1A2A2Li;S8aVnW;Vpartial;A2A3SaA3").
Hypothesis COVF : ltac2:(tb__ "0|0|
S0S7S32S4S4S33S4S9eR1A1S8aVnW;Vpartial;A2A3Li;S66U0SbS13S1fS56VF;A1A1A2A2A3SaA3").
Hypothesis XFn : ax_X F = [].
Hypothesis BFb : ax_base F = base_sv.
Hypothesis FPF : ltac2:(tb__ "0|0|
S34S17S8S17S65VW;Vst;A2S64S63A1A3S1cS56VF;A1A1A3").
Hypothesis FXF : ltac2:(tb__ "0|0|
S34S17VFXP;S1cS56VF;A1A1A3").
Hypothesis FPAR : ltac2:(tb__ "0|0|
S31S17S7S17Lpartial;Vpartial;S22S6aA1S6aX7x2S1cS56VF;A1A1A3").

Hypothesis Hc1 : ltac2:(tb__ "0|0|
S1S31S16S70Vc1;A3S1S31S16S6cVc1;A3S1S31S16S6dVc1;A3S1S31S16S71Vc1;A3S1S31S16S6fVNRESe;A1Vc1;A3S31S16S6eVc1;A3A2A2A2A2A2").
Hypothesis Hmc : ltac2:(tb__ "0|0|
S1S31S16S75Vnx;A1Vmc;A3S1S31S16S76Vmc;A3S1S31S16S77Vmc;A3S1S31S16S73Vmc;A3S1S31S16S74Vmc;A3S1S31S16S72Vnx;A1Vmc;A3S1S31S16S7aVmc;A3S1S31S16S7bVtyb;A1Vmc;A3S1S31S16S79Vmc;A3S31S16S78Vmc;A3A2A2A2A2A2A2A2A2A2").
Hypothesis Htyb : ltac2:(tb__ "0|0|
S0S7SeSeS52Z0Vtyb;A2S53Vtyb;Z100A2A2S51S54Vtyb;Z4A2Z1A2A2SaA3").
Hypothesis Hxc : In (xc_map nx) xc.

Let KU : list sobj := ltac2:(tb__ "0|0|
S8cVW;Vswc;Vnx;A3").
Definition idxsU (n : nat) : list nat := ltac2:(tb__ "0|2|
S8S4S5S4U0S66U1M0Vn;A2A3S8S4S5S4S55Vn;U3A2S9S4A1M1A3S5S4S55Vn;G0A2S5S4S55Vn;U2A2G1A3A3A3A3").
Hypothesis WCU : ltac2:(tb__ "0|0|
S0S7S25S99S56VF;A1S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3A2A1SaA3").
Hypothesis SELU : ltac2:(tb__ "0|0|
S0S6S13A1S98S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3S89VnW;A1A2VKU;A3").
Hypothesis NDU : ltac2:(tb__ "0|0|
S0S7S97S89VnW;A1A1SaA3").
Hypothesis BNDU : ltac2:(tb__ "0|0|
S0S7S32S4S4S9fR1SbS13S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3A2A2Li;S89VnW;A1A3SaA3").
Hypothesis COVU : ltac2:(tb__ "0|0|
S0S7S32S4S4S33S4S9eR1A1S89VnW;A1A3Li;S66U0SbS13S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3A2A2A3SaA3").
Hypothesis W9 : ltac2:(tb__ "0|0|
S0S7S25S8bVF;VKU;A2A1SaA3").
Hypothesis D9 : ltac2:(tb__ "0|4|
S0S10SdS6SdS18S18A2M0A1M1S6S17A1M2A2M3A1Sa0S99S56VF;A1VKU;A2S8bVF;VKU;A2A2SfG3ScG1G2S5G0ScS18S18S20Sa4A1S19P18A1A4S9G0A1A3S9S17A1A4A2A3").
Hypothesis XB9 : ltac2:(tb__ "0|0|
S0S7S5aS24S56VF;A1A1ScS18S18S69Vnx;A1S19PcA1A4A2SaA3").
Variable s9 : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S7S58S8dVF;VKU;Vnx;A3S92VW;Vst;A2Vs9;A3SaA3").
Hypothesis SID9 : wsub_idc s9 = true.
Hypothesis G110 : ltac2:(tb__ "0|0|
S0S18Sa1Vs9;S61A2S69Vnx;A1A3").

Theorem sec_finish_P : ltac2:(tb__ "0|6|
S35S5cS15S15S4aQ40M0A1M1S15S6G1A1M2G2S7cS6SdS57S84A2M3A1S31G3ScS57S84S92VW;Vst;A2S93VCST;VXGL;RaR9A4A4R1A3S85VW;Vst;A2S5dRbA1S12S0G1S14RbR1A2S14RcR1A2A3Fi;S12S0S6S4aQ8A1A1S1aRcR1A2S1aRdR1A2A3Fl;S5eVCST;VXGL;RfRfS1bRdA1S1bRcA1A6S4cS4dSbS37S36R10A1A2A1S38R10A1A2SdS11S11A2M4S31G4R1S88S3bVBX;S5bR12S49G0S14RfPcM5A2A2A2A1A1A1A3S86R2ScS11S11S49G0RfA2S8eS49G0S14R10G5A2A2A1A4A2F_;Fbn;S80Vsegs;VJG;VBX;R12R11RfReA5VF;RdRbRaA6S83Vsegs;S7eR11RdRaRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a rhoE tp0 tp w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB H.
  destruct w as [tr [ms md]].
  pose proof H as [HsmA HJ]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (SPA_facts_hold segs _ rhoE F tp _ H) as HFacts.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & E145 & E146 & E147 & Erm & Erl).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  assert (HFX : Forall (holds rhoE) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HFacts p (FXF p Hp))).
  pose proof (HPATH A Kc rho a rhoE tp tr md HJ HFX) as (Hblk & HROOM & ENRES).
  pose proof (msx_val nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as EMSX.
  cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. set (L := secmapsize nv) in *.
  set (As := BX (bumpV A nv)) in *.
  destruct (BXok (bumpV A nv)) as (Bg & Bc & Bci & Bs & Bl & Bqt & Bqg & Bfh & Bfb & Bii & BV & BKm & BKf). fold As in Bg, Bc, Bci, Bs, Bl, Bqt, Bqg, Bfh, Bfb, Bii, BV, BKm, BKf.
  cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_live aa_q_thread aa_q_global aa_fs_hint aa_fs_busy aa_internal_inited aa_V aa_Km aa_Kf bumpV] in Bg, Bc, Bci, Bs, Bl, Bqt, Bqg, Bfh, Bfb, Bii, BV, BKm, BKf.
  pose proof HJ as ((Hagw & Hagl & Hagm) & Ha & HA & HP & HK & Htp & HU & _ & Htop & HBud). fold nv As in HA. fold nv ua L in HP.
  set (G := aa_geom A) in *. set (T := ag_thread G). set (idx := Z.of_nat (length (aa_sec A))) in *. set (ub := ua + 6144). set (pw := ag_pab G + 8 * idx).
  assert (E153 : rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top G)). { rewrite <- (Hagw 153%positive) by (unfold GW; lia). reflexivity. }
  assert (E154 : rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom G)). { rewrite <- (Hagw 154%positive) by (unfold GW; lia). reflexivity. }
  assert (E156 : rw rhoE 156%positive = Z_to_bv 64 (ag_spacebeg G + kSpaceSize)). { rewrite <- (Hagw 156%positive) by (unfold GW; lia). reflexivity. }
  assert (ErmF : rm rhoE = rm rho). { apply functional_extensionality. intros x. exact (Erm x). }
  pose proof HA as (HG & HR & HFs & HRest & HM & HI3 & HBt). rewrite Bg in HG. fold G in HG.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & _). fold T in G4, G5. pose proof (topG_range G) as ACV.
  pose proof (urange a) as Ra. fold ua in Ra. unfold IMG_HI in IMG. unfold PG in AL, SMM.

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (HaK : SPA segs KJ F rhoE tp (tr, {| cfg_ms := ms; cfg_model := md |})) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_select segs KJ rhoE F (idxsF nW partial) tp _ HaK NDF
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BNDF i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COVF i ltac:(apply in_seq; lia)) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsel.
  rewrite SELF in Hsel. clear HaK.

  pose proof (SPA_unobj segs KJ rhoE (ax_setS F (set_objs (ax_S F) (K ++ R))) K R tp tr ms md eq_refl Hsel (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE R (vms md tp ms)) in *.
  pose proof (proj1 (proj1 Hsel)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S ax_setS] in Hsm1.
  set (v3 := view segs (rm rho3)). set (vE := view segs (rm rhoE)).
  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoE _ tr (vms md tp ms) (vmd md) K R o Hsm1 eq_refl Ho)).
  assert (INRS : forall o, In o RS -> In o R) by (intros o Ho; unfold R; apply in_or_app; right; exact Ho).

  assert (AOC : forall o c bZ offZ V, In o RS -> In c (ob_cells o) ->
            bv_unsigned (eval rhoE (ob_base o)) = bZ -> soff rhoE (c_off c) = offZ -> eval rhoE (SymState.c_val c) = Z_to_bv 64 V ->
            0 <= bZ + offZ -> bZ + offZ + c_width c <= 2 ^ 64 ->
            cell_ok v3 (mkACell (bZ + offZ) (Z.to_nat (c_width c)) V)).
  { intros o c bZ offZ V Ho Hc Eb Eo Ev B1 B2. destruct (AO o (INRS o Ho)) as (_ & CO & _). destruct (CO c Hc) as (_ & _ & CJ).
    rewrite Eb, Eo, Ev in CJ. intros k Hk. cbn [c_addr c_w RtCells.c_val] in *. unfold v3. rewrite view_in by (clear -B1 B2 Hk; lia). exact (CJ k Hk). }
  assert (AOP : forall o z, In o RS -> (ob_dflt o = DUnknown \/ ob_dflt o = DZero) -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb).
  { intros o z Ho DD Hz. destruct (AO o (INRS o Ho)) as (Bo & _ & Po & _). unfold obj_range in Hz. cbn [fst snd] in Hz.
    unfold v3. rewrite view_in by (clear -Bo Hz; unfold obj_lo_of, obj_hi_of in *; lia).
    replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) by (clear; lia).
    apply Po; [exact DD | clear -Hz; unfold obj_lo_of, obj_hi_of in *; lia]. }
  assert (AOZ : forall o z, In o RS -> ob_dflt o = DZero -> ob_cells o = [] -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) ->
                        rd_of segs (rm rho3) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
  { intros o z Ho DZ NC Hz. destruct (AO o (INRS o Ho)) as (Bo & _ & _ & Zo). unfold obj_range in Hz. cbn [fst snd] in Hz.
    replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) by (clear; lia).
    apply Zo; [exact DZ | clear -Hz; unfold obj_lo_of, obj_hi_of in *; lia |]. rewrite NC. intros HX. inversion HX. }

  assert (EVnx : bv_unsigned (eval rhoE (SVar nx)) = ua) by (cbn [eval]; rewrite Enx; reflexivity).
  assert (UAB : 6565888 <= ua /\ ua + L <= 140737479966720 /\ 73728 <= L) by (clear -IMG TOP SMB; lia).
  assert (LB : nv + 8192 <= L).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  assert (WZ : forall w : word, w = Z_to_bv 64 (bv_unsigned w)) by (intros w0; symmetry; apply Z_to_bv_bv_unsigned).

  assert (IN_Mlo : In (O_Mlo nx mc) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_seci : In (O_seciF c1) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_secm : In O_secmF RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_px : In (O_pxF blk dpx xc) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_4z : In (O_4z nx) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  destruct Hmc as (M0 & M8 & M16 & M24 & M4096 & M4104 & M6128 & M6129 & M6130 & M6132).
  destruct Hc1 as (I0 & I8 & I16 & I24 & I48 & I56).
  assert (SOL : forall z, 0 <= z < 2 ^ 62 -> soff rhoE (SLit z) = z) by (intros z Hz; apply soff_lit_small; lia).

  assert (C0 : cell_ok v3 (mkACell ua 8 ua)).
  { replace ua with (ua + 0) at 1 by (clear; lia). apply (AOC (O_Mlo nx mc) (mc_map nx) ua 0 ua IN_Mlo M0 EVnx (SOL 0 ltac:(clear; lia))); [cbn [SymState.c_val mc_map eval]; rewrite Enx; apply WZ | clear -UAB; lia | cbn [c_width mc_map]; clear -UAB; lia]. }
  assert (C8 : cell_ok v3 (mkACell (ua + 8) 8 L)).
  { apply (AOC (O_Mlo nx mc) mc_ms ua 8 L IN_Mlo M8 EVnx (SOL 8 ltac:(clear; lia))); [cbn [SymState.c_val mc_ms]; rewrite (WZ (eval rhoE msx)), EMSX; reflexivity | clear -UAB; lia | cbn [c_width mc_ms]; clear -UAB; lia]. }
  assert (C16 : cell_ok v3 (mkACell (ua + 16) 8 (secneeded nv))).
  { apply (AOC (O_Mlo nx mc) mc_ns ua 16 (secneeded nv) IN_Mlo M16 EVnx (SOL 16 ltac:(clear; lia))); [cbn [SymState.c_val mc_ns eval]; exact E141 | clear -UAB; lia | cbn [c_width mc_ns]; clear -UAB; lia]. }
  assert (C24 : cell_ok v3 (mkACell (ua + 24) 8 idx)).
  { apply (AOC (O_Mlo nx mc) mc_idx ua 24 idx IN_Mlo M24 EVnx (SOL 24 ltac:(clear; lia))); [cbn [SymState.c_val mc_idx eval]; exact E147 | clear -UAB; lia | cbn [c_width mc_idx]; clear -UAB; lia]. }
  assert (VMG0 : cell_ok v3 (mkACell (ua + 4096) 8 kAllocBegMagic)).
  { apply (AOC (O_Mlo nx mc) mc_magic ua 4096 kAllocBegMagic IN_Mlo M4096 EVnx (SOL 4096 ltac:(clear; lia))); [reflexivity | clear -UAB; lia | cbn [c_width mc_magic]; clear -UAB; lia]. }
  assert (VMG8 : cell_ok v3 (mkACell (ua + 4104) 8 (ub - 16))).
  { apply (AOC (O_Mlo nx mc) (mc_cptr nx) ua 4104 (ub - 16) IN_Mlo M4104 EVnx (SOL 4104 ltac:(clear; lia))); [| clear -UAB; lia | cbn [c_width mc_cptr]; clear -UAB; lia].
    cbn [SymState.c_val mc_cptr]. apply bv_eq. cbn [eval]. rewrite Enx, add_val, !u64_lit by (unfold ub; clear -UAB; lia). fold ua. rewrite Z.mod_small by (clear -UAB; lia). unfold ub. clear. lia. }

  assert (EN12 : eval rhoE (SVar 12) = Z_to_bv 64 nv) by (cbn [eval]; rewrite E12; apply WZ).
  assert (B1E : forall z, 0 <= z < 256 -> nth 0 (enc_bytes 1 (Z_to_bv 64 z)) (Z_to_bv 8 0) = Z_to_bv 8 z).
  { intros z Hz. rewrite (ReprGlue.nth_enc_bytes 1 0 z ltac:(clear; lia) ltac:(clear; lia)). apply f_equal. unfold MallocInv.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by (clear -Hz; lia). reflexivity. }
  assert (VH2 : v3 (ub - 16) = Some (Z_to_bv 8 2)).
  { pose proof (AOC (O_Mlo nx mc) mc_state ua 6128 2 IN_Mlo M6128 EVnx (SOL 6128 ltac:(clear; lia)) eq_refl ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_state]; clear -UAB; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width mc_state Z.of_nat] in X. rewrite Z.add_0_r in X.
    replace (ub - 16) with (ua + 6128) by (unfold ub; clear; lia). rewrite X. apply f_equal. exact (B1E 2 ltac:(clear; lia)). }
  assert (VH1 : exists t, v3 (ub - 15) = Some t /\ bv_unsigned t mod 4 = 1).
  { apply andb_prop in Htyb as [Ht1 Ht2]. apply andb_prop in Ht1 as [Ht0 Ht1]. apply Z.leb_le in Ht0. apply Z.ltb_lt in Ht1. apply Z.eqb_eq in Ht2.
    pose proof (AOC (O_Mlo nx mc) (mc_type tyb) ua 6129 tyb IN_Mlo M6129 EVnx (SOL 6129 ltac:(clear; lia)) eq_refl ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_type]; clear -UAB; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width mc_type Z.of_nat] in X. rewrite Z.add_0_r in X.
    exists (Z_to_bv 8 tyb). split.
    - replace (ub - 15) with (ua + 6129) by (unfold ub; clear; lia). rewrite X. apply f_equal. exact (B1E tyb (conj Ht0 Ht1)).
    - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small tyb 256) by (clear -Ht0 Ht1; lia). exact Ht2. }
  assert (VHN : cell_ok v3 (mkACell (ub - 12) 4 (nv mod 2 ^ 32))).
  { pose proof (AOC (O_Mlo nx mc) mc_size ua 6132 nv IN_Mlo M6132 EVnx (SOL 6132 ltac:(clear; lia)) EN12 ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_size]; clear -UAB; lia)) as X.
    intros k Hk. specialize (X k Hk). cbn [c_addr c_w RtCells.c_val c_width mc_size] in X, Hk |- *. change (Z.to_nat 4) with 4%nat in X, Hk.
    replace (ub - 12 + Z.of_nat k) with (ua + 6132 + Z.of_nat k) by (unfold ub; clear; lia). rewrite X. apply f_equal.
    rewrite !(ReprGlue.nth_enc_bytes 4 k) by (first [exact Hk | clear; lia]). apply f_equal. unfold MallocInv.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by (clear; lia). reflexivity. }
  assert (VH0 : cell_ok v3 (mkACell (ub - 14) 2 (nv / 2 ^ 32))).
  { assert (EV : eval rhoE (SAlu ALU_SRL (SVar 12) (SLit 32)) = Z_to_bv 64 (nv / 2 ^ 32)).
    { apply bv_eq. cbn [eval]. rewrite E12, srl_val. fold nv. change (32 mod 64) with 32. rewrite Z.shiftr_div_pow2 by (clear; lia).
      symmetry. apply u64_lit. pose proof (Z.div_pos nv (2 ^ 32) ltac:(clear -HN; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound nv (2 ^ 32) (2 ^ 7) ltac:(clear; lia) ltac:(clear -HN; lia)). lia. }
    pose proof (AOC (O_Mlo nx mc) mc_sizehi ua 6130 (nv / 2 ^ 32) IN_Mlo M6130 EVnx (SOL 6130 ltac:(clear; lia)) EV ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_sizehi]; clear -UAB; lia)) as X.
    replace (ub - 14) with (ua + 6130) by (unfold ub; clear; lia). exact X. }

  assert (EV0 : bv_unsigned (eval rhoE (SLit 0)) = 0) by reflexivity.
  assert (SECB : 0 <= SEC_INST /\ 0xead04 <= 2 ^ 62) by (unfold SEC_INST; clear; lia).
  assert (CI0 : cell_ok v3 (mkACell SEC_INST 8 PG)).
  { pose proof (AOC (O_seciF c1) ic_pg 0 SEC_INST PG IN_seci I0 EV0 (SOL SEC_INST ltac:(unfold SEC_INST; clear; lia)) eq_refl ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI8 : cell_ok v3 (mkACell (SEC_INST + 8) 8 (ag_pab G))).
  { pose proof (AOC (O_seciF c1) ic_c1 0 (SEC_INST + 8) (ag_pab G) IN_seci I8 EV0 (SOL (SEC_INST + 8) ltac:(unfold SEC_INST; clear; lia)) ltac:(cbn [SymState.c_val ic_c1 eval]; exact E145) ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI16 : cell_ok v3 (mkACell (SEC_INST + 16) 8 (ag_pab G))).
  { pose proof (AOC (O_seciF c1) ic_c2 0 (SEC_INST + 16) (ag_pab G) IN_seci I16 EV0 (SOL (SEC_INST + 16) ltac:(unfold SEC_INST; clear; lia)) ltac:(cbn [SymState.c_val ic_c2 eval]; exact E145) ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI24 : cell_ok v3 (mkACell (SEC_INST + 24) 8 kPtrArrayReserve)).
  { pose proof (AOC (O_seciF c1) ic_rs 0 (SEC_INST + 24) kPtrArrayReserve IN_seci I24 EV0 (SOL (SEC_INST + 24) ltac:(unfold SEC_INST; clear; lia)) eq_refl ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (C48 : cell_ok v3 (mkACell (SEC_INST + 48) 8 (aa_ptr_committed As / 8))).
  { pose proof (AOC (O_seciF c1) (ic_nres NRESe) 0 (SEC_INST + 48) (aa_ptr_committed As / 8) IN_seci I48 EV0 (SOL (SEC_INST + 48) ltac:(unfold SEC_INST; clear; lia)) ENRES ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  pose proof (Zle_0_nat (length (aa_sec A))) as IDX0. fold idx in IDX0.
  pose proof HRest as (_ & _ & _ & HSRs & _). pose proof (pab_facts _ As HSRs) as (P1 & P2 & P3 & P4 & P5). rewrite Bg in P1, P2, P3. rewrite Bs in P4. fold G in P1, P2, P3. fold idx in P4.
  unfold IMG_HI in P1. unfold kPtrArrayReserve in P2, P4.
  assert (C56 : cell_ok v3 (mkACell (SEC_INST + 56) 8 (idx + 1))).
  { assert (EV : eval rhoE (SAlu ALU_ADD (SVar V_NCH) (SLit 1)) = Z_to_bv 64 (idx + 1)).
    { apply bv_eq. cbn [eval]. rewrite E147, add_val, !u64_lit by (clear -IDX0 P4; lia). fold idx. apply Z.mod_small. clear -IDX0 P4. lia. }
    pose proof (AOC (O_seciF c1) ic_nch 0 (SEC_INST + 56) (idx + 1) IN_seci I56 EV0 (SOL (SEC_INST + 56) ltac:(unfold SEC_INST; clear; lia)) EV ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CMU : cell_ok v3 (mkACell 0xead00 4 0)).
  { pose proof (AOC O_secmF (mkCell (SLit 0xead00) 1 (SLit 0)) 0 0xead00 0 IN_secm ltac:(cbn; left; reflexivity) EV0 (SOL 0xead00 ltac:(clear; lia)) eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)) as X1.
    pose proof (AOC O_secmF (mkCell (SLit 0xead01) 3 (SLit 0)) 0 0xead01 0 IN_secm ltac:(cbn; right; left; reflexivity) EV0 (SOL 0xead01 ltac:(clear; lia)) eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)) as X3.
    assert (ZB : forall w k, (k < w)%nat -> (w <= 8)%nat -> nth k (enc_bytes w (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros w0 k0 H1 H2. rewrite (ReprGlue.nth_enc_bytes w0 k0 0 H1 H2). apply f_equal. unfold MallocInv.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
    intros k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite (ZB 4%nat k Hk ltac:(clear; lia)).
    destruct k as [|k].
    - specialize (X1 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width] in X1. change (Z.to_nat 1) with 1%nat in X1. rewrite (ZB 1%nat 0%nat ltac:(clear; lia) ltac:(clear; lia)) in X1.
      replace (0xead00 + Z.of_nat 0) with (0 + 0xead00 + Z.of_nat 0) by (clear; lia). exact X1.
    - specialize (X3 k ltac:(cbn; clear -Hk; lia)). cbn [c_addr c_w RtCells.c_val c_width] in X3. change (Z.to_nat 3) with 3%nat in X3. rewrite (ZB 3%nat k ltac:(clear -Hk; lia) ltac:(clear; lia)) in X3.
      replace (0xead00 + Z.of_nat (S k)) with (0 + 0xead01 + Z.of_nat k) by (clear; lia). exact X3. }

  assert (EBw : bv_unsigned (eval rhoE Bw) = pw).
  { unfold Bw, pw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G idx. rewrite !u64_lit by (clear -P1 P2 P4 IDX0 ACV; lia).
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
    rewrite (Z.mod_small (idx * 8)) by (clear -IDX0 P4; lia). rewrite Z.mod_small by (clear -P1 P2 P4 IDX0 ACV; lia). clear. lia. }
  assert (PWB : ag_pab G <= pw /\ pw + blk <= ag_pab G + 8388608) by (unfold pw; clear -IDX0 HROOM P4; lia).
  assert (CPW : cell_ok v3 (mkACell pw 8 ua)).
  { pose proof (AOC (O_pxF blk dpx xc) (xc_map nx) pw 0 ua IN_px Hxc EBw (SOL 0 ltac:(clear; lia)) ltac:(cbn [SymState.c_val xc_map eval]; rewrite Enx; apply WZ)
                  ltac:(clear -PWB P1; lia) ltac:(cbn [c_width xc_map]; clear -PWB P2 ACV Hblk; lia)) as X.
    rewrite Z.add_0_r in X. exact X. }

  destruct (site8_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB4 & EL4 & _). cbn zeta in EB4, EL4. fold nv ua in EB4, EL4.
  assert (ESHub : Sh ub = Sh ua + 768).
  { unfold Sh, ub. replace (ua + 6144) with (ua + 768 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear. lia. }
  pose proof (Z.div_pos nv 8 ltac:(clear -HN; lia) ltac:(clear; lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(clear; lia) ltac:(clear -HN; lia)) as NU.
  assert (SHB : 2147450880 <= Sh ua /\ Sh ua + L / 8 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos ua 8 ltac:(clear -UAB; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_le_mono (ua + L) 140737479966720 8 ltac:(clear; lia) ltac:(clear -UAB; lia)) as D1. change (140737479966720 / 8) with 17592184995840 in D1.
    assert (DS : ua / 8 + L / 8 <= (ua + L) / 8) by (apply Z.div_le_lower_bound; [clear; lia|]; pose proof (Z.mul_div_le ua 8 ltac:(clear; lia)); pose proof (Z.mul_div_le L 8 ltac:(clear; lia)); lia).
    clear -D0 D1 DS. lia. }
  assert (L8B : nv / 8 + 1024 <= L / 8).
  { pose proof (Z.div_le_mono (nv + 8192) L 8 ltac:(clear; lia) LB) as D. replace (nv + 8192) with (nv + 1024 * 8) in D by (clear; lia). rewrite Z.div_add in D by (clear; lia). exact D. }
  assert (VZ : forall g, 0 <= g < nv / 8 -> v3 (Sh ub + g) = Some (Z_to_bv 8 0)).
  { intros g Hg. destruct (AO _ (INRS _ IN_4z)) as (_ & _ & _ & ZO). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_4z] in ZO. specialize (ZO eq_refl g).
    unfold obj_lo_of, obj_hi_of in ZO. cbn [ob_lo ob_hi ob_cells ob_base O_4z] in ZO. rewrite soff_lit_small in ZO by (clear; lia).
    rewrite (soff_of_val rhoE (a2e8 nx) (nv / 8) EL4) in ZO by (clear -NP NU; lia). rewrite EB4 in ZO.
    unfold v3. rewrite view_in by (rewrite ESHub; clear -SHB Hg L8B; lia). rewrite ESHub.
    apply ZO; [exact Hg|]. intros HC. unfold covered in HC. apply Exists_exists in HC as (cc & Hcc & _). exact Hcc. }
  pose proof (nmod8_of_par nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (PAR0 & PAR1). fold nv in PAR0, PAR1.
  pose proof (proj1 (Forall_forall _ _) HFacts _ FPAR) as HPARF.
  destruct (site9_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (_ & EBP9). cbn zeta in EBP9. fold nv ua in EBP9.
  assert (VP : nv mod 8 <> 0 -> v3 (Sh ub + nv / 8) = Some (Z_to_bv 8 (nv mod 8))).
  { intros Hm. destruct partial eqn:EP; [|exfalso; exact (Hm (PAR0 HPARF))].
    assert (IN_P : In (O_Pf9 nx) RS) by (unfold RS, RSF; try rewrite EP; cbn [app In]; repeat (first [left; reflexivity | right])).
    assert (EV : eval rhoE (SAlu ALU_AND (SVar 12) (SLit 7)) = Z_to_bv 64 (nv mod 8)).
    { apply bv_eq. cbn [eval]. rewrite E12, and_val. fold nv. rewrite (u64_lit 7) by (clear; lia). rewrite land_7 by (clear -HN; lia). symmetry. apply u64_lit. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)). lia. }
    pose proof (AOC (O_Pf9 nx) (mkCell (SLit 0) 1 (SAlu ALU_AND (SVar 12) (SLit 7))) (Sh ua + 768 + nv / 8) 0 (nv mod 8) IN_P ltac:(cbn; left; reflexivity) EBP9 (SOL 0 ltac:(clear; lia)) EV
                  ltac:(clear -SHB NP; lia) ltac:(cbn [c_width]; clear -SHB L8B; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width Z.of_nat] in X. rewrite !Z.add_0_r in X.
    rewrite ESHub. rewrite X. apply f_equal. apply B1E. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)). lia. }

  destruct (site7_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM. fold nv ua L in EBR, EL3b, V512, VM.
  destruct (site3_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB3 & _ & EL3). fold ua in EB3.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB1 & EL1 & _). fold ua in EB1.
  assert (EUB : bv_unsigned (eval rhoE (UBs nx)) = ub).
  { unfold UBs. cbn [eval]. rewrite Enx, add_val, !u64_lit by (clear; lia). fold ua. rewrite Z.mod_small by (clear -UAB; lia). reflexivity. }
  assert (EVT : bv_unsigned (eval rhoE vT) = T) by (unfold vT; cbn [eval]; rewrite E151; apply u64_lit; fold G T; clear -G4 G5 ACV; lia).
  assert (RG_Mlo : obj_range rhoE (O_Mlo nx mc) = (ua, ua + 6144)) by (unfold O_Mlo; rewrite obj_range_mk by (clear; lia); rewrite EVnx; f_equal; clear; lia).
  assert (RG_fill : obj_range rhoE (O_fill nx) = (ub, ub + 4096)) by (unfold O_fill; rewrite obj_range_mk by (clear; lia); rewrite EVnx; unfold ub; f_equal; clear; lia).
  assert (RG_Mhi : obj_range rhoE (O_Mhi nx) = (ua + 10240, ua + L)).
  { unfold O_Mhi, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (SVar V_MS) L) by (first [cbn [eval]; rewrite E142; apply u64_lit; clear -UAB; lia | clear -UAB; lia]). rewrite EVnx. reflexivity. }
  assert (RG_1 : obj_range rhoE (O_1 nx) = (Sh ua, Sh ua + 512)) by (unfold O_1, L1; rewrite obj_range_mk by (clear; lia); rewrite EB1; f_equal; clear; lia).
  assert (RG_3 : obj_range rhoE (O_3 nx) = (Sh ua + 512, Sh ua + 768)) by (unfold O_3, L3; rewrite obj_range_mk by (clear; lia); rewrite EB3; f_equal; clear; lia).
  assert (RG_4z : obj_range rhoE (O_4z nx) = (Sh ua + 768, Sh ua + 768 + nv / 8)).
  { unfold O_4z, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (a2e8 nx) (nv / 8) EL4) by (clear -NP NU; lia). rewrite EB4. f_equal. clear. lia. }
  set (v8 := secneeded nv / 8) in *.
  assert (RG_3b : obj_range rhoE (O_3b nx) = (Sh ua + v8 + 256, Sh ua + L / 8)).
  { unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE L3b (L / 8 - v8 - 256) EL3b) by (clear -V512 VM SHB; lia). rewrite EBR. f_equal; clear; lia. }
  assert (RG_P : obj_range rhoE (O_Pf9 nx) = (Sh ua + 768 + nv / 8, Sh ua + 768 + nv / 8 + 1)) by (unfold O_Pf9; rewrite obj_range_mk by (clear; lia); rewrite EBP9; f_equal; clear; lia).
  assert (RG_px : obj_range rhoE (O_pxF blk dpx xc) = (pw, pw + blk)) by (unfold O_pxF; rewrite obj_range_mk by (clear -Hblk; lia); rewrite EBw; f_equal; clear; lia).
  assert (RG_st : obj_range rhoE (O_stF c5) = (T + 2768, T + 3168)) by (unfold O_stF; rewrite obj_range_mk by (clear; lia); rewrite EVT; reflexivity).
  assert (RG_seci : obj_range rhoE (O_seciF c1) = (SEC_INST, SEC_INST + 64)) by (unfold O_seciF; rewrite obj_range_mk by (unfold SEC_INST; clear; lia); reflexivity).
  assert (RG_secs : obj_range rhoE (O_secsF c2) = (SEC_INST + 64, 0xead00)) by (unfold O_secsF; rewrite obj_range_mk by (unfold SEC_INST; clear; lia); reflexivity).
  assert (RG_secm : obj_range rhoE O_secmF = (0xead00, 0xead04)) by (unfold O_secmF; rewrite obj_range_mk by (clear; lia); reflexivity).
  assert (RG_secg : obj_range rhoE (O_secgF c4) = (0xead08, 0xead30)) by (unfold O_secgF; rewrite obj_range_mk by (clear; lia); reflexivity).
  assert (RG_san : obj_range rhoE O_san = (0xe67b8, 0xe67c0)).
  { change O_san with (mkObj (SLit 0) (SLit 0xe67b8) (SLit 0xe67c0) (ob_cells O_san) DUnknown). rewrite obj_range_mk by (clear; lia). reflexivity. }
  assert (RG_oom : obj_range rhoE O_oom = (0x170320, 0x170322)).
  { change O_oom with (mkObj (SLit 0) (SLit 0x170320) (SLit 0x170322) (ob_cells O_oom) DUnknown). rewrite obj_range_mk by (clear; lia). reflexivity. }
  assert (RG_errno : obj_range rhoE O_errno = (ERRNO_A, ERRNO_A + 4)).
  { change O_errno with (mkObj (SLit 0) (SLit ERRNO_A) (SLit (ERRNO_A + 4)) (ob_cells O_errno) DUnknown). rewrite obj_range_mk by (unfold ERRNO_A; clear; lia). reflexivity. }

  assert (PARB : if partial then nv mod 8 <> 0 else nv mod 8 = 0) by (destruct partial; [exact (PAR1 HPARF) | exact (PAR0 HPARF)]).
  assert (EV8 : v8 = 768 - 256 + nv / 8 + (if partial then 1 else 0)).
  { unfold v8. rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia).
    unfold round_up. rewrite Z.div_mul by (clear; lia). pose proof (Z.div_mod nv 8 ltac:(clear; lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)) as MN.
    destruct partial.
    - replace ((nv + 8 - 1) / 8) with (nv / 8 + 1) by (apply Z.div_unique with (nv mod 8 - 1); clear -DN MN PARB; lia). clear. lia.
    - replace ((nv + 8 - 1) / 8) with (nv / 8) by (apply Z.div_unique with 7; clear -DN MN PARB; lia). clear. lia. }

  assert (DUK : forall o, In o RS -> ob_dflt o = DUnknown \/ ob_dflt o = DZero).
  { intros o Ho. unfold RS, RSF in Ho. apply in_app_or in Ho as [Ho|Ho]; [|apply in_app_or in Ho as [Ho|Ho]; [|apply in_app_or in Ho as [Ho|Ho]]].
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [ob_dflt O_fill O_4z O_3b O_3 O_1]; first [left; reflexivity | right; reflexivity].
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; left; reflexivity.
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[]]]]; cbn [ob_dflt O_Mlo O_Mhi O_pxF]; [right; reflexivity | right; reflexivity | exact Hdpx].
    - destruct partial; cbn [In] in Ho; [destruct Ho as [<-|[]]; left; reflexivity | destruct Ho]. }
  assert (INL : forall o, In o ([O_fill nx; O_4z nx; O_3b nx; O_3 nx; O_1 nx] ++ [O_seciF c1; O_secsF c2; O_secmF; O_secgF c4; O_san; O_oom; O_errno; O_stF c5] ++ [O_Mlo nx mc; O_Mhi nx; O_pxF blk dpx xc]) -> In o RS).
  { intros o Ho. unfold RS, RSF. apply in_app_or in Ho as [Ho|Ho]; [apply in_or_app; left; exact Ho|].
    apply in_app_or in Ho as [Ho|Ho]; apply in_or_app; right; apply in_or_app; [left; exact Ho | right; apply in_or_app; left; exact Ho]. }
  assert (PRESo : forall o z, In o RS -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb) by (intros o z Ho Hz; exact (AOP o z Ho (DUK o Ho) Hz)).
  assert (PRES : forall z, chg_s G ua L pw blk z -> exists b, v3 z = Some b).
  { intros z [X|[X|[[X|X]|X]]].
    - unfold zimg in X. destruct X as [X|[X|[X|X]]].
      + destruct (Z_lt_dec z (SEC_INST + 64)) as [L1|L1]; [|destruct (Z_lt_dec z 0xead00) as [L2|L2]].
        * apply (PRESo (O_seciF c1) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_seci; cbn [fst snd]; clear -X L1; lia].
        * apply (PRESo (O_secsF c2) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secs; cbn [fst snd]; clear -X L1 L2; lia].
        * apply (PRESo O_secmF z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secm; cbn [fst snd]; clear -X L2; lia].
      + apply (PRESo (O_secgF c4) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secg; cbn [fst snd]; exact X].
      + apply (PRESo O_oom z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_oom; cbn [fst snd]; clear -X; lia].
      + apply (PRESo O_errno z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_errno; cbn [fst snd]; exact X].
    - apply (PRESo (O_stF c5) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_st; cbn [fst snd]; exact X].
    - destruct (Z_lt_dec z (ua + 6144)) as [L1|L1]; [|destruct (Z_lt_dec z (ua + 10240)) as [L2|L2]].
      + apply (PRESo (O_Mlo nx mc) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_Mlo; cbn [fst snd]; clear -X L1; lia].
      + apply (PRESo (O_fill nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_fill; cbn [fst snd]; unfold ub; clear -L1 L2; lia].
      + apply (PRESo (O_Mhi nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_Mhi; cbn [fst snd]; clear -X L2; lia].
    - destruct (Z_lt_dec z (Sh ua + 512)) as [L1|L1]; [|destruct (Z_lt_dec z (Sh ua + 768)) as [L2|L2]; [|destruct (Z_lt_dec z (Sh ua + 768 + nv / 8)) as [L3|L3]]].
      + apply (PRESo (O_1 nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_1; cbn [fst snd]; clear -X L1; lia].
      + apply (PRESo (O_3 nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_3; cbn [fst snd]; clear -L1 L2; lia].
      + apply (PRESo (O_4z nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_4z; cbn [fst snd]; clear -L2 L3; lia].
      + destruct (Z_lt_dec z (Sh ua + v8 + 256)) as [L4|L4].
        *
          destruct partial eqn:EP; [|exfalso; clear -L3 L4 EV8; lia].
          apply (PRESo (O_Pf9 nx) z); [unfold RS, RSF; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity | rewrite RG_P; cbn [fst snd]; clear -L3 L4 EV8; lia].
        * apply (PRESo (O_3b nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_3b; cbn [fst snd]; clear -X L4; lia].
    - apply (PRESo (O_pxF blk dpx xc) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_px; cbn [fst snd]; exact X]. }

  set (K_san := ((SLit 0, 0xe67b8, 0xe67c0, [(0xe67b8, 8%nat, SLit 0x1a309)]) : carve_spec)).
  assert (ESAN : carve_obj K_san = O_san) by reflexivity.
  assert (SM_san : spec_small K_san) by (unfold K_san, spec_small; split; [lia|]; split; [lia|]; split; [lia|]; unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  assert (INR : forall x : word, in_ranges rhoE R x ->
            (exists k, In k (N_m1 ++ [K_san]) /\ fst (spec_range rhoE k) <= bv_unsigned x < snd (spec_range rhoE k))
            \/ chg_s G ua L pw blk (bv_unsigned x) \/ bv_unsigned x = 0x170321).
  { intros x (o & HoR & Hr). unfold R in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [apply in_or_app; left; exact Hk|].
      rewrite (carve_range rhoE k (proj1 (Forall_forall _ _) N_m1_small k Hk)) in Hr. exact Hr.
    - set (z := bv_unsigned x) in *.
      assert (RUNZ : Sh ua <= z < Sh ua + L / 8 -> chg_s G ua L pw blk z) by (intros X; right; right; left; right; exact X).
      assert (MAPZ : ua <= z < ua + L -> chg_s G ua L pw blk z) by (intros X; right; right; left; left; exact X).
      assert (IMGZ : zimg z -> chg_s G ua L pw blk z) by (intros X; left; exact X).
      unfold RS, RSF in HoR. apply in_app_or in HoR as [HoR|HoR]; [|apply in_app_or in HoR as [HoR|HoR]; [|apply in_app_or in HoR as [HoR|HoR]]].
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[<-|[<-|[]]]]]]; right; left.
        * rewrite RG_fill in Hr. cbn [fst snd] in Hr. apply MAPZ. unfold ub in Hr. clear -Hr LB HN. lia.
        * rewrite RG_4z in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B. lia.
        * rewrite RG_3b in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr V512. lia.
        * rewrite RG_3 in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia.
        * rewrite RG_1 in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia.
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
        * right; left. apply IMGZ. rewrite RG_seci in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secs in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secm in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secg in Hr. cbn [fst snd] in Hr. unfold zimg in *. clear -Hr. lia.
        * left. exists K_san. split; [apply in_or_app; right; left; reflexivity|]. rewrite <- (carve_range rhoE K_san SM_san), ESAN. exact Hr.
        * rewrite RG_oom in Hr. cbn [fst snd] in Hr. destruct (Z.eq_dec z 0x170320) as [E0|NE0]; [right; left; apply IMGZ; unfold zimg; clear -E0; lia | right; right; clear -Hr NE0; lia].
        * right; left. apply IMGZ. rewrite RG_errno in Hr. cbn [fst snd] in Hr. unfold zimg. clear -Hr. lia.
        * right; left. right; left. rewrite RG_st in Hr. exact Hr.
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[]]]]; right; left.
        * rewrite RG_Mlo in Hr. cbn [fst snd] in Hr. apply MAPZ. clear -Hr UAB. lia.
        * rewrite RG_Mhi in Hr. cbn [fst snd] in Hr. apply MAPZ. clear -Hr. lia.
        * rewrite RG_px in Hr. right; right; right. exact Hr.
      + destruct partial; cbn [In] in HoR; [|destruct HoR]. destruct HoR as [<-|[]]. right; left. rewrite RG_P in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia. }

  pose proof HRest as (Hsep & _ & _ & _ & _ & _ & _ & _ & HMIs).
  assert (HAg : AInv As rhoE tp md) by exact HA.
  assert (NK : forall k, In k (N_m1 ++ [K_san]) -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoE (rd_of segs (rm rhoE)) (fst (spec_range rhoE k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk. apply in_app_or in Hk as [Hk|Hk].
    - split; [unfold R; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
      split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
      split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
      pose proof (proj1 (Forall_forall _ _) (N_m1_civ AInvA_die As rhoE tp md HAg ltac:(rewrite Bg; exact E151) ltac:(rewrite Bg; exact E152) ltac:(rewrite Bg; exact E153) ltac:(rewrite Bg; exact E154)
                                               ltac:(rewrite Bg; exact E155) ltac:(rewrite Bg; exact E156)) k Hk) as CV. cbn beta in CV.
      destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by (clear; lia). exact CV.
    - destruct Hk as [<-|[]].
      split; [unfold R; apply in_or_app; right; rewrite ESAN; apply INL; cbn [app In]; repeat (first [left; reflexivity | right])|].
      split; [exact SM_san|].
      split; [apply coverb_sound; reflexivity|].
      destruct HMIs as (HMIc & _ & _). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMIc))))) as HSAN.
      assert (CSAN : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xe67b8) 8 0x1a309)).
      { intros j Hj. specialize (HSAN j Hj). cbn [c_addr c_w RtCells.c_val] in HSAN, Hj |- *. rewrite Bg in HSAN. fold G in HSAN.
        rewrite maskv_out in HSAN by (apply (fs_footb_img G _ HG); clear -Hj; lia). exact HSAN. }
      cbn [spec_range fst K_san]. replace (bv_unsigned (eval rhoE (SLit 0)) + 0xe67b8 - 0xe67b8) with 0 by (cbn [eval]; rewrite u64_lit by (clear; lia); clear; lia).
      unfold cells_in_view. apply Forall_cons; [|apply Forall_nil].
      exact (civ_cell rhoE (rm rhoE) 0 0xe67b8 8 0x1a309 (SLit 0x1a309) CSAN eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)). }
  assert (VO : forall z, ~ chg_s G ua L pw blk z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z) as [l|n]; [destruct (Z_lt_dec z (2 ^ 64)) as [l0|n]|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoE R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by (clear -l l0; lia).
      + unfold rho3. exact (absorb_specs_view rhoE _ tr (vms md tp ms) (vmd md) K R (N_m1 ++ [K_san]) (rd_of segs (rm rhoE)) Hsm1 eq_refl NK z k Hk Hr).
      + exfalso. exact (Hz Hc).
      +
        assert (IN_oom : In O_oom R) by (apply INRS; apply INL; cbn [app In]; repeat (first [left; reflexivity | right])).
        destruct (AO _ IN_oom) as (_ & CE & _ & _). change (ob_cells O_oom) with [mkCell (SLit 0x170321) 1 (SLit 1)] in CE.
        destruct (CE _ (or_introl eq_refl)) as (_ & _ & CEj). pose proof (CEj 0%nat ltac:(cbn; clear; lia)) as X. clear CEj.
        change (ob_base O_oom) with (SLit 0) in X. cbn [c_off c_width SymState.c_val eval] in X. change (Z.to_nat 1) with 1%nat in X. change (Z.of_nat 0) with 0 in X.
        rewrite soff_lit_small, (u64_lit 0), Z.add_0_r in X by (clear; lia). rewrite Z.add_0_l in X. rewrite E1. unfold rho3.
        transitivity (Some (nth 0 (enc_bytes 1 (Z_to_bv 64 1)) (Z_to_bv 8 0))); [exact X|]. symmetry.
        destruct HMIs as (HMIc & _ & _). pose proof (Forall_inv HMIc) as C9. specialize (C9 0%nat ltac:(cbn; clear; lia)).
        cbn [c_addr c_w RtCells.c_val Z.of_nat] in C9. rewrite Z.add_0_r in C9. rewrite Bg in C9. fold G in C9.
        rewrite maskv_out in C9 by (apply (fs_footb_img G _ HG); clear; lia). rewrite view_in in C9 by (clear; lia). exact C9.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (RMO : forall x, 0 <= x < 2 ^ 64 -> ~ rt_zoneM G x -> ~ chg_s G ua L pw blk x -> ~ in_rangesZ IMG_S x -> rm rho3 (Z_to_bv 64 x) = rm rhoE (Z_to_bv 64 x)).
  { intros x Bx Hz1 Hz2 Hz4. unfold rho3. apply rm_absorb_out. intros Hin.
    destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by exact Bx.
    - apply in_app_or in Hk as [Hk|Hk].
      + apply Hz1. exact (N_m1_zone G rhoE k x HG E151 E152 Hk Hr).
      + destruct Hk as [<-|[]]. apply Hz4. cbn [spec_range fst snd K_san eval] in Hr. rewrite (u64_lit 0) in Hr by (clear; lia).
        unfold IMG_S, in_rangesZ. exists 0xe67b8, 8. split; [right; right; left; reflexivity | clear -Hr; lia].
    - exact (Hz2 Hc).
    - apply Hz4. unfold IMG_S, in_rangesZ. exists 0x170320, 2. split; [right; right; right; left; reflexivity | clear -E1; lia]. }
  assert (RWR : Forall (fun o => dflt_writable (ob_dflt o) = true) R).
  { unfold R. apply Forall_app. split.
    - pose proof (R9_writable [] [] []) as X. unfold R9 in X. apply Forall_app in X. exact (proj1 X).
    - apply Forall_forall. intros o Ho. destruct (DUK o Ho) as [E|E]; rewrite E; reflexivity. }
  assert (DEFM : forall x, IMG_HI <= x < 2 ^ 64 -> rm rhoE (Z_to_bv 64 x) <> None -> rm rho3 (Z_to_bv 64 x) <> None).
  { intros x Bx Hd. destruct (in_ranges_dec rhoE R (Z_to_bv 64 x)) as [Hin|Hout].
    - unfold rho3. apply (absorb_defined rhoE _ tr (vms md tp ms) (vmd md) K R (Z_to_bv 64 x) Hsm1 eq_refl RWR Hin). rewrite u64_lit by (unfold IMG_HI in Bx; clear -Bx; lia). exact (proj1 Bx).
    - unfold rho3. rewrite rm_absorb_out by exact Hout. exact Hd. }
  assert (DEFB : forall x, SHADOW_BAND_LO <= x < SHADOW_BAND_HI -> rm rhoE (Z_to_bv 64 x) <> None -> rm rho3 (Z_to_bv 64 x) <> None).
  { intros x Bx. apply DEFM. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *. clear -Bx. lia. }

  assert (HPDs : pendS As ua L md).
  { destruct HP as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12). unfold pendS. rewrite Bg, Bs. fold G.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
    split; [exact Q9|]. split; [exact Q10|]. split; [exact Q11|]. exact HDB. }
  assert (HKMs : idx + 1 <= aa_Km As) by (rewrite BKm; unfold idx; clear -HL9; lia).
  pose proof (sec_rebuild As rhoE rho3 tp md nv ua blk HA HN) as RB. cbn zeta in RB. rewrite Bg, Bs in RB. fold G idx L ub pw v3 vE in RB.
  specialize (RB HPDs (proj1 Hblk) HROOM HKMs C0 C8 C16 C24 CPW CI0 CI8 CI16 CI24 C48 C56 CMU VH2 VHN VH0 VH1 VMG0 VMG8 VZ VP PRES VO DEFB).
  pose proof (sec_kept CST XGL HCST HXGL HCSTM HCSTS As rhoE rho3 tp md nv ua blk HA HN) as KP. cbn zeta in KP. rewrite Bg, Bs in KP. fold G idx L pw in KP.
  specialize (KP HPDs (proj1 Hblk) HROOM RMO DEFB).

  set (A1 := ax_setS (ax_setS F (set_objs (ax_S F) (K ++ R))) (set_objs (ax_S (ax_setS F (set_objs (ax_S F) (K ++ R)))) K)) in Hb.
  assert (EV3 : forall e, eval rho3 e = eval rhoE e) by (intros e; unfold rho3; apply eval_absorb).
  assert (OR3 : forall o, obj_range rho3 o = obj_range rhoE o) by (intros o; unfold obj_range, obj_lo_of, obj_hi_of, soff; rewrite !EV3; reflexivity).
  assert (HFXP : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoE p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HFacts p (FPF p Hp))).
  assert (Hhigh : holds rhoE F_sp_high) by (apply HFXP; apply in_or_app; right; unfold pre_facts; cbn [app In]; right; left; reflexivity).
  destruct (sw_range_gen segs rhoE (set_objs (ax_S F) (K ++ R)) _ (sw9 swc) Hsm1 ltac:(cbn; left; reflexivity) eq_refl Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE (sw9 swc))) by (rewrite (sw_lo_gen rhoE (sw9 swc) eq_refl); exact Htop).
  assert (LNK : Forall (fun o => topG G + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG G)); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp. apply HFXP. apply in_or_app. left. exact (chain_pre_factsS W st p HW Hp). }
  pose proof HP as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & PDT & _ & PDB). fold G in PDT. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB.

  assert (KDISJ : forall lo hi, 6565888 <= lo -> hi <= topG G -> Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo, hi)) K).
  { intros lo hi Hlo Hhi. unfold K, KEPTF. constructor.
    - unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Hhi. lia.
    - apply Forall_app. split.
      + eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
        unfold ranges_disjoint. rewrite obj_range_mk by (clear; lia). cbn [fst snd]. right; right; right. clear -B1 Hhi. lia.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
          unfold ranges_disjoint; rewrite obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite u64_lit by (clear; lia); right; right; left; clear -Hlo; lia. }
  assert (RM3 : forall z, ua <= z < ua + L \/ Sh ua <= z < Sh ua + L / 8 -> rm rho3 (Z_to_bv 64 z) <> None).
  { intros z Hz. assert (CZ : chg_s G ua L pw blk z) by (right; right; left; exact Hz). destruct (PRES z CZ) as [bb Hbb].
    assert (BZ : 0x643000 <= z < 2 ^ 64) by (destruct Hz as [Hz|Hz]; [clear -Hz UAB; lia | clear -Hz SHB; lia]).
    unfold v3 in Hbb. rewrite view_in in Hbb by (clear -BZ; lia). rewrite (rd_off_image _ _ _ BZ Hbb). discriminate. }
  assert (Hcv : SPA segs KJ (ax_setS A1 (set_objs (ax_S F) (K ++ [O_UBs nx]))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { pose proof (SPA_carve_zero_sym segs KJ rho3 A1 tp _ (UBs nx) (SLit 0) (SVar 12) (ss_next (ax_S A1)) Hb) as CV. cbn zeta in CV.
    rewrite !EV3 in CV. unfold soff in CV. rewrite !EV3 in CV. fold (soff rhoE (SLit 0)) (soff rhoE (SVar 12)) in CV.
    rewrite (SOL 0 ltac:(clear; lia)), EUB in CV. rewrite (soff_of_val rhoE (SVar 12) nv) in CV by (first [rewrite EN12; apply u64_lit; clear -HN; lia | clear -HN; lia]).
    apply CV; clear CV.
    - exact WCU.
    - apply Pos.le_refl.
    - clear -HN. lia.
    - clear -HN. lia.
    - unfold ub. clear -UAB. lia.
    - unfold ub. clear -UAB LB. lia.
    - change (ss_objs (ax_S A1)) with K. eapply Forall_impl; [|exact (KDISJ (ub + 0) (ub + nv) ltac:(unfold ub; clear -UAB; lia) ltac:(unfold ub; clear -LB PDT; lia))].
      intros o Ho. rewrite OR3. exact Ho.
    - intros z Hz. pose proof (RM3 z ltac:(left; unfold ub in Hz; clear -Hz LB; lia)) as D.
      assert (ZZ : rd_of segs (rm rho3) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
      { destruct (Z_lt_dec z (ua + 10240)) as [L2|L2].
        - apply (AOZ (O_fill nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | rewrite RG_fill; cbn [fst snd]; unfold ub in *; clear -Hz L2; lia].
        - apply (AOZ (O_Mhi nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | rewrite RG_Mhi; cbn [fst snd]; unfold ub in *; clear -Hz L2 LB; lia]. }
      split; [|exact ZZ]. unfold wok_of. destruct (rm rho3 (Z_to_bv 64 z)) as [x|]; [reflexivity | exfalso; exact (D eq_refl)].
    - intros rr y j Hin. change (ax_X A1) with (ax_X F) in Hin. rewrite XFn in Hin. destruct Hin. }

  pose proof (SPA_select segs KJ rho3 _ (idxsU nW) tp _ Hcv NDU
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BNDU i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COVU i ltac:(apply in_seq; exact (conj (Nat.le_0_l i) Hi))) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsu.
  cbn [ax_S ax_setS ss_objs set_objs] in Hsu. rewrite SELU in Hsu. clear Hcv.

  match type of Hsu with SPA _ _ ?AU _ _ _ => set (A2 := AU) in Hsu end.
  assert (Hc : SPA segs KJ (ax_setS A2 (S2F F KU)) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { eapply SPA_restate; [exact W9 | exact D9 | reflexivity | | constructor | exact Hsu].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. pose proof (geom_old _ HG) as HGt. destruct HGt as (_ & _ & _ & G4' & _). unfold G in G4'. rewrite G4'. reflexivity. }
  clear Hsu.

  assert (EUB3 : bv_unsigned (eval rho3 (UBs nx)) = ub) by (rewrite EV3; exact EUB).
  assert (E12_3 : bv_unsigned (eval rho3 (SVar 12)) = nv) by (rewrite EV3, EN12; apply u64_lit; clear -HN; lia).
  assert (RGUB : obj_range rhoE (O_UBs nx) = (ub, ub + nv)).
  { unfold O_UBs, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (SVar 12) nv) by (first [rewrite EN12; apply u64_lit; clear -HN; lia | clear -HN; lia]). rewrite EUB. f_equal. clear. lia. }
  assert (OUTK : forall z, SHADOW_OFF <= z < 17594333495296 -> outside_all rho3 KU (Z_to_bv 64 z)).
  { intros z Hz. unfold SHADOW_OFF in Hz. unfold KU, KUB, outside_all. rewrite u64_lit by (clear -Hz; lia). apply Forall_app. split; [constructor|apply Forall_app; split].
    - cbn zeta. rewrite OR3. clear -SW0 SW3 Hz ACV. lia.
    - eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
      cbn zeta. rewrite OR3, obj_range_mk by (clear; lia). cbn [fst snd]. clear -B1 Hz ACV. lia.
    - constructor; [|constructor]. cbn zeta. rewrite OR3, RGUB. cbn [fst snd]. unfold ub. clear -Hz PDB LB UAB. lia.
    - unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil; cbn zeta;
        rewrite obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite u64_lit by (clear; lia); clear -Hz; lia. }
  assert (UA8 : exists q, ua = 4096 * q) by (exists (ua / 4096); pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X; rewrite AL, Z.add_0_r in X; exact X).
  destruct UA8 as [qu Hqu].
  assert (L8q : exists q, L = 4096 * q) by (exists (L / 4096); pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X; rewrite SMM, Z.add_0_r in X; exact X).
  destruct L8q as [ql Hql].
  assert (ESHua : Sh ua = 512 * qu + SHADOW_OFF) by (unfold Sh; rewrite Hqu; replace (4096 * qu) with (512 * qu * 8) by (clear; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
  assert (EL8 : L / 8 = 512 * ql) by (rewrite Hql; replace (4096 * ql) with (512 * ql * 8) by (clear; lia); apply Z.div_mul; clear; lia).
  assert (Hd : SPA segs KJ (ax_setX (ax_setS A2 (S2F F KU)) ((UBs nx, SVar 12) :: ax_X (ax_setS A2 (S2F F KU)))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { apply SPA_x_publish; [exact XB9 | | exact Hc].
    change (ax_base (ax_setS A2 (S2F F KU))) with (ax_base F). rewrite BFb. change (ss_objs (ax_S (ax_setS A2 (S2F F KU)))) with KU.
    unfold xr_ok. cbn [fst snd]. rewrite EUB3, E12_3. unfold base_sv. cbn [eval]. rewrite u64_lit by (unfold SHADOW_OFF; clear; lia).
    split; [unfold ub; rewrite Hqu; apply Z.mod_divide; [clear; lia|]; exists (512 * qu + 768); clear; lia|].
    split; [unfold ub; clear -UAB LB; lia|].
    intros x Hx.
    pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DMa. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MBa.
    pose proof (Z.div_mod nv 8 ltac:(clear; lia)) as DMn. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)) as MBn.
    set (pa := x / 8) in *.
    assert (PA : 512 * qu + 768 <= pa /\ 8 * pa <= x /\ pa <= 512 * qu + 768 + nv / 8 /\ (pa = 512 * qu + 768 + nv / 8 -> nv mod 8 <> 0)).
    { unfold ub in Hx. rewrite Hqu in Hx. clear -Hx DMa MBa DMn MBn. lia. }
    assert (SHA : SHADOW_OFF + pa = Sh ub + (pa - 512 * qu - 768)) by (rewrite ESHub, ESHua; clear; lia).
    assert (INRUN : Sh ua <= SHADOW_OFF + pa < Sh ua + L / 8) by (rewrite ESHua; clear -PA L8B; lia).
    split; [clear -INRUN SHB; lia|].
    split; [unfold shadow_addr; fold pa; apply OUTK; clear -INRUN SHB; unfold SHADOW_OFF in *; lia|].
    split.
    { intros j Hj. unfold word_byte.
      assert (WIN : Sh ua <= (SHADOW_OFF + pa) / 8 * 8 + j < Sh ua + L / 8).
      { pose proof (Z.div_mod (SHADOW_OFF + pa) 8 ltac:(clear; lia)) as DMs. pose proof (Z.mod_pos_bound (SHADOW_OFF + pa) 8 ltac:(clear; lia)) as MBs.
        rewrite ESHua, EL8 in INRUN |- *. unfold SHADOW_OFF in *.
        assert (Q1 : 64 * qu + 268431360 <= (2147450880 + pa) / 8) by (apply Z.div_le_lower_bound; [clear; lia | clear -INRUN; lia]).
        assert (Q2 : (2147450880 + pa) / 8 < 64 * qu + 268431360 + 64 * ql) by (apply Z.div_lt_upper_bound; [clear; lia | clear -INRUN; lia]).
        clear -Q1 Q2 Hj. lia. }
      split; [apply OUTK; clear -WIN SHB; unfold SHADOW_OFF in *; lia | apply RM3; right; exact WIN]. }
    destruct (Z_lt_dec (pa - 512 * qu - 768) (nv / 8)) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      unfold shadow_addr. fold pa. rewrite SHA. pose proof (VZ (pa - 512 * qu - 768) ltac:(clear -LT PA; lia)) as X. unfold v3 in X.
      rewrite view_in in X by (rewrite <- SHA; clear -INRUN SHB; lia).
      refine (rd_off_image _ _ _ _ X). rewrite <- SHA. clear -INRUN SHB. lia.
    - assert (EQ : pa - 512 * qu - 768 = nv / 8 /\ nv mod 8 <> 0) by (split; [clear -GE PA; lia | apply (proj2 (proj2 (proj2 PA))); clear -GE PA; lia]).
      destruct EQ as [EQ NZ]. exists (Z_to_bv 8 (nv mod 8)). split.
      + unfold shadow_addr. fold pa. rewrite SHA, EQ. pose proof (VP NZ) as X. unfold v3 in X.
        rewrite view_in in X by (rewrite <- EQ, <- SHA; clear -INRUN SHB; lia).
        refine (rd_off_image _ _ _ _ X). rewrite <- EQ, <- SHA. clear -INRUN SHB. lia.
      + right. split.
        * rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small (nv mod 8) 256) by (clear -MBn; lia).
          unfold ub. rewrite Hqu. replace (4096 * qu + 6144 + nv) with (nv + (512 * qu + 768) * 8) by (clear; lia). rewrite Z_mod_plus_full. reflexivity.
        * fold pa. unfold ub. rewrite Hqu. replace (4096 * qu + 6144 + nv) with (nv + (512 * qu + 768) * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear -EQ. lia. }
  clear Hc.

  change (ax_setX (ax_setS A2 (S2F F KU)) ((UBs nx, SVar 12) :: ax_X (ax_setS A2 (S2F F KU))))
    with (mkAX (S2F F KU) ((UBs nx, SVar 12) :: ax_X F) (ax_base F)) in Hd.
  rewrite XFn, BFb in Hd. change (mkAX (S2F F KU) [(UBs nx, SVar 12)] base_sv) with (XF_of F KU nx) in Hd.
  pose proof (smatchA_entails segs (XF_of F KU nx) (Lc_ok W st) s9 rho3 tp _ ENT9 (proj1 Hd)) as Hsm4.
  set (rho4 := rho_sub rho3 s9) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ (wsub_idc_below _ SID9) Hk). cbn [eval]. unfold rho3. cbn [rho_absorb rw]. reflexivity. }
  assert (E110 : bv_unsigned (rw rho4 V_RES) = ub). { unfold rho4. cbn [rho_sub rw]. rewrite G110. exact EUB3. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 s9).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).
  assert (LOWE : forall k, (k < NF)%positive -> rw rhoE k = rw rho0 k).
  { intros k Hk. rewrite <- (Hagw k) by (unfold GW, NF in *; clear -Hk; lia). rewrite <- (RMw k Hk). exact (HLw k). }

  assert (CLE : forall x, client_addrA CST As x <-> client_addrA CST A x).
  { intros x. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag. rewrite Bl, Bfb, Bg. cbn [aa_live aa_fs_busy aa_geom bumpV]. split; intros X; exact X. }
  assert (CLE' : forall x, client_addrA CST A x -> client_addrA CST (secA As ua nv) x).
  { intros x Hx. apply (proj2 (CLE x)) in Hx. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag in Hx |- *. cbn [aa_live aa_fs_busy aa_geom secA].
    destruct Hx as [[X|[X|[X|X]]]|X]; [left; left; exact X | left; right; left | left; right; right; left; exact X | left; right; right; right; exact X | right; exact X].
    destruct X as (b & n & Hbn & Hb0). exists b, n. split; [right; exact Hbn | exact Hb0]. }
  apply (LQPA_intro segs NF rho0 tp0 _ (Lc_ok W st) (JLc_ok CST XGL A Kc) rho4 tp _ KJ).
  - exact HPin.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi), (LOWE i Hi). reflexivity.
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite (Erl l). symmetry. exact (HLl l).
  - intros _. unfold JLc_ok. split.
    2:{ split; unfold rho4; cbn [rho_sub rw]; [rewrite (wsub_idc_143 _ SID9) | rewrite (wsub_idc_144 _ SID9)]; cbn [eval]; unfold rho3; cbn [rho_absorb rw].
        - rewrite <- (Hagw 143%positive) by (unfold GW; clear; lia). rewrite (rhoM_of_keep A rho 143%positive) by tauto. exact (HLw 143%positive).
        - rewrite <- (Hagw 144%positive) by (unfold GW; clear; lia). rewrite (rhoM_of_keep A rho 144%positive) by tauto. exact (HLw 144%positive). }
    unfold JL_malloc_ok. cbn [w_tr w_cfg cfg_model].
    exists (secA As ua nv), [], (aa_live A). cbn [app].
    assert (E12_0 : bv_unsigned (rw rho0 12%positive) = nv) by (rewrite <- (HLw 12%positive); reflexivity).
    split; [unfold AInv, AInvA in RB |- *; rewrite Erm4; exact RB|].
    split; [cbn [aa_live secA]; rewrite Bl, E110, E12_0; reflexivity|].
    split; [reflexivity|].
    split; [unfold aa_frames; cbn [aa_fs_busy secA]; rewrite Bfb; reflexivity|].
    split; [cbn [aa_V secA]; rewrite BV, E12_0; reflexivity|].
    split; [cbn [aa_Km secA]; rewrite BKm; reflexivity|]. split; [cbn [aa_Kf secA]; rewrite BKf; reflexivity|]. split; [cbn [aa_geom secA]; exact Bg|].
    split.
    {
      destruct HKEPT0 as [K01 K02]. destruct KP as [KP1 KP2]. rewrite Erm4. split.
      - intros x Bx Hcl.
        assert (EQ0 : rm rho (Z_to_bv 64 x) = rm rho0 (Z_to_bv 64 x)).
        { apply (K01 x Bx). destruct Hcl as [(X & _ & NE)|(X & _ & DEF)]; [left; exact (conj X (conj X NE)) | right; exact (conj X (conj X DEF))]. }
        assert (Hcl' : (client_addrA CST As x /\ client_addrA CST (secA As ua nv) x /\ ~ errno_addrA x)
                       \/ (client_shadowA CST XGL As x /\ client_shadowA CST XGL (secA As ua nv) x /\ rm rhoE (Z_to_bv 64 x) <> None)).
        { destruct Hcl as [(X & Y & NE)|(X & Y & DEF)].
          - left. split; [apply (proj2 (CLE x)); exact X | exact (conj Y NE)].
          - right. split; [|split; [exact Y | rewrite ErmF, EQ0; exact DEF]].
            destruct X as [(y & Y1 & Y2)|Y']; [left; exists y; split; [apply (proj2 (CLE y)); exact Y1 | exact Y2] | right; exact Y']. }
        rewrite (KP1 x Bx Hcl'). rewrite ErmF. exact EQ0.
      - intros xx jj Hx Hj Hdef. apply (KP2 xx jj); [| exact Hj |].
        + destruct Hx as [[X Y]|X]; [left; split; [apply (proj2 (CLE xx)); exact X | exact Y] | right; exact X].
        + rewrite ErmF. apply (K02 xx jj); [| exact Hj | exact Hdef].
          destruct Hx as [[X Y]|X]; [left; exact (conj X X) | right; exact X]. }
    split; [exact HK|].

    intros c0 Hc0 Hor Hfr. unfold class_fresh in Hfr |- *. cbn [aa_cls secA]. rewrite Bc. exact Hfr.
Qed.

Theorem sec_finish : ltac2:(tb__ "0|5|
S35S5cS15S15S4aQ40M0A1M1S15S6G1A1M2G2S7cS85VW;Vst;A2S5dR9A1S12S0G1S14R9R1A2S14RaR1A2A3Fi;S12S0S6S4aQ8A1A1S1aRaR1A2S1aRbR1A2A3Fl;S5eVCST;VXGL;RdRdS1bRbA1S1bRaA1A6S4cS4dSbS37S36ReA1A2A1S38ReA1A2SdS11S11A2M3S31G3R1S88S3bVBX;S5bR10S49G0S14RdPcM4A2A2A2A1A1A1A3S86R2ScS11S11S49G0RdA2S8eS49G0S14ReG4A2A2A1A4A2F_;Fbn;S80Vsegs;VJG;VBX;R10RfRdRcA5VF;RbR9R8A6S83Vsegs;S7eRfRbS94VCST;VXGL;VW;Vst;R11R10A6R9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a rhoE tp0 tp w. apply sec_finish_P. unfold PFc. right. left. reflexivity.
Qed.

Variable DF9 : axst.
Hypothesis CertF : ltac2:(tb__ "0|1|
S0S7Sa2Sa6Ufa0S9S11A1Sa9Vnx;A1S5S57VDF9;S9S57A1M0A3S5S57VF;G0A3A6SaA3").
Theorem sec_g48_P : ltac2:(tb__ "0|6|
S7cOF_;S35S5cS15S15S4aQ40M0A1M1S6G1A1M2S6SdS57S84A2M3A1S31G3ScS57S84S92VW;Vst;A2S93VCST;VXGL;R7R6A4A4R1A3S85VW;Vst;A2S8fVW;Vst;A2S5dR9A1S82Vsegs;RcS81RaA1A3S12S0G1S14RaR1A2S14RbR1A2A3Fi;S12S0S6S4aQ8A1A1S1aRbR1A2S1aRcR1A2A3Fl;S5eVCST;VXGL;ReReS1bRcA1S1bRbA1A6S4cS4dSbS37S36RfA1A2A1S38RfA1A2SdS11S11A2M4S31G4R1S88S3bVBX;S5bR11S49G0S14RePcM5A2A2A2A1A1A1A3S86R2ScS11S11S49G0ReA2S8eS49G0S14RfG5A2A2A1A4A2F_;Fbn;S15G2S7dVsegs;R14S80Vsegs;VJG;VBX;R13R12R10RfA5VDF9;R2R1A5S83Vsegs;S7eR11ReRdA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT0 HL9 HDB rhoX tpX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [] (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx) [DF9] [F] (JG BX A Kc rho a) ok _ tpX Hokf HST CertF); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
  intros w Hw. exact (sec_finish_P A Kc rho0 rho a rE tp0 tpX w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB Hw).
Qed.
Theorem sec_g48 : ltac2:(tb__ "0|5|
S7cOF_;S35S5cS15S15S4aQ40M0A1M1S6G1A1M2S85VW;Vst;A2S8fVW;Vst;A2S5dR7A1S82Vsegs;RaS81R8A1A3S12S0G1S14R8R1A2S14R9R1A2A3Fi;S12S0S6S4aQ8A1A1S1aR9R1A2S1aRaR1A2A3Fl;S5eVCST;VXGL;RcRcS1bRaA1S1bR9A1A6S4cS4dSbS37S36RdA1A2A1S38RdA1A2SdS11S11A2M3S31G3R1S88S3bVBX;S5bRfS49G0S14RcPcM4A2A2A2A1A1A1A3S86R2ScS11S11S49G0RcA2S8eS49G0S14RdG4A2A2A1A4A2F_;Fbn;S15G2S7dVsegs;R12S80Vsegs;VJG;VBX;R11R10ReRdA5VDF9;R2R1A5S83Vsegs;S7eRfRcS94VCST;VXGL;VW;Vst;R11R10A6A5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0. apply sec_g48_P. unfold PFc. right. left. reflexivity.
Qed.
End FIN.

Lemma hpath_a : ltac2:(tb__ "0|6|
S35S35Fx;S35S5cS15S4aQ40M0A1M1S15S6G1A1S6S91A1S90S35S0S3cS39RaR1A1A1S39R1A1A3FX;S35S0S6S37A1S36RbR1A1A1S36R1A1A3FX;S35S0S11S3aRcR1A1A1S4eS3aR1A1M2Sa5A2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S67S17S1eR8A1S5S17S21S95S19S9aA1S19S9bA1M3A3S9S17A1A3A3ReS5bRdS49G0S14RbPcA2A2A2A1S35S1S1S4cZ8M4Z20000M5A2S4cG5G5A2A2S1S4cS4eS50G4S4dSbS37S36ReA1A2A1A2G5A2G2A2S0G1S1dRaS28S96G3S20Z4000A1A3A2S4bG0S4fG2G4A2A2A3A2A2TAs;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF. apply Forall_inv in HF. cbn zeta.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  destruct HJ as (_ & _ & HA & _). pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. cbn zeta in X.
  destruct X as (P1 & P2 & P3 & P4 & P5 & P6 & _).
  rewrite BXp. cbn [aa_ptr_committed bumpV].
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  assert (EDV : (c + kPtrArrayCommit) / 8 = c / 8 + 16384) by (change kPtrArrayCommit with (16384 * 8); apply Z.div_add; lia).
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  assert (C17 : c mod 2 ^ 17 = 0).
  { pose proof (Z.mod_add c 1 (2 ^ 17) ltac:(lia)) as MA. rewrite <- MA. rewrite <- P6. f_equal. }
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite C17, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  cbn [holds eval] in HF. rewrite E147, E146 in HF. fold c in HF.
  assert (C0 : 0 <= c).
  { destruct (Z_lt_le_dec c 0) as [Hneg|]; [exfalso | assumption].
    assert (Ec : c = - 2 ^ 17) by (clear -X Hneg P5 NN; lia).
    assert (En : Z.of_nat (length (aa_sec A)) = 0) by (clear -Ec P5 NN; lia).
    rewrite En, Ec in HF. vm_compute in HF. discriminate HF. }
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(clear -P5; lia) ltac:(clear -P5; lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HF by (clear -DP DM NN P5; lia). apply Z.eqb_eq in HF.
  assert (HcN : 8 * Z.of_nat (length (aa_sec A)) = c) by (rewrite HF; clear -X8; lia).
  split; [lia|]. split; [clear -HcN; lia|].
  apply bv_eq. cbn [eval]. rewrite E146. fold c. rewrite add_val, !u64_lit by (clear -DP DM; lia). rewrite Z.mod_small by (clear -DP DM; lia).
  rewrite EDV. reflexivity.
Qed.

Lemma hpath_b : ltac2:(tb__ "0|5|
S35S35Fx;S35S5cS15S4aQ40M0A1M1S15S6G1A1S6S91A1S90S35S0S3cS39RaR1A1A1S39R1A1A3FX;S35S0S6S37A1S36RbR1A1A1S36R1A1A3FX;S35S0S11S3aRcR1A1A1S3aR1A1M2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S67S17S1eR8A1S5S17S22S21S95S19S9aA1S19S9bA1M3A3A1S9S17A1A3A3ReS5bRdS49G0S14RbPcA2A2A2A1S35S1S1S4cZ8M4G4A2S4cG4Z20000A2A2S1S4cS4eS50G4S4dSbS37S36ReA1A2A1A2G4A2G2A2S0G1S1dRaG3A2S4bG0S4fG2G4A2A2A3A2A2TAs;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF. apply Forall_inv in HF. cbn zeta.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  pose proof (site_b nW st tmax nx Hnx Pret_ms Pret_ms Pret_ms Pret_ms eq_refl eq_refl BX A Kc rho a r tp tr md BXg BXs BXp HJ HF) as (_ & B1 & B2 & _). cbn zeta in B1, B2.
  rewrite BXp. cbn [aa_ptr_committed bumpV].
  split; [lia|]. split; [clear -B2; lia|]. cbn [eval]. exact E146.
Qed.
End SEC7.
End SpineCallocSec7.

(* [comment removed for export] *)
Module SpineCallocSec5I.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "leafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "X5s"; "WI"; "T5d"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "C5S"; "coveredbL"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5I.INST"; "X5ac"; "X5bc"; "T4a_i"; "T4b_i"; "nobja"; "nobjb"; "U4ac"; "U4bc"; "s4a_i"; "s4b_i"; "R4a_i"; "R4b_i"; "pm__15"; "pm__16"; "pm__43"; "pm__44"; "C5ac"; "C5bc"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__37"; "pm__38"; "pm__39"; "pm__40"; "pm__41"; "pm__42"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__49"; "pm__50"; "pm__51"; "pm__52"; "pm__9"; "sda_i"; "sdb_i"; "CPa1"; "CPa2"; "CPb1"; "CPb2"; "EXoa"; "EXob"; "pm__0"; "pm__1"; "pm__2"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__29"; "pm__3"; "pm__30"; "pm__31"; "pm__32"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__4"; "pm__5"; "pm__53"; "pm__54"; "pm__55"; "pm__6"; "pm__7"; "pm__8"; "run5a"; "run5b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "S"; "nat"; "option"; "pair"; "Some"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_facts"; "ss_next"; "SVar"; "ss_objs"; "sprop_below"; "SAlu"; "SPUle"; "swf"; "SExt"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "isSome"; "O_1"; "O_2"; "O_blk"; "O_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "omrg"; "oreb"; "F_call"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4I"; "T4ac"; "T4bc"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma by_cases12 : ltac2:(tb__ "0|2|
SaOF_;R1Z1M0A1R2Z2M1A1SaS1S2G0R1A2S2R1G1A2A2R5R2A1F_;Fsz;F_;F_;FP;").
Proof. intros P H1 H2 sz Hsz. assert (E : sz = 1 \/ sz = 2) by lia. destruct E as [-> | ->]; assumption. Qed.
Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
S77S74S74S9fS73S7eA1M0A2S5A2M1A1G1Lo;Vo;G1R1Lx;S78S74S73S74SbS7cA2M2A1M3G0A2S5S78G3G0S71G2A1S71S7eA1A4S98Z0A1A4X77x2").
Lemma Htmax_0 : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.

Definition U4ac : axst := Eval vm_compute in (U4p nx0 T4ac).
Lemma WU4a_0 : ltac2:(tb__ "0|0|
S0S6fS88S4S25A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4a_0 : ltac2:(tb__ "0|4|
S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4SabA1S4S25A1A2S79G3S78G1G2S71G0A1Sa9S9dA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4a_0 : ltac2:(tb__ "0|0|
S0SbS82S4S25A1A1S82S4SabA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4a_0 : ltac2:(tb__ "0|0|
S0S5S7SabS4S25A1A2S25A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5a : option (list leafA) := Eval vm_compute in (runT5 U4ac).
Lemma run5a__runeq : ltac2:(tb__ "0|1|
S0S73S77S73S9A1A1M0A1Sb1SaaUfa0S72SaSa8S71SaA1A3S72S5S25S71S5A1A3A4S72G0S6dS71G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5a]). Qed.
Definition X5ac : axst := Eval vm_compute in (leafS 0 run5a).
Lemma Cert5a_0 : ltac2:(tb__ "0|1|
S0S6fSb0SaaUfa0S72SaSa8S71SaA1A3VGS0;S72S5S25S71S5A1M0A3S72S5S1fG0A3A6S70A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4ac] [X5ac] [run5a]); [exact run5a__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5ac : axst := Eval vm_compute in (C5S X5ac).

Definition CPa1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 1) 1)).
Definition CPa2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 2) 2)).
Definition CPa (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
S6fS74S74S9fS73S7eA1A2S5A2L_;S3Vsz;Z1A2S4fS50X6fx2").
Definition s4a_i (sz : Z) : wsub := fst (fst (CPa sz)).
Definition R4a_i (sz : Z) : list sobj := snd (fst (CPa sz)).
Definition T4a_i (sz : Z) : axst := snd (CPa sz).
Definition nobja : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4a_i 1) (X5s X5ac 1))))).
Definition sda_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
SaeVGS0;S4SeS23S21Vsz;A1ScS1fVsz;A2A3A1S4S2fA1A3").
Definition EXoa : list sobj := ltac2:(tb__ "0|0|
S72S7eS8eS9dA1S72S7eS8dS9dA1S72S7eS8fS71S7eA1A3A3A3").

Lemma NXEa_0 : ltac2:(tb__ "0|0|
S0S6fSbcVGS0;S82S4S1fA1A1A2S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEa_0 : ltac2:(tb__ "0|0|
S0S6fS94S7dS85S82S4S1fA1A1A1S93A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5a_0 : ax_X X5ac = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192a_0 : ltac2:(tb__ "0|1|
S95S7dS72S7dS87S7fZ1A1S83Pc0A1M0A2S72S7dS87G0S7fVtmax;A1A2S71S7dA1A3A3S81S4S1fA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPa_0 : ltac2:(tb__ "0|0|
S95S7dSb8Sb7A1S81S4S1fA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWa_0 : ltac2:(tb__ "0|0|
S95S7dSb9VW;Vst;A2S81S4S1fA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBa_0 : ltac2:(tb__ "0|0|
S96S7dS8aSa2S83Sb5A1S83Sb6A1A3S81S4S1fA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Ltac PM_sub0 t := t.
Ltac PM_all0 := idtac.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S5S1bS1fA1S55A3"). Proof. cbv delta [X5f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X5f X5ac) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S5SfS1fZ1A2S56A3"). Proof. cbv delta [X5r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X5r X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|0|
S0S5SfS1fZ2A2S57A3"). Proof. cbv delta [X5r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X5r X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S5S18S1fZ1A2S5dA3"). Proof. cbv delta [X5a pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X5a X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|0|
S0S5S18S1fZ2A2S65A3"). Proof. cbv delta [X5a pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X5a X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S5S19S1fZ1A2S66A3"). Proof. cbv delta [X5b pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X5b X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|0|
S0S5S19S1fZ2A2S6aA3"). Proof. cbv delta [X5b pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X5b X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S5S1aS1fZ1A2S6bA3"). Proof. cbv delta [X5c pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X5c X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|0|
S0S5S1aS1fZ2A2S6cA3"). Proof. cbv delta [X5c pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X5c X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S5ScS1fZ1A2S4cA3"). Proof. cbv delta [X5s pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X5s X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|0|
S0S5ScS1fZ2A2S31A3"). Proof. cbv delta [X5s pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X5s X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac2:(tb__ "0|0|
Sa7S21Z1A1S81S4S4cA1A1A2").
Lemma pm__11_eq : ltac2:(tb__ "0|1|
S0S5S11S21Z1M0A1ScS1fG0A2A2S32A3"). Proof. cbv delta [T50 pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (T50 (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac2:(tb__ "0|0|
Sa7S21Z2A1S81S4S31A1A1A2").
Lemma pm__12_eq : ltac2:(tb__ "0|1|
S0S5S11S21Z2M0A1ScS1fG0A2A2S33A3"). Proof. cbv delta [T50 pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (T50 (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac2:(tb__ "0|0|
S92S32U0A2").
Lemma pm__13_eq : ltac2:(tb__ "0|1|
S0S5S12S21Z1M0A1ScS1fG0A2A2S34A3"). Proof. cbv delta [T5a pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (T5a (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac2:(tb__ "0|0|
S92S33U0A2").
Lemma pm__14_eq : ltac2:(tb__ "0|1|
S0S5S12S21Z2M0A1ScS1fG0A2A2S35A3"). Proof. cbv delta [T5a pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (T5a (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac2:(tb__ "0|0|
S92S34U1A2").
Lemma pm__15_eq : ltac2:(tb__ "0|1|
S0S5S13S21Z1M0A1ScS1fG0A2A2S2bA3"). Proof. cbv delta [T5b pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (T5b (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac2:(tb__ "0|0|
S92S35U1A2").
Lemma pm__16_eq : ltac2:(tb__ "0|1|
S0S5S13S21Z2M0A1ScS1fG0A2A2S2cA3"). Proof. cbv delta [T5b pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (T5b (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac2:(tb__ "0|1|
S7S2bSa6S4S2bA1M0Sa4S84G0A1S10S23A1A2A2A2").
Lemma pm__17_eq : ltac2:(tb__ "0|1|
S0S5S14S23S21Z1M0A1ScS1fG0A2A3S36A3"). Proof. cbv delta [T5c pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac2:(tb__ "0|1|
S7S2cSa6S4S2cA1M0Sa4S84G0A1S10S23A1A2A2A2").
Lemma pm__18_eq : ltac2:(tb__ "0|1|
S0S5S14S23S21Z2M0A1ScS1fG0A2A3S37A3"). Proof. cbv delta [T5c pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac2:(tb__ "0|0|
S91S36SdA2").
Lemma pm__19_eq : ltac2:(tb__ "0|1|
S0S5S15S23S21Z1M0A1ScS1fG0A2A3S38A3"). Proof. cbv delta [T5m1 pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac2:(tb__ "0|0|
S91S37SdA2").
Lemma pm__20_eq : ltac2:(tb__ "0|1|
S0S5S15S23S21Z2M0A1ScS1fG0A2A3S39A3"). Proof. cbv delta [T5m1 pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
S91S38SdA2").
Lemma pm__21_eq : ltac2:(tb__ "0|1|
S0S5S16S23S21Z1M0A1ScS1fG0A2A3S3aA3"). Proof. cbv delta [T5m2 pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
S91S39SdA2").
Lemma pm__22_eq : ltac2:(tb__ "0|1|
S0S5S16S23S21Z2M0A1ScS1fG0A2A3S3bA3"). Proof. cbv delta [T5m2 pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
S91S3aSdA2").
Lemma pm__23_eq : ltac2:(tb__ "0|1|
S0S5S17S23S21Z1M0A1ScS1fG0A2A3S3cA3"). Proof. cbv delta [T5m3 pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
S91S3bSdA2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S5S17S23S21Z2M0A1ScS1fG0A2A3S3dA3"). Proof. cbv delta [T5m3 pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|0|
S91S3cSdA2").
Lemma pm__25_eq : ltac2:(tb__ "0|1|
S0S5SeS23S21Z1M0A1ScS1fG0A2A3S58A3"). Proof. cbv delta [T5d pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|0|
S91S3dSdA2").
Lemma pm__26_eq : ltac2:(tb__ "0|1|
S0S5SeS23S21Z2M0A1ScS1fG0A2A3S59A3"). Proof. cbv delta [T5d pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Definition pm__27 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub27 t in exact t).
Lemma pm__27_eq : ltac2:(tb__ "0|0|
S0S5S1cS1fA1S5aA3"). Proof. cbv delta [C5S pm__27]; cbv beta zeta. PM_all27. reflexivity. Qed.
Ltac PM_sub28 t := let t := lazymatch (eval pattern (C5S X5ac) in t) with ?P _ => eval cbv beta in (P pm__27) end in PM_sub27 t.
Ltac PM_all28 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__27_eq; PM_all27.
Lemma WX5ra_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS88S4SfS1fR2A2A1A1S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5ra_0 : ltac2:(tb__ "0|4|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4S1bS1fA1A1S4SfS1fR2A2A1A2S79G3S78G1G2S72G0S78S7cS7cS89S7aQ20S83Pc0A1A3S7fR2A1A4S71G0A1A3S71S7dA1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4SfS1fR2A2A1SdS7fNf10A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S18S1fR2A2A1S75SdA1S7fN910A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S19S1fR2A2A1S75S75SdA1A1S7fN848A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S1aS1fR2A2A1S75S75S75SdA1A1A1S7fN50A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERa_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S73S7eA1M0A1Sb3ScS1fR2A2S98R2A1S27R2A1A3S79G0S29R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S5Sb4S27R2A1S98R2A1S99R2A1ScS1fR2A2S29R2A1A5S21R2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6ScS1fR2A2A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4ScS1fR2A2A1M0A1A1S81G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSb2ScS1fR2A2S98R2A1S27R2A1S29R2A1S72S5S99R2A1S71S5A1A3A5S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0SbS82S4ScS1fR2A2A1A1S82S4S1fA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS27R2A1PaM0A2S86Sa1S83G0A1S7fN910A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS27R2A1PfA2S7fN600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS27R2A1PcA2S86Sa1S83PaA1S7fN848A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7eS1eU0S9dS53A3S29R2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOa_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S7eA1SafS4S98R2A1A1S4S99R2A1A1A2S71S7eA1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPosta_0 : ltac2:(tb__ "0|1|
SaS0S73S74S7cS7cA2M0A1S6S99R1A1A1S71G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4S21R2A1A1A1A1S81S4ScS1fR2A2A1A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6S21R2A1A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S11S21R2A1ScS1fR2A2A2A1U0A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S12S21R2A1ScS1fR2A2A2A1U1A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nda_0 : ltac2:(tb__ "0|0|
S0S6fSa5S10S23A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lta_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76SbbR1S23A2Li;S10S23A1A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_cova_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76S97S76SbaR1A1S10S23A1A3Li;SadU0S23A2A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lena_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S76S7bS7eS84S4S13S21R2A1ScS1fR2A2A2A1A1A2S23A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S14S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S15S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S16S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S17S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8SeS23S21R2A1ScS1fR2A2A3S2fS4dR2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSa0S4dR2A1VGS0;A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4cova_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS1dS81S4SeS23S21R2A1ScS1fR2A2A3A1M0A1S29R2A1S84G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

Definition U4bc : axst := Eval vm_compute in (U4p nx0 T4bc).
Lemma WU4b_0 : ltac2:(tb__ "0|0|
S0S6fS88S4S26A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4b_0 : ltac2:(tb__ "0|4|
S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4SacA1S4S26A1A2S79G3S78G1G2S71G0A1Sa9S9dA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4b_0 : ltac2:(tb__ "0|0|
S0SbS82S4S26A1A1S82S4SacA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4b_0 : ltac2:(tb__ "0|0|
S0S5S7SacS4S26A1A2S26A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5b : option (list leafA) := Eval vm_compute in (runT5 U4bc).
Lemma run5b__runeq : ltac2:(tb__ "0|1|
S0S73S77S73S9A1A1M0A1Sb1SaaUfa0S72SaSa8S71SaA1A3S72S5S26S71S5A1A3A4S72G0S6eS71G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5b]). Qed.
Definition X5bc : axst := Eval vm_compute in (leafS 0 run5b).
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S0S6fSb0SaaUfa0S72SaSa8S71SaA1A3VGS0;S72S5S26S71S5A1M0A3S72S5S20G0A3A6S70A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4bc] [X5bc] [run5b]); [exact run5b__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5bc : axst := Eval vm_compute in (C5S X5bc).

Definition CPb1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 1) 1)).
Definition CPb2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 2) 2)).
Definition CPb (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
S6fS74S74S9fS73S7eA1A2S5A2L_;S3Vsz;Z1A2S51S52X6fx2").
Definition s4b_i (sz : Z) : wsub := fst (fst (CPb sz)).
Definition R4b_i (sz : Z) : list sobj := snd (fst (CPb sz)).
Definition T4b_i (sz : Z) : axst := snd (CPb sz).
Definition nobjb : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4b_i 1) (X5s X5bc 1))))).
Definition sdb_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
SaeVGS0;S4SeS24S22Vsz;A1ScS20Vsz;A2A3A1S4S30A1A3").
Definition EXob : list sobj := ltac2:(tb__ "0|0|
S72S7eS8eS9dA1S72S7eS8dS9dA1S72S7eS90S71S7eA1A3A3A3").

Lemma NXEb_0 : ltac2:(tb__ "0|0|
S0S6fSbcVGS0;S82S4S20A1A1A2S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEb_0 : ltac2:(tb__ "0|0|
S0S6fS94S7dS85S82S4S20A1A1A1S93A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5b_0 : ax_X X5bc = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192b_0 : ltac2:(tb__ "0|1|
S95S7dS72S7dS87S7fZ1A1S83Pc0A1M0A2S72S7dS87G0S7fVtmax;A1A2S71S7dA1A3A3S81S4S20A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPb_0 : ltac2:(tb__ "0|0|
S95S7dSb8Sb7A1S81S4S20A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWb_0 : ltac2:(tb__ "0|0|
S95S7dSb9VW;Vst;A2S81S4S20A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBb_0 : ltac2:(tb__ "0|0|
S96S7dS8bS8aSa2S83Sb5A1S83Sb6A1A3A1S81S4S20A1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pm__28 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub28 t in exact t).
Lemma pm__28_eq : ltac2:(tb__ "0|0|
S0S5S1bS20A1S5bA3"). Proof. cbv delta [X5f pm__28]; cbv beta zeta. PM_all28. reflexivity. Qed.
Ltac PM_sub29 t := let t := lazymatch (eval pattern (X5f X5bc) in t) with ?P _ => eval cbv beta in (P pm__28) end in PM_sub28 t.
Ltac PM_all29 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__28_eq; PM_all28.
Definition pm__29 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub29 t in exact t).
Lemma pm__29_eq : ltac2:(tb__ "0|0|
S0S5SfS20Z1A2S5cA3"). Proof. cbv delta [X5r pm__29]; cbv beta zeta. PM_all29. reflexivity. Qed.
Ltac PM_sub30 t := let t := lazymatch (eval pattern (X5r X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__29) end in PM_sub29 t.
Ltac PM_all30 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__29_eq; PM_all29.
Definition pm__30 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub30 t in exact t).
Lemma pm__30_eq : ltac2:(tb__ "0|0|
S0S5SfS20Z2A2S5eA3"). Proof. cbv delta [X5r pm__30]; cbv beta zeta. PM_all30. reflexivity. Qed.
Ltac PM_sub31 t := let t := lazymatch (eval pattern (X5r X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__30) end in PM_sub30 t.
Ltac PM_all31 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__30_eq; PM_all30.
Definition pm__31 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub31 t in exact t).
Lemma pm__31_eq : ltac2:(tb__ "0|0|
S0S5S18S20Z1A2S5fA3"). Proof. cbv delta [X5a pm__31]; cbv beta zeta. PM_all31. reflexivity. Qed.
Ltac PM_sub32 t := let t := lazymatch (eval pattern (X5a X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__31) end in PM_sub31 t.
Ltac PM_all32 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__31_eq; PM_all31.
Definition pm__32 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub32 t in exact t).
Lemma pm__32_eq : ltac2:(tb__ "0|0|
S0S5S18S20Z2A2S60A3"). Proof. cbv delta [X5a pm__32]; cbv beta zeta. PM_all32. reflexivity. Qed.
Ltac PM_sub33 t := let t := lazymatch (eval pattern (X5a X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__32) end in PM_sub32 t.
Ltac PM_all33 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__32_eq; PM_all32.
Definition pm__33 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub33 t in exact t).
Lemma pm__33_eq : ltac2:(tb__ "0|0|
S0S5S19S20Z1A2S61A3"). Proof. cbv delta [X5b pm__33]; cbv beta zeta. PM_all33. reflexivity. Qed.
Ltac PM_sub34 t := let t := lazymatch (eval pattern (X5b X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__33) end in PM_sub33 t.
Ltac PM_all34 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__33_eq; PM_all33.
Definition pm__34 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub34 t in exact t).
Lemma pm__34_eq : ltac2:(tb__ "0|0|
S0S5S19S20Z2A2S62A3"). Proof. cbv delta [X5b pm__34]; cbv beta zeta. PM_all34. reflexivity. Qed.
Ltac PM_sub35 t := let t := lazymatch (eval pattern (X5b X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__34) end in PM_sub34 t.
Ltac PM_all35 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__34_eq; PM_all34.
Definition pm__35 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub35 t in exact t).
Lemma pm__35_eq : ltac2:(tb__ "0|0|
S0S5S1aS20Z1A2S63A3"). Proof. cbv delta [X5c pm__35]; cbv beta zeta. PM_all35. reflexivity. Qed.
Ltac PM_sub36 t := let t := lazymatch (eval pattern (X5c X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__35) end in PM_sub35 t.
Ltac PM_all36 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__35_eq; PM_all35.
Definition pm__36 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub36 t in exact t).
Lemma pm__36_eq : ltac2:(tb__ "0|0|
S0S5S1aS20Z2A2S64A3"). Proof. cbv delta [X5c pm__36]; cbv beta zeta. PM_all36. reflexivity. Qed.
Ltac PM_sub37 t := let t := lazymatch (eval pattern (X5c X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__36) end in PM_sub36 t.
Ltac PM_all37 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__36_eq; PM_all36.
Definition pm__37 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub37 t in exact t).
Lemma pm__37_eq : ltac2:(tb__ "0|0|
S0S5ScS20Z1A2S3eA3"). Proof. cbv delta [X5s pm__37]; cbv beta zeta. PM_all37. reflexivity. Qed.
Ltac PM_sub38 t := let t := lazymatch (eval pattern (X5s X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__37) end in PM_sub37 t.
Ltac PM_all38 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__37_eq; PM_all37.
Definition pm__38 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub38 t in exact t).
Lemma pm__38_eq : ltac2:(tb__ "0|0|
S0S5ScS20Z2A2S3fA3"). Proof. cbv delta [X5s pm__38]; cbv beta zeta. PM_all38. reflexivity. Qed.
Ltac PM_sub39 t := let t := lazymatch (eval pattern (X5s X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__38) end in PM_sub38 t.
Ltac PM_all39 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__38_eq; PM_all38.
Definition pm__39 : axst := ltac2:(tb__ "0|0|
Sa7S22Z1A1S81S4S3eA1A1A2").
Lemma pm__39_eq : ltac2:(tb__ "0|1|
S0S5S11S22Z1M0A1ScS20G0A2A2S40A3"). Proof. cbv delta [T50 pm__39]; cbv beta zeta. PM_all39. reflexivity. Qed.
Ltac PM_sub40 t := let t := lazymatch (eval pattern (T50 (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__39) end in PM_sub39 t.
Ltac PM_all40 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__39_eq; PM_all39.
Definition pm__40 : axst := ltac2:(tb__ "0|0|
Sa7S22Z2A1S81S4S3fA1A1A2").
Lemma pm__40_eq : ltac2:(tb__ "0|1|
S0S5S11S22Z2M0A1ScS20G0A2A2S41A3"). Proof. cbv delta [T50 pm__40]; cbv beta zeta. PM_all40. reflexivity. Qed.
Ltac PM_sub41 t := let t := lazymatch (eval pattern (T50 (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__40) end in PM_sub40 t.
Ltac PM_all41 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__40_eq; PM_all40.
Definition pm__41 : axst := ltac2:(tb__ "0|0|
S92S40U0A2").
Lemma pm__41_eq : ltac2:(tb__ "0|1|
S0S5S12S22Z1M0A1ScS20G0A2A2S42A3"). Proof. cbv delta [T5a pm__41]; cbv beta zeta. PM_all41. reflexivity. Qed.
Ltac PM_sub42 t := let t := lazymatch (eval pattern (T5a (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__41) end in PM_sub41 t.
Ltac PM_all42 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__41_eq; PM_all41.
Definition pm__42 : axst := ltac2:(tb__ "0|0|
S92S41U0A2").
Lemma pm__42_eq : ltac2:(tb__ "0|1|
S0S5S12S22Z2M0A1ScS20G0A2A2S43A3"). Proof. cbv delta [T5a pm__42]; cbv beta zeta. PM_all42. reflexivity. Qed.
Ltac PM_sub43 t := let t := lazymatch (eval pattern (T5a (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__42) end in PM_sub42 t.
Ltac PM_all43 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__42_eq; PM_all42.
Definition pm__43 : axst := ltac2:(tb__ "0|0|
S92S42U1A2").
Lemma pm__43_eq : ltac2:(tb__ "0|1|
S0S5S13S22Z1M0A1ScS20G0A2A2S2dA3"). Proof. cbv delta [T5b pm__43]; cbv beta zeta. PM_all43. reflexivity. Qed.
Ltac PM_sub44 t := let t := lazymatch (eval pattern (T5b (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__43) end in PM_sub43 t.
Ltac PM_all44 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__43_eq; PM_all43.
Definition pm__44 : axst := ltac2:(tb__ "0|0|
S92S43U1A2").
Lemma pm__44_eq : ltac2:(tb__ "0|1|
S0S5S13S22Z2M0A1ScS20G0A2A2S2eA3"). Proof. cbv delta [T5b pm__44]; cbv beta zeta. PM_all44. reflexivity. Qed.
Ltac PM_sub45 t := let t := lazymatch (eval pattern (T5b (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__44) end in PM_sub44 t.
Ltac PM_all45 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__44_eq; PM_all44.
Definition pm__45 : axst := ltac2:(tb__ "0|1|
S7S2dSa6S4S2dA1M0Sa4S84G0A1S10S24A1A2A2A2").
Lemma pm__45_eq : ltac2:(tb__ "0|1|
S0S5S14S24S22Z1M0A1ScS20G0A2A3S44A3"). Proof. cbv delta [T5c pm__45]; cbv beta zeta. PM_all45. reflexivity. Qed.
Ltac PM_sub46 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__45) end in PM_sub45 t.
Ltac PM_all46 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__45_eq; PM_all45.
Definition pm__46 : axst := ltac2:(tb__ "0|1|
S7S2eSa6S4S2eA1M0Sa4S84G0A1S10S24A1A2A2A2").
Lemma pm__46_eq : ltac2:(tb__ "0|1|
S0S5S14S24S22Z2M0A1ScS20G0A2A3S45A3"). Proof. cbv delta [T5c pm__46]; cbv beta zeta. PM_all46. reflexivity. Qed.
Ltac PM_sub47 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__46) end in PM_sub46 t.
Ltac PM_all47 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__46_eq; PM_all46.
Definition pm__47 : axst := ltac2:(tb__ "0|0|
S91S44SdA2").
Lemma pm__47_eq : ltac2:(tb__ "0|1|
S0S5S15S24S22Z1M0A1ScS20G0A2A3S46A3"). Proof. cbv delta [T5m1 pm__47]; cbv beta zeta. PM_all47. reflexivity. Qed.
Ltac PM_sub48 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__47) end in PM_sub47 t.
Ltac PM_all48 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__47_eq; PM_all47.
Definition pm__48 : axst := ltac2:(tb__ "0|0|
S91S45SdA2").
Lemma pm__48_eq : ltac2:(tb__ "0|1|
S0S5S15S24S22Z2M0A1ScS20G0A2A3S47A3"). Proof. cbv delta [T5m1 pm__48]; cbv beta zeta. PM_all48. reflexivity. Qed.
Ltac PM_sub49 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__48) end in PM_sub48 t.
Ltac PM_all49 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__48_eq; PM_all48.
Definition pm__49 : axst := ltac2:(tb__ "0|0|
S91S46SdA2").
Lemma pm__49_eq : ltac2:(tb__ "0|1|
S0S5S16S24S22Z1M0A1ScS20G0A2A3S48A3"). Proof. cbv delta [T5m2 pm__49]; cbv beta zeta. PM_all49. reflexivity. Qed.
Ltac PM_sub50 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__49) end in PM_sub49 t.
Ltac PM_all50 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__49_eq; PM_all49.
Definition pm__50 : axst := ltac2:(tb__ "0|0|
S91S47SdA2").
Lemma pm__50_eq : ltac2:(tb__ "0|1|
S0S5S16S24S22Z2M0A1ScS20G0A2A3S49A3"). Proof. cbv delta [T5m2 pm__50]; cbv beta zeta. PM_all50. reflexivity. Qed.
Ltac PM_sub51 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__50) end in PM_sub50 t.
Ltac PM_all51 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__50_eq; PM_all50.
Definition pm__51 : axst := ltac2:(tb__ "0|0|
S91S48SdA2").
Lemma pm__51_eq : ltac2:(tb__ "0|1|
S0S5S17S24S22Z1M0A1ScS20G0A2A3S4aA3"). Proof. cbv delta [T5m3 pm__51]; cbv beta zeta. PM_all51. reflexivity. Qed.
Ltac PM_sub52 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__51) end in PM_sub51 t.
Ltac PM_all52 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__51_eq; PM_all51.
Definition pm__52 : axst := ltac2:(tb__ "0|0|
S91S49SdA2").
Lemma pm__52_eq : ltac2:(tb__ "0|1|
S0S5S17S24S22Z2M0A1ScS20G0A2A3S4bA3"). Proof. cbv delta [T5m3 pm__52]; cbv beta zeta. PM_all52. reflexivity. Qed.
Ltac PM_sub53 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__52) end in PM_sub52 t.
Ltac PM_all53 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__52_eq; PM_all52.
Definition pm__53 : axst := ltac2:(tb__ "0|0|
S91S4aSdA2").
Lemma pm__53_eq : ltac2:(tb__ "0|1|
S0S5SeS24S22Z1M0A1ScS20G0A2A3S67A3"). Proof. cbv delta [T5d pm__53]; cbv beta zeta. PM_all53. reflexivity. Qed.
Ltac PM_sub54 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__53) end in PM_sub53 t.
Ltac PM_all54 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__53_eq; PM_all53.
Definition pm__54 : axst := ltac2:(tb__ "0|0|
S91S4bSdA2").
Lemma pm__54_eq : ltac2:(tb__ "0|1|
S0S5SeS24S22Z2M0A1ScS20G0A2A3S68A3"). Proof. cbv delta [T5d pm__54]; cbv beta zeta. PM_all54. reflexivity. Qed.
Ltac PM_sub55 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__54) end in PM_sub54 t.
Ltac PM_all55 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__54_eq; PM_all54.
Definition pm__55 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub55 t in exact t).
Lemma pm__55_eq : ltac2:(tb__ "0|0|
S0S5S1cS20A1S69A3"). Proof. cbv delta [C5S pm__55]; cbv beta zeta. PM_all55. reflexivity. Qed.
Ltac PM_sub56 t := let t := lazymatch (eval pattern (C5S X5bc) in t) with ?P _ => eval cbv beta in (P pm__55) end in PM_sub55 t.
Ltac PM_all56 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__55_eq; PM_all55.
Lemma WX5rb_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS88S4SfS20R2A2A1A1S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5rb_0 : ltac2:(tb__ "0|4|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4S1bS20A1A1S4SfS20R2A2A1A2S79G3S78G1G2S72G0S78S7cS7cS89S7aQ20S83Pc0A1A3S7fR2A1A4S71G0A1A3S71S7dA1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4SfS20R2A2A1SdS7fNf10A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S18S20R2A2A1S75SdA1S7fN910A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S19S20R2A2A1S75S75SdA1A1S7fN848A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S1aS20R2A2A1S75S75S75SdA1A1A1S7fN50A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERb_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S73S7eA1M0A1Sb3ScS20R2A2S98R2A1S28R2A1A3S79G0S2aR2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S5Sb4S28R2A1S98R2A1S99R2A1ScS20R2A2S2aR2A1A5S22R2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6ScS20R2A2A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4ScS20R2A2A1M0A1A1S81G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSb2ScS20R2A2S98R2A1S28R2A1S2aR2A1S72S5S99R2A1S71S5A1A3A5S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0SbS82S4ScS20R2A2A1A1S82S4S20A1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS28R2A1PaM0A2S86Sa1S83G0A1S7fN910A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS28R2A1PfA2S7fN600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS28R2A1PcA2S86Sa1S83PaA1S7fN848A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7eS1eU0S9dS54A3S2aR2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOb_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S7eA1SafS4S98R2A1A1S4S99R2A1A1A2S71S7eA1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPostb_0 : ltac2:(tb__ "0|1|
SaS0S73S74S7cS7cA2M0A1S6S99R1A1A1S71G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4S22R2A1A1A1A1S81S4ScS20R2A2A1A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6S22R2A1A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S11S22R2A1ScS20R2A2A2A1U0A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S12S22R2A1ScS20R2A2A2A1U1A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_ndb_0 : ltac2:(tb__ "0|0|
S0S6fSa5S10S24A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_ltb_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76SbbR1S24A2Li;S10S24A1A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_covb_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76S97S76SbaR1A1S10S24A1A3Li;SadU0S24A2A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lenb_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S76S7bS7eS84S4S13S22R2A1ScS20R2A2A2A1A1A2S24A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S14S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S15S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S16S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S17S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8SeS24S22R2A1ScS20R2A2A3S30S4eR2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSa0S4eR2A1VGS0;A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4covb_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS1dS81S4SeS24S22R2A1ScS20R2A2A3A1M0A1S2aR2A1S84G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

End INST.
End SpineCallocSec5I.

(* [comment removed for export] *)
Module SpineCallocSec5IL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "leafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "X5s"; "WI"; "T5d"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "C5S"; "coveredbL"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5IL.INST"; "X5ac"; "X5bc"; "T4a_i"; "T4b_i"; "nobja"; "nobjb"; "U4ac"; "U4bc"; "s4a_i"; "s4b_i"; "R4a_i"; "R4b_i"; "pm__15"; "pm__16"; "pm__43"; "pm__44"; "C5ac"; "C5bc"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__37"; "pm__38"; "pm__39"; "pm__40"; "pm__41"; "pm__42"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__49"; "pm__50"; "pm__51"; "pm__52"; "pm__9"; "sda_i"; "sdb_i"; "CPa1"; "CPa2"; "CPb1"; "CPb2"; "EXoa"; "EXob"; "pm__0"; "pm__1"; "pm__2"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__29"; "pm__3"; "pm__30"; "pm__31"; "pm__32"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__4"; "pm__5"; "pm__53"; "pm__54"; "pm__55"; "pm__6"; "pm__7"; "pm__8"; "run5a"; "run5b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "S"; "nat"; "option"; "pair"; "Some"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_facts"; "ss_next"; "SVar"; "ss_objs"; "sprop_below"; "SAlu"; "SPUle"; "swf"; "SExt"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "isSome"; "O_1"; "O_2"; "O_blk"; "O_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "omrg"; "oreb"; "F_call"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IL"; "T4ac"; "T4bc"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma by_cases12 : ltac2:(tb__ "0|2|
SaOF_;R1Z1M0A1R2Z2M1A1SaS1S2G0R1A2S2R1G1A2A2R5R2A1F_;Fsz;F_;F_;FP;").
Proof. intros P H1 H2 sz Hsz. assert (E : sz = 1 \/ sz = 2) by lia. destruct E as [-> | ->]; assumption. Qed.
Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
S77S74S74S9fS73S7eA1M0A2S5A2M1A1G1Lo;Vo;G1R1Lx;S78S74S73S74SbS7cA2M2A1M3G0A2S5S78G3G0S71G2A1S71S7eA1A4S98Z0A1A4X77x2").
Lemma Htmax_0 : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.

Definition U4ac : axst := Eval vm_compute in (U4p nx0 T4ac).
Lemma WU4a_0 : ltac2:(tb__ "0|0|
S0S6fS88S4S25A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4a_0 : ltac2:(tb__ "0|4|
S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4SabA1S4S25A1A2S79G3S78G1G2S71G0A1Sa9S9dA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4a_0 : ltac2:(tb__ "0|0|
S0SbS82S4S25A1A1S82S4SabA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4a_0 : ltac2:(tb__ "0|0|
S0S5S7SabS4S25A1A2S25A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5a : option (list leafA) := Eval vm_compute in (runT5 U4ac).
Lemma run5a__runeq : ltac2:(tb__ "0|1|
S0S73S77S73S9A1A1M0A1Sb1SaaUfa0S72SaSa8S71SaA1A3S72S5S25S71S5A1A3A4S72G0S6dS71G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5a]). Qed.
Definition X5ac : axst := Eval vm_compute in (leafS 0 run5a).
Lemma Cert5a_0 : ltac2:(tb__ "0|1|
S0S6fSb0SaaUfa0S72SaSa8S71SaA1A3VGS0;S72S5S25S71S5A1M0A3S72S5S1fG0A3A6S70A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4ac] [X5ac] [run5a]); [exact run5a__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5ac : axst := Eval vm_compute in (C5S X5ac).

Definition CPa1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 1) 1)).
Definition CPa2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 2) 2)).
Definition CPa (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
S6fS74S74S9fS73S7eA1A2S5A2L_;S3Vsz;Z1A2S4fS50X6fx2").
Definition s4a_i (sz : Z) : wsub := fst (fst (CPa sz)).
Definition R4a_i (sz : Z) : list sobj := snd (fst (CPa sz)).
Definition T4a_i (sz : Z) : axst := snd (CPa sz).
Definition nobja : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4a_i 1) (X5s X5ac 1))))).
Definition sda_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
SaeVGS0;S4SeS23S21Vsz;A1ScS1fVsz;A2A3A1S4S2fA1A3").
Definition EXoa : list sobj := ltac2:(tb__ "0|0|
S72S7eS8eS9dA1S72S7eS8dS9dA1S72S7eS8fS71S7eA1A3A3A3").

Lemma NXEa_0 : ltac2:(tb__ "0|0|
S0S6fSbcVGS0;S82S4S1fA1A1A2S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEa_0 : ltac2:(tb__ "0|0|
S0S6fS94S7dS85S82S4S1fA1A1A1S93A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5a_0 : ax_X X5ac = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192a_0 : ltac2:(tb__ "0|1|
S95S7dS72S7dS87S7fZ1A1S83Pc0A1M0A2S72S7dS87G0S7fVtmax;A1A2S71S7dA1A3A3S81S4S1fA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPa_0 : ltac2:(tb__ "0|0|
S95S7dSb8Sb7A1S81S4S1fA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWa_0 : ltac2:(tb__ "0|0|
S95S7dSb9VW;Vst;A2S81S4S1fA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBa_0 : ltac2:(tb__ "0|0|
S96S7dS8aSa2S83Sb5A1S83Sb6A1A3S81S4S1fA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Ltac PM_sub0 t := t.
Ltac PM_all0 := idtac.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S5S1bS1fA1S55A3"). Proof. cbv delta [X5f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X5f X5ac) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S5SfS1fZ1A2S56A3"). Proof. cbv delta [X5r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X5r X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|0|
S0S5SfS1fZ2A2S57A3"). Proof. cbv delta [X5r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X5r X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S5S18S1fZ1A2S5dA3"). Proof. cbv delta [X5a pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X5a X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|0|
S0S5S18S1fZ2A2S65A3"). Proof. cbv delta [X5a pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X5a X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S5S19S1fZ1A2S66A3"). Proof. cbv delta [X5b pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X5b X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|0|
S0S5S19S1fZ2A2S6aA3"). Proof. cbv delta [X5b pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X5b X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S5S1aS1fZ1A2S6bA3"). Proof. cbv delta [X5c pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X5c X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|0|
S0S5S1aS1fZ2A2S6cA3"). Proof. cbv delta [X5c pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X5c X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S5ScS1fZ1A2S4cA3"). Proof. cbv delta [X5s pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X5s X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|0|
S0S5ScS1fZ2A2S31A3"). Proof. cbv delta [X5s pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X5s X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac2:(tb__ "0|0|
Sa7S21Z1A1S81S4S4cA1A1A2").
Lemma pm__11_eq : ltac2:(tb__ "0|1|
S0S5S11S21Z1M0A1ScS1fG0A2A2S32A3"). Proof. cbv delta [T50 pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (T50 (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac2:(tb__ "0|0|
Sa7S21Z2A1S81S4S31A1A1A2").
Lemma pm__12_eq : ltac2:(tb__ "0|1|
S0S5S11S21Z2M0A1ScS1fG0A2A2S33A3"). Proof. cbv delta [T50 pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (T50 (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac2:(tb__ "0|0|
S92S32U0A2").
Lemma pm__13_eq : ltac2:(tb__ "0|1|
S0S5S12S21Z1M0A1ScS1fG0A2A2S34A3"). Proof. cbv delta [T5a pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (T5a (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac2:(tb__ "0|0|
S92S33U0A2").
Lemma pm__14_eq : ltac2:(tb__ "0|1|
S0S5S12S21Z2M0A1ScS1fG0A2A2S35A3"). Proof. cbv delta [T5a pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (T5a (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac2:(tb__ "0|0|
S92S34U1A2").
Lemma pm__15_eq : ltac2:(tb__ "0|1|
S0S5S13S21Z1M0A1ScS1fG0A2A2S2bA3"). Proof. cbv delta [T5b pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (T5b (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac2:(tb__ "0|0|
S92S35U1A2").
Lemma pm__16_eq : ltac2:(tb__ "0|1|
S0S5S13S21Z2M0A1ScS1fG0A2A2S2cA3"). Proof. cbv delta [T5b pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (T5b (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac2:(tb__ "0|1|
S7S2bSa6S4S2bA1M0Sa4S84G0A1S10S23A1A2A2A2").
Lemma pm__17_eq : ltac2:(tb__ "0|1|
S0S5S14S23S21Z1M0A1ScS1fG0A2A3S36A3"). Proof. cbv delta [T5c pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac2:(tb__ "0|1|
S7S2cSa6S4S2cA1M0Sa4S84G0A1S10S23A1A2A2A2").
Lemma pm__18_eq : ltac2:(tb__ "0|1|
S0S5S14S23S21Z2M0A1ScS1fG0A2A3S37A3"). Proof. cbv delta [T5c pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac2:(tb__ "0|0|
S91S36SdA2").
Lemma pm__19_eq : ltac2:(tb__ "0|1|
S0S5S15S23S21Z1M0A1ScS1fG0A2A3S38A3"). Proof. cbv delta [T5m1 pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac2:(tb__ "0|0|
S91S37SdA2").
Lemma pm__20_eq : ltac2:(tb__ "0|1|
S0S5S15S23S21Z2M0A1ScS1fG0A2A3S39A3"). Proof. cbv delta [T5m1 pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
S91S38SdA2").
Lemma pm__21_eq : ltac2:(tb__ "0|1|
S0S5S16S23S21Z1M0A1ScS1fG0A2A3S3aA3"). Proof. cbv delta [T5m2 pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
S91S39SdA2").
Lemma pm__22_eq : ltac2:(tb__ "0|1|
S0S5S16S23S21Z2M0A1ScS1fG0A2A3S3bA3"). Proof. cbv delta [T5m2 pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
S91S3aSdA2").
Lemma pm__23_eq : ltac2:(tb__ "0|1|
S0S5S17S23S21Z1M0A1ScS1fG0A2A3S3cA3"). Proof. cbv delta [T5m3 pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
S91S3bSdA2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S5S17S23S21Z2M0A1ScS1fG0A2A3S3dA3"). Proof. cbv delta [T5m3 pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|0|
S91S3cSdA2").
Lemma pm__25_eq : ltac2:(tb__ "0|1|
S0S5SeS23S21Z1M0A1ScS1fG0A2A3S58A3"). Proof. cbv delta [T5d pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|0|
S91S3dSdA2").
Lemma pm__26_eq : ltac2:(tb__ "0|1|
S0S5SeS23S21Z2M0A1ScS1fG0A2A3S59A3"). Proof. cbv delta [T5d pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Definition pm__27 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub27 t in exact t).
Lemma pm__27_eq : ltac2:(tb__ "0|0|
S0S5S1cS1fA1S5aA3"). Proof. cbv delta [C5S pm__27]; cbv beta zeta. PM_all27. reflexivity. Qed.
Ltac PM_sub28 t := let t := lazymatch (eval pattern (C5S X5ac) in t) with ?P _ => eval cbv beta in (P pm__27) end in PM_sub27 t.
Ltac PM_all28 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__27_eq; PM_all27.
Lemma WX5ra_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS88S4SfS1fR2A2A1A1S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5ra_0 : ltac2:(tb__ "0|4|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4S1bS1fA1A1S4SfS1fR2A2A1A2S79G3S78G1G2S72G0S78S7cS7cS89S7aQ20S83Pc0A1A3S7fR2A1A4S71G0A1A3S71S7dA1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4SfS1fR2A2A1SdS7fNf10A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S18S1fR2A2A1S75SdA1S7fN910A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S19S1fR2A2A1S75S75SdA1A1S7fN848A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S1aS1fR2A2A1S75S75S75SdA1A1A1S7fN50A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERa_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S73S7eA1M0A1Sb3ScS1fR2A2S98R2A1S27R2A1A3S79G0S29R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S5Sb4S27R2A1S98R2A1S99R2A1ScS1fR2A2S29R2A1A5S21R2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6ScS1fR2A2A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4ScS1fR2A2A1M0A1A1S81G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSb2ScS1fR2A2S98R2A1S27R2A1S29R2A1S72S5S99R2A1S71S5A1A3A5S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0SbS82S4ScS1fR2A2A1A1S82S4S1fA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS27R2A1PaM0A2S86Sa1S83G0A1S7fN910A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS27R2A1PfA2S7fN600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS27R2A1PcA2S86Sa1S83PaA1S7fN848A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7eS1eU0S9dS53A3S29R2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOa_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S7eA1SafS4S98R2A1A1S4S99R2A1A1A2S71S7eA1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPosta_0 : ltac2:(tb__ "0|1|
SaS0S73S74S7cS7cA2M0A1S6S99R1A1A1S71G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4S21R2A1A1A1A1S81S4ScS1fR2A2A1A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4a_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6S21R2A1A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S11S21R2A1ScS1fR2A2A2A1U0A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S12S21R2A1ScS1fR2A2A2A1U1A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nda_0 : ltac2:(tb__ "0|0|
S0S6fSa5S10S23A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lta_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76SbbR1S23A2Li;S10S23A1A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_cova_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76S97S76SbaR1A1S10S23A1A3Li;SadU0S23A2A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lena_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S76S7bS7eS84S4S13S21R2A1ScS1fR2A2A2A1A1A2S23A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S14S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S15S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S16S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S17S23S21R2A1ScS1fR2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8SeS23S21R2A1ScS1fR2A2A3S2fS4dR2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5a_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSa0S4dR2A1VGS0;A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4cova_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS1dS81S4SeS23S21R2A1ScS1fR2A2A3A1M0A1S29R2A1S84G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all28; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

Definition U4bc : axst := Eval vm_compute in (U4p nx0 T4bc).
Lemma WU4b_0 : ltac2:(tb__ "0|0|
S0S6fS88S4S26A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4b_0 : ltac2:(tb__ "0|4|
S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4SacA1S4S26A1A2S79G3S78G1G2S71G0A1Sa9S9dA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4b_0 : ltac2:(tb__ "0|0|
S0SbS82S4S26A1A1S82S4SacA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4b_0 : ltac2:(tb__ "0|0|
S0S5S7SacS4S26A1A2S26A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5b : option (list leafA) := Eval vm_compute in (runT5 U4bc).
Lemma run5b__runeq : ltac2:(tb__ "0|1|
S0S73S77S73S9A1A1M0A1Sb1SaaUfa0S72SaSa8S71SaA1A3S72S5S26S71S5A1A3A4S72G0S6eS71G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5b]). Qed.
Definition X5bc : axst := Eval vm_compute in (leafS 0 run5b).
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S0S6fSb0SaaUfa0S72SaSa8S71SaA1A3VGS0;S72S5S26S71S5A1M0A3S72S5S20G0A3A6S70A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4bc] [X5bc] [run5b]); [exact run5b__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5bc : axst := Eval vm_compute in (C5S X5bc).

Definition CPb1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 1) 1)).
Definition CPb2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 2) 2)).
Definition CPb (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
S6fS74S74S9fS73S7eA1A2S5A2L_;S3Vsz;Z1A2S51S52X6fx2").
Definition s4b_i (sz : Z) : wsub := fst (fst (CPb sz)).
Definition R4b_i (sz : Z) : list sobj := snd (fst (CPb sz)).
Definition T4b_i (sz : Z) : axst := snd (CPb sz).
Definition nobjb : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4b_i 1) (X5s X5bc 1))))).
Definition sdb_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
SaeVGS0;S4SeS24S22Vsz;A1ScS20Vsz;A2A3A1S4S30A1A3").
Definition EXob : list sobj := ltac2:(tb__ "0|0|
S72S7eS8eS9dA1S72S7eS8dS9dA1S72S7eS90S71S7eA1A3A3A3").

Lemma NXEb_0 : ltac2:(tb__ "0|0|
S0S6fSbcVGS0;S82S4S20A1A1A2S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEb_0 : ltac2:(tb__ "0|0|
S0S6fS94S7dS85S82S4S20A1A1A1S93A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5b_0 : ax_X X5bc = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192b_0 : ltac2:(tb__ "0|1|
S95S7dS72S7dS87S7fZ1A1S83Pc0A1M0A2S72S7dS87G0S7fVtmax;A1A2S71S7dA1A3A3S81S4S20A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPb_0 : ltac2:(tb__ "0|0|
S95S7dSb8Sb7A1S81S4S20A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWb_0 : ltac2:(tb__ "0|0|
S95S7dSb9VW;Vst;A2S81S4S20A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBb_0 : ltac2:(tb__ "0|0|
S96S7dS8bS8aSa2S83Sb5A1S83Sb6A1A3A1S81S4S20A1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pm__28 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub28 t in exact t).
Lemma pm__28_eq : ltac2:(tb__ "0|0|
S0S5S1bS20A1S5bA3"). Proof. cbv delta [X5f pm__28]; cbv beta zeta. PM_all28. reflexivity. Qed.
Ltac PM_sub29 t := let t := lazymatch (eval pattern (X5f X5bc) in t) with ?P _ => eval cbv beta in (P pm__28) end in PM_sub28 t.
Ltac PM_all29 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__28_eq; PM_all28.
Definition pm__29 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub29 t in exact t).
Lemma pm__29_eq : ltac2:(tb__ "0|0|
S0S5SfS20Z1A2S5cA3"). Proof. cbv delta [X5r pm__29]; cbv beta zeta. PM_all29. reflexivity. Qed.
Ltac PM_sub30 t := let t := lazymatch (eval pattern (X5r X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__29) end in PM_sub29 t.
Ltac PM_all30 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__29_eq; PM_all29.
Definition pm__30 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub30 t in exact t).
Lemma pm__30_eq : ltac2:(tb__ "0|0|
S0S5SfS20Z2A2S5eA3"). Proof. cbv delta [X5r pm__30]; cbv beta zeta. PM_all30. reflexivity. Qed.
Ltac PM_sub31 t := let t := lazymatch (eval pattern (X5r X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__30) end in PM_sub30 t.
Ltac PM_all31 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__30_eq; PM_all30.
Definition pm__31 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub31 t in exact t).
Lemma pm__31_eq : ltac2:(tb__ "0|0|
S0S5S18S20Z1A2S5fA3"). Proof. cbv delta [X5a pm__31]; cbv beta zeta. PM_all31. reflexivity. Qed.
Ltac PM_sub32 t := let t := lazymatch (eval pattern (X5a X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__31) end in PM_sub31 t.
Ltac PM_all32 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__31_eq; PM_all31.
Definition pm__32 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub32 t in exact t).
Lemma pm__32_eq : ltac2:(tb__ "0|0|
S0S5S18S20Z2A2S60A3"). Proof. cbv delta [X5a pm__32]; cbv beta zeta. PM_all32. reflexivity. Qed.
Ltac PM_sub33 t := let t := lazymatch (eval pattern (X5a X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__32) end in PM_sub32 t.
Ltac PM_all33 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__32_eq; PM_all32.
Definition pm__33 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub33 t in exact t).
Lemma pm__33_eq : ltac2:(tb__ "0|0|
S0S5S19S20Z1A2S61A3"). Proof. cbv delta [X5b pm__33]; cbv beta zeta. PM_all33. reflexivity. Qed.
Ltac PM_sub34 t := let t := lazymatch (eval pattern (X5b X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__33) end in PM_sub33 t.
Ltac PM_all34 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__33_eq; PM_all33.
Definition pm__34 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub34 t in exact t).
Lemma pm__34_eq : ltac2:(tb__ "0|0|
S0S5S19S20Z2A2S62A3"). Proof. cbv delta [X5b pm__34]; cbv beta zeta. PM_all34. reflexivity. Qed.
Ltac PM_sub35 t := let t := lazymatch (eval pattern (X5b X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__34) end in PM_sub34 t.
Ltac PM_all35 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__34_eq; PM_all34.
Definition pm__35 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub35 t in exact t).
Lemma pm__35_eq : ltac2:(tb__ "0|0|
S0S5S1aS20Z1A2S63A3"). Proof. cbv delta [X5c pm__35]; cbv beta zeta. PM_all35. reflexivity. Qed.
Ltac PM_sub36 t := let t := lazymatch (eval pattern (X5c X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__35) end in PM_sub35 t.
Ltac PM_all36 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__35_eq; PM_all35.
Definition pm__36 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub36 t in exact t).
Lemma pm__36_eq : ltac2:(tb__ "0|0|
S0S5S1aS20Z2A2S64A3"). Proof. cbv delta [X5c pm__36]; cbv beta zeta. PM_all36. reflexivity. Qed.
Ltac PM_sub37 t := let t := lazymatch (eval pattern (X5c X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__36) end in PM_sub36 t.
Ltac PM_all37 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__36_eq; PM_all36.
Definition pm__37 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub37 t in exact t).
Lemma pm__37_eq : ltac2:(tb__ "0|0|
S0S5ScS20Z1A2S3eA3"). Proof. cbv delta [X5s pm__37]; cbv beta zeta. PM_all37. reflexivity. Qed.
Ltac PM_sub38 t := let t := lazymatch (eval pattern (X5s X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__37) end in PM_sub37 t.
Ltac PM_all38 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__37_eq; PM_all37.
Definition pm__38 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub38 t in exact t).
Lemma pm__38_eq : ltac2:(tb__ "0|0|
S0S5ScS20Z2A2S3fA3"). Proof. cbv delta [X5s pm__38]; cbv beta zeta. PM_all38. reflexivity. Qed.
Ltac PM_sub39 t := let t := lazymatch (eval pattern (X5s X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__38) end in PM_sub38 t.
Ltac PM_all39 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__38_eq; PM_all38.
Definition pm__39 : axst := ltac2:(tb__ "0|0|
Sa7S22Z1A1S81S4S3eA1A1A2").
Lemma pm__39_eq : ltac2:(tb__ "0|1|
S0S5S11S22Z1M0A1ScS20G0A2A2S40A3"). Proof. cbv delta [T50 pm__39]; cbv beta zeta. PM_all39. reflexivity. Qed.
Ltac PM_sub40 t := let t := lazymatch (eval pattern (T50 (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__39) end in PM_sub39 t.
Ltac PM_all40 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__39_eq; PM_all39.
Definition pm__40 : axst := ltac2:(tb__ "0|0|
Sa7S22Z2A1S81S4S3fA1A1A2").
Lemma pm__40_eq : ltac2:(tb__ "0|1|
S0S5S11S22Z2M0A1ScS20G0A2A2S41A3"). Proof. cbv delta [T50 pm__40]; cbv beta zeta. PM_all40. reflexivity. Qed.
Ltac PM_sub41 t := let t := lazymatch (eval pattern (T50 (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__40) end in PM_sub40 t.
Ltac PM_all41 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__40_eq; PM_all40.
Definition pm__41 : axst := ltac2:(tb__ "0|0|
S92S40U0A2").
Lemma pm__41_eq : ltac2:(tb__ "0|1|
S0S5S12S22Z1M0A1ScS20G0A2A2S42A3"). Proof. cbv delta [T5a pm__41]; cbv beta zeta. PM_all41. reflexivity. Qed.
Ltac PM_sub42 t := let t := lazymatch (eval pattern (T5a (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__41) end in PM_sub41 t.
Ltac PM_all42 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__41_eq; PM_all41.
Definition pm__42 : axst := ltac2:(tb__ "0|0|
S92S41U0A2").
Lemma pm__42_eq : ltac2:(tb__ "0|1|
S0S5S12S22Z2M0A1ScS20G0A2A2S43A3"). Proof. cbv delta [T5a pm__42]; cbv beta zeta. PM_all42. reflexivity. Qed.
Ltac PM_sub43 t := let t := lazymatch (eval pattern (T5a (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__42) end in PM_sub42 t.
Ltac PM_all43 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__42_eq; PM_all42.
Definition pm__43 : axst := ltac2:(tb__ "0|0|
S92S42U1A2").
Lemma pm__43_eq : ltac2:(tb__ "0|1|
S0S5S13S22Z1M0A1ScS20G0A2A2S2dA3"). Proof. cbv delta [T5b pm__43]; cbv beta zeta. PM_all43. reflexivity. Qed.
Ltac PM_sub44 t := let t := lazymatch (eval pattern (T5b (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__43) end in PM_sub43 t.
Ltac PM_all44 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__43_eq; PM_all43.
Definition pm__44 : axst := ltac2:(tb__ "0|0|
S92S43U1A2").
Lemma pm__44_eq : ltac2:(tb__ "0|1|
S0S5S13S22Z2M0A1ScS20G0A2A2S2eA3"). Proof. cbv delta [T5b pm__44]; cbv beta zeta. PM_all44. reflexivity. Qed.
Ltac PM_sub45 t := let t := lazymatch (eval pattern (T5b (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__44) end in PM_sub44 t.
Ltac PM_all45 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__44_eq; PM_all44.
Definition pm__45 : axst := ltac2:(tb__ "0|1|
S7S2dSa6S4S2dA1M0Sa4S84G0A1S10S24A1A2A2A2").
Lemma pm__45_eq : ltac2:(tb__ "0|1|
S0S5S14S24S22Z1M0A1ScS20G0A2A3S44A3"). Proof. cbv delta [T5c pm__45]; cbv beta zeta. PM_all45. reflexivity. Qed.
Ltac PM_sub46 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__45) end in PM_sub45 t.
Ltac PM_all46 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__45_eq; PM_all45.
Definition pm__46 : axst := ltac2:(tb__ "0|1|
S7S2eSa6S4S2eA1M0Sa4S84G0A1S10S24A1A2A2A2").
Lemma pm__46_eq : ltac2:(tb__ "0|1|
S0S5S14S24S22Z2M0A1ScS20G0A2A3S45A3"). Proof. cbv delta [T5c pm__46]; cbv beta zeta. PM_all46. reflexivity. Qed.
Ltac PM_sub47 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__46) end in PM_sub46 t.
Ltac PM_all47 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__46_eq; PM_all46.
Definition pm__47 : axst := ltac2:(tb__ "0|0|
S91S44SdA2").
Lemma pm__47_eq : ltac2:(tb__ "0|1|
S0S5S15S24S22Z1M0A1ScS20G0A2A3S46A3"). Proof. cbv delta [T5m1 pm__47]; cbv beta zeta. PM_all47. reflexivity. Qed.
Ltac PM_sub48 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__47) end in PM_sub47 t.
Ltac PM_all48 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__47_eq; PM_all47.
Definition pm__48 : axst := ltac2:(tb__ "0|0|
S91S45SdA2").
Lemma pm__48_eq : ltac2:(tb__ "0|1|
S0S5S15S24S22Z2M0A1ScS20G0A2A3S47A3"). Proof. cbv delta [T5m1 pm__48]; cbv beta zeta. PM_all48. reflexivity. Qed.
Ltac PM_sub49 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__48) end in PM_sub48 t.
Ltac PM_all49 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__48_eq; PM_all48.
Definition pm__49 : axst := ltac2:(tb__ "0|0|
S91S46SdA2").
Lemma pm__49_eq : ltac2:(tb__ "0|1|
S0S5S16S24S22Z1M0A1ScS20G0A2A3S48A3"). Proof. cbv delta [T5m2 pm__49]; cbv beta zeta. PM_all49. reflexivity. Qed.
Ltac PM_sub50 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__49) end in PM_sub49 t.
Ltac PM_all50 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__49_eq; PM_all49.
Definition pm__50 : axst := ltac2:(tb__ "0|0|
S91S47SdA2").
Lemma pm__50_eq : ltac2:(tb__ "0|1|
S0S5S16S24S22Z2M0A1ScS20G0A2A3S49A3"). Proof. cbv delta [T5m2 pm__50]; cbv beta zeta. PM_all50. reflexivity. Qed.
Ltac PM_sub51 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__50) end in PM_sub50 t.
Ltac PM_all51 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__50_eq; PM_all50.
Definition pm__51 : axst := ltac2:(tb__ "0|0|
S91S48SdA2").
Lemma pm__51_eq : ltac2:(tb__ "0|1|
S0S5S17S24S22Z1M0A1ScS20G0A2A3S4aA3"). Proof. cbv delta [T5m3 pm__51]; cbv beta zeta. PM_all51. reflexivity. Qed.
Ltac PM_sub52 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__51) end in PM_sub51 t.
Ltac PM_all52 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__51_eq; PM_all51.
Definition pm__52 : axst := ltac2:(tb__ "0|0|
S91S49SdA2").
Lemma pm__52_eq : ltac2:(tb__ "0|1|
S0S5S17S24S22Z2M0A1ScS20G0A2A3S4bA3"). Proof. cbv delta [T5m3 pm__52]; cbv beta zeta. PM_all52. reflexivity. Qed.
Ltac PM_sub53 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__52) end in PM_sub52 t.
Ltac PM_all53 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__52_eq; PM_all52.
Definition pm__53 : axst := ltac2:(tb__ "0|0|
S91S4aSdA2").
Lemma pm__53_eq : ltac2:(tb__ "0|1|
S0S5SeS24S22Z1M0A1ScS20G0A2A3S67A3"). Proof. cbv delta [T5d pm__53]; cbv beta zeta. PM_all53. reflexivity. Qed.
Ltac PM_sub54 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__53) end in PM_sub53 t.
Ltac PM_all54 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__53_eq; PM_all53.
Definition pm__54 : axst := ltac2:(tb__ "0|0|
S91S4bSdA2").
Lemma pm__54_eq : ltac2:(tb__ "0|1|
S0S5SeS24S22Z2M0A1ScS20G0A2A3S68A3"). Proof. cbv delta [T5d pm__54]; cbv beta zeta. PM_all54. reflexivity. Qed.
Ltac PM_sub55 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__54) end in PM_sub54 t.
Ltac PM_all55 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__54_eq; PM_all54.
Definition pm__55 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub55 t in exact t).
Lemma pm__55_eq : ltac2:(tb__ "0|0|
S0S5S1cS20A1S69A3"). Proof. cbv delta [C5S pm__55]; cbv beta zeta. PM_all55. reflexivity. Qed.
Ltac PM_sub56 t := let t := lazymatch (eval pattern (C5S X5bc) in t) with ?P _ => eval cbv beta in (P pm__55) end in PM_sub55 t.
Ltac PM_all56 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__55_eq; PM_all55.
Lemma WX5rb_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS88S4SfS20R2A2A1A1S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5rb_0 : ltac2:(tb__ "0|4|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S74S73S74S7cS7cA2M0A1M1S73S7dA1M2A2M3A1Sa3S4S1bS20A1A1S4SfS20R2A2A1A2S79G3S78G1G2S72G0S78S7cS7cS89S7aQ20S83Pc0A1A3S7fR2A1A4S71G0A1A3S71S7dA1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4SfS20R2A2A1SdS7fNf10A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S18S20R2A2A1S75SdA1S7fN910A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S19S20R2A2A1S75S75SdA1A1S7fN848A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9bS4S1aS20R2A2A1S75S75S75SdA1A1A1S7fN50A1A3A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERb_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S77S73S7eA1M0A1Sb3ScS20R2A2S98R2A1S28R2A1A3S79G0S2aR2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S5Sb4S28R2A1S98R2A1S99R2A1ScS20R2A2S2aR2A1A5S22R2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6ScS20R2A2A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4ScS20R2A2A1M0A1A1S81G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSb2ScS20R2A2S98R2A1S28R2A1S2aR2A1S72S5S99R2A1S71S5A1A3A5S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0SbS82S4ScS20R2A2A1A1S82S4S20A1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS28R2A1PaM0A2S86Sa1S83G0A1S7fN910A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS28R2A1PfA2S7fN600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S7cS9eS28R2A1PcA2S86Sa1S83PaA1S7fN848A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7eS1eU0S9dS54A3S2aR2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOb_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S7eA1SafS4S98R2A1A1S4S99R2A1A1A2S71S7eA1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPostb_0 : ltac2:(tb__ "0|1|
SaS0S73S74S7cS7cA2M0A1S6S99R1A1A1S71G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS94S7dS85S82S4S22R2A1A1A1A1S81S4ScS20R2A2A1A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4b_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S73S74S7cS7cA2M0A1S6S22R2A1A1S71G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S11S22R2A1ScS20R2A2A2A1U0A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9cS4S12S22R2A1ScS20R2A2A2A1U1A2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_ndb_0 : ltac2:(tb__ "0|0|
S0S6fSa5S10S24A1A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_ltb_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76SbbR1S24A2Li;S10S24A1A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_covb_0 : ltac2:(tb__ "0|0|
S0S6fS94S76S76S97S76SbaR1A1S10S24A1A3Li;SadU0S24A2A3S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lenb_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S76S7bS7eS84S4S13S22R2A1ScS20R2A2A2A1A1A2S24A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S14S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S15S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S16S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8cS80S9aS4S17S24S22R2A1ScS20R2A2A3A1SdA2A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS8SeS24S22R2A1ScS20R2A2A3S30S4eR2A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5b_0 : ltac2:(tb__ "0|0|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fSa0S4eR2A1VGS0;A2S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4covb_0 : ltac2:(tb__ "0|1|
SaS1S2Z1R1A2S2R1Vtmax;A2A2S0S6fS1dS81S4SeS24S22R2A1ScS20R2A2A3A1M0A1S2aR2A1S84G0A1A3S70A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all56; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

End INST.
End SpineCallocSec5IL.

(* [comment removed for export] *)
Module SpineMallocSec6JLW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sobj"; "rl"; "sv"; "holds"; "sprop"; "SVar"; "eval"; "obj_range"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_ptr_committed"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "AE_A"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2"; "nx0"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5ILW2"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.SpineMallocSec6ILW2"; "FXPa"; "FXPb"; "PXa"; "PXb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7"; "bx_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.SpineMallocSec6ILW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S46VCST;R1A2S46S55R2A2S1fF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S6S46VCST;R1A2S46S56R2A2S1fF_;F_;Fa;").

Lemma PXnba_0 : ltac2:(tb__ "0|2|
S17S16S2aS8S27Q40A1M0S8S0G0A1S0S39A1S38S31U2Vst;S33S26S16S37R1A1LX;R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S4fA3S0SbA1S1cS0S1S1SdSdA2SdA2M1A1S35SbG1S4aR1A4S35SbG1S4aS51A4A3S34SbSbS32S12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxa_noband 2%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXoka_0 : ltac2:(tb__ "0|0|
S17S53S26S16S37R1A1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHa_0 : ltac2:(tb__ "0|6|
S17S16S2aS8S27Q40M0A1M1S8S0G1A1S0S39A1S38S31U2Vst;S33S26S16S37R1A1LX;M2R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S4fA3S26G2RbS4cRaS28G0S9R8PcA2A2A2A3S16S1dS1dS20Z8M3Z20000M4A2S20G4G4A2A2S1dS20S21S25G3S23S2S19S18RbA1A2A1A2G4A2S1bR1A1M5A2S1cG1S11R7S13S54S10S4bA1S14Z4000A1A3A2S29G0S22G5G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_a 2%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_2la_P : ltac2:(tb__ "0|9|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S0S1S40S42A2M3A1S36G3S3S40S42S2fS2bVW;Vst;A3S2eS44S15A1VCST;VXGL;R8R7A5A4R1A3S49VW;Vst;A2S2cR9A1S3fS15RcS3eRaA1A3S7S1cG1S9RaR1A2S9RbR1A2A3Fi;S7S1cS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2dVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S19S18RfA1A2A1S1aRfA1A2S1S6S6A2M5S36G5R1S47RbA1A3S45R2S3S6S6S28G0ReA2M6S48S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1dS20S43G6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1eS1cS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S3aS15R15S3dS15S31U2Vst;S33S26S16S37R1A1LX;ReA2R14R13R11R10A8S4dR2R1A5S41S15S3cR12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) C5ac C5Aa Y6Aa E6a CT6a CO6a T6a s6Aa s6a R6a
           FLOWa_0 HC5Aa_0 FBAa_0 Cert6Aa_0 E6Aa_0 I6Aa_0
           WC6a_0 DF6a_0 NX6a_0 HC6a_0 SK6a_0 FC6a_0 FX6a_0 XC6a_0 HCO6a_0 WCO6a_0 He6a_0 Hchk6a_0 HT6a_0 FBC6a_0 FBT6a_0 NXC6a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_triple 2%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D6La U7a ET7a CT7a CO7a CR7a CS7a CM7a T7a s7a R7a n7a
           WU7a_0 DU7a_0 NXU7a_0 HU7a_0 Cert7a_0 WC7a_0 DF7a_0 NX7a_0 HC7a_0 SK7a_0 FC7a_0 FX7a_0 XC7a_0 HCO7a_0 WCO7a_0
           RB7a_0 HCR7a_0 LEN7a_0 PERM_nd7a_0 PERM_lt7a_0 PERM_cov7a_0 HCS7a_0 MRG7a_0 HCM7a_0 He7a_0 Hchk7a_0 HT7a_0 FBC7a_0 FBT7a_0 NXC7a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_triple 2%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D7La U8a ET8a CT8a CO8a T8a s8a R8a
           WU8a_0 DU8a_0 NXU8a_0 HU8a_0 Cert8a_0 WC8a_0 DF8a_0 NX8a_0 HC8a_0 SK8a_0 FC8a_0 FX8a_0 XC8a_0 HCO8a_0 WCO8a_0
           He8a_0 Hchk8a_0 HT8a_0 FBC8a_0 FBT8a_0 NXC8a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_triple 2%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D8La U9a E9fa E9pa CO9pa E9qa
           WU9a_0 DU9a_0 NXU9a_0 HU9a_0 Cert9a_0 SK9a_0 FC9a_0 FX9a_0 FP9a_0 XC9a_0 HCO9a_0 WCO9a_0 Cert9qa_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 2%nat st tmax nx0 Hnx_0 NXG_0 BX E9fa S9afa S9bfa T9fa iMfa s9fa R9fa HS9afa_0 HS9bfa_0 He9fa_0 Hchk9fa_0 HT9fa_0 FBC9fa_0 FBT9fa_0 NXC9fa_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9fa_0.
    exact (sec_g48_P 2%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfa swcfa c1fa c2fa c4fa c5fa mcfa xcfa tybfa SELFfa_0 NDFfa_0 BNDFfa_0 COVFfa_0 XFnfa_0 BFbfa_0 FPFfa_0 FXFfa_0 FPARfa_0
             Hc1fa_0 Hmcfa_0 Htybfa_0 Hxcfa_0 WCUfa_0 SELUfa_0 NDUfa_0 BNDUfa_0 COVUfa_0 W9fa_0 D9fa_0 XB9fa_0 sFfa ENT9fa_0 SID9fa_0 G110fa_0 D9fa CertFfa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 2%nat st tmax nx0 Hnx_0 NXG_0 BX E9qa S9aqa S9bqa T9qa iMqa s9qa R9qa HS9aqa_0 HS9bqa_0 He9qa_0 Hchk9qa_0 HT9qa_0 FBC9qa_0 FBT9qa_0 NXC9qa_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9qa_0.
    exact (sec_g48_P 2%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqa swcqa c1qa c2qa c4qa c5qa mcqa xcqa tybqa SELFqa_0 NDFqa_0 BNDFqa_0 COVFqa_0 XFnqa_0 BFbqa_0 FPFqa_0 FXFqa_0 FPARqa_0
             Hc1qa_0 Hmcqa_0 Htybqa_0 Hxcqa_0 WCUqa_0 SELUqa_0 NDUqa_0 BNDUqa_0 COVUqa_0 W9qa_0 D9qa_0 XB9qa_0 sFqa ENT9qa_0 SID9qa_0 G110qa_0 D9qa CertFqa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_2la : ltac2:(tb__ "0|8|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S49VW;Vst;A2S2cR7A1S3fS15RaS3eR8A1A3S7S1cG1S9R8R1A2S9R9R1A2A3Fi;S7S1cS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2dVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S19S18RdA1A2A1S1aRdA1A2S1S6S6A2M4S36G4R1S47R9A1A3S45R2S3S6S6S28G0RcA2M5S48S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1dS20S43G5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1eS1cS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S3aS15R13S3dS15S31U2Vst;S33S26S16S37R1A1LX;RcA2R12R11RfReA8S4dR2R1A5S41S15S3cR10RdS30S2bS44S15A1VCST;VXGL;VW;Vst;R12R11A8A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_2la_P ok A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Lemma PXnbb_0 : ltac2:(tb__ "0|2|
S17S16S2aS8S27Q40A1M0S8S0G0A1S0S39A1S38S31U2Vst;S33S26S16R1LX;R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S50A3S0SbA1S1cS0S1S1SdSdA2SdA2M1A1S35SbG1S4aR1A4S35SbG1S4aS52A4A3S34SbSbS32S12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxb_noband 2%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXokb_0 : ltac2:(tb__ "0|0|
S17S53S26S16R1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHb_0 : ltac2:(tb__ "0|5|
S17S16S2aS8S27Q40M0A1M1S8S0G1A1S0S39A1S38S31U2Vst;S33S26S16R1LX;M2R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S50A3S26G2RbS4cRaS28G0S9R8PcA2A2A2A3S16S1dS1dS20Z8M3G3A2S20G3Z20000A2A2S1dS20S21S25G3S23S2S19S18RbA1A2A1A2G3A2S1bR1A1M4A2S1cG1S11R7S10S4bA1A2S29G0S22G4G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_b 2%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_2lb_P : ltac2:(tb__ "0|9|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S0S1S40S42A2M3A1S36G3S3S40S42S2fS2bVW;Vst;A3S2eS44S15A1VCST;VXGL;R8R7A5A4R1A3S49VW;Vst;A2S2cR9A1S3fS15RcS3eRaA1A3S7S1cG1S9RaR1A2S9RbR1A2A3Fi;S7S1cS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2dVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S19S18RfA1A2A1S1aRfA1A2S1S6S6A2M5S36G5R1S47RbA1A3S45R2S3S6S6S28G0ReA2M6S48S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1dS20S43G6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1eS1cS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S3aS15R15S3dS15S31U2Vst;S33S26S16R1LX;ReA2R14R13R11R10A8S4eR2R1A5S41S15S3cR12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) C5bc C5Ab Y6Ab E6b CT6b CO6b T6b s6Ab s6b R6b
           FLOWb_0 HC5Ab_0 FBAb_0 Cert6Ab_0 E6Ab_0 I6Ab_0
           WC6b_0 DF6b_0 NX6b_0 HC6b_0 SK6b_0 FC6b_0 FX6b_0 XC6b_0 HCO6b_0 WCO6b_0 He6b_0 Hchk6b_0 HT6b_0 FBC6b_0 FBT6b_0 NXC6b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_triple 2%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D6Lb U7b ET7b CT7b CO7b CR7b CS7b CM7b T7b s7b R7b n7b
           WU7b_0 DU7b_0 NXU7b_0 HU7b_0 Cert7b_0 WC7b_0 DF7b_0 NX7b_0 HC7b_0 SK7b_0 FC7b_0 FX7b_0 XC7b_0 HCO7b_0 WCO7b_0
           RB7b_0 HCR7b_0 LEN7b_0 PERM_nd7b_0 PERM_lt7b_0 PERM_cov7b_0 HCS7b_0 MRG7b_0 HCM7b_0 He7b_0 Hchk7b_0 HT7b_0 FBC7b_0 FBT7b_0 NXC7b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_triple 2%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D7Lb U8b ET8b CT8b CO8b T8b s8b R8b
           WU8b_0 DU8b_0 NXU8b_0 HU8b_0 Cert8b_0 WC8b_0 DF8b_0 NX8b_0 HC8b_0 SK8b_0 FC8b_0 FX8b_0 XC8b_0 HCO8b_0 WCO8b_0
           He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_triple 2%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 2%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D8Lb U9b E9fb E9pb CO9pb E9qb
           WU9b_0 DU9b_0 NXU9b_0 HU9b_0 Cert9b_0 SK9b_0 FC9b_0 FX9b_0 FP9b_0 XC9b_0 HCO9b_0 WCO9b_0 Cert9qb_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 2%nat st tmax nx0 Hnx_0 NXG_0 BX E9fb S9afb S9bfb T9fb iMfb s9fb R9fb HS9afb_0 HS9bfb_0 He9fb_0 Hchk9fb_0 HT9fb_0 FBC9fb_0 FBT9fb_0 NXC9fb_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9fb_0.
    exact (sec_g48_P 2%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfb swcfb c1fb c2fb c4fb c5fb mcfb xcfb tybfb SELFfb_0 NDFfb_0 BNDFfb_0 COVFfb_0 XFnfb_0 BFbfb_0 FPFfb_0 FXFfb_0 FPARfb_0
             Hc1fb_0 Hmcfb_0 Htybfb_0 Hxcfb_0 WCUfb_0 SELUfb_0 NDUfb_0 BNDUfb_0 COVUfb_0 W9fb_0 D9fb_0 XB9fb_0 sFfb ENT9fb_0 SID9fb_0 G110fb_0 D9fb CertFfb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 2%nat st tmax nx0 Hnx_0 NXG_0 BX E9qb S9aqb S9bqb T9qb iMqb s9qb R9qb HS9aqb_0 HS9bqb_0 He9qb_0 Hchk9qb_0 HT9qb_0 FBC9qb_0 FBT9qb_0 NXC9qb_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9qb_0.
    exact (sec_g48_P 2%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqb swcqb c1qb c2qb c4qb c5qb mcqb xcqb tybqb SELFqb_0 NDFqb_0 BNDFqb_0 COVFqb_0 XFnqb_0 BFbqb_0 FPFqb_0 FXFqb_0 FPARqb_0
             Hc1qb_0 Hmcqb_0 Htybqb_0 Hxcqb_0 WCUqb_0 SELUqb_0 NDUqb_0 BNDUqb_0 COVUqb_0 W9qb_0 D9qb_0 XB9qb_0 sFqb ENT9qb_0 SID9qb_0 G110qb_0 D9qb CertFqb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_2lb : ltac2:(tb__ "0|8|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S49VW;Vst;A2S2cR7A1S3fS15RaS3eR8A1A3S7S1cG1S9R8R1A2S9R9R1A2A3Fi;S7S1cS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2dVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S19S18RdA1A2A1S1aRdA1A2S1S6S6A2M4S36G4R1S47R9A1A3S45R2S3S6S6S28G0RcA2M5S48S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1dS20S43G5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1eS1cS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S3aS15R13S3dS15S31U2Vst;S33S26S16R1LX;RcA2R12R11RfReA8S4eR2R1A5S41S15S3cR10RdS30S2bS44S15A1VCST;VXGL;VW;Vst;R12R11A8A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_2lb_P ok A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JLW2.

