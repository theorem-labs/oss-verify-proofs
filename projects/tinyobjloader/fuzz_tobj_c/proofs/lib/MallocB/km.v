(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From Stdlib Require NArith Bool PArith FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3 TopGlueA InvQ8 j1.

(* [comment removed for export] *)
Module DepotKT.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@Corelib.Init.Datatypes"; "list"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_Kf"; "aa_Km"; "aa_depot"; "dN"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache.

Section DepotKT.
Let segs : list Segment := segsA.
Variables (A0 : AA) (rhoE : valuation).

Hypothesis HKT : ltac2:(tb__ "0|0|
S2S1S7VA0;A1S6VA0;A1A2S0A2").

Lemma dN_entry_tol : ltac2:(tb__ "0|0|
S3SaQ40A1A1S4S5Vsegs;VA0;VrhoE;R2R1A5S2S9S8VA0;A1A1S1S0Z1A2A2F_;Fmd;Ftp;").
Proof.
  intros tp md HA. destruct (AInvA_X A0 rhoE tp md HA) as (_ & _ & L6). clear -L6 HKT. lia.
Qed.
End DepotKT.
End DepotKT.

(* [comment removed for export] *)
Module F0T_depotG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "proj1"; "ex"; "not"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "prod"; "andb"; "app"; "pair"; "cons"; "Some"; "option"; "false"; "fst"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SLit"; "SAlu"; "ss_facts"; "SVar"; "sprop_below"; "ss_next"; "valuation"; "rw"; "sprop_eqb"; "ss_objs"; "sv_eqb"; "agree_below"; "holds"; "obj_range"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "PostDv"; "PreDv"; "SZT"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "wsub"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "ge"; "opp"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "DG"; "dN"; "aa_depot"; "AA"; "aa_geom"; "aa_sec"; "aa_Kf"; "aa_Km"; "ageom"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "chain_pre"; "free_depth"; "F_depth"; "Wcan"; "V_DEPTH"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone"; "rng_below"; "zoneF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "coveredb"; "KEEPD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "alloc_top"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "smatchA"; "liftKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "NPRE"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "JLD"; "JD"; "DNMAX"; "dep_cost"; "droom"; "DFP"; "dfp_static"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG.FD.SITE"; "site_factsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "isnil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "HDF"; "HDFE"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2"; "KD_laws2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKF"; "KD"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG"; "dchkbT"; "dchkbT_sound"; "segD_TE_stmt"; "segD_T_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface SegQ_defs Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ik.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require TopGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.TopGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.DepotKT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition segD_T_stmt : Prop := ltac2:(tb__ "0|4|
S3eS64F_;S3dS7fS3bR2S6cR1A4S68OF_;S3eS65S3bR2R5R1A1A3FG;S3eS80S3bR3R6R1A1A3FG;S3dS1S35Z7fff7f800000R1A2S35R1Z7fffff800000A2A2S3eS1eS8S5cQ40M0A1A1M1S8S60A1S5fRdR5R4R3R2R1A5S0S3dS61S62R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S3dS1S35Z1M2R1A2S35R1S2eA2A2S1eG1S3eS35S36S3fR1A1G2A2S71A2S35S3fR2A1S36S78G2A2A2S37RfS36S72R3A1S73R3A1A2A2S1S35RbS36S5dG0S1fR6PaA2A2S5eG0S1fR6S53A2A2A2A2S35RbS5dG0S1fR6PcA2A2A2A2S6aS3bRfS63S3bS70S3bR12R5A3S6dR9A1R7R6A5S4aS3bS6cR7R6SeSaS29S49A2M3SdS29S49S6eR9A1S6fS3bR12R5A3A4S9G3A1A3A5A4F_;F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK;").
Definition segD_TE_stmt : Prop := ltac2:(tb__ "0|4|
S3eS64F_;S3dS7fS3bR2S6cR1A4S3dS1S35Z7fff7f800000R1A2S35R1Z7fffff800000A2A2S3eS1eS8S5cQ40M0A1A1M1S8S60A1S5fRaR5R4R3R2R1A5S0S3dS61S62R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S3dS1S35Z1M2R1A2S35R1S2eA2A2S1eG1S3eS35S36S3fR1A1G2A2S71A2S35S3fR2A1S36S78G2A2A2S37RcS36S72R3A1S73R3A1A2A2S1S35RbS36S5dG0S1fR6PaA2A2S5eG0S1fR6S53A2A2A2A2S35RbS5dG0S1fR6PcA2A2A2A2S69S3bS63S3bS70S3bRfR5A3S6dR9A1R7R6A5S4aS3bS6cR7R6SeSaS29S49A2M3SdS29S49S6eR9A1S6fS3bRfR5A3A4S9G3A1A3A5A3F_;F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK;").

Lemma PreDv_wf : ltac2:(tb__ "0|0|
S3dS0S7S26S27S6dR1A1A1A1S6A3Fsz;").
Proof. intros sz. vm_compute. reflexivity. Qed.
Lemma PreDv_diff : ltac2:(tb__ "0|4|
S3dS0S10SaS8SaS16S16A2M0A1M1S8S15A1M2A2M3A1S89S27S2dA1S27S6dR1A1A1A2SfG3SdG1G2SeG0SdS16S16S1bPdA1S18R1A1A4S9G0A1A3S9S15A1A4A2A3Fsz;").
Proof. intros sz. vm_compute. reflexivity. Qed.
Lemma PreDv_size : ltac2:(tb__ "0|2|
S64S1eS8S5cQ40M0A1A1S68S63S3bR4S2dR3R2R1A6S1S35Z1S5dG0S1fR4PdA2A2M1A2S35G1S2eA2A2F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hw. pose proof (SPA_facts_hold segsA _ _ _ _ _ Hw) as HF.
  assert (F1 : holds rho (SPUle (SLit 1) (SVar 13))) by (apply (proj1 (Forall_forall _ _) HF); cbn [ss_facts ax_S PreDv mkA]; apply in_or_app; right; left; reflexivity).
  assert (F2 : holds rho (SPUle (SVar 13) (SLit SZT))) by (apply (proj1 (Forall_forall _ _) HF); cbn [ss_facts ax_S PreDv mkA]; apply in_or_app; right; right; left; reflexivity).
  clear HF Hw. cbn [holds eval] in F1, F2. unfold SZT in *. rewrite u64_lit in F1, F2 by lia. lia.
Qed.
Lemma PreDv_restate : ltac2:(tb__ "0|1|
S64S1eS8S5cQ40M0A1A1S68S63S3bR4S2dR3R2R1A6S63S3bR5S6dS5dG0S1fR4PdA2A2A1R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hw. set (sz := bv_unsigned (rw rho 13%positive)).
  change (PreD sz) with (ax_setS PreDv (ax_S (PreD sz))).
  eapply SPA_restate; [exact (PreDv_wf sz) | exact (PreDv_diff sz) | reflexivity | | constructor | exact Hw].
  constructor; [|constructor]. cbn [fst snd eval]. unfold sz. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma seg_Dv_sound : ltac2:(tb__ "0|4|
S88S3eS64F_;S3dS7fS3bR2S6cR1A4S68OF_;S3eS65S3bR2R5R1A1A3FG;S3eS80S3bR3R6R1A1A3FG;S3dS1S35Z7fff7f800000R1A2S35R1Z7fffff800000A2A2S3eS1eS8S5cQ40M0A1A1M1S8S60A1S5fRdR5R4R3R2R1A5S0S3dS61S62R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S1eG1S3eS35S36S3fR1A1Z1M2A2S71A2S35S3fR2A1S36S78G2A2A2S37RdS36S72R3A1S73R3A1A2A2S1S35R9S36S5dG0S1fR6PaA2A2S5eG0S1fR6S53A2A2A2A2S35R9S5dG0S1fR6PcA2A2A2A2S6aS3bRdS63S3bS70S3bR10R5A3S2dR7R6A5S4aS3bS6cR7R6SeSaS29S49A2M3SdS29S49S2cS6fS3bR10R5A3A4S9G3A1A3A5A4F_;F_;F_;F_;FG;Ftp;Frho;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK;F_;").
Proof.
  intros HS K hc HKD ok HKok HKokp top Htop HKT rho tp G HDN HKM Hhc HT0.
  apply (triple_by_pure segsA ok (1 <= bv_unsigned (rw rho 13%positive) <= SZT)); [intros w Hw; exact (PreDv_size _ rho tp w Hw)|]. intros Hsz.
  eapply triple_conseq; [intros w Hw; exact (PreDv_restate _ rho tp w Hw) | intros w Hw; exact Hw |].
  exact (HS K hc HKD ok HKok HKokp top Htop HKT _ Hsz rho tp G HDN HKM Hhc HT0).
Qed.
Lemma seg_Dv_complete : ltac2:(tb__ "0|4|
S87S3eS64F_;S3dS7fS3bR2S6cR1A4S3dS1S35Z7fff7f800000R1A2S35R1Z7fffff800000A2A2S3eS1eS8S5cQ40M0A1A1M1S8S60A1S5fRaR5R4R3R2R1A5S0S3dS61S62R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S1eG1S3eS35S36S3fR1A1Z1M2A2S71A2S35S3fR2A1S36S78G2A2A2S37RaS36S72R3A1S73R3A1A2A2S1S35R9S36S5dG0S1fR6PaA2A2S5eG0S1fR6S53A2A2A2A2S35R9S5dG0S1fR6PcA2A2A2A2S69S3bS63S3bS70S3bRdR5A3S2dR7R6A5S4aS3bS6cR7R6SeSaS29S49A2M3SdS29S49S2cS6fS3bRdR5A3A4S9G3A1A3A5A3F_;F_;F_;F_;FG;Ftp;Frho;F_;F_;Ftop;F_;Fhc;FK;F_;").
Proof.
  intros HS K hc HKD top Htop HKT rho tp G HDN HKM Hhc HT0.
  apply (etriple_by_pure segsA (1 <= bv_unsigned (rw rho 13%positive) <= SZT)); [intros w Hw; exact (PreDv_size _ rho tp w Hw)|]. intros Hsz.
  eapply etriple_conseq; [intros w Hw; exact (PreDv_restate _ rho tp w Hw) | intros w Hw; exact Hw |].
  exact (HS K hc HKD top Htop HKT _ Hsz rho tp G HDN HKM Hhc HT0).
Qed.

Definition dchkbT (nW : nat) (rdok : sobj -> bool) (ED TD : axst) (sD : wsub) (RD : list sobj) : bool := ltac2:(tb__ "0|8|
SbS7aSaS16S16A2M0S28VED;A1A2SbS7aG0S28VTD;A1A2SbS5bS3cS1dS27VED;A1M1A1M2A2SbS2aS15S1cG2A1S1aG1A1M3A3SbS2aS15S1cS1dS27S48VsD;S2dS2cVED;VRD;A5A1A1A1G3A3SbS22S30VsD;PaM4A2S19S2fS1bG4A1M5S18N880A1A3A2SbS22S30VsD;PfM6A2S19S2fS1bG6A1S18Z880A1A3A2SbS22S30VsD;PcA2S19S2fG5S18N840A1A3A2SbS2aS17Vrdok;VRD;A3SbS2aS17S55S3cA1VRD;A3SbS2aS15S15S2bS15S20R1A1G3A3Lf;ScS15S4fS52VnW;A1A1S51S50A1A3A3SbS7aS17S57S27S2dA1S27S2cA1A2A2SbS7aG0S28S2cA1A2S59S1aS27VTD;A1M7A1VRD;S21G7A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma dchkbT_sound : ltac2:(tb__ "0|b|
S13S17S7F_;S29S29S34S8S17A1M0S0S7S85R6R5R4R3R2R1A6S6A3S1S0S8SaS16S16A2M1A1M2S28R5A1S9G1A1M3A3S1S0G2S28R4A1G3A3S1S0S7S5bS3cS1dS27R5A1M4A1M5A2S6A3S1S0S7S2aS15S1cG5A1S1aG4A1M6A3S6A3S1S0S7S2aS15S1cS1dS27S48R3S2dS2cR5R2A5A1A1A1G6A3S6A3S1S0S16S30R3PaM7A2S19S2fS1bG7A1M8S18N880A1A3A3S1S0S16S30R3PfM9A2S19S2fS1bG9A1S18Z880A1A3A3S1S0S16S30R3PcA2S19S2fG8S18N840A1A3A3S1S0S7S2aS17R6R2A3S6A3S1S0S7S2aS17S55S3cA1R2A3S6A3S1S0S7S2aS15S15S2bS15S20R1A1S1aS27R6A1A1A3Lf;ScS15S4fS52R7A1A1S51S50A1A3A3S6A3S1S0G0S57S27S2dA1S27S2cA1A2S9S17A1A3S1S0G2S28S2cA1G3A3S0S7S59S1aS27R4A1MaA1R2S21GaA1A3S6A3A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FRD;FsD;FTD;FED;Frdok;FnW;").
Proof.
  intros nW rdok ED TD sD RD H. unfold dchkbT in H.
  repeat (apply andb_prop in H as [?X H]).
  repeat match goal with X : isnil _ = true |- _ => apply isnil_sound in X | X : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in X end.
  apply isnil_sound in X10, X11 || idtac.
  repeat split; assumption.
Qed.

Section FD.
Variable nW : nat. Variable rdok : sobj -> bool.
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S3dS8cVCST;R1A2S5S75R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Variables (ED TD : axst) (sD : wsub) (RD : list sobj).
Hypothesis HER : ltac2:(tb__ "0|1|
S0S10S8S17A1M0A1S4dVED;S2dVsD;A3SfG0VRD;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S7S4cVED;S2dVsD;VRD;SeS29S2cS9S29A1A3A5S6A3").
Hypothesis HTD : ltac2:(tb__ "0|0|
S0S29VTD;S8aS48VsD;S2dS2cVED;VRD;A5S1aS27VED;A1A1A2A3").
Hypothesis DCHK : ltac2:(tb__ "0|0|
S0S7S85VnW;Vrdok;VED;VTD;VsD;VRD;A6S6A3").
Let PARTS := dchkbT_sound nW rdok ED TD sD RD DCHK.
Let XXE : ax_X ED = [] := proj1 PARTS.
Let XTD : ax_X TD = [] := proj1 (proj2 PARTS).
Let NXE : Pos.leb GW (ss_next (ax_S ED)) = true := proj1 (proj2 (proj2 PARTS)).
Let FBX : forallb (sprop_below (ss_next (ax_S ED))) (ss_facts (ax_S ED)) = true := proj1 (proj2 (proj2 (proj2 PARTS))).
Let FBT : forallb (sprop_below (ss_next (ax_S (import_postA sD (PreDv) (PostDv) ED RD)))) (ss_facts (ax_S ED)) = true := proj1 (proj2 (proj2 (proj2 (proj2 PARTS)))).
Let WG10 : wsub_get sD 10 = SAlu ALU_ADD (SVar 10) (SLit (-2176)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))).
Let WG15 : wsub_get sD 15 = SAlu ALU_ADD (SVar 15) (SLit 2176) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))).
Let WG12 : wsub_get sD 12 = SAlu ALU_ADD (SVar 10) (SLit (-2112)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))).
Let RDOK : forallb rdok RD = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))).
Let RDWF : forallb (rng_below GW) RD = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))).
Let FCH : forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S ED))) (chain_pre W ++ F_depth free_depth) = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))).
Let NEWO : new_objs (ax_S (PreDv)) (ax_S (PostDv)) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))))).
Let XPost : ax_X (PostDv) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).
Let RDcov : coveredb (ss_facts (ax_S TD)) RD (ss_objs (ax_S TD)) = true := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).

Section SITE.
Variables (A : AA) (Kc : KcA) (rho1 : valuation).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HKMAX : ltac2:(tb__ "0|0|
S35S36S45VA;A1S44VA;A1A2S78A2").

Hypothesis HZ : ltac2:(tb__ "0|1|
S1eS23S3cVrho1;R1A3S54VA;R2A2S35S5eQ40S1fR3S53A2A2S38S50A1A2S82S15S24R4A1S4fVW;A1A3S17S0S7Vrdok;R1A1S6A3S0S7S55S3cR2A2S6A3S3dS1S35S12S3dS3dS25R9R4A2M0A3R1A2S39R1S14S3dS3dG0A3A2A2S56VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;").

Definition site_factsF (rhoE : valuation) : Prop := ltac2:(tb__ "0|1|
S1S23S3cVrho1;VrhoE;A3S1S54VA;VrhoE;A2S1S1S35S38S3aZ2Z28A2A1S5eQ40S1fVrhoE;S53A2A2M0A2S35G0S38S50A1A2A2S82S15S24VrhoE;A1S4fVW;A1A3A2A2A2").

Lemma fd_facts : ltac2:(tb__ "0|0|
S1eS8S5cQ40A1A1S68S63Vsegs;S7bVnW;Vst;S6VA;VKc;Vrho1;A6VED;R3R2R1A6S79R4A1F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Htop).
  pose proof (proj1 Hw) as (Hsm & _). unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (FIN : forall f, In f (chain_pre W ++ F_depth free_depth) -> holds rhoE f).
  { intros f Hf. pose proof (proj1 (forallb_forall _ _) FCH f Hf) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    exact (proj1 (Forall_forall _ _) HFa f Hg). }
  split; [exact Hag|]. split; [exact Htop|]. split.
  - assert (D1 : holds rhoE (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply FIN; apply in_or_app; right; left; reflexivity).
    assert (D2 : holds rhoE (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply FIN; apply in_or_app; right; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1, D2. unfold bv_lts in D1, D2. apply negb_true_iff in D1, D2. apply Z.ltb_ge in D1, D2.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. change (bv_signed (Z_to_bv 64 (- 2 ^ 40))) with (- 2 ^ 40) in D2. lia.
  - apply Forall_forall. intros f Hf. apply FIN. apply in_or_app. left. exact Hf.
Qed.

Lemma fd_R4 : ltac2:(tb__ "0|2|
S1eS79R1A1S41S1eS8S5cQ40M0A1M1A1S5fG1S8bR5R4R3R2A4S0S46S42R6A1S42VA;A1A3S0S8S47A1S43R7A1S43VA;A1A3S33RaVRD;R4A3S5S74S40R9A1S5dG0R5A2A2A1F_;F_;F_;F_;Fa;Fmdx;Ftpx;Frx;FAx;F_;FrhoE;").
Proof.
  intros rhoE (Hag & Htop & Hdep & Hch) Ax rx tpx mdx a HX EG ES (o & Ho & Hoa).
  apply (zoneF_not_DFP A Ax rx tpx mdx (bv_unsigned a) HX EG ES).
  exact (HZ rhoE Hag Htop (proj2 Hdep) Hch o (proj1 (forallb_forall _ _) RDOK o Ho) (proj1 (forallb_forall _ _) RDWF o Ho) (bv_unsigned a) Hoa).
Qed.

Lemma fd_entry : ltac2:(tb__ "0|1|
S1eS8S5cQ40A1A1S8S60A1M0S76S5fS79R5A1S66Vsegs;R6R5VED;SdG0S83R4S84R3R2A2A4A5S7bVnW;Vst;S6VA;VKc;Vrho1;R7R6R5R3AaS70S3bS81VA;VKc;R8A3S40VA;A1S32S31R8VRD;S77R4R7R5A3A3VsD;A2R7R6R4A7F_;F_;F_;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md SF Hsm0 [Hag0 HJ0].
  pose proof SF as (_ & Htop & Hdep & _). unfold top_high in Htop. unfold free_depth in Hdep.
  pose proof HJ0 as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2176 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2176)))) = bv_unsigned (rw rhoE 10%positive) - 2176).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2176))) with (2 ^ 64 - 2176) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2112)))) = bv_unsigned (rw rhoE 10%positive) - 2112).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2112))) with (2 ^ 64 - 2112) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  - apply (KD_intro A Kc rhoE HB HKm0 HKf0 tp tr0 md HA HK). unfold TOPr, V_DEPTH. cbn [rw rho_sub rho_absorb].
    rewrite WG10, WG15, WG12, !eval_absorb, Em2176, Em2112.
    rewrite signed_add_lit by (cbn [eval]; unfold V_DEPTH in Hdep; lia). cbn [eval]. unfold V_DEPTH in Htop, Hdep. lia.
  - destruct (AInvA_X A rhoE tp md HA) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot A) rhoE _ md tp); [|exact HD0]. intros a Ha. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin. apply (fd_R4 rhoE SF A rhoE tp md _ HX0 eq_refl eq_refl Hin). rewrite u64_lit by exact Hr. exact Ha.
Qed.

Lemma fd_exit_ok : ltac2:(tb__ "0|2|
S1eS8S5cQ40A1A1M0S8S60A1M1S76S5fS1eG0G1S76S5fS79RaA1S6fS3bS81VA;VKc;RbA3S40VA;A1A3S49S32S31RcVRD;S77R8RbR9A3A3VsD;A2S1eR2R1RcR8R7R6R4A6S4eReS77RaRdRbA3VRD;VsD;S2dS2cVED;R9A8F_;TrhoC;TJL;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' ms' md' SF JL rhoC HJL. subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros a Hin. apply HRM. pose proof HKD' as (HXK & _). exact (fd_R4 rhoE SF _ rhoE tpL md' a HXK eq_refl eq_refl Hin).
  - intros o' oR Ho' HoR. rewrite NEWO in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite XPost in Hr. destruct Hr.
  - intros r a j Hr. rewrite XXE in Hr. destruct Hr.
Qed.

Lemma fd_exit_core : ltac2:(tb__ "0|2|
S1eS8S5cQ40A1A1M0S8S60A1M1S76S5fS1eG0G1S76S5fS79RaA1S6fS3bS81VA;VKc;RbA3S40VA;A1A3S49S32S31RcVRD;S77R8RbR9A3A3VsD;A2S1eS66Vsegs;RdRcVED;SdG1S83RbS84RaR9A2A4A5S7bVnW;Vst;S6VA;VKc;Vrho1;ReRdRcRaAaR4R3ReRaR9R8R6A6S1eS68S58R12S77ReR11RfA3VRD;VsD;S27S2dA1S27VED;A1S27S2cA1R2RdA9S63Vsegs;S4bR8R7R12ReRdA5S48VsD;S2dS2cVED;VRD;A5R3RdR2A6S4S41S41S4S1eS1eS4S1eS1eS1S7eVA;R3A2S1S8dS5aVCST;VXGL;VA;A3Vrho1;R2A3S63Vsegs;S7bVnW;Vst;S11R3VKc;R2A6VTD;R1R11R6A6A2A2LrhoX;A2Lrho'';A2LA';A2F_;F_;Fw';Frho';F_;F_;F_;TrhoC;TJL;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' ms' md' SF JL rhoC Hsm0 [Hag0 HJ0] HJL rho' w' HLK [Hsm' HJ'].
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as (HA0' & HU0 & HL0 & HK0 & Htp0 & _ & Htop0). unfold top_high in Htop0.
  subst JL.
  destruct (entails_frA_sound segs ED (PreDv) sD RD rhoE tp tr0 ms0 md HER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as (HX2 & HK2 & HL2 & HT2).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S ED))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. apply Pos.leb_le. exact NXE. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S ED))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros f Hf.
    exact (proj1 (holds_agree_vals _ rhoE rho' f Hag' (proj1 (forallb_forall _ _) FBX f Hf)) (proj1 (Forall_forall _ _) Hfacts4 f Hf)). }
  assert (HT40 : SPA segs (J_ofPA (JLD segsA (KD A Kc rhoE) (aa_depot A)) (rho_sub (rho_absorb rhoE RD (vms md tp ms0)) sD) tp rhoL tpL) TD rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite HTD. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact FBT | intros _; exact HF4]. }
  match type of HT40 with SPA _ ?Jx _ _ _ _ => set (JP := Jx) in HT40 end.

  assert (RNG : forall o, In o RD -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S ED))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := bumpKf (with_depot A G2)).
  set (rho5 := rho_absorb rho' RD (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho1) (rl rho1) (rm rho5)).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' RD a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' RD a <-> in_ranges rhoE RD a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (R4DFP : forall a, in_ranges rhoE RD a -> ~ DFP G2 (bv_unsigned a)).
  { intros a Hin. exact (fd_R4 rhoE SF A' rhoE tpL md2 a HX2 eq_refl eq_refl Hin). }
  assert (KEY : forall a, ~ DFP G2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' RD a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (KEYin : forall a, in_ranges rhoE RD a -> rm rho5 a = rm rhoE a).
  { intros a Hi. rewrite RM5. destruct (in_ranges_dec rho' RD a) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE a) Hi)). }
  assert (BAND : forall a, SHADOW_BAND_LO <= a < SHADOW_BAND_HI -> ~ DFP G2 a).
  { intros a HB'. apply (zoneF_not_DFP A A' rhoE tpL md2 a HX2 eq_refl eq_refl). unfold zoneF. cbn zeta. do 5 right. left. exact HB'. }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE RD (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' RD (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros a Ha. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' RD (Z_to_bv 64 a)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 a) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Ha. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X A rhoE tp md HA0') as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A'. cbn [aa_depot aa_Km aa_Kf bumpKf with_depot]. lia. }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (HJF5 : JF nW st false A' Kc rho'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold rho''. cbn [rw]. rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite (Hagl l). exact (proj2 Hag' l).
      + intros a. reflexivity.
    - split; [exact HA5|]. split; [exact (stopJ_le _ _)|].
      split; [rewrite (RW5 12%positive), (RW5 13%positive) by (unfold GW; lia); exact HL0|]. split; [exact HK2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact I|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }

  assert (HT5 : SPA segs (JF nW st false A' Kc rho'') TD rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT40)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact XTD | | exact HT40 | exact HJF5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT RDcov Ho Ha). }
  exists A', rho'', rho5. split; [|split; [|exact HT5]].
  - unfold depot_onlyKf, A'. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf bumpKf with_depot].
    repeat split; reflexivity.
  - split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros a Hk. unfold rho''. cbn [rm]. rewrite KEY; [symmetry; exact (Hagm a)|].
      exact (keep_not_DFP UStopLe CST XGL HCST HXGL HCSTD A' rhoE tpL md2 (bv_unsigned a) HX2 Hk).
    + intros a HBa Hdef. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); exact Hdef|]. exact (BAND (bv_unsigned a) HBa).
Qed.

Theorem depot_call_HDFT : ltac2:(tb__ "0|1|
S68OF_;S6bS65Vsegs;R2S67VKc;A1M0A3S80Vsegs;R3G0A3S7cVnW;Vst;S5aVCST;VXGL;VA;A3R4VA;VKc;Vrho1;VED;VTD;R3AaF_;F_;FQ;Fok;").
Proof.
  intros ok Q Hokl Hokpl rhoE tp Hcont k HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (fd_facts rhoE tp _ Hw) as SF.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB. pose proof (proj1 HA) as HG.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t0 tr0 md1, KD A Kc rhoE G r t0 tr0 md1 -> alloc_top (m_vmmaps md1) = topG (aa_geom A)).
  { intros G r t0 tr0 md1 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t0 tr0 md1 HKG). }
  apply (call_soundPA segs ok (JF nW st true A Kc rho1) (JD segsA (KD A Kc rhoE) (aa_depot A)) ED (PreDv) sD RD
           [(PostDv, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp HER).
  - change (map fst [(PostDv, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostDv]. exact Hchk.
  - intros rhoP tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    refine (seg_Dv_sound HSEG (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE HKc HB HKm0 HKf0 NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              rhoP tp1 (aa_depot A) (dN_entry A rhoE HB tp md HA) (dN_entry_tol A rhoE HKMAX tp md HA) (hcD_entry A rhoE HB tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t0 tr0 ms0 md1 msv' HKG HMI Hh Hp Hs. exact (Hokl r t0 tr0 ms0 md1 msv' (KD_Kc A Kc rhoE G r t0 tr0 md1 HKG) HMI Hh Hp Hs).
    + intros G r t0 tr0 ms0 md1 x8 HKG Hp Hok. exact (Hokpl r t0 tr0 ms0 md1 x8 (KD_Kc A Kc rhoE G r t0 tr0 md1 HKG) Hp Hok).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (fd_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (fd_exit_ok rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF HJL)|].
    intros rho' HLK n' Hg' w' Hw'.
    destruct (fd_exit_core rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
    exact (Hcont A' rho'' rhoX tpL Hdo Hl n' Hg' w' HC5).
  - exact HgQ.
  - exact Hw.
Qed.

Theorem depot_call_HDFET : ltac2:(tb__ "0|0|
S68OF_;S7dVnW;Vst;S5aVCST;VXGL;VA;A3VA;VKc;Vrho1;VED;VTD;R1A9FQ;").
Proof.
  intros Q rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (fd_facts rhoE tp _ Hw) as SF.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB. pose proof (proj1 HA) as HG.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t0 tr0 md1, KD A Kc rhoE G r t0 tr0 md1 -> alloc_top (m_vmmaps md1) = topG (aa_geom A)).
  { intros G r t0 tr0 md1 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t0 tr0 md1 HKG). }
  apply (call_completePA segs (JF nW st true A Kc rho1) (JD segsA (KD A Kc rhoE) (aa_depot A)) ED (PreDv) sD RD
           [(PostDv, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp HER).
  - change (map fst [(PostDv, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostDv]. exact Hchk.
  - intros rhoP tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    exact (seg_Dv_complete HSEGE (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE HKc HB HKm0 HKf0 NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              rhoP tp1 (aa_depot A) (dN_entry A rhoE HB tp md HA) (dN_entry_tol A rhoE HKMAX tp md HA) (hcD_entry A rhoE HB tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (fd_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (fd_exit_ok rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF HJL)|].
    intros rho' HLK w' Hw'.
    destruct (fd_exit_core rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
    exact (Hcont A' rho'' rhoX tpL Hdo Hl w' HC5).
  - exact Hw.
Qed.
End SITE.
End FD.
End F0T_depotG.

(* [comment removed for export] *)
Module F0A_dL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2A"; "q_L2A"; "ED_L2A_1"; "ED_L2A_2"; "ED_L2A_3"; "ED_L2A_4"; "TD_L2A_1"; "TD_L2A_2"; "TD_L2A_3"; "TD_L2A_4"; "RD_L2A_1"; "RD_L2A_2"; "RD_L2A_3"; "RD_L2A_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L2A_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_L2A_1, TD_of, RD_L2A_1; reflexivity. Qed.
Theorem hdf_L2A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_1 TD_L2A_1 (sD_of ED_L2A_1 1) RD_L2A_1 HeD_L2A_1 HchkD_L2A_1 HTD_L2A_1 DCHK_L2A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_1 TD_L2A_1 (sD_of ED_L2A_1 1) RD_L2A_1 HeD_L2A_1 HchkD_L2A_1 HTD_L2A_1 DCHK_L2A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2A_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_L2A_2, TD_of, RD_L2A_2; reflexivity. Qed.
Theorem hdf_L2A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_2 TD_L2A_2 (sD_of ED_L2A_2 2) RD_L2A_2 HeD_L2A_2 HchkD_L2A_2 HTD_L2A_2 DCHK_L2A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_2 TD_L2A_2 (sD_of ED_L2A_2 2) RD_L2A_2 HeD_L2A_2 HchkD_L2A_2 HTD_L2A_2 DCHK_L2A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2A_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_L2A_3, TD_of, RD_L2A_3; reflexivity. Qed.
Theorem hdf_L2A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_3 TD_L2A_3 (sD_of ED_L2A_3 3) RD_L2A_3 HeD_L2A_3 HchkD_L2A_3 HTD_L2A_3 DCHK_L2A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_3 TD_L2A_3 (sD_of ED_L2A_3 3) RD_L2A_3 HeD_L2A_3 HchkD_L2A_3 HTD_L2A_3 DCHK_L2A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2A_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_L2A_4, TD_of, RD_L2A_4; reflexivity. Qed.
Theorem hdf_L2A_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_4 TD_L2A_4 (sD_of ED_L2A_4 4) RD_L2A_4 HeD_L2A_4 HchkD_L2A_4 HTD_L2A_4 DCHK_L2A_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_4 TD_L2A_4 (sD_of ED_L2A_4 4) RD_L2A_4 HeD_L2A_4 HchkD_L2A_4 HTD_L2A_4 DCHK_L2A_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL2A.

(* [comment removed for export] *)
Module F0A_dL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be"; "q_L2Be"; "ED_L2Be_1"; "ED_L2Be_2"; "ED_L2Be_3"; "ED_L2Be_4"; "TD_L2Be_1"; "TD_L2Be_2"; "TD_L2Be_3"; "TD_L2Be_4"; "RD_L2Be_1"; "RD_L2Be_2"; "RD_L2Be_3"; "RD_L2Be_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L2Be_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_L2Be_1, TD_of, RD_L2Be_1; reflexivity. Qed.
Theorem hdf_L2Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_1 TD_L2Be_1 (sD_of ED_L2Be_1 1) RD_L2Be_1 HeD_L2Be_1 HchkD_L2Be_1 HTD_L2Be_1 DCHK_L2Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_1 TD_L2Be_1 (sD_of ED_L2Be_1 1) RD_L2Be_1 HeD_L2Be_1 HchkD_L2Be_1 HTD_L2Be_1 DCHK_L2Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Be_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_L2Be_2, TD_of, RD_L2Be_2; reflexivity. Qed.
Theorem hdf_L2Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_2 TD_L2Be_2 (sD_of ED_L2Be_2 2) RD_L2Be_2 HeD_L2Be_2 HchkD_L2Be_2 HTD_L2Be_2 DCHK_L2Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_2 TD_L2Be_2 (sD_of ED_L2Be_2 2) RD_L2Be_2 HeD_L2Be_2 HchkD_L2Be_2 HTD_L2Be_2 DCHK_L2Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Be_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_L2Be_3, TD_of, RD_L2Be_3; reflexivity. Qed.
Theorem hdf_L2Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_3 TD_L2Be_3 (sD_of ED_L2Be_3 3) RD_L2Be_3 HeD_L2Be_3 HchkD_L2Be_3 HTD_L2Be_3 DCHK_L2Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_3 TD_L2Be_3 (sD_of ED_L2Be_3 3) RD_L2Be_3 HeD_L2Be_3 HchkD_L2Be_3 HTD_L2Be_3 DCHK_L2Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Be_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_L2Be_4, TD_of, RD_L2Be_4; reflexivity. Qed.
Theorem hdf_L2Be_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_4 TD_L2Be_4 (sD_of ED_L2Be_4 4) RD_L2Be_4 HeD_L2Be_4 HchkD_L2Be_4 HTD_L2Be_4 DCHK_L2Be_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_4 TD_L2Be_4 (sD_of ED_L2Be_4 4) RD_L2Be_4 HeD_L2Be_4 HchkD_L2Be_4 HTD_L2Be_4 DCHK_L2Be_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL2Be.

(* [comment removed for export] *)
Module F0A_dL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf"; "q_L2Bf"; "ED_L2Bf_1"; "ED_L2Bf_2"; "ED_L2Bf_3"; "ED_L2Bf_4"; "TD_L2Bf_1"; "TD_L2Bf_2"; "TD_L2Bf_3"; "TD_L2Bf_4"; "RD_L2Bf_1"; "RD_L2Bf_2"; "RD_L2Bf_3"; "RD_L2Bf_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L2Bf_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_L2Bf_1, TD_of, RD_L2Bf_1; reflexivity. Qed.
Theorem hdf_L2Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_1 TD_L2Bf_1 (sD_of ED_L2Bf_1 1) RD_L2Bf_1 HeD_L2Bf_1 HchkD_L2Bf_1 HTD_L2Bf_1 DCHK_L2Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_1 TD_L2Bf_1 (sD_of ED_L2Bf_1 1) RD_L2Bf_1 HeD_L2Bf_1 HchkD_L2Bf_1 HTD_L2Bf_1 DCHK_L2Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Bf_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_L2Bf_2, TD_of, RD_L2Bf_2; reflexivity. Qed.
Theorem hdf_L2Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_2 TD_L2Bf_2 (sD_of ED_L2Bf_2 2) RD_L2Bf_2 HeD_L2Bf_2 HchkD_L2Bf_2 HTD_L2Bf_2 DCHK_L2Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_2 TD_L2Bf_2 (sD_of ED_L2Bf_2 2) RD_L2Bf_2 HeD_L2Bf_2 HchkD_L2Bf_2 HTD_L2Bf_2 DCHK_L2Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Bf_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_L2Bf_3, TD_of, RD_L2Bf_3; reflexivity. Qed.
Theorem hdf_L2Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_3 TD_L2Bf_3 (sD_of ED_L2Bf_3 3) RD_L2Bf_3 HeD_L2Bf_3 HchkD_L2Bf_3 HTD_L2Bf_3 DCHK_L2Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_3 TD_L2Bf_3 (sD_of ED_L2Bf_3 3) RD_L2Bf_3 HeD_L2Bf_3 HchkD_L2Bf_3 HTD_L2Bf_3 DCHK_L2Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Bf_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_L2Bf_4, TD_of, RD_L2Bf_4; reflexivity. Qed.
Theorem hdf_L2Bf_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_4 TD_L2Bf_4 (sD_of ED_L2Bf_4 4) RD_L2Bf_4 HeD_L2Bf_4 HchkD_L2Bf_4 HTD_L2Bf_4 DCHK_L2Bf_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_4 TD_L2Bf_4 (sD_of ED_L2Bf_4 4) RD_L2Bf_4 HeD_L2Bf_4 HchkD_L2Bf_4 HTD_L2Bf_4 DCHK_L2Bf_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL2Bf.

(* [comment removed for export] *)
Module F0T_drain.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "proj1"; "not"; "or"; "ex"; "False"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "cons"; "prod"; "app"; "pair"; "false"; "Some"; "option"; "nat"; "fst"; "orb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "sobj"; "SLit"; "SAlu"; "ss_facts"; "ss_next"; "sprop_below"; "valuation"; "rw"; "ss_objs"; "sprop_eqb"; "sv_eqb"; "rl"; "rm"; "holds"; "ss_lenient"; "SPBranch"; "SPNot"; "obj_range"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "ax_setS"; "leafA"; "entailsA"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "In"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PreQ3"; "PostQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "chain_pre"; "free_depth"; "F_depth"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "top_high"; "V_DEPTH"; "mem_keptA"; "J_free_preT"; "Pre_freeI"; "tp_ok"; "ulink"; "unwind_objs"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "qbatch"; "aa_geom"; "aa_live"; "aa_cache_inited"; "aa_q_thread"; "budget_bound"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_frames"; "budget_ok_free"; "aa_internal_inited"; "ageom"; "cls_kept_freeA"; "topG"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "cs_allocated_user"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "rq_okb"; "qchkb"; "F_cne"; "drain_sum"; "drain_sumE"; "qchkb_sound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone"; "rng_below"; "same_rng"; "winpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "kQuarantineMin"; "kQuarantineBatchSize"; "kUserSpaceSize"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "opp"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "smatchA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "qcond"; "j_min"; "junkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain.DR.SITE"; "JC"; "site_factsQ"; "JX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "qbounded"; "JQ3"; "JLQ3"; "qpost"; "cls_of"; "q_pure"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "isnil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "depot_onlyKf"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "RETF"; "FUELF"; "leaves_at"; "qvar"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "maskv"; "restrictv"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "PostsQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"; "AInvA"; "IA_BEG"; "IA_END"; "fs_footb"; "fs_inv"; "geom_ok"; "inv3"; "live_sep"; "primary_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "AInvB"; "IMG_F"; "freeA"; "freeQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain.DR"; "JC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "QG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface SegQ_defs Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_rebuildW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition F_cne : sprop := ltac2:(tb__ "0|0|
S2aS29S3fS1bS89SdcZa0A2A1S1cS3eS19P97A1S1bZ50A1A3A3A1").

Definition drain_sum (ok : world -> Prop) (Kc : KcA) : Prop := ltac2:(tb__ "0|1|
S61S20SaS4aQ40A1A1S4S0SaS62A1S66R3A1SbS62A1A3A1S0S8S65R4A1S9A3Sa6R5A1S88S67R6A1Sa3A2S98S8eVok;S8fS8eSa7S8eSa4VKc;A1M0R7A3S40R6R5A5S45S8eSceR6R5SbfG0R7A2A5A4F_;F_;F_;F_;Ftp;Frho;FA;").
Definition drain_sumE (Kc : KcA) : Prop := ltac2:(tb__ "0|1|
S61S20SaS4aQ40A1A1S4S0SaS62A1S66R3A1SbS62A1A3A1S0S8S65R4A1S9A3Sa6R5A1S88S67R6A1Sa3A2S97S8eS8fS8eSa7S8eSa4VKc;A1M0R7A3S40R6R5A5S45S8eSceR6R5SbfG0R7A2A5A3F_;F_;F_;F_;Ftp;Frho;FA;").

Lemma budget_depot : ltac2:(tb__ "0|0|
S61S61S6cR2A1SafR3R2A2S88S67R3A1Sa3A2F_;F_;FA';FA;").
Proof.
  intros A A' HB (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EV & EKm & EKf).
  unfold budget_ok_free, limit_ok_free in HB. unfold budget_bound. rewrite EV, EKm, EKf. exact HB.
Qed.
Lemma entry_budget : ltac2:(tb__ "0|0|
SaS5eA1S60S61S54S20SaS4aQ40A1A1S96S8fS8eS5bSc4S8eA1R7R6R5R4A5S5cS52R7R6A3R3R2R1A6S6cR6A1F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof. intros W st A Kc rho tp w [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HB & _). exact HB. Qed.

Definition rq_okb (nW : nat) (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S83Vo;A1S3aS1aS82Vo;A1S5fS4eVnW;A1A1A3A2").

Definition qchkb (nW : nat) (Cd Pq TQ : axst) (sQ : wsub) (RQ : list sobj) : bool := ltac2:(tb__ "0|c|
S39S8S8R1Lb;ScS8SaeSdS17S17A2M0S34VCd;A1A2ScS8SaeG0S34VTQ;A1A2ScS8S75S42S1eS33VCd;A1M1A1M2A2ScS8S39S18S1fG2A1S1dG1A1M3A3ScS8S39S18S1fS1eS33S43VsQ;S40VPq;VCd;VRQ;A5A1A1A1G3A3ScS8S24S2dVsQ;PaM4A2S1cS3eS19G4A1S1bN8a0A1A3A2ScS8S24S2dVsQ;PfM5A2S1cS3eS19G5A1S1bZ8a0A1A3A2ScS8S24S2dVsQ;P18M6A2S19G6A1A2ScS8S24S2dVsQ;P97M7A2S19G7A1A2ScS8S24S2dVsQ;P98M8A2S19G8A1A2ScS8S24S2dVsQ;P9bM9A2S19G9A1MaA2ScS8S24S2dVsQ;P9cA2S1cS3eGaS1bS84A1A3A2ScS8S39S1aS78VnW;A1VRQ;A3ScS8S39S1aS81S42A1VRQ;A3ScS8S39S18S18S3aS18S23R1A1G3A3Lf;SeS18S4fS4eVnW;A1A1S51S50A1A3A3ScS8SaeS1aS7eS33S40A1S33VPq;A1A2A2ScS8SaeG0S34VPq;A1A2ScS8S80S1dS33VTQ;A1MbA1VRQ;S22GbA1A3SbS8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma qchkb_sound : ltac2:(tb__ "0|f|
S13S35S35S35S31SaS1aA1M0S0S8S79R6R5R4R3R2R1A6S9A3S1S0SaSdS17S17A2M1A1M2S34R6A1SbG1A1M3A3S1S0G2S34R4A1G3A3S1S0S8S75S42S1eS33R6A1M4A1M5A2S9A3S1S0S8S39S18S1fG5A1S1dG4A1M6A3S9A3S1S0S8S39S18S1fS1eS33S43R3S40R5R6R2A5A1A1A1G6A3S9A3S1S0S17S2dR3PaM7A2S1cS3eS19G7A1S1bN8a0A1A3A3S1S0S17S2dR3PfM8A2S1cS3eS19G8A1S1bZ8a0A1A3A3S1S0S17S2dR3P18M9A2S19G9A1A3S1S0S17S2dR3P97MaA2S19GaA1A3S1S0S17S2dR3P98MbA2S19GbA1A3S1S0S17S2dR3P9bMcA2S19GcA1MdA3S1S0S17S2dR3P9cA2S1cS3eGdS1bS84A1A3A3S1S0S8S39S1aS78R7A1R2A3S9A3S1S0S8S39S1aS81S42A1R2A3S9A3S1S0S8S39S18S18S3aS18S23R1A1S1dS33R7A1A1A3Lf;SeS18S4fS4eR7A1A1S51S50A1A3A3S9A3S1S0G0S7eS33S40A1S33R5A1A2SbS1aA1A3S1S0G2S34R5A1G3A3S0S8S80S1dS33R4A1MeA1R2S22GeA1A3S9A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FRQ;FsQ;FTQ;FPq;FCd;FnW;").
Proof.
  intros nW Cd Pq TQ sQ RQ H. unfold qchkb in H. cbn [forallb] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 H].
  apply andb_prop in H as [H5 H]. apply andb_prop in H as [H6 H]. apply andb_prop in H as [H7 H]. apply andb_prop in H as [H8 H].
  apply andb_prop in H as [H9 H]. apply andb_prop in H as [H10 H]. apply andb_prop in H as [H11 H]. apply andb_prop in H as [H12 H].
  apply andb_prop in H as [H13 H]. apply andb_prop in H as [H14 H]. apply andb_prop in H as [H15 H]. apply andb_prop in H as [H16 H].
  apply andb_prop in H as [H17 H]. apply andb_prop in H as [H18 _].
  apply isnil_sound in H1, H2, H16, H17. apply sv_eqb_sound in H6, H7, H8, H9, H10, H11, H12.
  repeat split; assumption.
Qed.

Lemma rq_top : ltac2:(tb__ "0|1|
S13S61S20S1aS3cS58R4R3A2S88S4dQ40S21R4S59A2A2S8aS50A1A2Sc1S18S27R5A1S4fS4eR7A1A1A3S0S8S78R8R5A2S9A3S1S88S14S3cS3cS2bR7R6A2M0A3R5A2S8bR5S16S3cS3cG0A3A2A2S88S70S63R9A1A1R6A2F_;F_;F_;F_;F_;Fa;Fo;FrhoE;FA;FnW;").
Proof.
  intros nW A rhoE o a HTOP HDEP HCH Hok Ha. unfold rq_okb in Hok. apply Bool.orb_prop in Hok as [Hok|Hok].
  - unfold winpb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [lo| | | | | | | ]; try discriminate. destruct ohi as [hi| | | | | | | ]; try discriminate.
    apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2, H3. unfold free_depth in *.
    rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. unfold top_high in HTOP. lia.
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (same_rng_range rhoE o o' Hs) in Ha.
    assert (LNK : Forall (fun o => bv_unsigned (rw rhoE 10%positive) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs (Wcan nW))).
    { unfold unwind_objs. destruct (Wcan nW) as [|l W'] eqn:EW; [constructor|].
      unfold chain_pre in HCH. cbn [app] in HCH.
      pose proof (Forall_inv HCH) as C0. pose proof (Forall_inv (Forall_inv_tail HCH)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCH))) as C2. do 3 apply Forall_inv_tail in HCH.
      cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
      pose proof (urange (rw rhoE 10%positive)). rewrite Z.mod_small in C1 by lia.
      eapply Forall_impl; [|apply (chain_facts_bases rhoE (SVar 28) (l :: W') HCH); cbn [eval]; lia].
      intros o0 (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (L1 & L2 & L3).
    destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in L1, L2, L3. subst olo ohi. rewrite obj_range_mk in Ha by lia. cbn [fst snd] in Ha.
    unfold top_high in HTOP. unfold free_depth in HDEP. lia.
Qed.

Lemma qsize_freeQ : ltac2:(tb__ "0|1|
Sb5S61S3cS3cS9bR4R3A2S88Z0R2A2S1S4S0SaS62A1Sd6R6R5R4R3A4M0SbS62A1A3A1S88Sc3G0A1S89S89Sc3S66R5A1A1R3A2S86A2A2A2F_;F_;Fn;Fp;FA;Fq;").
Proof.
  intros q A p n QC Hn. unfold freeQ, kQuarantineBatchSize. destruct q; cbn zeta.
  - destruct QC as [HNE _]. split; [intros E; apply app_eq_nil in E as [_ E]; discriminate|].
    rewrite F0A_rebuild.qsize_app. rewrite (F0A_rebuild.qsize_removelast_last _ HNE). unfold qsize at 2. cbn [fold_right qb_size]. lia.
  - destruct QC as [HE _]. split; [discriminate|]. rewrite HE. unfold qsize. cbn [fold_right qb_size]. unfold kQuarantineBatchSize. lia.
  - split; [intros E; apply app_eq_nil in E as [_ E]; discriminate|].
    rewrite F0A_rebuild.qsize_app. unfold qsize at 2. cbn [fold_right qb_size]. unfold kQuarantineBatchSize. lia.
Qed.

Section DR.
Let nW : nat := 0%nat. Variable q : qvar.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S3cSbaVCST;R1A2S4SdbR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Variables (Cd TQ TQr : axst) (sQ : wsub) (RQ : list sobj).
Hypothesis HEQ : ltac2:(tb__ "0|1|
S0S12SaS1aA1M0A1S48VCd;S40VsQ;A3S11G0VRQ;A2A3").
Hypothesis HCK : ltac2:(tb__ "0|0|
S0S8S47VCd;S40VsQ;VRQ;ScS35S41ScS35SbeSbS35A1A3A3A5S9A3").
Hypothesis HTQ : ltac2:(tb__ "0|0|
S0S35VTQ;SadS43VsQ;S40S41VCd;VRQ;A5S1dS33VCd;A1A1A2A3").
Hypothesis HTQr : ltac2:(tb__ "0|0|
S0S35VTQr;SadS43VsQ;S40SbeVCd;VRQ;A5S1dS33VCd;A1A1A2A3").
Hypothesis QCHK : ltac2:(tb__ "0|0|
S0S8S79VnW;VCd;S41VTQ;VsQ;VRQ;A6S9A3").
Hypothesis QCHKr : ltac2:(tb__ "0|0|
S0S8S79VnW;VCd;SbeVTQr;VsQ;VRQ;A6S9A3").
Let PARTS := qchkb_sound nW Cd PostQ3 TQ sQ RQ QCHK.
Let XXC : ax_X Cd = [] := proj1 PARTS.
Let NXC : Pos.leb GW (ss_next (ax_S Cd)) = true := proj1 (proj2 (proj2 PARTS)).
Let FBX : forallb (sprop_below (ss_next (ax_S Cd))) (ss_facts (ax_S Cd)) = true := proj1 (proj2 (proj2 (proj2 PARTS))).
Let WG10 : wsub_get sQ 10 = SAlu ALU_ADD (SVar 10) (SLit (-2208)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))).
Let WG15 : wsub_get sQ 15 = SAlu ALU_ADD (SVar 15) (SLit 2208) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))).
Let WG24 : wsub_get sQ 24 = SVar 24 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))).
Let WG151 : wsub_get sQ 151 = SVar 151 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))).
Let WG152 : wsub_get sQ 152 = SVar 152 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))).
Let WG155 : wsub_get sQ 155 = SVar 155 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))).
Let WG156 : wsub_get sQ 156 = SAlu ALU_ADD (SVar 155) (SLit kSpaceSize) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))))).
Let RQOK : forallb (rq_okb nW) RQ = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).
Let RQWF : forallb (rng_below GW) RQ = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))))))).
Let FCH : forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S Cd))) (chain_pre W ++ F_depth free_depth) = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))))).

Variables (Xf2 XM2 XR2 : axst) (XEX2 : list axform) (sX2 : wsub) (l7 : list leafA).
Hypothesis NX7 : ltac2:(tb__ "0|1|
S1S0S8S28S33VTQ;A1M0A1S10A3S0S8S75S42S1eG0A1A2S9A3A2").
Hypothesis RUN7 : ltac2:(tb__ "0|0|
S0SaS37A1Sd0Sb3ScS3cSb2SbS3cA1A3VTQ;A3Vl7;A3").
Hypothesis L7 : ltac2:(tb__ "0|0|
S1S0S8Sb4Vl7;ScS3cSb2SbS3cA1A3A2S9A3S0S35ScfU0Vl7;A2VXf2;A3A2").

Variable l7r : list leafA.
Hypothesis NX7r : ltac2:(tb__ "0|1|
S1S0S8S28S33VTQr;A1M0A1S10A3S0S8S75S42S1eG0A1A2S9A3A2").
Hypothesis RUN7r : ltac2:(tb__ "0|0|
S0SaS37A1Sd0Sb3ScS3cSb2SbS3cA1A3VTQr;A3Vl7r;A3").
Hypothesis L7r : ltac2:(tb__ "0|0|
S1S0S8Sb4Vl7r;ScS3cSb2SbS3cA1A3A2S9A3S0S35ScfU0Vl7r;A2VXf2;A3A2").
Hypothesis AXE2 : ltac2:(tb__ "0|0|
S0S12S35A1Sc2VXf2;VXEX2;A2S11S35VXM2;A2A3").
Hypothesis WXR2 : ltac2:(tb__ "0|0|
S0S8S2cS33VXR2;A1A1S9A3").
Hypothesis DXR2 : ltac2:(tb__ "0|4|
S0S12SdSaSdS17S17A2M0A1M1SaS18A1M2A2M3A1Sd1S33VXM2;A1S33VXR2;A1A2S11G3SfG1G2ScG0SfS17S17S1bSb8A1S19P18A1A4SbG0A1A3SbS18A1A4A2A3").
Hypothesis NXR2 : ltac2:(tb__ "0|0|
S0S3dS1eS33VXR2;A1A1S1eS33VXM2;A1A1A3").
Hypothesis EQR2 : ltac2:(tb__ "0|0|
S0S35S36VXM2;S33VXR2;A1A2VXR2;A3").
Hypothesis ENT2 : ltac2:(tb__ "0|0|
S0S8S38VXR2;Sa2S52A1VsX2;A3S9A3").
Hypothesis SID2 : ltac2:(tb__ "0|0|
S0S8S32VsX2;S99A2S9A3").

Section SITE.
Variables (A A2 : AA) (Kc : KcA) (rho rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HRIG : ltac2:(tb__ "0|3|
S1S0S4aQ40M0A1M1S21Vrho1;P97A2S4cG0S73S63VA;A1M2A1A2A3S1S0G1S21Vrho1;P98A2S4cG0S71G2A1A2A3S0G1S21Vrho1;P9bA2S4cG0S72G2A1A2A3A2A2").

Definition JC : jpredA := ltac2:(tb__ "0|4|
S20SaS4aQ40A1M0A1SaS95A1S94S1Sd3S8dS8cZ2Z30A2Z1M1A2VA2;R4R3R1A5S1S1S0SaSdS3cS3cA2M2A1M3S64VA;A1SeG2Vl1;ScG2SfS3cS3cVp;Vn;A4Vl2;A3A3A3S1S0G3S64VA2;A1SeG2Vl1;Vl2;A3A3S1S0G3S6bVA2;A1S6bVA;A1A3S1S0S3cS6aVA2;A1S6aVA;A1A3S1S0S3cS69VA2;A1S69VA;A1A3S1S0S3cS68VA2;A1S89S68VA;A1G1A2A3S1S0S6eS63VA2;A1S63VA;A1A3S6fVA;VA2;A2A2A2A2A2A2A2A2S1S5aVCST;VXGL;VA;VA2;S26Vrho;A1S26R4A1A6S1VKc;R2R1A2S1S3dS76R1S42A2S0G0S21R6R2A2S21Vrho1;R2A2A3F_;Fi;S1S3dS0SaS4aQ8A1A1S25R5R1A2S25Vrho1;R1A2A3Fl;S1S5dVA2;R4A2S58VA2;R4A2A2A2A2A2A2A2A2Lmd;Ltr;Ltpx;Lr;").

Definition site_factsQ (rhoE : valuation) : Prop := ltac2:(tb__ "0|1|
S1S1S88S8aS8cZ2Z28A2A1S4dQ40S21VrhoE;S59A2A2M0A2S88G0S8aS50A1A2A2Sc1S18S27VrhoE;A1S4fVW;A1A3A2").
Lemma dr_facts : ltac2:(tb__ "0|0|
S20SaS4aQ40A1A1S96S8fVsegs;S9fVCd;R3R2R1A6Sa0R4A1F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj1 Hw) as (Hsm & _). unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (FIN : forall f, In f (chain_pre W ++ F_depth free_depth) -> holds rhoE f).
  { intros f Hf. pose proof (proj1 (forallb_forall _ _) FCH f Hf) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    exact (proj1 (Forall_forall _ _) HFa f Hg). }
  split.
  - assert (D1 : holds rhoE (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply FIN; apply in_or_app; right; left; reflexivity).
    assert (D2 : holds rhoE (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply FIN; apply in_or_app; right; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1, D2. unfold bv_lts in D1, D2. apply negb_true_iff in D1, D2. apply Z.ltb_ge in D1, D2.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. change (bv_signed (Z_to_bv 64 (- 2 ^ 40))) with (- 2 ^ 40) in D2. lia.
  - apply Forall_forall. intros f Hf. apply FIN. apply in_or_app. left. exact Hf.
Qed.

Lemma dr_RQ_top : ltac2:(tb__ "0|1|
S20Sa0R1A1S58VA2;R2A2S4aQ40M0A1S30R4VRQ;R1A3S88S70S63VA2;A1A1S4bG0R2A2A2F_;Fa;F_;F_;FrhoE;").
Proof.
  intros rhoE (Hdep & Hch) Htop a (o & Ho & Hoa).
  exact (rq_top nW A2 rhoE o (bv_unsigned a) Htop (proj2 Hdep) Hch (proj1 (forallb_forall _ _) RQOK o Ho) Hoa).
Qed.

Lemma AInvQ_parts : ltac2:(tb__ "0|5|
S61S20SaS4aQ40A1A1S94Sa5R4R3R2R1A4S1Sc9S63R5A1M0A1S1ScaR5A1S1SabR5A1S1S3cS1S88Z1R1A2S88R1Z1eA2A2S1S88Z0S74SaaR7R2A2A1M1A2S88G1S87A2A2F_;Fc;S1ScbR5A1S1SccSbbSc7G0A1M2SbdS8eS26R4A1A2M3A2M4R5A2S1ScdG4R5A2Sc8SbcG2G3A2R5A2A2A2A2A2A2A2A2F_;Fmd;Ftpx;Fr;FAx;").
Proof.
  intros Ax r tpx md (HG & _ & HF & HRest & _ & HI3 & _). cbn zeta in HRest, HF. destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  split; [exact HG|]. split; [exact HI3|]. split; [exact R5|]. split; [|exact (conj R1 (conj R3 (conj R4 HF)))].
  intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. lia.
Qed.

Lemma dr_entry : ltac2:(tb__ "0|0|
S20SaS4aQ40A1A1SaS95A1SacS94Sa0R5A1S9fR6R5R4R2A4Sa7S8eSa4VKc;A1VA2;S2fS2eR7VRQ;S9eR3R6R4A3A3VsQ;A2R6R5R3A7F_;F_;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md SF (HB & HP & HKEPT & HK & HRW & HRL & Htp & Htop).
  destruct HP as (_ & _ & _ & _ & _ & _ & EG & _).
  destruct (AInvB_Q _ A2 rhoE tp md HB) as (HAQ & HQM & QB1 & QB2).
  destruct (AInvQ_parts A2 rhoE tp md HAQ) as (HG & HI3 & HQP & HAU & _ & _ & HSR & _).
  pose proof SF as (Hdep & _). unfold free_depth in Hdep.
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A2)) as TG.
  assert (AV : forall z, z < topG (aa_geom A2) -> view segsA (rm (rho_sub (rho_absorb rhoE RQ (vms md tp ms0)) sQ)) z = view segsA (rm rhoE) z).
  { intros z Hz. apply view_agree. intros Hr. apply rm_absorb_out. intros Hin.
    pose proof (dr_RQ_top rhoE SF Htop _ Hin) as X. rewrite u64_lit in X by exact Hr. lia. }
  split.
  - split; [exact (AInvQ_frame_top A2 rhoE _ tp md HAQ AV)|]. split; [exact HK|]. split; [|split].
    + unfold tp_ok in *. cbn [rw rho_sub]. rewrite WG24. cbn [eval rho_absorb rw]. exact Htp.
    + unfold top_high in *. unfold V_DEPTH in *. cbn [rw rho_sub]. rewrite WG10, WG15, !eval_absorb.
      assert (Em : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2208)))) = bv_unsigned (rw rhoE 10%positive) - 2208).
      { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2208))) with (2 ^ 64 - 2208) by reflexivity.
        rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite Em. rewrite signed_add_lit by (cbn [eval]; lia). cbn [eval]. lia.
    + destruct HRIG as (E151 & E152 & E155). unfold rigidQ. rewrite EG. cbn [rw rho_sub]. rewrite WG151, WG152, WG155, WG156. cbn [eval rho_absorb rw].
      rewrite !HRW by (unfold GW; lia). rewrite E151, E152, E155.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply add_lit.
  - exact (q_mem_frame_top A2 HG HI3 HQP HAU _ HSR _ _ (fun z Hz => AV z Hz) HQM).
Qed.

Definition JX (A3 : AA) : jpredA := ltac2:(tb__ "0|1|
S20SaS4aQ40A1M0A1SaS95A1S94S1VAInv;VA3;R4R3R1A4S1VKc;R2R1A2S1S5aVCST;VXGL;VA;VA3;S26Vrho;A1S26R4A1A6S1S3dS76R1S42A2S0G0S21R6R2A2S21Vrho1;R2A2A3F_;Fi;S3dS0SaS4aQ8A1A1S25R5R1A2S25Vrho1;R1A2A3Fl;A2A2A2A2Lmd;Ltr;Ltpx;Lr;").

Section POSTQ.
Variables (Pq TQx : axst).
Hypothesis HTQx : ltac2:(tb__ "0|0|
S0S35VTQx;SadS43VsQ;S40VPq;VCd;VRQ;A5S1dS33VCd;A1A1A2A3").
Hypothesis QCHKx : ltac2:(tb__ "0|0|
S0S8S79VnW;VCd;VPq;VTQx;VsQ;VRQ;A6S9A3").
Let PARTSx := qchkb_sound nW Cd Pq TQx sQ RQ QCHKx.
Let XTQ : ax_X TQx = [] := proj1 (proj2 PARTSx).
Let FBT : forallb (sprop_below (ss_next (ax_S (import_postA sQ PreQ3 Pq Cd RQ)))) (ss_facts (ax_S Cd)) = true := proj1 (proj2 (proj2 (proj2 (proj2 PARTSx)))).
Let NEWO : new_objs (ax_S PreQ3) (ax_S Pq) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTSx))))))))))))))).
Let XPost : ax_X Pq = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTSx)))))))))))))))).
Let RQcov : coveredb (ss_facts (ax_S TQx)) RQ (ss_objs (ax_S TQx)) = true := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTSx)))))))))))))))).

Lemma dr_exit_ok : ltac2:(tb__ "0|2|
S20SaS4aQ40A1A1M0SaS95A1M1SacS94S20G0G1S94Sa0R9A1S9fRaR9R8R6A4Sa8S8eSa4VKc;A1VA2;S2fS2eRbVRQ;S9eR7RaR8A3A3VsQ;A2RaR6R5R4R3A9S49RcS9eR8RbR9A3VRQ;VsQ;S40VPq;VCd;R7A8F_;F_;F_;Fmd';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' md' SF (HB & _ & _ & _ & _ & _ & _ & Htop) HJL.
  destruct (AInvB_Q _ A2 rhoE tp md HB) as (HAQ & _). destruct (AInvQ_parts A2 rhoE tp md HAQ) as (HG & HI3 & HQP & HAU & _).
  destruct HJL as (A3 & _ & _ & _ & HRM & _).
  split; [split|split].
  - intros a Hin. apply HRM. intros HQ. pose proof HAQ as (_ & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & _ & R4 & _).
    pose proof (QRD_lt_top A2 HG HI3 HQP HAU _ R4 _ HQ) as X. pose proof (dr_RQ_top rhoE SF Htop a Hin) as Y. lia.
  - intros o' oR Ho' HoR. rewrite NEWO in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite XPost in Hr. destruct Hr.
  - intros r a j Hr. rewrite XXC in Hr. destruct Hr.
Qed.

Lemma dr_exit_core : ltac2:(tb__ "0|2|
S20SaS4aQ40A1A1M0SaS95A1M1SacS94S20G0G1S94Sa0R9A1Sa8S8eSa4VKc;A1VA2;A3S44S2fS2eRbVRQ;S9eR7RaR8A3A3VsQ;A2S20S92Vsegs;RcRbVCd;SfG1Sb6RaSb7R9R8A2A4A5S9fRdRcRbR9A4R4R3RdR9R8R7R6A6S20S96S7fR11S9eRdR10ReA3VRQ;VsQ;S33S40A1S33VCd;A1S33VPq;A1R2RcA9S8fVsegs;S46R8R7R11RdRcA5S43VsQ;S40VPq;VCd;VRQ;A5R3RcR2A6S6S61S61S6S20S20S1Sa9VA2;R2A2S8fVsegs;Sa1R2A1VTQx;R1RfR5A6A2Lrho5;A2LA3;A2F_;F_;Fw';Frho';F_;F_;F_;TrhoC;TJL;F_;Fmd';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' md' SF JL rhoC Hsm0 HJ0 _ rho' w' HLK [Hsm' HJ'].
  pose proof HJ0 as (HB & HP & HKEPT & HK & HRW & HRL & Htp & Htop).
  destruct (AInvB_Q _ A2 rhoE tp md HB) as (HAQ & _).
  subst JL.
  destruct (entails_frA_sound segs Cd PreQ3 sQ RQ rhoE tp tr0 ms0 md HEQ Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (A3 & HK3 & HQM3 & HQPOST & HRM & HVW & HRL3 & EtpL & HDEF).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S Cd))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. apply Pos.leb_le. exact NXC. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S Cd))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros f Hf.
    exact (proj1 (holds_agree_vals _ rhoE rho' f Hag' (proj1 (forallb_forall _ _) FBX f Hf)) (proj1 (Forall_forall _ _) Hfacts4 f Hf)). }
  assert (HT40 : SPA segs (J_ofPA (JLQ3 segsA (K0 Kc) A2) rhoC tp rhoL tpL) TQx rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite HTQx. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact FBT | intros _; exact HF4]. }

  assert (RNG : forall o, In o RQ -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S Cd))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (rho5 := rho_absorb rho' RQ (ms_with_mem ms2 (rm rhoE))).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' RQ a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' RQ a <-> in_ranges rhoE RQ a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (RTOP : forall a : word, in_ranges rhoE RQ a -> topG (aa_geom A2) <= bv_unsigned a) by exact (dr_RQ_top rhoE SF Htop).
  destruct (AInvQ_parts A2 rhoE tp md HAQ) as (HG2 & HI32 & HQP2 & HAU2 & _).

  assert (KEY : forall a : word, ~ QRD A2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' RQ a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (DEF5 : forall a : word, SHADOW_BAND_LO <= bv_unsigned a < SHADOW_BAND_HI -> rm rhoE a <> None -> rm rho5 a <> None).
  { intros a HBa Hd. rewrite RM5. destruct (in_ranges_dec rho' RQ a) as [Hi|Hn]; [exact Hd|].
    apply (HDEF a HBa). unfold rhoC. cbn [rm rho_sub]. rewrite (rm_absorb_out _ _ _ _ (fun Hi => Hn (proj2 (IRE a) Hi))). exact Hd. }

  pose proof (qpost_geom A2 A3 HQPOST) as EG3.
  pose proof HK3 as (HAQ3 & HKc3 & _).
  destruct (AInvQ_parts A3 rhoL tpL md2 HAQ3) as (HG3 & HI33 & HQP3 & HAU3 & _ & _ & HSR3 & _).
  assert (AV5 : forall z, z < topG (aa_geom A3) -> view segsA (rm rho5) z = view segsA (rm rhoL) z).
  { intros z Hz. apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' RQ (Z_to_bv 64 z)) as [Hi|]; [|reflexivity]. exfalso.
    pose proof (RTOP _ (proj1 (IRE _) Hi)) as X. rewrite u64_lit in X by exact Hr. rewrite EG3 in Hz. lia. }
  assert (HA5 : AInv A3 rho5 tpL md2).
  { destruct HQPOST as (_ & ET3 & _ & _ & EQG3).
    apply (AInvQ_back A3 rho5 tpL md2 (AInvQ_frame_top A3 rhoL rho5 tpL md2 HAQ3 AV5)).
    - exact (q_mem_frame_top A3 HG3 HI33 HQP3 HAU3 _ HSR3 _ _ (fun z Hz => AV5 z Hz) HQM3).
    - rewrite ET3. cbn. unfold kQuarantineCacheMax. lia.
    - exact EQG3. }
  exists A3, rho5. split; [exact HQPOST|].
  assert (HJX5 : JX A3 rho5 tpL tr2 md2).
  { split; [exact HA5|]. split; [exact HKc3|].
    split; [exact (mem_kept_drain CST XGL HCST HXGL HCSTQ A A2 A3 tp md rhoE (rm rho) (rm rho5) HAQ (proj1 HQPOST) KEY DEF5 HKEPT)|].
    split.
    - intros i Hi. unfold rho5. cbn [rw rho_absorb]. rewrite <- (proj1 Hag' i (NXlt i Hi)). exact (HRW i Hi).
    - intros l. unfold rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l). exact (HRL l). }
  pose proof (proj1 (proj1 HT40)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
  unfold rho5. apply (SPA_absorb_any segs (J_ofPA (JLQ3 segsA (K0 Kc) A2) rhoC tp rhoL tpL)); [exact XTQ | | exact HT40 | exact HJX5].
  intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT RQcov Ho Ha).
Qed.

End POSTQ.

Lemma JX_stable : ltac2:(tb__ "0|0|
S61S3dS77S42R1A2S93Vsegs;R2Sa1R3A1A3F_;Fk;FA3;").
Proof.
  intros A3 k Hk r r' tpx tr md md' Hag Hme (HA & HK & HM & HW & HL). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [|split; [|split; [|split]]].
  - unfold AInv, AInvA in HA |- *. rewrite Erm. exact (AInvA_mat segs A3 r tpx md md' HA Hme).
  - destruct Hme as ((mat' & ->) & _). rewrite <- (with_vm_backing_id md) in HK. exact (Kc_ok_mat Kc tr md _ _ _ _ HKc HK).
  - rewrite Erm. exact HM.
  - intros i Hi. rewrite <- (Hw i ltac:(lia)). exact (HW i Hi).
  - intros l. rewrite <- (Hl l). exact (HL l).
Qed.
Lemma JX_okf : ltac2:(tb__ "0|0|
S96OF_;S61S90Vsegs;R2S91VKc;A1A3S90Vsegs;R3Sa1R2A1A3F_;FA3;Fok;").
Proof. intros ok A3 H r tpx tr ms md msv' (_ & HK & _). exact (H r tpx tr ms md msv' HK). Qed.

Variable tp : list word.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S0S3cS4bQ40S21Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S0S3cS4bQ40S21Vrho;PdA2A2Vn;A3").
Hypothesis HAGW : ltac2:(tb__ "0|0|
S3dS76R1S99A2S0S4aQ40A1S21Vrho;R2A2S21Vrho1;R2A2A3F_;Fk;").
Hypothesis HAGL : ltac2:(tb__ "0|0|
S3dS0SaS4aQ8A1A1S25Vrho;R1A2S25Vrho1;R1A2A3Fl;").
Hypothesis HTP24 : ltac2:(tb__ "0|0|
S0S3cS4bQ40S21Vrho1;P18A2A2Sb8A3").
Hypothesis HPURE : ltac2:(tb__ "0|2|
S1S0SaSdS3cS3cA2M0A1M1S64VA;A1SeG0Vl1;ScG0SfS3cS3cVp;Vn;A4Vl2;A3A3A3S1S0G1S64VA2;A1SeG0Vl1;Vl2;A3A3S1S0G1S6bVA2;A1S6bVA;A1A3S1S0S3cS6aVA2;A1S6aVA;A1A3S1S0S3cS69VA2;A1S69VA;A1A3S1S0S3cS68VA2;A1S89S68VA;A1Z1A2A3S1S0S6eS63VA2;A1S63VA;A1A3S6fVA;VA2;A2A2A2A2A2A2A2A2").

Theorem dr_finish : ltac2:(tb__ "0|1|
S61S20SaS4aQ40A1A1S96Sa9VA2;R4A2S8fVsegs;Sa1R5A1VXf2;R4R3R2A6S45Vsegs;S99Vrho;Vtp;ScSdS35S44A2M0SfS35S44Sa2S52A1S53VAInv;VCST;VXGL;VA;VKc;A5A4SbG0A1A3R3A6F_;F_;Fw;FtpL;FrhoX;FA3;").
Proof.
  intros A3 rhoX tpL w HQPOST H. destruct w as [tr [ms md]].
  pose proof (proj2 H) as (HA3 & HK & HM & HW & HL). cbn [w_tr w_cfg cfg_model fst snd] in HA3, HK.
  pose proof (SPA_axforms segs (JX A3) XEX2 rhoX Xf2 XM2 tpL _ AXE2 H) as Ha.
  assert (Hc : SPA segs (JX A3) XR2 rhoX tpL (tr, mkCfg ms md)).
  { rewrite <- EQR2. eapply SPA_restate; [exact WXR2 | exact DXR2 | exact NXR2 | | constructor | exact Ha].
    constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    rewrite (HW 24%positive) by (unfold GW; clear; lia). symmetry. exact HTP24. }
  pose proof (smatchA_entails segs _ _ _ rhoX tpL _ ENT2 (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rhoX sX2) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoX k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ SID2 Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rhoX) by exact (rm_rho_sub' rhoX sX2).
  exists (L_free_tol AE_A), (JL_free AInv CST XGL A Kc), rho4, tpL.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { split.
    - intros k Hk. rewrite (Hlow k Hk), (HW k) by (unfold NF, GW in *; clear -Hk; lia). exact (HAGW k Hk).
    - intros l. unfold rho4. cbn [rl rho_sub]. rewrite (HL l). exact (HAGL l). }
  cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_free. exists A3, l1, l2.
  destruct HPURE as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). destruct HQPOST as (ESB & _ & _ & HFR & _).
  assert (E3 : aa_live A3 = aa_live A2 /\ aa_frames A3 = aa_frames A2 /\ aa_V A3 = aa_V A2 /\ aa_Km A3 = aa_Km A2 /\ aa_Kf A3 = aa_Kf A2 /\ aa_geom A3 = aa_geom A2).
  { unfold same_but_qcs in ESB. rewrite ESB. unfold aa_frames. cbn [aa_live aa_fs_busy aa_V aa_Km aa_Kf aa_geom]. repeat split; reflexivity. }
  destruct E3 as (F1 & F2 & F3 & F4 & F5 & F6).
  split; [unfold AInv, AInvA in HA3 |- *; rewrite Erm4; exact HA3|].
  split; [rewrite Hp12, Hn13; exact P1|].
  split; [rewrite F1; exact P2|]. split; [rewrite F2; exact P3|]. split; [rewrite F3; exact P4|]. split; [rewrite F4; exact P5|].
  split; [rewrite F5; exact P6|]. split; [rewrite F6; exact P7|].
  split; [rewrite Erm4; exact HM|]. split; [exact HK|].
  intros c Hc0 NE Hfr. exact (HFR c (P8 c Hc0 NE Hfr)).
Qed.

Theorem drain_call : ltac2:(tb__ "0|1|
S96OF_;S90Vsegs;R1S91VKc;A1A3S7bR2VKc;A2S4S0SaS62A1S66VA2;A1SbS62A1A3A1S0S8S65VA2;A1S9A3Sa6VA2;A1S88S67VA2;A1Sa3A2S20SaS4aQ40A1A1S98Vsegs;R9S8fVsegs;S9fVCd;R2R1A5S45Vsegs;S99Vrho;Vtp;ScSdS35S44A2M0SfS35S44Sa2S52A1S53VAInv;VCST;VXGL;VA;VKc;A5A4SbG0A1A3A5A4FtpE;FrhoE;F_;F_;F_;F_;F_;F_;Fok;").
Proof.
  intros ok Hokl HDS HT2 HCI2 HQB2 HBD2 rhoE tpE k HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dr_facts rhoE tpE _ Hw) as SF.
  apply (call_soundPA segs ok JC (JQ3 segsA (K0 Kc) A2) Cd PreQ3 sQ RQ (PostsQ3 (K0 Kc) A2)
           (LQPA segs NF rho tp [(L_free_tol AE_A, JL_free AInv CST XGL A Kc)]) rhoE tpE HEQ).
  - change (map fst (PostsQ3 (K0 Kc) A2)) with [PostQ3; PostQ3r]. exact HCK.
  - intros rhoP tp1. exact (HDS A2 rhoP tp1 HT2 HCI2 HQB2 HBD2).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (dr_entry rhoE tpE tr0 ms0 md1 SF HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[EL|[]]]; pose proof (f_equal fst EL) as EL1; pose proof (f_equal snd EL) as EL2; cbn [fst snd] in EL1, EL2; subst L JL; clear EL.
    + split; [exact (dr_exit_ok PostQ3 TQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK n' Hg' w' Hw'.
      destruct (dr_exit_core PostQ3 TQ HTQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_cont1 FUELF [RETF] TQ l7 (ss_next (ax_S TQ)) Xf2 (proj1 NX7) eq_refl RUN7 (proj2 L7) RETF (JX A3) ok rho5 tpL
                (LQPA segs NF rho tp [(L_free_tol AE_A, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7)) (JX_okf ok A3 Hokl) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7))) _ n' Hg' w' HC5).
      intros rhoX _. eapply triple_conseq; [intros w0 Hw0; exact Hw0 | | apply triple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
    + split; [exact (dr_exit_ok PostQ3r TQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK n' Hg' w' Hw'.
      destruct (dr_exit_core PostQ3r TQr HTQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_cont1 FUELF [RETF] TQr l7r (ss_next (ax_S TQr)) Xf2 (proj1 NX7r) eq_refl RUN7r (proj2 L7r) RETF (JX A3) ok rho5 tpL
                (LQPA segs NF rho tp [(L_free_tol AE_A, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7r)) (JX_okf ok A3 Hokl) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7r))) _ n' Hg' w' HC5).
      intros rhoX _. eapply triple_conseq; [intros w0 Hw0; exact Hw0 | | apply triple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
  - exact HgQ.
  - exact Hw.
Qed.

Theorem drain_callE : ltac2:(tb__ "0|1|
S7cVKc;A1S4S0SaS62A1S66VA2;A1SbS62A1A3A1S0S8S65VA2;A1S9A3Sa6VA2;A1S88S67VA2;A1Sa3A2S20SaS4aQ40A1A1S97Vsegs;S8fVsegs;S9fVCd;R2R1A5S45Vsegs;S99Vrho;Vtp;ScSdS35S44A2M0SfS35S44Sa2S52A1S53VAInv;VCST;VXGL;VA;VKc;A5A4SbG0A1A3A5A3FtpE;FrhoE;F_;F_;F_;F_;F_;").
Proof.
  intros HDS HT2 HCI2 HQB2 HBD2 rhoE tpE w Hw. destruct w as [tr [ms md]].
  pose proof (dr_facts rhoE tpE _ Hw) as SF.
  apply (call_completePA segs JC (JQ3 segsA (K0 Kc) A2) Cd PreQ3 sQ RQ (PostsQ3 (K0 Kc) A2)
           (LQPA segs NF rho tp [(L_free_tol AE_A, JL_free AInv CST XGL A Kc)]) rhoE tpE HEQ).
  - change (map fst (PostsQ3 (K0 Kc) A2)) with [PostQ3; PostQ3r]. exact HCK.
  - intros rhoP tp1. exact (HDS A2 rhoP tp1 HT2 HCI2 HQB2 HBD2).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (dr_entry rhoE tpE tr0 ms0 md1 SF HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[EL|[]]]; pose proof (f_equal fst EL) as EL1; pose proof (f_equal snd EL) as EL2; cbn [fst snd] in EL1, EL2; subst L JL; clear EL.
    + split; [exact (dr_exit_ok PostQ3 TQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK w' Hw'.
      destruct (dr_exit_core PostQ3 TQ HTQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_econt1 FUELF [RETF] TQ l7 (ss_next (ax_S TQ)) Xf2 (proj1 NX7) eq_refl RUN7 (proj2 L7) RETF (JX A3) rho5 tpL
                (LQPA segs NF rho tp [(L_free_tol AE_A, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7)) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7))) _ w' HC5).
      intros rhoX _. eapply etriple_conseq; [intros w0 Hw0; exact Hw0 | | apply etriple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
    + split; [exact (dr_exit_ok PostQ3r TQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK w' Hw'.
      destruct (dr_exit_core PostQ3r TQr HTQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_econt1 FUELF [RETF] TQr l7r (ss_next (ax_S TQr)) Xf2 (proj1 NX7r) eq_refl RUN7r (proj2 L7r) RETF (JX A3) rho5 tpL
                (LQPA segs NF rho tp [(L_free_tol AE_A, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7r)) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7r))) _ w' HC5).
      intros rhoX _. eapply etriple_conseq; [intros w0 Hw0; exact Hw0 | | apply etriple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
  - exact Hw.
Qed.
End SITE.

Hypothesis HCSTF : ltac2:(tb__ "0|0|
S3cSbaVCST;R1A2S5SbaSd4R2A2S1S88Sc5R2A2S8bR2Sc6A2A2A2S7F_;F_;Fa;").

Variables (Edr XMd XKd : axst) (KEPTd RESTd : list sobj) (XEXd : list axform).
Hypothesis AXEd : ltac2:(tb__ "0|0|
S0S12S35A1Sc2VEdr;VXEXd;A2S11S35VXMd;A2A3").
Hypothesis OBJSd : ltac2:(tb__ "0|0|
S0SaS1aA1S22S33VXMd;A1A1SeS1aVKEPTd;VRESTd;A3A3").
Hypothesis EQKd : ltac2:(tb__ "0|0|
S0S35S36VXMd;Sd2S33VXMd;A1VKEPTd;A2A2VXKd;A3").
Hypothesis RCLSd : ltac2:(tb__ "0|0|
S0S8Sd8Vq;VRESTd;A2S9A3").
Hypothesis RCIVd : rcivb RESTd = true.
Hypothesis RCELLd : ltac2:(tb__ "0|0|
S0S8Sd7Vq;VRESTd;A2S9A3").
Hypothesis RWRd : rwrb RESTd = true.
Hypothesis RSHPd : ltac2:(tb__ "0|0|
S0S8Sd9Vq;VRESTd;A2S9A3").
Hypothesis ECd : ltac2:(tb__ "0|0|
S0S35VCd;SadVXKd;SeS18S1dS33VXKd;A1A1ScS18S7aSbS18A1A3A3A2A3").
Hypothesis FBCd : ltac2:(tb__ "0|1|
S0S8S39S18S1fS1eS33VXKd;A1M0A1A1SeS18S1dG0A1ScS18S7aSbS18A1A3A3A3S9A3").

Lemma dr_release : ltac2:(tb__ "0|6|
S61S54S20SaS4aQ40M0A1A1M1S3cS3cS3cS9dS3cOF_;S61S20S20G1SaS95A1M2SacS94SaSdS3cS3cA2M3A1M4G4S55R11A1S0S3cS4bG0S21R11PcA2A2RfA3S0S3cS4bG0S21R12PdA2A2RfA3S3bG3SfS3cS3cR11R10A4S64R15A1M5A3Sb9R12R11A2S0S8S6dR17A1S9A3S9bVq;R18A2Sb1R17S9aR19R17R15R14R13R12A6A2S0S3cS9cR13A1S85A3S3cS5S56VCST;R1cR1A3S57VCST;VXGL;R1cR1A4A2R15R2A1F_;Fa;SafR1cR13A2Sc0R15S9aR1dR1bR19R18R17R16A6R13A3S0G4G5SeG3ReScG3SfS3cS3cR1aR19A4RdA3A3A3S8fVsegs;Sb0VnW;Vst;S10R16R1eR15A6VEdr;R14R13SfG2Sb6R12Sb7R11R10A2A4A6Sd5Vq;R17R10RfR1cR1bA6S61S9aR21R1fR1dR1cR1bR1aA6S20S1S8fVsegs;SdaR22R2R21R20R1R12R11R1eR1dA9VCd;S2eR17VRESTd;S9eR13R16R14A3A3R16SfG2Sb6R15Sb7R14R13A2A4A6S1S4S0SaS62A1S66R2A1SbS62A1A3A1S1Sa6R2A1S1S0S8S65R2A1S65R22A1A3S0S3cS4bG0S21R1P18A2A2Sb8A3A2A2A2A2Trho1;TA2;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fmd;Fms;Ftr;FtpE;FrhoE;Frho1';FA';Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md l1 l2 HKc Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP HDO HLK ELV Hw A2 rho1. subst A2 rho1.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ. pose proof HJ as (HA' & _ & HL' & _).
  pose proof HDO as (EG & EC & ECI & ESEC & EPC & EL & EQT & EQG & EII & EFB & EFH & EV & EKM & EKF).

  assert (QC' : qcond q A').
  { clear -QC EC EQT ECI. unfold qcond, lastq, cache24 in *. rewrite EQT, ECI, EC. exact QC. }
  pose proof HA' as (HG' & _ & _ & HRest' & _). destruct HRest' as (HLS' & _ & _ & _ & HQR' & _). destruct HQR' as (_ & _ & _ & _ & _ & _ & _ & QT8 & QG9 & _).
  assert (Hn0 : 1 <= n /\ n < 2 ^ 47).
  { rewrite <- EL in HL. destruct (HLS' p n HL) as (N1 & N2 & N3 & _). pose proof (topG_range (aa_geom A')) as TG. unfold IMG_HI in N2. lia. }
  destruct (qsize_freeQ q A' p n QC' ltac:(lia)) as [FNE FSZ].
  assert (HQB : qsize (freeQ q A' p n) <= 2 ^ 48 - 1) by (unfold kQuarantineCacheMax, kQuarantineBatchSize in *; lia).
  destruct (f0_released CST XGL HCST HXGL HCSTF q Edr XMd XKd XKd KEPTd RESTd XEXd AXEd OBJSd EQKd eq_refl RCLSd RCIVd RCELLd RWRd RSHPd
              A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md Hp12 Hn13 HL HHI Hii QC HR HJMIN HDO HLK HKEEP Hw (2 ^ 48 - 1) l1 l2 ELV HQB)
    as (Hb & HRB & HRW & HRL & Htp & Htop).
  unfold rebuilt_stmt in HRB. destruct HRB as (HB2 & _ & P1 & P2 & P3 & P4 & P5 & P6 & P7 & HKEPT & HK & P8).
  set (rho3 := rho_absorb rhoE RESTd (vms md tpE ms)) in *.
  assert (HJC : JC A (freeA q A' l1 l2 p n) Kc rho (rhoF_of A rho p n t jv) l1 l2 p n rho3 tpE tr md).
  { split; [exact HB2|]. split; [exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 P8)))))))|].
    split; [exact HKEPT|]. split; [exact HK|]. split; [exact HRW|]. split; [exact HRL|].
    split; [unfold tp_ok in *; exact Htp | unfold top_high in *; exact Htop]. }
  assert (E24 : bv_unsigned (rw (rhoF_of A rho p n t jv) 24%positive) = TP_A).
  { rewrite <- (HRW 24%positive) by (unfold GW; lia). unfold rho3. cbn [rho_absorb rw]. unfold tp_ok in Htp. rewrite Htp.
    destruct (geom_old _ HG') as (_ & _ & _ & G4 & _). rewrite G4. reflexivity. }
  split; [|split; [exact FNE | split; [split; [cbn [aa_q_thread freeA]; lia | exact QG9] | split; [exact ECI | exact E24]]]].

  rewrite ECd. apply (SPA_refacts segs); [exact (conj (proj1 Hb) HJC) | exact FBCd |].
  intros HF. apply Forall_app. split; [exact HF|]. constructor; [|constructor].
  unfold F_cne. cbn [holds eval]. intros E. unfold branch_taken, bv_eqb in E. apply Z.eqb_eq in E.
  assert (E151 : rw rho3 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by (rewrite HRW by (unfold GW; lia); reflexivity).
  rewrite E151, add_lit in E. pose proof (geom_numsS _ HG') as (_ & _ & _ & T1 & T2 & _). pose proof (topG_range (aa_geom A')) as TG.
  pose proof (geom_bands _ HG') as (_ & _ & _ & _ & TI & _). rewrite EG in T1, T2, TI, TG. unfold IMG_LO, IMG_HI in TI.
  rewrite !u64_lit in E by (unfold QG; lia). unfold QG in E. lia.
Qed.

Theorem f0_drain : ltac2:(tb__ "0|3|
S96OF_;S61S54S20SaS4aQ40M0A1A1M1S3cS3cS3cS9dS3cOF_;S55R8A1S90Vsegs;RbS91R9A1A3S7bRcRaA2S6cRcA1S0S3cS4bG0S21RbPcA2A2R9A3S0S3cS4bG0S21RcPdA2A2R9A3S3bSdS3cS3cA2SfS3cS3cRbRaA4S64RfA1A3Sb9RcRbA2S0S8S6dR11A1S9A3S9bVq;R12A2Sb1R11S9aR13R11RfReRdRcA6A2S0S3cS9cRdA1S85A3S3cS5S56VCST;R16R1A3S57VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S61S20S20G1SafR1aR4A2Sc0R13S9aR1bR19R17R16R15R14A6R4A3S98Vsegs;R1dS8fVsegs;Sb0VnW;Vst;S10R6R1bR5A6VEdr;R4R3A5S45Vsegs;S99R1aR19ScSdS35S44A2M2SfS35S44Sa2S52A1S53VAInv;VCST;VXGL;R1cR1bA5A4SbG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv keep HKc Hokl HDS HBud Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP A' rho1' rhoE tpE HDO HLK k HgQ w Hw.
  destruct w as [tr [ms md]].
  assert (HL' : In (p, n) (aa_live A')) by (destruct HDO as (_ & _ & _ & _ & _ & EL & _); rewrite EL; exact HL).
  destruct (in_split _ _ HL') as (l1 & l2 & ELV).
  destruct (dr_release A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md l1 l2 HKc Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP HDO HLK ELV Hw) as (HC & HT2 & HQB2 & ECI2 & E24).
  pose proof (proj2 HC) as (HB2 & HPURE & _).

  assert (HCI2 : aa_cache_inited (freeA q A' l1 l2 p n) = true).
  { destruct HB2 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & I9). apply I9. intros E. apply app_eq_nil in E as [E _]. exact (HT2 E). }
  destruct (rg_agree _ _ HR) as [HAGW HAGL].
  exact (drain_call A (freeA q A' l1 l2 p n) Kc rho (rhoF_of A rho p n t jv) l1 l2 p n HKc (conj eq_refl (conj eq_refl eq_refl)) tp Hp12 Hn13 HAGW HAGL E24 HPURE
           ok Hokl HDS HT2 HCI2 HQB2 (budget_depot A A' HBud HDO) _ tpE k HgQ _ HC).
Qed.
Theorem ef0_drain : ltac2:(tb__ "0|3|
S61S54S20SaS4aQ40M0A1A1M1S3cS3cS3cS9dS3cOF_;S55R8A1S7cR9A1S6cRbA1S0S3cS4bG0S21RaPcA2A2R8A3S0S3cS4bG0S21RbPdA2A2R8A3S3bSdS3cS3cA2SfS3cS3cRaR9A4S64ReA1A3Sb9RbRaA2S0S8S6dR10A1S9A3S9bVq;R11A2Sb1R10S9aR12R10ReRdRcRbA6A2S0S3cS9cRcA1S85A3S3cS5S56VCST;R15R1A3S57VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S61S20S20G1SafR19R4A2Sc0R12S9aR1aR18R16R15R14R13A6R4A3S97Vsegs;S8fVsegs;Sb0VnW;Vst;S10R6R1aR5A6VEdr;R4R3A5S45Vsegs;S99R19R18ScSdS35S44A2M2SfS35S44Sa2S52A1S53VAInv;VCST;VXGL;R1bR1aA5A4SbG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv keep HKc HDS HBud Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP A' rho1' rhoE tpE HDO HLK w Hw.
  destruct w as [tr [ms md]].
  assert (HL' : In (p, n) (aa_live A')) by (destruct HDO as (_ & _ & _ & _ & _ & EL & _); rewrite EL; exact HL).
  destruct (in_split _ _ HL') as (l1 & l2 & ELV).
  destruct (dr_release A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md l1 l2 HKc Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP HDO HLK ELV Hw) as (HC & HT2 & HQB2 & ECI2 & E24).
  pose proof (proj2 HC) as (HB2 & HPURE & _).

  assert (HCI2 : aa_cache_inited (freeA q A' l1 l2 p n) = true).
  { destruct HB2 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & I9). apply I9. intros E. apply app_eq_nil in E as [E _]. exact (HT2 E). }
  destruct (rg_agree _ _ HR) as [HAGW HAGL].
  exact (drain_callE A (freeA q A' l1 l2 p n) Kc rho (rhoF_of A rho p n t jv) l1 l2 p n HKc (conj eq_refl (conj eq_refl eq_refl)) tp Hp12 Hn13 HAGW HAGL E24 HPURE
           HDS HT2 HCI2 HQB2 (budget_depot A A' HBud HDO) _ tpE _ HC).
Qed.
End DR.
End F0T_drain.

