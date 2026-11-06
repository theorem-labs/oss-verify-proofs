(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall RefillBits je jm.

(* [comment removed for export] *)
Module DepotCallS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "pow"; "ltb"; "mul"; "opp"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "rw"; "SVar"; "SLit"; "sprop"; "ss_next"; "sstate"; "ss_facts"; "sv_eqb"; "ob_base"; "ob_hi"; "ob_lo"; "cell"; "obj_range"; "ss_objs"; "soff"; "holds"; "sprop_below"; "SAlu"; "SPUle"; "mkObj"; "rl"; "rm"; "DZero"; "SExt"; "c_off"; "eval"; "mkSS"; "ob_cells"; "ob_dflt"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "list"; "cons"; "pair"; "true"; "false"; "nil"; "prod"; "S"; "option"; "andb"; "fst"; "snd"; "orb"; "Some"; "app"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_depot"; "aa_geom"; "DG"; "ag_pab"; "ageom"; "aa_Km"; "ag_ctx"; "ag_thread"; "budget_ok_alloc"; "topG"; "aa_Kf"; "aa_V"; "aa_live"; "depot_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "WI"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "coveredbL"; "hi_lebL"; "lo_gebL"; "T5d"; "call_cellS"; "cov_exact"; "cov_itv"; "havS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"; "nocells"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "lt"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "V_DEPTH"; "malloc_depth"; "unwind_objs"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "isSome"; "rstS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS.DCS"; "site_factsS"; "AXK"; "dlink"; "zoneS"; "MAPO"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "JLD"; "DFP"; "JD"; "MAP1"; "MAP1N"; "STORE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP"; "KDP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "firstn";
"skipn"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "import_okPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "omrg"; "osplit"; "lit63"; "oreb"; "F_call"; "rt_okD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sitv"; "set_objs"; "snorm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "bumpK"; "with_depot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "bumpV"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "LIVE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU"; "DPRET"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl"; "sobjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ik.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition WI : nat := 2.
Definition X5f (X : axst) : axst := ax_add_facts F_call X.
Definition X5r (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|1|
S98S6eVX;A1S39S3eS37S10A2M0S3aS37S10UbS15Vsz;A1A4S3dG0A1A3S3dS16A1A3").
Definition X5a (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc9S62VX;Vsz;A2S61S15Nee0A1A3").
Definition X5b (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc9S6bVX;Vsz;A2S3fS61A1S15N8e0A1A3").
Definition X5c (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc9S6cVX;Vsz;A2S3fS3fS61A1A1S15N840A1A3").
Definition X5s (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc9S6dVX;Vsz;A2S3fS3fS3fS61A1A1A1S15N48A1A3").

Definition T50 (T X : axst) : axst := ltac2:(tb__ "0|0|
Se1VT;S19S49VX;A1A1A2").
Definition T5a (T X : axst) : axst := ltac2:(tb__ "0|0|
ScbS64VT;VX;A2U0A2").
Definition T5b (T X : axst) : axst := ltac2:(tb__ "0|0|
ScbS65VT;VX;A2U1A2").
Definition permS (n : nat) : list nat := ltac2:(tb__ "0|1|
S46S37S39S37U9S39S37UaS39S37UbS39S37U0S39S37UcS39S37U1S39S37UdS39S37U2S39S37U3S39S37U4S39S37U5S39S37U6S39S37U7S39S37U8S3dS37A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb6UeM0SdcVn;G0A2A2A3").
Definition T5c (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|2|
S4cS66VT;VX;A2M0Sd4S49G0A1M1Se0S20G1A1S63Vn;A1A2A2A2").
Definition T5m1 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S67Vn;VT;VX;A3S61A2").
Definition T5m2 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S68Vn;VT;VX;A3S61A2").
Definition T5m3 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S69Vn;VT;VX;A3S61A2").
Definition T5d (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S6aVn;VT;VX;A3S61A2").

Definition havS (n : positive) : list (nat * sv) := ltac2:(tb__ "0|1|
S39S3eS37S10A2M0S3aS37S10UaS14Vn;A1A4S39G0S3aS37S10U1S15Se4A1A4S39G0S3aS37S10U5S14S7aVn;P1A2A1A4S39G0S3aS37S10U6S14S7aVn;P2A2A1A4S39G0S3aS37S10U7S14S7aVn;P3A2A1A4S39G0S3aS37S10UbS14S7aVn;P4A2A1A4S39G0S3aS37S10UcS14S7aVn;P5A2A1A4S39G0S3aS37S10UdS14S7aVn;P6A2A1A4S39G0S3aS37S10UeS14S7aVn;P7A2A1A4S39G0S3aS37S10UfS14S7aVn;P8A2A1A4S39G0S3aS37S10U10S14S7aVn;P9A2A1A4S39G0S3aS37S10U11S14S7aVn;PaA2A1A4S39G0S3aS37S10U1cS14S7aVn;PbA2A1A4S39G0S3aS37S10U1dS14S7aVn;PcA2A1A4S39G0S3aS37S10U1eS14S7aVn;PdA2A1A4S39G0S3aS37S10U1fS14S7aVn;PeA2A1A4S3dG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition call_cellS (c : cell) : bool := ltac2:(tb__ "0|4|
S10S36Lx;S2bVc;A1S0S41S6Se3Sd5R1A1M0A2S48S41S6N840G0A2S8G0N48A2A2A1A2Lz;S1S3bLi;Sb9S10S10S3bLb;La;M1Lop;M2G2SbaG1Lop;M3G3S36S2S10S3bLa;Lw;Lsgn;S1S10S0S3bLk;Li;Ll;X10x8").
Definition C5S (X : axst) : axst := ltac2:(tb__ "0|3|
S49VX;A1S18S40S12A1S4aLx;S95S12S20R1A1S61A3S12S4cVX;S2dZ7ec58SddS33R2A1S76S17R2A1M0A1A2S31R2A1S30R2A1S34R2A1S46S12Sb7S12S61S20R2A1M1A3S39S12S26S1bR1A1S1dR1A1S1cR1A1SedS1eS38S1eA1SefS1eA1S1eSecS73R1A1M2A1Lc;S1eSeeG2A1Lx;S2eR1A1A6S2fR1A1A5Sb8S12S3fS61A1G1A3A3A3S19R2A1S7aG0PfA2S32R2A1A9A2Lo;VX;X40x2TS0;").

Definition lo_gebL (facts : list sprop) (l l' : sv) : bool := ltac2:(tb__ "0|5|
S36S36L_;M0S1aVl;Vl';A2S3bS10S36Ll;Vl;S0G0ScaR1A1S40S3eS0S0A2M1A1S36Lx;Sd3Vfacts;Vl';A2G1G1S36Lp;R1S0S0S6R1R4A2Lh';Lz;X3ex1Lp;S3cX40x2S3cX36x2La;S1S3cLi;Sb9S10S10S3cLb;La;M2Lop;M3G3SbaG2Lop;M4G4S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll0;X10x8X36x2").
Definition hi_lebL (facts : list sprop) (h h' : sv) : bool := ltac2:(tb__ "0|5|
S36S36L_;M0S1aVh;Vh';A2S3bS10S36Lh;Vh;S0G0ScaR1A1S40S3eS0S0A2M1A1S36Lx;Sd3Vfacts;Vh';A2G1G1S36Lp;R1S0S0S6R4R2A2Lz;Ll';X3ex1Lp;S3cX40x2S3cX36x2La;S1S3cLi;Sb9S10S10S3cLb;La;M2Lop;M3G3SbaG2Lop;M4G4S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll;X10x8X36x2").
Lemma lo_gebL_sound : ltac2:(tb__ "0|0|
S11S38S16A1S10S10Sb5S16S22R4A1R3A3ScS36S71R4R3R2A3S3bA3S3S21R6R3A2S21R6R4A2A2F_;F_;Fl';Fl;Ffacts;Frho;").
Proof.
  intros rho facts l l' HF H. apply (lo_geb_sound rho facts l l' HF). unfold lo_gebL in H. unfold lo_geb.
  destruct (sv_eqb l l'); [reflexivity|]. cbn [orb]. destruct l; try discriminate H. destruct (lit63 z); [exact H | discriminate H].
Qed.
Lemma hi_lebL_sound : ltac2:(tb__ "0|0|
S11S38S16A1S10S10Sb5S16S22R4A1R3A3ScS36S70R4R3R2A3S3bA3S3S21R6R4A2S21R6R3A2A2F_;F_;Fh';Fh;Ffacts;Frho;").
Proof.
  intros rho facts h h' HF H. apply (hi_leb_sound rho facts h h' HF). unfold hi_lebL in H. unfold hi_leb.
  destruct (sv_eqb h h'); [reflexivity|]. cbn [orb]. destruct h; try discriminate H. destruct (lit63 z); [exact H | discriminate H].
Qed.
Definition cov_exact (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S36S36L_;M0S1aS1bVo;A1S1bVo';A1A2G0S1aS1dVo;A1S1dVo';A1A2S1aS1cVo;A1S1cVo';A1A2S3cX36x2S3cX36x2").
Definition cov_itv (facts : list sprop) (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S36S36L_;M0S1aS1bVo;A1S1bVo';A1A2G0S71Vfacts;S1dVo;A1S1dVo';A1A3S70Vfacts;S1cVo;A1S1cVo';A1A3S3cX36x2S3cX36x2").
Definition coveredbL (facts : list sprop) (R objs : list sobj) : bool := ltac2:(tb__ "0|0|
S92S12S12S36S36L_;S93S12S74R1A1Vobjs;A3S3bS93S12S75Vfacts;R1A2Vobjs;A3X36x2Lo;VR;A3").
Lemma coveredbL_sound : ltac2:(tb__ "0|6|
S38S16A1S38S12A1M0G0S11S12S4fQ40M1A1Sb5S16S22R3A1R6A3ScS36S6fR7R6R5A3S3bA3S91S12R4R7A3SbS3S42S0S0S1fR6R5A2M2A3S4eG1R4A2M3A2S4G3S43S0S0G2A3A2A2SeS12S12SbS91S12R1R9A3SbS3S42S0S0S1fR8R1A2M4A3S4eG1R6A2M5A2S4G5S43S0S0G4A3A2A2A2Lo';A2F_;F_;F_;F_;Fa;Fo;Frho;Fobjs;FR;Ffacts;").
Proof.
  intros facts R objs rho o a HF H Ho Ha. pose proof (proj1 (forallb_forall _ _) H o Ho) as X. cbn beta in X.
  destruct (existsb (cov_exact o) objs) eqn:EX.
  - apply existsb_exists in EX as (o' & Ho' & E). unfold cov_exact in E.
    destruct (sv_eqb (ob_base o) (ob_base o')) eqn:Eb; [|discriminate E]. destruct (sv_eqb (ob_lo o) (ob_lo o')) eqn:El; [|discriminate E].
    apply sv_eqb_sound in Eb. apply sv_eqb_sound in El. apply sv_eqb_sound in E. exists o'. split; [exact Ho'|].
    unfold obj_range, obj_lo_of, obj_hi_of in Ha |- *. cbn [fst snd] in Ha |- *. rewrite <- Eb, <- El, <- E. exact Ha.
  - apply existsb_exists in X as (o' & Ho' & E). unfold cov_itv in E.
    destruct (sv_eqb (ob_base o) (ob_base o')) eqn:Eb; [|discriminate E]. destruct (lo_gebL facts (ob_lo o) (ob_lo o')) eqn:Hl; [|discriminate E].
    apply sv_eqb_sound in Eb. exists o'. split; [exact Ho'|].
    pose proof (lo_gebL_sound rho facts _ _ HF Hl) as L. pose proof (hi_lebL_sound rho facts _ _ HF E) as Hi.
    unfold obj_range, obj_lo_of, obj_hi_of in Ha |- *. cbn [fst snd] in Ha |- *. rewrite <- Eb. lia.
Qed.

Section DCS.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
ScS1Sd7VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
ScS36S7bSe5Vnx;A2S3bA3").

Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S52ScS57S54VAX;R1A1A1S54R1A1A3FX;").
Hypothesis AXd : ltac2:(tb__ "0|0|
S52ScS60S53VAX;R1A1A1S53R1A1A3FX;").
Hypothesis AXV : ltac2:(tb__ "0|0|
S52ScS0S5eVAX;R1A1A1S5eR1A1A3FX;").
Hypothesis AXKm : ltac2:(tb__ "0|0|
S52ScS0S58VAX;R1A1A1S58R1A1A3FX;").
Hypothesis AXKf : ltac2:(tb__ "0|0|
S52ScS0S5dVAX;R1A1A1S5dR1A1A3FX;").
Hypothesis AXlive : ltac2:(tb__ "0|0|
S52ScS38S3eS0S0A2A1S5fVAX;R1A1A1S5fR1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
Se9VnW;Vst;Vnx;VBX;A4").

Definition AXK (G2 : DG) : AA -> AA := ltac2:(tb__ "0|0|
S52Sd9SdaVAX;R1A1VG2;A2A1LX;").
Hypothesis Htmax : 1 <= tmax <= SZMAX.

Definition dlink (G2 : DG) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|3|
SbS1ScS4fQ40M0A1M1S13Vrho';R1A2S13Vrho;R1A2A3Fi;SbS1ScS38S4fQ8A1M2A1S27Vrho';R1A2S27Vrho;R1A2A3Fl;G1SfSa9VG2;S4eG0R1A2A2A1ScS40G2A1S28Vrho';R2A2S28Vrho;R2A2A3F_;Fa;A2A2").

Variables (X5 C5 : axst).
Hypothesis NXE : ltac2:(tb__ "0|0|
ScS36S7bVGS;S17S49VX5;A1A1A2S3bA3").
Hypothesis FBE : ltac2:(tb__ "0|0|
ScS36S92S16S23S17S49VX5;A1A1A1SccA3S3bA3").
Hypothesis XE5 : ax_X X5 = [].
Hypothesis F192 : ltac2:(tb__ "0|1|
S94S16S39S16S25S15Z1A1S14Pc0A1M0A2S39S16S25G0S15Vtmax;A1A2S3dS16A1A3A3S19S49VX5;A1A1A3").
Hypothesis FDEP : ltac2:(tb__ "0|0|
S94S16S8eS8cA1S19S49VX5;A1A1A3").

Hypothesis FUNW : ltac2:(tb__ "0|0|
S94S16S8fVW;Vst;A2S19S49VX5;A1A1A3").
Hypothesis WX5r : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S35S49S62VX5;R2A2A1A1S3bA3F_;Fsz;").
Hypothesis DX5r : ltac2:(tb__ "0|4|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS40S3eS38S3eS10S10A2M0A1M1S38S16A1M2A2M3A1SdeS49S6eVX5;A1A1S49S62VX5;R2A2A1A2S45G3S3aG1G2S39G0S3aS10S10S2aS3cQ20S14Pc0A1A3S15R2A1A4S3dG0A1A3S3dS16A1A4A2A3F_;Fsz;").
Hypothesis SPL1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbdS49S62VX5;R2A2A1S61S15Nee0A1A3A2S3bA3F_;Fsz;").
Hypothesis SPL2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbdS49S6bVX5;R2A2A1S3fS61A1S15N8e0A1A3A2S3bA3F_;Fsz;").
Hypothesis SPL3 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbdS49S6cVX5;R2A2A1S3fS3fS61A1A1S15N840A1A3A2S3bA3F_;Fsz;").
Hypothesis SPL4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbdS49S6dVX5;R2A2A1S3fS3fS3fS61A1A1A1S15N48A1A3A2S3bA3F_;Fsz;").

Variables (s4 : Z -> wsub) (R4 : Z -> list sobj) (T4 : Z -> axst).
Let X4 (sz : Z) : axst := X5s X5 sz.
Hypothesis HER : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS40S38S12A1M0A1Sc7VX4;R2A1S78R2A1Vs4;R2A1A3S45G0VR4;R2A1A2A3F_;Fsz;").
Hypothesis HT4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS4aSc2Vs4;R2A1S78R2A1S77R2A1VX4;R2A1VR4;R2A1A5VT4;R2A1A3F_;Fsz;").
Hypothesis XX4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS38S3eS10S10A2M0A1S4bVX4;R2A1A1S3dG0A1A3F_;Fsz;").
Hypothesis FBX4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S92S16S23S17S49VX4;R2A1A1M0A1A1S19G0A1A3S3bA3F_;Fsz;").
Hypothesis Hchk4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36Sc6VX4;R2A1S78R2A1Vs4;R2A1VR4;R2A1S39S4aS77R2A1S3dS4aA1A3A5S3bA3F_;Fsz;").
Hypothesis NX4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS1S17S49VX4;R2A1A1A1S17S49VX5;A1A1A3F_;Fsz;").
Hypothesis WG10 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10Sb0Vs4;R2A1PaM0A2S24SbbS14G0A1S15N8e0A1A3A3F_;Fsz;").
Hypothesis WG15 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10Sb0Vs4;R2A1PfA2S15N600A1A3F_;Fsz;").
Hypothesis WG12 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10Sb0Vs4;R2A1PcA2S24SbbS14PaA1S15N840A1A3A3F_;Fsz;").

Variable EXo : list sobj.
Definition MAPO : sobj := ltac2:(tb__ "0|0|
S26S14Vnx;A1S15Z0A1S14Sd6A1S3dS1eA1S29A5").
Definition in_fambS (o : sobj) : bool := ltac2:(tb__ "0|4|
S44S44S44ScdVo;A1S93S12S12Se8S79Vo;A1S79R1A1A2Lo';M0S39S12Sa4VEXo;A3A3A2S41S1aS1bVo;A1S14PaA1A2S10S36Lx;S1dVo;A1S0S41S6N8e0R1A2S6R1Z0A2A2Llo;S1S41S7dR1S8bA2S1aS1cVo;A1S15Nee0A1A2A2Li;Sb9S10S10S3cLb;La;M1Lop;M2G2SbaG1Lop;M3G3S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll;X10x8A2A2S93S12G0S8dVW;A1A3A2").
Hypothesis FAM4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S92S12Sa5VR4;R2A1A3S3bA3F_;Fsz;").

Hypothesis EX_zone : ltac2:(tb__ "0|3|
S52S87S11S4fQ40A1M0S11S38G0A1S9cS12S0S7eVsegs;VJG;VAX;R9R8R7R6A5VX5;R5R4R3A6S91S12R3VEXo;A3SbS3S42S0S0S1fR7R4A2M1A3R3A2S4R3S43S0S0G1A3A2A2SdSbS3Sd0R4A2S4R4ScfA2A2SbS3S56S54RcA1A1M2R4A2S4R4S5G2Sd1A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Hypothesis NEWO : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS38S12A1Sc1S49S78R2A1A1S49S77R2A1A1A2S3dS12A1A3F_;Fsz;").
Hypothesis XPost : ltac2:(tb__ "0|1|
S0ScS38S3eS10S10A2M0A1S4bS77R1A1A1S3dG0A1A3Fsz;").

Hypothesis FBT4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S92S16S23S17S49VT4;R2A1A1A1A1S19S49VX4;R2A1A1A1A3S3bA3F_;Fsz;").
Hypothesis XT4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS38S3eS10S10A2M0A1S4bVT4;R2A1A1S3dG0A1A3F_;Fsz;").
Hypothesis RB1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbeS49S64VT4;R2A1VX4;R2A1A2A1U0A2A2S3bA3F_;Fsz;").
Hypothesis RB2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbeS49S65VT4;R2A1VX4;R2A1A2A1U1A2A2S3bA3F_;Fsz;").
Variable nobj : nat.
Hypothesis PERM_nd : ltac2:(tb__ "0|0|
ScS36SdfS63Vnobj;A1A1S3bA3").
Hypothesis PERM_lt : ltac2:(tb__ "0|0|
ScS36S92S37S37SebR1Vnobj;A2Li;S63Vnobj;A1A3S3bA3").
Hypothesis PERM_cov : ltac2:(tb__ "0|0|
ScS36S92S37S37S93S37SeaR1A1S63Vnobj;A1A3Li;Sb6U0Vnobj;A2A3S3bA3").
Hypothesis PERM_len : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS37S47S12S20S49S66VT4;R2A1VX4;R2A1A2A1A1A2Vnobj;A3F_;Fsz;").
Hypothesis MRG1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbcS49S67Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3bA3F_;Fsz;").
Hypothesis MRG2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbcS49S68Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3bA3F_;Fsz;").
Hypothesis MRG3 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbcS49S69Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3bA3F_;Fsz;").
Hypothesis MRG4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S97S18SbcS49S6aVnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3bA3F_;Fsz;").
Let T4d (sz : Z) : axst := ltac2:(tb__ "0|0|
S72Vnobj;VT4;Vsz;A1VX4;Vsz;A1A3").
Variable sd : Z -> wsub.
Hypothesis ENT5 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S4dVT4d;R2A1VC5;Vsd;R2A1A3S3bA3F_;Fsz;").
Hypothesis SID5 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36Sb2Vsd;R2A1VGS;A2S3bA3F_;Fsz;").
Hypothesis R4cov : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S6fS19S49VT4d;R2A1A1M0A1VR4;R2A1S20G0A1A3S3bA3F_;Fsz;").

Definition zoneS (T C pab ua L top a : Z) : Prop := ltac2:(tb__ "0|1|
SdSbSbS3Sd2Va;A2S4Va;SceA2A2SdS4Va;SadA2S3S5SabS9Z8SacA2A2Va;A2A2A2SdSbS3VT;Va;A2S4Va;S5VT;Z1000M0A2A2A2SdSbS3VC;Va;A2S4Va;S5VC;G0A2A2A2SdSbS3Sd0Va;A2S4Va;ScfA2A2SdSbS3Vpab;Va;A2S4Va;S5Vpab;Sd1A2A2A2SdSbS3Vua;Va;A2S4Va;S5Vua;VL;A2A2A2S3Vtop;Va;A2A2A2A2A2A2A2").

Definition site_factsS (A : AA) (rho : valuation) (a : word) (rhoE : valuation) (sz : Z) : Prop := ltac2:(tb__ "0|9|
S4eQ40M0S13Vrho;PcA2A2S0S4eG0Va;A2S0S82R2A1S0SbSbS3Z1Vsz;A2S3Vsz;Vtmax;A2A2SbS3S51G0S13VrhoE;S8bA2A2M1SaS8cA1A2SbSe7S54VA;A1M2A1SbScS4fG0A1M3S13VrhoE;Vnx;A2Va;A3SbScG3S13VrhoE;Sd6A2S50G0R1A2A3SbScG3S13VrhoE;P97A2S50G0S5aG2A1A2A3SbScG3S13VrhoE;P98A2S50G0S59G2A1A2A3SbS3S5cG2A1M4S5S4eG0S13VrhoE;PaA2A2G1A2A2SbSbS3Zfc01R3A2S4R3S7Z2M5Z27A2A2A2SbSbS3Z12000R1A2S3R1S5R3Z3007A2A2A2SbS3SceR2A2SbS3S5R2R1A2Z7fffff800000A2SbS12S0S91S12R2VEXo;A3SbS3S42S0S0S1fVrhoE;R3A2M6A3R2A2S4R2S43S0S0G6A3A2A2SdSbS3Sd0R3A2S4R3ScfA2A2SbS3S56G2A1M7R3A2S4R3S5G7Sd1A2A2A2A2F_;F_;Fz;Fo;Sb5S12S12SbSbS3S5G4Z10A2S4eG0S2cVrhoE;S1bR1A1A2A2M8A2S3G8S7G5Z2fA2A2A2SbScS10S1dR1A1S15N10A1A3ScS10S1cR1A1S15Z0A1A3A2A2Lo;S8dVW;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2TL;Tua;Tnv;").

Lemma R4_zoneS : ltac2:(tb__ "0|3|
S0S52S11S4fQ40M0A1S11S12S0Sa0R6R5R4R3R7A5S91S12R3VR4;R8A1A3SbS3S42S0S0S1fR5R4A2M1A3R3A2S4R3S43S0S0G1A3A2A2Sa3S5aS54R9A1M2A1S59G2A1S56G2A1S4eG0R7A2S82S4eG0S13R8PcA2A2A1S5cG2A1R4A7F_;F_;F_;Fz;Fo;FrhoE;Fa;Frho;FA;Fsz;").
Proof.
  intros sz A rho a rhoE o z (Hsz & DEP & HG & Enx & EMS & E151 & E152 & TOP & HN & SMB & IMG & HTOP & HEX & LNK) Ho Ha.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T1 & T2 & _ & C1 & C2 & _ & _ & S1 & S2 & _ & TG).
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (L := secmapsize nv) in *.
  pose proof (proj1 (forallb_forall _ _) (FAM4 sz Hsz) o Ho) as Fo. unfold in_fambS in Fo. apply orb_prop in Fo as [Fo|FL].
  2: {
    apply existsb_exists in FL as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoE o), Eo, (obj_range_nocells rhoE o') in Ha.
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (B & Elo & Ehi). destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in B, Elo, Ehi. subst olo ohi.
    pose proof (topG_range (aa_geom A)) as TGr.
    rewrite obj_range_mk in Ha by (clear -B TGr; lia). cbn [fst snd] in Ha. do 6 right. clear -Ha B. lia. }
  apply orb_prop in Fo as [Fo|Fo]; [apply orb_prop in Fo as [OK|Fo]|].
  -
    unfold rt_okD in OK. destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in OK.
    destruct lo as [lo|i1|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate OK.
    destruct hi as [hi|i2|o2 a2 b2|o2 a2 b2|o2 a2 b2|o2 a2 b2|sg2 wd2 a2|l2 i2 k2]; try discriminate OK.
    apply orb_prop in OK as [OK|OK]; [apply orb_prop in OK as [OK|OK]|];
      apply andb_prop in OK as [EB OK]; apply sv_eqb_sound in EB; subst b.
    + apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply andb_prop in OK as [OK X1].
      apply Z.leb_le in OK. apply Z.leb_le in X1. apply Z.leb_le in X0.
      rewrite obj_range_mk in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). cbn [fst snd eval] in Ha. rewrite u64_lit in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). left.
      unfold IMG_LO, IMG_HI, STORE, MAP1, MAP1N in *. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
    + apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
      rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E151, u64_lit in Ha by lia. right. left. lia.
    + apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
      rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E152, u64_lit in Ha by lia. right. right. left. lia.
  -
    apply existsb_exists in Fo as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoE o), Eo, (obj_range_nocells rhoE o') in Ha.
    destruct Ho' as [<-|Ho'].
    + do 5 right. left.
      assert (SO : soff rhoE (SVar V_MS) = L).
      { unfold soff. cbn [eval]. rewrite EMS, signed_lit. unfold snorm. rewrite Z.mod_small by (clear -SMB HN; lia).
        destruct (Z.ltb_spec L (2 ^ 63)); clear -SMB HN H; lia. }
      unfold MAPO, obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi fst snd] in Ha.
      rewrite SO, soff_lit_small in Ha by lia. cbn [eval] in Ha. rewrite Enx in Ha. clear -Ha. lia.
    + destruct (HEX o' z Ho' Ha) as [B|P]; [do 3 right; left; exact B | do 4 right; left; exact P].
  -
    apply andb_prop in Fo as [Fb Fl]. apply sv_eqb_sound in Fb.
    destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in Fb, Fl. subst b.
    pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (srange (rw rhoE V_DEPTH)) as R15.
    do 6 right. unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
    destruct lo as [lo|i|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate Fl.
    + apply andb_prop in Fl as [Fl Fl2]. apply Z.leb_le in Fl. apply Z.leb_le in Fl2. cbn [fst snd] in Ha.
      rewrite soff_lit_small in Ha by lia. unfold malloc_depth in DEP. lia.
    + apply andb_prop in Fl as [Fi Fl]. apply Pos.eqb_eq in Fi. subst i. apply sv_eqb_sound in Fl. subst hi. rewrite soff_lit_small in Ha by lia.
      unfold soff in Ha. cbn [eval] in Ha. change 15%positive with V_DEPTH in Ha. cbn [fst snd] in Ha. lia.
Qed.

Lemma zoneS_not_DFP : ltac2:(tb__ "0|1|
S52S11S38S4fQ40A1A1S84S0S0S0Sd8R7R6R5R4A4S3SceR4A2S3eS0S0A2M0S91G0R1Sa7S53RaA1A1A3Sa6R2S3aS0S0R7R6A4A2F_;Fbn;S54RaA1S57Sa3S5aR1A1S59R1A1S56R1A1R7R6S5cR1A1R5A7SfSa9S53RcA1R6A2A1F_;TG;F_;F_;F_;Fz;FL;Fua;Fmd;Ftp;Frho;FAx;").
Proof.
  intros Ax rho tp md ua L z HX IMG HSEP G HZ HD. subst G.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4' & _); exact X4').
  pose proof (zones_not_DFPw Ax z HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  pose proof (dyn_ok_big _ _ _ HPAB ltac:(unfold kPtrArrayReserve; lia)) as PB.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot Ax) z) -> P -> ~ dfp_static z -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= z < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static z).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range z Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZB|[ZP|[ZM|ZK]]]]]].
  - apply (GOAL (IMG_LO <= z < IMG_HI /\ ~ dstatw z)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range z Hs). lia.
    + intros Hs. pose proof (dstat_range z Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (SHADOW_BAND_LO <= z < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | exact ZB |].
    apply (NS SHADOW_BAND_LO (z + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl H)))))))) ZP).
    apply (NS (ag_pab (aa_geom Ax)) (z + 1)); [lia | unfold IMG_HI in PB; unfold MAP1, MAP1N; lia].
  -
    destruct HD as [Hs|[(b & Hb & Hbz)|(b & Hb & Hbz)]].
    + pose proof (dstat_range z Hs) as DR. unfold IMG_HI in IMG. unfold MAP1, MAP1N, STORE in DR. clear -DR IMG ZM. lia.
    + pose proof (HSEP (b, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as SP.
      unfold sepZ in SP. cbn [fst snd] in SP. clear -SP Hbz ZM. lia.
    + pose proof (HSEP (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as SP.
      unfold sepZ in SP. cbn [fst snd] in SP. clear -SP Hbz ZM. lia.
  - apply (GOAL (topG (aa_geom Ax) <= z)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom Ax)) (z + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma GS_lt_next : ltac2:(tb__ "0|0|
S1S7cR1VGS;A2S7cR2S17S49VX5;A1A1A2F_;Fi;").
Proof. intros i Hi. eapply Pos.lt_le_trans; [exact Hi | apply Pos.leb_le; exact NXE]. Qed.

Lemma stopJ_triv : ltac2:(tb__ "0|0|
ScS8aVst;S89A3ScS38S86A1VW;S3dS86A1A3F_;S11S90VW;Vst;R1A3Fr;F_;").
Proof. intros HW r. unfold unwind_stopJ. destruct W as [|u us] eqn:EW; [exact I|]. destruct st; [exact I|]. discriminate (HW eq_refl). Qed.

Lemma budget_A0 : ltac2:(tb__ "0|0|
S52S0S5bR2R1A2S5bVAX;SdbR3R2A2A1Z0A2F_;Fnv;FA;").
Proof.
  intros A nv (HL & HR & HP). split; [|split].
  - rewrite AXV, AXKm, AXKf. cbn [aa_V aa_Km aa_Kf bumpV]. unfold limit_ok_alloc in *. rewrite Z.add_0_r. exact HL.
  - unfold sec_room, large_live in *. rewrite AXlive. cbn [aa_live bumpV]. exact HR.
  - apply (prim_room_same A (AX (bumpV A nv))); [rewrite AXlive; reflexivity | exact HP].
Qed.

Lemma dcS_facts : ltac2:(tb__ "0|2|
S52S87S11S4fQ40M0A1M1S11S38G1A1S9cS7eVsegs;VJG;VAX;R7R6R5R4A5VX5;R3R2R1A6Sa0R8R6R5R4S4eG0S13R4Pc0A2A2A5F_;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w Hw. pose proof (SPA_facts_hold segs _ rhoE X5 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx AX A Kc rho a rhoE tp tr md HJ) as (E12 & Enx & _ & E142 & E151 & E152 & _).
  pose proof (JGs_nums nW st tmax nx Hnx AX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _).
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & Htop & _). unfold top_high in Htop.
  assert (FACT : forall p, In p (ss_facts (ax_S X5)) -> holds rhoE p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HF p Hp)).
  pose proof (FACT _ (F192 _ (or_introl eq_refl))) as Fs1. pose proof (FACT _ (F192 _ (or_intror (or_introl eq_refl)))) as Fs2.
  cbn [holds eval] in Fs1, Fs2. rewrite u64_lit in Fs1 by lia. rewrite u64_lit in Fs2 by (unfold SZMAX in Htmax; lia).
  pose proof (FACT _ (FDEP _ ltac:(unfold pre_facts, F_depth; cbn [app]; do 2 right; left; reflexivity))) as Fd1.
  cbn [holds eval branch_taken] in Fd1. unfold bv_lts in Fd1. apply negb_true_iff in Fd1. apply Z.ltb_ge in Fd1.
  change (bv_signed (Z_to_bv 64 (- malloc_depth))) with (- malloc_depth) in Fd1.
  pose proof (proj1 HA) as HG. rewrite AXg in HG. cbn [aa_geom bumpV] in HG.
  unfold site_factsS. cbn zeta.
  split; [lia|]. split; [exact Fd1|]. split; [exact HG|]. split; [exact Enx|]. split; [exact E142|]. split; [exact E151|]. split; [exact E152|].
  split; [exact Htop|]. split; [exact HN|]. split; [exact SMB|]. split; [exact IMG|]. split; [exact HTOP|].
  split; [intros o z Ho Hz; exact (EX_zone A Kc rho a rhoE tp _ o z Hw Ho Hz)|].

  pose proof (topG_range (aa_geom A)) as TGr. pose proof (srange (rw rhoE V_DEPTH)) as R15. unfold malloc_depth in Fd1.
  apply (unwind_objs_above W rhoE (topG (aa_geom A))); [|clear -Htop Fd1; lia | clear -TGr; lia].
  apply Forall_forall. intros p Hp. apply FACT. apply FUNW.
  unfold unwind_factsS. destruct st; [apply chain_pre_in; exact Hp|]. destruct W as [|l0 W0']; [destruct Hp | exact Hp].
Qed.

Lemma dcS_site : ltac2:(tb__ "0|2|
S52S87S11S4fQ40M0A1M1S11S38G1A1S9cS7eVsegs;VJG;VAX;R7R6R5R4A5VX5;R3R2R1A6S7eVsegs;VJG;VAX;R8R7R6R5A5VX4;S4eG0S13R4Pc0A2A2A1R4R3R2A6F_;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w Hw. pose proof (dcS_facts A Kc rho a rhoE tp w Hw) as (Hsz & Fd1 & HG & _ & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *. destruct w as [tr [ms md]].
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG. unfold malloc_depth in Fd1.
  assert (Em3808 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-3808)))) = bv_unsigned (rw rhoE 10%positive) - 3808).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-3808))) with (2 ^ 64 - 3808) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2112)))) = bv_unsigned (rw rhoE 10%positive) - 2112).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2112))) with (2 ^ 64 - 2112) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HwF : SPA segs (JG AX A Kc rho a) (X5f X5) rhoE tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hw)]. unfold X5f. apply (smatchA_add_facts segs rhoE tp F_call _ _ (proj1 Hw)); [|exact FBE]. unfold F_call.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?Em3808, ?Em2112; cbn [eval]; rewrite ?u64_lit by lia; lia. }
  assert (HwR : SPA segs (JG AX A Kc rho a) (X5r X5 sz) rhoE tp (tr, mkCfg ms md)).
  { unfold X5r, rstS. eapply SPA_restate; [exact (WX5r sz Hsz) | exact (DX5r sz Hsz) | reflexivity | | constructor | exact HwF].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd eval].
    apply bv_eq. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. rewrite u64_lit by (unfold SZMAX in Htmax; lia).
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by (unfold SZMAX in Htmax; lia). reflexivity. }
  assert (OS : forall (Jx : jpredA) X i mid, isSome (split_obj_at (ax_S X) i mid) = true ->
            SPA segs Jx X rhoE tp (tr, mkCfg ms md) -> SPA segs Jx (osplit X i mid) rhoE tp (tr, mkCfg ms md)).
  { intros Jx X i mid Hs HX. unfold osplit. destruct (split_obj_at (ax_S X) i mid) as [S'|] eqn:E; [|exact HX]. eapply (SPA_split segs); [exact E | exact HX]. }
  unfold X4, X5s. apply OS; [exact (SPL4 sz Hsz)|]. unfold X5c. apply OS; [exact (SPL3 sz Hsz)|]. unfold X5b. apply OS; [exact (SPL2 sz Hsz)|].
  unfold X5a. apply OS; [exact (SPL1 sz Hsz)| exact HwR].
Qed.

Lemma dcS_R4 : ltac2:(tb__ "0|3|
S52S11S4fQ40M0A1M1S11S0Sa0R5R4R3R2R1A5S52S11S38G1A1S84G1Sd8R5R4R3R2A4ScS57S54R6A1S54RcA1A3S3eS0S0A2M2S91G2R1Sa7S53R8A1A1A3Sa6R2S3aS0S0S4eG0RdA2S82S4eG0S13RePcA2A2A1A4A2F_;Fbn;Sb1RbVR4;RaA1R4A3SfSa9S53R9A1S4eG0R5A2A2A1F_;F_;F_;F_;Fx;Fmdx;Ftpx;Frx;FAx;F_;Fsz;FrhoE;Fa;Frho;FA;").
Proof.
  intros A rho a rhoE sz SF Ax rx tpx mdx x HX EG HSEP (o & Ho & Hox).
  pose proof (R4_zoneS sz A rho a rhoE o (bv_unsigned x) SF Ho Hox) as HZ. rewrite <- EG in HZ.
  pose proof SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG & _).
  exact (zoneS_not_DFP Ax rx tpx mdx _ _ (bv_unsigned x) HX IMG HSEP HZ).
Qed.

Let A0 (A : AA) (rho : valuation) : AA := ltac2:(tb__ "0|0|
VAX;SdbVA;S4eQ40S13Vrho;PcA2A2A2A1").
Lemma A0_geom : ltac2:(tb__ "0|0|
S52S11ScS57S54VA0;R2R1A2A1S54R2A1A3Frho;FA;").
Proof. intros A rho. unfold A0. rewrite AXg. reflexivity. Qed.
Lemma A0_depot : ltac2:(tb__ "0|0|
S52S11ScS60S53VA0;R2R1A2A1S53R2A1A3Frho;FA;").
Proof. intros A rho. unfold A0. rewrite AXd. reflexivity. Qed.

Lemma dcS_entry : ltac2:(tb__ "0|4|
S52S87S11S4fQ40M0A1M1S11S38G1A1S0S38S85A1M2S99S84Sa0RaR8R7R6R4A5S88RaA1S7fVsegs;R8R7VX4;R6A1S3aG2S9aR5S9bR4R3A2A4A5VJG;VAX;RdRcRbRaR9R8R6R4A9SaaSb4Sb3VA0;ReRcA2M3RdRaS4eG0RbA2S82S4eG0S13RcPcA2A2A1A5S53G3A1SafSaeRaVR4;R8A1S96R5R9R6A3A3Vs4;R8A1A2R9R7R5A7F_;F_;F_;F_;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0.
  pose proof SF as (Hsz & Fd1 & HG & Enx & EMS & E151 & E152 & Htop & HN & SMB & IMG & HTOP & HEX). unfold malloc_depth in Fd1.
  pose proof HJ0 as (_ & _ & HA0 & HP0 & HK0 & _ & _ & _ & _ & HB0). cbn zeta in HA0, HP0, HB0. fold (A0 A rho) in HA0.
  pose proof (AInvA_budget (A0 A rho) rhoE tp md0 HA0) as (_ & _ & _ & HKm0 & _).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2272 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2272)))) = bv_unsigned (rw rhoE 10%positive) - 2272).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2272))) with (2 ^ 64 - 2272) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2112)))) = bv_unsigned (rw rhoE 10%positive) - 2112).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2112))) with (2 ^ 64 - 2112) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  pose proof HP0 as (PIn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PSep).
  split.
  - apply (KDP_intro (A0 A rho) Kc rhoE 0 (budget_A0 A _ HB0) HKm0 _ _ tp tr0 md0 HA0 HK0 PIn).
    + rewrite A0_depot. exact PSep.
    + unfold TOPr, V_DEPTH. rewrite A0_geom. cbn [rw rho_sub rho_absorb].
      rewrite (WG10 sz Hsz), (WG15 sz Hsz), (WG12 sz Hsz), !eval_absorb, Em2272, Em2112.
      change (bv_signed (eval rhoE (SLit (-1536)))) with (-1536). lia.
  - destruct (AInvA_X (A0 A rho) rhoE tp md0 HA0) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot (A0 A rho)) rhoE _ md0 tp); [|exact HD0]. intros z Hz. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin.
    apply (dcS_R4 A rho a rhoE sz SF (A0 A rho) rhoE tp md0 _ HX0 (A0_geom A rho) ltac:(rewrite A0_depot; exact PSep) Hin). rewrite u64_lit by exact Hr. exact Hz.
Qed.

Lemma dcS_exit_ok : ltac2:(tb__ "0|5|
S52S87S11S4fQ40M0A1M1S11S38G1A1M2S0S38S85A1M3S99S84S11G2G3S99S84Sa0RfRdRcRbR9A5S88RfA1Sa8Sb4Sb3VA0;R11RfA2M4R10RdS4eG0ReA2S82S4eG0S13RfPcA2A2A1A5S53G4A1A3Sc3SafSaeReVR4;RcA1S96R9RdRaA3A3Vs4;RcA1A2S11S7fVsegs;RfReVX4;RdA1S3aG3S9aRcS9bRbRaA2A4A5VJG;VAX;R14R13R12R11R10RfRdRbA9SbfS17S49S78RfA1A1A1R3RbA3S7fVsegs;RcRbS77R10A1S3aG3S9aRaS9bR9R8A2A4A5R6R5R12RdRcRbR9A6Sc5R14S96RfR13R10A3VR4;R12A1Vs4;R12A1S78R12A1S77R12A1VX4;R12A1ReA8F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  pose proof SF as (Hsz & _). subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros x Hin. apply HRM. pose proof HKD' as ((HXK & _) & (_ & HSEP')).
    exact (dcS_R4 A rho a rhoE sz SF _ rhoE tpL md' x HXK (A0_geom A rho) HSEP' Hin).
  - intros o' oR Ho' HoR. rewrite (NEWO sz Hsz) in Ho'. destruct Ho'.
  - intros r x j oR Hr. rewrite (XPost sz) in Hr. destruct Hr.
  - intros r x j Hr. rewrite (XX4 sz Hsz) in Hr. destruct Hr.
Qed.

Lemma dcS_exit_core : ltac2:(tb__ "0|7|
S52S87S11S4fQ40M0A1M1S11S38G1A1M2S0S38S85A1M3S99S84S11G2G3S99S84ScS8aVst;S89A3ScS38S86A1VW;S3dS86A1A3F_;S83VW;Vst;A2Sa0R11RfReRdRbA5S88R11A1Sa8Sb4Sb3VA0;R13R11A2M4R12RfS4eG0R10A2S82S4eG0S13R11PcM5A2A2A1A5S53G4A1A3Sc3SafSaeR10VR4;ReA1S96RbRfRcA3A3Vs4;ReA1A2S11S7fVsegs;R11R10VX4;RfA1S3aG3S9aReS9bRdRcA2A4A5VJG;VAX;R16R15R14R13R12R11RfRdA9SbfS17S49S78R11A1A1A1R3RdA3S7fVsegs;ReRdS77R12A1S3aG3S9aRcS9bRbRaA2A4A5R6R5R14RfReRdRbA6S11S9cSc0R18S96R13R17R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R2R12A9S7eVsegs;Sc4RaR9R18R13R12A5Sc2Vs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R3R12R2A6SeS55S55SeS11S11SeS11S11SbS3eS0S0A2M6S91G6R1Sa7R4A1A3Sa6R2S3aS0S0S4eG0R20A2S82S4eG0S13R21G5A2A2A1A4A2F_;Fbn;SbSa2R3R1fR2A3S7eVsegs;VJG;Sa1R3A1R21R20R2R1eA5VC5;R1R16R6A6A2A2LrhoX;A2Lrho'';A2LG2;A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL rho' w' HLK [Hsm' HJ'].
  pose proof SF as (Hsz & Fd1 & HG & Enx & EMS & E151 & E152 & Htop & HN & SMB & IMG & HTOP & HEX).
  pose proof HJ0 as (Hag0 & Ha0 & HA0 & HP0 & HK0 & Htp0 & HU0 & HN0 & Htop0 & HB0). cbn zeta in HA0, HP0, HB0, HN0. fold (A0 A rho) in HA0. unfold top_high in Htop0.
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof (HER sz Hsz) as ER. pose proof (HT4 sz Hsz) as ET4.
  subst JL.
  destruct (entails_frA_sound segs (X4 sz) (PreD sz) (s4 sz) (R4 sz) rhoE tp tr0 ms0 md0 ER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as ((HX2 & HK2 & HL2 & HT2) & (PIn2 & HSEP2)).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  rewrite ET4 in Hsm'.
  assert (NXlt : forall i, (i < GS)%positive -> (i < ss_next (ax_S (X4 sz)))%positive).
  { intros i Hi. rewrite (NX4 sz Hsz). exact (GS_lt_next i Hi). }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (X4 sz)))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros p Hp.
    exact (proj1 (holds_agree_vals _ rhoE rho' p Hag' (proj1 (forallb_forall _ _) (FBX4 sz Hsz) p Hp)) (proj1 (Forall_forall _ _) Hfacts4 p Hp)). }
  match type of HJc with ?Jx _ _ _ _ => set (JP := Jx) in * end.
  assert (HT40 : SPA segs JP (T50 (T4 sz) (X4 sz)) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T50. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact (FBT4 sz Hsz) | intros _; exact HF4]. }
  assert (AXr : forall X i, ax_X (oreb X i) = ax_X X) by (intros X i; unfold oreb; destruct (rebase_obj_at _ _); reflexivity).
  assert (AXm : forall X i, ax_X (omrg X i) = ax_X X) by (intros X i; unfold omrg; destruct (merge_objs_at _ _); reflexivity).
  assert (AX40 : ax_X (T50 (T4 sz) (X4 sz)) = []) by (unfold T50, ax_with_facts; cbn [ax_X ax_setS]; exact (XT4 sz Hsz)).
  assert (OR : forall (Jx : jpredA) X i, isSome (rebase_obj_at (ax_S X) i) = true -> ax_X X = [] ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (oreb X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX0 HX. unfold oreb. destruct (rebase_obj_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_rebase segs); [exact E | exact HX0 | exact HX]. }
  assert (OM : forall (Jx : jpredA) X i, isSome (merge_objs_at (ax_S X) i) = true ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (omrg X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX. unfold omrg. destruct (merge_objs_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_merge segs); [exact E | exact HX]. }
  assert (HT4b : SPA segs JP (T5b (T4 sz) (X4 sz)) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T5b. apply OR; [exact (RB2 sz Hsz) | unfold T5a; rewrite AXr; exact AX40 |]. unfold T5a. apply OR; [exact (RB1 sz Hsz) | exact AX40 | exact HT40]. }
  assert (HT4c : SPA segs JP (T5c nobj (T4 sz) (X4 sz)) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T5c. apply (SPA_select segs); [exact HT4b | exact PERM_nd | |].
    - intros i Hi. rewrite (PERM_len sz Hsz). apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt i Hi).
    - intros i Hi. rewrite (PERM_len sz Hsz) in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }
  assert (HT4d : SPA segs JP (T4d sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4d, T5d. apply OM; [exact (MRG4 sz Hsz)|]. unfold T5m3. apply OM; [exact (MRG3 sz Hsz)|]. unfold T5m2. apply OM; [exact (MRG2 sz Hsz)|].
    unfold T5m1. apply OM; [exact (MRG1 sz Hsz)| exact HT4c]. }
  assert (AX4d : ax_X (T4d sz) = []).
  { unfold T4d, T5d, T5m3, T5m2, T5m1. rewrite !AXm. unfold T5c. cbn [ax_X ax_setS]. unfold T5b, T5a. rewrite !AXr. exact AX40. }
  clear HT40 HT4b HT4c OR OM.

  assert (RNG : forall o, In o (R4 sz) -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (X4 sz)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := AXK G2 (bumpV A (bv_unsigned (rw rho 12%positive)))).
  set (rho5 := rho_absorb rho' (R4 sz) (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho) (rl rho) (rm rho5)).
  assert (RM5 : forall x, rm rho5 x = if in_ranges_dec rho' (R4 sz) x then rm rhoE x else rm rhoL x).
  { intros x. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall x, in_ranges rho' (R4 sz) x <-> in_ranges rhoE (R4 sz) x).
  { intros x. split; intros (o & Ho & Hox); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hox). }
  assert (R4DFP : forall x, in_ranges rhoE (R4 sz) x -> ~ DFP G2 (bv_unsigned x)).
  { intros x Hin. exact (dcS_R4 A rho a rhoE sz SF _ rhoE tpL md2 x HX2 (A0_geom A rho) HSEP2 Hin). }
  assert (KEY : forall x, ~ DFP G2 (bv_unsigned x) -> rm rho5 x = rm rhoE x).
  { intros x Hx. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) x) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 x Hx). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE x) Hi)). }
  assert (KEYin : forall x, in_ranges rhoE (R4 sz) x -> rm rho5 x = rm rhoE x).
  { intros x Hi. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) x) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE x) Hi)). }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE (R4 sz) (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros z Hz. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 z) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Hz. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X (A0 A rho) rhoE tp md0 HA0) as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A', AXK. cbn [aa_depot aa_Km aa_Kf bumpK with_depot]. fold (A0 A rho). lia. }
  assert (RW5 : forall i, (i < GS)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (GWS : forall i, (i < GW)%positive -> (i < GS)%positive) by (intros i Hi; exact (lt_GW_GS nx NXG i Hi)).
  assert (HJG5 : JG (AXK G2) A Kc rho'' a rho5 tpL tr2 md2).
  { unfold JG, JGs. cbn zeta. change (rw rho'' 12%positive) with (rw rho 12%positive).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - split; [|split].
      + intros i Hi. refine (eq_trans _ (eq_trans (Hagw i Hi) (eq_sym (RW5 i (GWS i Hi))))).
        unfold rhoM_of, cnt_of, chk_of, cst_of. change (rw rho'' 12%positive) with (rw rho 12%positive). apply rw_rho_sets_ext. intros j. reflexivity.
      + intros l. unfold rhoM_of. rewrite rl_rho_sets. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l), <- (Hagl l).
        unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
      + intros x. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
    - rewrite (RW5 nx (nx_lt_GS nx)). exact Ha0.
    - exact HA5.
    - destruct HP0 as (_ & PR). exact (conj PIn2 PR).
    - exact HK2.
    - unfold tp_ok in Htp0 |- *. rewrite (RW5 24%positive) by (apply GWS; unfold GW; lia). exact Htp0.
    - exact (stopJ_triv HW rho5).
    - exact HN0.
    - unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (apply GWS; unfold GW, V_DEPTH; lia). exact Htop0.
    - exact HB0. }

  assert (HT5 : SPA segs (JG (AXK G2) A Kc rho'' a) (T4d sz) rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT4d)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact AX4d | | exact HT4d | exact HJG5].
    intros o x Ho Hx. exact (coveredbL_sound _ _ _ rho' o x HfT (R4cov sz Hsz) Ho Hx). }
  pose proof (SPA_entails segs (JG (AXK G2) A Kc rho'' a) GS (T4d sz) C5 _ rho5 tpL _ (ENT5 sz Hsz) (SID5 sz Hsz)
                (JGs_stable nW st tmax nx Hnx NXG (AXK G2) A Kc rho'' a HUS HKc) HT5) as HC5.
  exists G2, rho'', (rho_sub rho5 (sd sz)). split; [exact HSEP2|]. split; [|exact HC5].
  split; [intros i; reflexivity|]. split; [intros l; reflexivity|].
  intros x Hx. unfold rho''. cbn [rm]. rewrite (KEY x Hx). rewrite <- (Hagm x). unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
Qed.

Lemma dcS_exit : ltac2:(tb__ "0|7|
S9cOF_;S52S87S11S4fQ40M0A1M1S11S38G1A1M2S9fS0S38S85A1M3S99S84S11G2G3S99S84ScS8aVst;S89A3ScS38S86A1VW;S3dS86A1A3F_;S83VW;Vst;A2S55S11S11G2S3eS0S0A2M4S91G4R1Sa7R5A1A3Sa6R2S3aS0S0S4eG0R15A2S82S4eG0S13R16PcM5A2A2A1A4A2F_;Fbn;Sa2R5R15R4A3S9eVsegs;R19S7eVsegs;VJG;Sa1R6A1R18R17R5R15A5VC5;R4R3A5R12A4F_;F_;Ftp';FrhoX;Frho';FG2;Sa0R13R11R10RfRcA5S88R13A1Sa8Sb4Sb3VA0;R15R13A2M6R14R11S4eG0R12A2S82S4eG0S13R13G5A2A2A1A5S53G6A1A3Sc3SafSaeR12VR4;RfA1S96RcR11RdA3A3Vs4;RfA1A2S11S7fVsegs;R13R12VX4;R10A1S3aG3S9aRfS9bReRdA2A4A5VJG;VAX;R18R17R16R15R14R13R10ReA9SbfS17S49S78R12A1A1A1R3ReA3S7fVsegs;RfReS77R13A1S3aG3S9aRdS9bRcRbA2A4A5R6R5R16R10RfReRcA6SbSc5R18S96R12R17R13A3VR4;R15A1Vs4;R15A1S78R15A1S77R15A1VX4;R15A1R11A8S11Sc0R19S96R13R18R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R1R12A9S9eVsegs;R1fS7eVsegs;Sc4R9R8R19R13R12A5Sc2Vs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R2R12A5R18A4F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dcS_exit_ok A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK n' Hg' w' Hw'.
  destruct (dcS_exit_core A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (G2 & rho'' & rhoX & Hsep & Hl & HC5).
  exact (Hcont G2 rho'' rhoX tpL Hsep Hl n' Hg' w' HC5).
Qed.

Lemma dcS_exitE : ltac2:(tb__ "0|7|
S52S87S11S4fQ40M0A1M1S11S38G1A1M2S9cOF_;S0S38S85A1M3S99S84S11G2G3S99S84ScS8aVst;S89A3ScS38S86A1VW;S3dS86A1A3F_;S83VW;Vst;A2S55S11S11G2S3eS0S0A2M4S91G4R1Sa7R5A1A3Sa6R2S3aS0S0S4eG0R15A2S82S4eG0S13R16PcM5A2A2A1A4A2F_;Fbn;Sa2R5R15R4A3S9dVsegs;S7eVsegs;VJG;Sa1R6A1R18R17R5R15A5VC5;R4R3A5R12A3F_;F_;Ftp';FrhoX;Frho';FG2;Sa0R13R11R10RfRcA5S88R13A1Sa8Sb4Sb3VA0;R15R13A2M6R14R11S4eG0R12A2S82S4eG0S13R13G5A2A2A1A5S53G6A1A3Sc3SafSaeR12VR4;RfA1S96RcR11RdA3A3Vs4;RfA1A2S11S7fVsegs;R13R12VX4;R10A1S3aG3S9aRfS9bReRdA2A4A5VJG;VAX;R18R17R16R15R14R13R10ReA9SbfS17S49S78R12A1A1A1R3ReA3S7fVsegs;RfReS77R13A1S3aG3S9aRdS9bRcRbA2A4A5R6R5R16R10RfReRcA6SbSc5R18S96R12R17R13A3VR4;R15A1Vs4;R15A1S78R15A1S77R15A1VX4;R15A1R11A8S11Sc0R19S96R13R18R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R1R12A9S9dVsegs;S7eVsegs;Sc4R9R8R19R13R12A5Sc2Vs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R2R12A5R18A3F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dcS_exit_ok A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK w' Hw'.
  destruct (dcS_exit_core A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (G2 & rho'' & rhoX & Hsep & Hl & HC5).
  exact (Hcont G2 rho'' rhoX tpL Hsep Hl w' HC5).
Qed.

Lemma dcS_nums : ltac2:(tb__ "0|4|
S52S87S11S4fQ40M0A1M1S11S38G1A1S38S85A1S84VJG;VAX;R8R7R6R5R4R3R2R1A9S4eG0R6A2S0S82S4eG0S13R8PcA2A2A1S0SbS5bVA0;RbR9A2M2Z0M3A2SbS3G3S58G2A1A2SbS3G3R2A2SbS3G3R1A2SbS4S5R2R1A2S7Z2Z40A2A2Se6Vsegs;G2R7R6R4A5A2A2A2A2A2TL;Tua;F_;Fmd;Ftr;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp tr md HJ. cbn zeta.
  pose proof (JGs_nums nW st tmax nx Hnx AX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _).
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & _ & HB). cbn zeta in HA, HB. fold (A0 A rho) in HA.
  pose proof (AInvA_budget (A0 A rho) rhoE tp md HA) as (_ & _ & _ & HKm0 & _). pose proof (urange a) as Ra.
  split; [exact (budget_A0 A _ HB)|]. split; [exact HKm0|]. split; [lia|]. split; [lia|]. split; [lia | exact HA].
Qed.

Theorem depot_call_S : ltac2:(tb__ "0|4|
S9cOF_;S52S87S11S4fQ40M0A1M1S9fScS8aVst;S89A3ScS38S86A1VW;S3dS86A1A3F_;S83VW;Vst;A2S88R6A1S81Vsegs;R9S80R7A1A3Se2Vsegs;RaS80R8A1A3S55S11S11S38G1A1M2S3eS0S0A2M3S91G3R1Sa7R5A1A3Sa6R2S3aS0S0S4eG0RdA2S82S4eG0S13RePcA2A2A1A4A2F_;Fbn;Sa2R5RdR4A3S9eVsegs;R11S7eVsegs;VJG;Sa1R6A1R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S11G2S9eVsegs;ReS7eVsegs;VJG;VAX;RdRcRbRaA5VX5;R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rhoE tp n HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dcS_facts A Kc rho a rhoE tp _ Hw) as SF. pose proof (dcS_site A Kc rho a rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (dcS_nums A Kc rho a rhoE tp tr md HJ) as (HB & HKm0 & Hua & HL & HuaL & HA). cbn zeta in Hua, HL, HuaL.
  pose proof (topG_range (aa_geom A)) as TG.
  set (K := KDP (A0 A rho) Kc rhoE (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))).
  assert (HKT : forall G r t tr0 md0, K G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. pose proof (KD_top _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) as X. rewrite A0_geom in X.
    pose proof SF as (_ & _ & HG & _). rewrite (geom_top _ HG). exact X. }
  apply (call_soundPA segs ok (JG AX A Kc rho a) (JD segsA K (aa_depot (A0 A rho))) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as ((_ & _ & _ & HT1) & _). unfold TOPr in HT1. rewrite A0_geom in HT1.
    refine (seg_D_sound2 K (hcD (A0 A rho)) (KDP_laws (A0 A rho) Kc rhoE 0 HKc HB ltac:(lia) HKm0 _ _ Hua HL HuaL NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot (A0 A rho)) (dN_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) (hcD_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t tr0 ms0 md0 msv' HKG HMI Hh Hp Hs. exact (Hokl r t tr0 ms0 md0 msv' (KD_Kc _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) HMI Hh Hp Hs).
    + intros G r t tr0 ms0 md0 x8 HKG Hp Hok. exact (Hokpl r t tr0 ms0 md0 x8 (KD_Kc _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) Hp Hok).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dcS_entry A Kc rho a rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L0 JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L0 JL. clear EL.
    exact (dcS_exit ok A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact HgQ.
  - exact Hw4.
Qed.

Theorem depot_call_SE : ltac2:(tb__ "0|4|
S52S87S11S4fQ40M0A1M1S9cOF_;ScS8aVst;S89A3ScS38S86A1VW;S3dS86A1A3F_;S83VW;Vst;A2S88R6A1S55S11S11S38G1A1M2S3eS0S0A2M3S91G3R1Sa7R5A1A3Sa6R2S3aS0S0S4eG0RbA2S82S4eG0S13RcPcA2A2A1A4A2F_;Fbn;Sa2R5RbR4A3S9dVsegs;S7eVsegs;VJG;Sa1R6A1ReRdR5RbA5VC5;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S11G2S9dVsegs;S7eVsegs;VJG;VAX;RbRaR9R8A5VX5;R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc Hcont rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (dcS_facts A Kc rho a rhoE tp _ Hw) as SF. pose proof (dcS_site A Kc rho a rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (dcS_nums A Kc rho a rhoE tp tr md HJ) as (HB & HKm0 & Hua & HL & HuaL & HA). cbn zeta in Hua, HL, HuaL.
  pose proof (topG_range (aa_geom A)) as TG.
  set (K := KDP (A0 A rho) Kc rhoE (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))).
  assert (HKT : forall G r t tr0 md0, K G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. pose proof (KD_top _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) as X. rewrite A0_geom in X.
    pose proof SF as (_ & _ & HG & _). rewrite (geom_top _ HG). exact X. }
  apply (call_completePA segs (JG AX A Kc rho a) (JD segsA K (aa_depot (A0 A rho))) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as ((_ & _ & _ & HT1) & _). unfold TOPr in HT1. rewrite A0_geom in HT1.
    exact (seg_D_complete2 K (hcD (A0 A rho)) (KDP_laws (A0 A rho) Kc rhoE 0 HKc HB ltac:(lia) HKm0 _ _ Hua HL HuaL NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot (A0 A rho)) (dN_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) (hcD_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dcS_entry A Kc rho a rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L0 JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L0 JL. clear EL.
    exact (dcS_exitE A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact Hw4.
Qed.
End DCS.
End DepotCallS.

(* [comment removed for export] *)
Module SpineMallocR11.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "reg_sv"; "eval"; "ss_facts"; "valuation"; "ss_objs"; "swf"; "sprop_below"; "ss_lenient"; "ss_pc"; "sv_below"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "list"; "nil"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "GR"; "rMS"; "sMS"; "O_pcm"; "O_ri"; "beg1"; "beg2"; "cX"; "idx_rot"; "nobj"; "relM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "ge"; "le"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "ghosts"; "mlink"; "F0"; "U0"; "entryR"; "frozen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "ph_set"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "rigids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "O_shp"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10"; "a2_e"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition a0_e (eb : sv) : sv := SAlu ALU_AND eb (SLit 18446744073709547520).

Lemma a0_val : ltac2:(tb__ "0|1|
SfS8S22S0S22S34Q40M0SdR3R2A2A2R1A3S0S22S38R2Z1000A2Z0A3S0S33G0A1SdR5S50R4A1A2SdR5R4A2A3F_;F_;FB;Feb;Fr;").
Proof.
  intros r eb B EB HM. unfold a0_e. cbn [eval]. apply bv_eq. rewrite and_val. replace (bv_unsigned (Z_to_bv 64 18446744073709547520)) with 18446744073709547520 by reflexivity.
  rewrite EB. apply land_m4096_id; [|exact HM]. rewrite <- EB. apply urange.
Qed.

Section ADDR.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S53VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S47VA;Vrb;Vr;A3").

Lemma beg1_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2cA2A2S4aVA;Vrb;A2A3").
Proof.
  unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _ & (_ & AU0 & MU1 & _) & _ & _ & (G12 & G13 & G14 & TG) & _).
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). destruct GH as (_ & _ & _ & _ & Q224 & _).
  unfold beg1, rb_e, vMU, vSB, V_CLS, U0, region_beg, kRegionSize. cbn [eval]. rewrite !add_val, sll_val, E155, E158, Q224, !u64_lit by lia.
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma beg2_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2dA2A2S49VA;Vrb;A2A3").
Proof.
  unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _ & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rb 12%positive)))))) as NF0.
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). destruct GH as (_ & _ & Q222 & _).
  unfold beg2, fa_e2, rb_e, vMFA, vSB, V_CLS, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. cbn [eval].
  rewrite !add_val, sll_val, E155, E158, Q222, !u64_lit by lia.
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
  rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End ADDR.

Section PIECE.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S45Vst;S44A3S0S19S43A1VW;S1aS43A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S4bVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S21S4fVp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S4eVA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SfS4cVrb;R1A2S47VA;Vrb;R2A3S0S22S34Q40SdR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S37S35S60S5fVA;A1A1M0Z100000000A2VB;A2S1S37S35VB;Z40000A2S35G0Z2000000000A2A2S0S22S38VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM_c : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S48VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S36S40R2R3A2Z40000A2F_;Fmd;Ftp;").
Hypothesis HROOM_r : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S48VA;Vrb;Vtp0;Vmd0;S4dVp;U1Vph;A3R2R1A7S36S40R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable F : nat.
Variables (C0 : axst) (LX LM : leafA).
Let CX : axst := ltac2:(tb__ "0|0|
S2eS4VLX;A1Veb;A2").
Let G1 : axst := commit_post CX eb 262144.
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM eb.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.

Hypothesis R_x : ltac2:(tb__ "0|1|
S0S1dS19S3A1M0A1S5S25VF;S16S22Z706a0S1aS22A1A3VC0;S18A5S1cG0S16S3VLX;S1aS3A1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S0S17S13S2VC0;A1A1S20A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VC0;A1A1A2S18A3").
Hypothesis W_x : ltac2:(tb__ "0|0|
S0S17S11S2VCX;A1A1S18A3").
Hypothesis D_x : ltac2:(tb__ "0|4|
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2S4VLX;A1A1S2VCX;A1A2S1cG3S1eG1G2S16G0S1eS8S8S50Veb;A1Veb;A4S1aG0A1A3S1aS9A1A4A2A3").

Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VCX;A1A1A4S23S7G0S32S1fS7S52VW;A1S16S7S41S16S7S42S16S7S2aS16S7S2bS1aS7A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S57S9S51VW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCX;A1A1A2S18A3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S1dS3aA1S5cS25S14S2VCX;A1A1A2S1cS3aS3bA2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1Z11A2SbZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZaA2Veb;A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S17S15SaS2VCX;A1A1Veb;A2S18A3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZbA2SbZ40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZcA2SbZ3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZdA2SbZ32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZeA2SbZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZfA2SbZ0A1A3").

Hypothesis R_m : ltac2:(tb__ "0|1|
S0S1dS19S3A1M0A1S5S25VF;S16S22Zdb004S1aS22A1A3VG1;S18A5S1cG0S16S3VLM;S1aS3A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S17S13S2VG1;A1A1S20A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VG1;A1A1A2S18A3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VEM;A1A1A4S23S7G0S32S1fS7S52VW;A1S16S7S41S16S7S42S16S7S2aS16S7S2bS16S7S54Veb;A1S1aS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S57S9S51VW;Vst;A2SeS2VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S17S11S2VCMR;A1A1S18A3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2VEM;A1S2VCMR;A1A2S1cG3S1eG1G2S16G0S1eS8S8S62Veb;A1SbZ8000A1A4S1aG0A1A3S1aS9A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S17S11S2VCMC;A1A1S18A3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S1dS19S7A1M0A1S5eVCMC;S3cS29VCMC;A1A3S1cG0S28VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S17S5dVCMC;S3cS29VCMC;A1S28VCMC;A1S23S3S6S4S3dA4A5S18A3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S17S26S5aSaS2VCMC;A1A1A2S18A3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCMC;A1A1A2S18A3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S17S56S9S12SaS2VCMC;A1M0A1A1SeG0A1A3S18A3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S17S56S9S12SaS2S61VCMC;S29VCMC;A1S28VCMC;A1A3A1A1A1SeS2VCMC;A1A1A3S18A3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S17S5bS2fVDM;A1A1S18A3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S19S7A1S10S2VRM;A1A1M0S1fS7S24S7S58S30VDM;A1U2A2G0A3S16S7S54Veb;A1S16S7S55Veb;A1S1aS7A1A3A3A3A3").

Theorem piece_full : ltac2:(tb__ "0|1|
SfS19S33Q40A1A1M0S59SfG0VTR;S3fS25S46VA;VKc;Vrb;Vtp0;Vmd0;S4dVp;U3Vph;A3A6S31VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S3fS25S46VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x706a0] C0 [LX] ph r tp Q R_x LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LX) (ax_S CX) _ _ ph r1 tp Q W_x D_x ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    destruct HBn as (_ & _ & HB3). apply (a0_val r1 eb B (HBv r1 HFz HGh)).
    destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  change (ax_setS (la_state LX) (ax_S CX)) with CX.
  assert (HBn' : ag_spacebeg (aa_geom A) + 4294967296 <= B /\ B + 262144 <= ag_spacebeg (aa_geom A) + 137438953472 /\ B mod 4096 = 0).
  { destruct HBn as (H1 & H2 & HB3). split; [exact H1|]. split; [exact H2|].
    destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  apply (piece_commit A Kc rb tp0 md0 TR KIT HKc W st rho HW HE p eb ph PH0 PORD PQ HBv HBn' HROOM_c CX SK_x XF_x XX_x NX_x IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x r1 tp Q).
  fold G1.
  apply (piece_map A Kc rb tp0 md0 TR KIT HKc W st rho HW HE p eb (ph_set p 1 ph) (ph_get_set p 1 ph) (ph_quiet_set p 1 ph PQ) HBv HBn HROOM_r
           F G1 LM R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r r1 tp Q).
  intros r' tp'. rewrite ph_set_set. exact (HC r' tp').
Qed.
End PIECE.
End SpineMallocR11.

(* [comment removed for export] *)
Module SpineMallocR4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "ss_next"; "ss_objs"; "swf"; "eval"; "ss_facts"; "SLit"; "sprop_below"; "ss_lenient"; "DUnknown"; "cell"; "enc_bytes"; "mkObj"; "smatch"; "soff"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "ax_X"; "axst"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "cons"; "nil"; "Some"; "prod"; "app"; "option"; "false"; "pair"; "length"; "andb"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "ph_fill"; "ph_pop"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_ri"; "ph_u"; "entryR"; "frozen"; "gh_new"; "gh_nf"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "cE3b"; "O_pcm"; "F_x"; "GR"; "O_pccK"; "cE3a"; "ri_has"; "cE1"; "cE3"; "choffK"; "k_e"; "nobj"; "vK"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4"; "ph_setcnt"; "ph_setri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "sub"; "leb"; "ltb"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4.EXIT"; "O_rif"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_cache"; "class_state"; "cs_allocated_user"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "Build_machine_state"; "machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 DepotCall PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition cnt_mem (pce kk : Z) : word -> option byte := ltac2:(tb__ "0|5|
S39Q40M0A1S1cS24S39Q8M1A1M2A1L_;S28S57Vpce;S3bG0R1A2M3A2S58G3S52Vpce;Z4A2A2A2S21G2S3fG2S5aS56G3Vpce;A2A1S11U4S3aG0Vkk;A2A2S3aG1Z0A2M4A4A2S21G2G4A2X1cx2La;").
Definition msOfR (f : word -> option byte) (ms : machine_state) : machine_state := ltac2:(tb__ "0|0|
S76S7bVms;A1S79Vms;A1S7aVms;A1S7eVms;A1S7cVms;A1S78Vms;A1Vf;S7dVms;A1A8").

Definition ph_setcnt (p : phase) : phase := ltac2:(tb__ "0|0|
S30S34Vp;A1S32Vp;A1S2dVp;A1S2eVp;A1S1eS33Vp;A1A6").
Definition ph_setri (p : phase) : phase := ltac2:(tb__ "0|0|
S30S34Vp;A1S32Vp;A1S2dVp;A1S2eVp;A1S31Vp;A1S1eA6").

Section EXIT.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S66Vst;S65A3S0S1dS64A1VW;S20S64A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S35VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.
Variable phX : phase.
Hypothesis PHX : ltac2:(tb__ "0|0|
S1S0S2aS2eVphX;A1Vk;A3S1S0S1cS31VphX;A1S25A3S0S1cS33VphX;A1S25A3A2A2").
Hypothesis HFILLX : ltac2:(tb__ "0|4|
S53Z0M0S2dVphX;A1M1A2S1S51G0S38VA;Vrb;A2M2A2S1S51S54Z4S52G2S37VA;Vrb;A2M3A2A2Z20000000A2S51G1G3A2A2A2F_;").

Lemma cnt_rebase : ltac2:(tb__ "0|1|
S1aS29S5S1dS39Q40A1A1S60S0S1dS22S4S4A2M0A1S19R5A1S20G0A1A3S0S24S3A1S71S3S8S16R6A1A1R5A3S21S3S44A2A3S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6R7R5R4R3A6S2S5S5S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4eVphX;A1A6R9R1R6R5A6Lr';A2F_;F_;F_;Fw;Ftp;Fr;Fic;FX1;").
Proof.
  intros X1 ic r tp w HXX HIC Hsp. destruct w as [tr [ms md]].
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HFz & HGh & HK' & HM & HR & HRM).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & _ & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RNc : obj_range r O_pccK = (PCE A rb, PCE A rb + 4)).
  { unfold O_pccK. rewrite obj_range_mk by lia. rewrite EB. f_equal; lia. }
  set (msf := msOfR (cnt_mem (PCE A rb) k) ms).
  exists (rho_absorb r [O_pccK] msf).
  apply (SPA_absorb_any segs (JRp phX) (JRp (ph_setcnt phX)) r X1 [O_pccK] msf tp (tr, mkCfg ms md) HXX); [| exact Hsp |].
  { intros o a [<-|[]] Ha. exists O_pccK. split; [eapply nth_error_In; exact HIC | exact Ha]. }
  cbn [w_tr w_cfg cfg_model fst snd].
  set (r' := rho_absorb r [O_pccK] msf).
  assert (INR : forall z, 0 <= z < 2 ^ 64 -> (in_ranges r [O_pccK] (Z_to_bv 64 z) <-> PCE A rb <= z < PCE A rb + 4)).
  { intros z Hz. split.
    - intros (o & [<-|[]] & Hr). rewrite RNc in Hr. cbn [fst snd] in Hr. rewrite u64_lit in Hr by lia. exact Hr.
    - intros Hr. exists O_pccK. split; [left; reflexivity|]. rewrite RNc. cbn [fst snd]. rewrite u64_lit by lia. exact Hr. }
  assert (VOUT : forall z, ~ (PCE A rb <= z < PCE A rb + 4) -> view segs (rm r') z = view segs (rm r) z).
  { intros z Hz. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold rd_of, r'. rewrite rm_absorb_out; [reflexivity|]. intros Hin. apply Hz. apply (INR z ltac:(lia)). exact Hin. }
  assert (VIN : forall j, (j < 4)%nat -> view segs (rm r') (PCE A rb + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 8 0))).
  { intros j Hj. rewrite view_in by lia. unfold rd_of, r'. rewrite rm_absorb_in by (apply (INR (PCE A rb + Z.of_nat j) ltac:(lia)); lia).
    unfold msf, msOfR, cnt_mem. cbn [ms_mem]. rewrite u64_lit by lia.
    replace ((PCE A rb <=? PCE A rb + Z.of_nat j) && (PCE A rb + Z.of_nat j <? PCE A rb + 4))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.to_nat (PCE A rb + Z.of_nat j - PCE A rb)) with j by lia. reflexivity. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r [O_pccK] msf HRM); intros o [<-|[]]; rewrite RNc; cbn [fst snd];
           pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CFx; unfold cfacts in CFx; cbn zeta in CFx; fold nv c in CFx;
           destruct CFx as (_ & _ & _ & _ & _ & _ & (_ & _ & TIx & _) & _); unfold IMG_LO, IMG_HI; rewrite PCr; lia].
  unfold rlink in HR |- *. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6). destruct PHX as (PX1 & PX2 & PX3).
  assert (ZI : forall z, zoneR A rb (ph_setcnt phX) z <-> (zoneR A rb phX z \/ PCE A rb <= z < PCE A rb + 4)).
  { intros z. unfold zoneR, ph_setcnt. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. rewrite PX2. fold nv c. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; left; exact H.
      + right. exact (proj2 H).
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + destruct H as [H _]. discriminate H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; right; left. split; [reflexivity | exact H]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite VOUT by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec (PCE A rb) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 4)) as [H2|H2]|].
    + replace z with (PCE A rb + Z.of_nat (Z.to_nat (z - PCE A rb))) by lia. rewrite VIN by lia. discriminate.
    + rewrite VOUT by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite VOUT by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill ph_setcnt] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply VOUT.
    destruct (HFILLX ltac:(lia)) as (F1 & F2 & F3). rewrite PCr. change (Z.of_nat 4) with 4 in Hz.
    unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop ph_setcnt] in Hi'. eapply cell_ok_agree_range; [|exact (L4 i' Hi')]. cbn [c_addr c_w]. intros z Hz. apply VOUT. lia.
  - intros _. intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold nv c k. apply VIN. exact Hj.
  - intros X. cbn [ph_ri ph_setcnt] in X. rewrite PX3 in X. discriminate X.
Qed.

Hypothesis Hini : aa_cache_inited A = true.
Variables e16 e24 e32 e48 : sv.
Hypothesis HRIv : ltac2:(tb__ "0|2|
S5S36Vrb;R1A2S2fVA;Vrb;R2A3S5bVc;S5cVA;Vnv;A2A2S68S1S0S39Q40M0A1M1SaR4Ve16;A2S3aG0S55S27S2aS6aR1A1A2A1A2A3S1S0G1SaR4Ve24;A2S3aG0S6bR1A1A2A3S1S0G1SaR4Ve32;A2S3aG0S69R1A1A2A3S0G1SaR4Ve48;A2S3aG0S6cR1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Definition O_rif (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S12S4dScZ0A1ScZ80A1Vcells;SfA5").

Lemma ri_release : ltac2:(tb__ "0|4|
S15S1dS3A1M0S1dS10A1S5S1dS39Q40A1A1S1dS5fA1M1S77S5eS5eS0G0S8R9A1S23S3R8S1fS3S41S1fS3S5dR7A1S20S3A1M2A3A3A3A3S0S1cS46R8Ve16;Ve24;Ve32;Ve48;A5S1eA3S13S2bR8RbS26G1S7fR6S80R5R4A2A4A4S2cVA;VKc;Vrb;Vtp0;Vmd0;S4eVphX;A1M3R9R8R7R4AaS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fG3A1S82RaS1fS3S41S1fS3S5dRbA1G2A3A3R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fcells;FK;FS;").
Proof.
  intros S K cells r tp tr ms md mdJ HO HRI Hsm (HFz & HGh & HK' & HM & HR & HRM).
  set (R := [O_pcm; O_rif cells]). set (r3 := rho_absorb r R ms).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _ & _ & RNm & RNr). cbn zeta in RNr. fold nv c in RNr.
  destruct (entry_pc_cells _ _ _ _ _ _ _ HE Hini) as (D2 & _ & _). cbn zeta in D2. fold nv c in D2.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & _ & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (ri := region_info (ag_spacebeg (aa_geom A)) c) in *.
  assert (RIr : ag_spacebeg (aa_geom A) + 137438953472 <= ri /\ ri + 128 <= ag_spacebeg (aa_geom A) + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. lia. }
  assert (RNf : obj_range r (O_rif cells) = (ri, ri + 128)).
  { rewrite <- RNr. apply obj_range_skel. reflexivity. }
  pose proof HGh as (Q220 & _ & _ & _ & _ & Q225 & _). fold nv c in Q220. fold nv c ri in Q225.
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  unfold rlink in HR. fold m in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6). destruct PHX as (PX1 & PX2 & PX3).

  assert (NZm : forall z, PCE A rb + 4 <= z < PCE A rb + 8 -> ~ zoneR A rb (ph_setcnt phX) z).
  { intros z Hz HZ.
    destruct (zone_thread_gen A rb (ph_setcnt phX) z (entry_cfacts _ _ _ _ _ _ _ HE) HFILLX ltac:(rewrite PCr in Hz; lia) HZ) as [X|[_ X]]; cbn [ph_pop ph_setcnt] in X; lia. }
  assert (M3m : forall j, (j < 4)%nat -> m3 (PCE A rb + 4 + Z.of_nat j) = m (PCE A rb + 4 + Z.of_nat j)).
  { intros j Hj. rewrite (L1 (PCE A rb + 4 + Z.of_nat j) (NZm (PCE A rb + 4 + Z.of_nat j) ltac:(lia))). specialize (D2 j Hj). cbn [c_addr c_w RtCells.c_val] in D2. rewrite D2.
    destruct (absorb_obj r S tr ms md K R O_pcm Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 4) 4 vMC) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_pcm c_off SymState.c_val c_width] in ASb. rewrite EB, soff_lit_small in ASb by lia. unfold vMC in ASb. cbn [eval] in ASb. rewrite Q220 in ASb.
    unfold m3. rewrite view_in by lia. exact ASb. }
  assert (AGR : forall z, ~ (ri <= z < ri + 128) -> m3 z = m z).
  { intros z Hz. destruct (Z_le_dec (PCE A rb + 4) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 8)) as [H2|H2]|].
    - replace z with (PCE A rb + 4 + Z.of_nat (Z.to_nat (z - (PCE A rb + 4)))) by lia. apply M3m. lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd]; lia. }
  idtac "rr:1".
  destruct (absorb_obj r S tr ms md K R (O_rif cells) Hsm HO (or_intror (or_introl eq_refl))) as (_ & ASc & ASp & _).
  cbn [ob_base O_rif ob_cells ob_dflt] in ASc, ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_rif] in ASp. rewrite !soff_lit_small in ASp by lia.
  assert (ERI : bv_unsigned (eval r vRI) = ri) by (unfold vRI; cbn [eval]; rewrite Q225; apply u64_lit; lia).
  rewrite ERI in ASc, ASp.
  assert (RC : forall off (w : nat) e val, In (mkCell (SLit off) (Z.of_nat w) e) cells -> 0 <= off -> off + Z.of_nat w <= 128 -> eval r e = Z_to_bv 64 val ->
            cell_ok m3 (mkACell (ri + off) w val)).
  { intros off w e val Hin Ho1 Ho2 Ee j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (ASc _ Hin) as (_ & _ & ASb). cbn [c_off SymState.c_val c_width] in ASb. rewrite Nat2Z.id, soff_lit_small, Ee in ASb by lia.
    unfold m3. rewrite view_in by lia. exact (ASb j Hj). }
  assert (INC : forall cc, In cc [mkCell (SLit 0) 8 (SLit 0); mkCell (SLit 16) 8 e16; mkCell (SLit 24) 8 e24; mkCell (SLit 32) 8 e32; mkCell (SLit 40) 8 (SLit 0);
                               mkCell (SLit 48) 8 e48; mkCell (SLit 56) 8 (SLit 0); mkCell (SLit 68) 1 (SLit 0)] -> In cc cells).
  { intros cc Hcc. unfold ri_has in HRI. pose proof (proj1 (forallb_forall _ _) HRI cc Hcc) as X. apply existsb_exists in X as (c' & Hin & E).
    apply cell_eqb_sound in E. subst c'. exact Hin. }
  destruct (HRIv r HFz HGh) as (V16 & V24 & V32 & V48). cbn zeta in V16, V24, V32, V48.
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r R ms HRM); intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd];
           pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CFx; unfold cfacts in CFx; cbn zeta in CFx; fold nv c in CFx;
           destruct CFx as (_ & _ & _ & _ & _ & _ & (_ & _ & TIx & _) & _); unfold IMG_LO, IMG_HI; rewrite ?PCr; lia].
  fold r3 m3. unfold rlink.
  assert (ZI : forall z, zoneR A rb (ph_setri (ph_setcnt phX)) z <-> (zoneR A rb (ph_setcnt phX) z \/ ri <= z < ri + 128)).
  { intros z. unfold zoneR, ph_setri, ph_setcnt. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. rewrite PX3. fold nv c ri. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; left; exact H.
      + right. exact (proj2 H).
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + destruct H as [H _]. discriminate H.
      + right; right; right; right; right; right; right. split; [reflexivity | exact H]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec ri z) as [H1|H1]; [destruct (Z_lt_dec z (ri + 128)) as [H2|H2]|].
    + destruct (ASp (or_introl eq_refl) (z - ri) ltac:(lia)) as [x Hx]. replace (ri + (z - ri)) with z in Hx by lia.
      unfold m3, r3. rewrite view_in by lia. rewrite Hx. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill ph_setri ph_setcnt] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLX ltac:(lia)) as (F1 & F2 & F3). change (Z.of_nat 4) with 4 in Hz.
    unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
    clear -Hz C1 RIr Hj F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop ph_setri ph_setcnt] in Hi'. eapply cell_ok_agree_range; [|exact (L4 i' Hi')]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    change (Z.of_nat 4) with 4 in Hz. rewrite PX1 in Hi'. rewrite PCr in Hz. clear -Hz Hi' K1 C1 RIr PS1 T1 T2 G13 G14 TG. lia.
  - intros X. eapply cell_ok_agree_range; [|exact (L5 eq_refl)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    change (Z.of_nat 4) with 4 in Hz. rewrite PCr in Hz. clear -Hz C1 RIr PS1 T1 T2 G13 G14 TG. lia.
  - intros _. cbn zeta. fold nv c ri. unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    split; [apply (RC 0 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    split; [apply (RC 16 8%nat e16); [apply INC; cbn; tauto | lia | cbn; lia | exact V16]|].
    split; [apply (RC 24 8%nat e24); [apply INC; cbn; tauto | lia | cbn; lia | exact V24]|].
    split; [apply (RC 32 8%nat e32); [apply INC; cbn; tauto | lia | cbn; lia | exact V32]|].
    split; [apply (RC 40 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    split; [apply (RC 48 8%nat e48); [apply INC; cbn; tauto | lia | cbn; lia | exact V48]|].
    split; [apply (RC 56 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    apply (RC 68 1%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity].
Qed.

Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S2aS55S27S2aS67S5bVc;S5cVA;Vnv;A2A2A1A2A1Vk;A3").
Hypothesis HIDC : ltac2:(tb__ "0|0|
S2aS72S2aR1S67S5bVc;S5cVA;Vnv;A2A2A1A3S1S51Z0R2A2S53R2S59Z2Z1cA2A2A2F_;Fx;").
Notation phF := (ph_setri (ph_setcnt phX)).

Lemma choffK_val : ltac2:(tb__ "0|0|
S5S2fVA;Vrb;R1A3S0S2aS14R2S49A2S52Z10S54Z4S56Vk;Z1A2A2A2A3F_;Fr;").
Proof.
  intros r HGh. destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1.
  set (kk := k) in *. clearbody kk.
  unfold choffK, vK. rewrite soff_snorm. unfold U. cbn [eval]. rewrite Q227. clear -K1. rewrite add_val, sll_val, add_val. rewrite (u64_lit kk), (u64_lit 16) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
  replace ((kk + (2 ^ 64 - 1)) mod 2 ^ 64) with (kk - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
  unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((kk - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia.
Qed.

Lemma exit_carve : ltac2:(tb__ "0|4|
S1aS5S1dS39Q40A1A1S60S0S1dS22S22S4S4A2M0S4A2M1A1S3dS3G1S50S8S16R4A1A1A4S3dS3G1S50S23S3S6eVW;A1S1fS3S62S1fS3S63S20S3A1A3A3A3A4A3S0S1dG0A1S19R5A1S20G0A1A3S70S6S6dVW;Vst;A2SbS16R6A1A1A3S0S1cS9S16S45R7A1A1A1S1eA3S0S1cS9S16S40R8A1A1A1S1eA3S0S1cS6fS6SdS7S16S40R9A1A1M2A1A1S23S6S42SbG2A1A3A3S1eA3S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fS4eVphX;A1A1A6M3RaR9R8R7A6S3cS2bG3S48RbA1RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fr;FX2;").
Proof.
  intros X2 r tp w SK2 XX2 XF2 W3a W3b FB3 H.
  pose proof H as [HsmA (HFz & HGh & _ & _ & HR & _)].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & _ & _). cbn zeta in RNs.
  destruct (entry_pc_cells _ _ _ _ _ _ _ HE Hini) as (_ & D3 & PE0). cbn zeta in D3, PE0. fold nv c in D3.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S X2) [O_pcc0; O_st] r _ HW HE HFz Hsm SK2 XF2) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  pose proof CF0 as CF1. unfold cfacts in CF1. cbn zeta in CF1. fold nv c in CF1.
  destruct CF1 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & TI & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  destruct PHX as (PX1 & PX2 & PX3).
  set (m := view segs (rm r)) in *. unfold rlink in HR. fold m in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as (_ & E148 & _). fold nv c in E148.
  pose proof HGh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q229).

  assert (NZ : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> ~ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k) -> ~ zoneR A rb phF z).
  { intros z Hz Hn HZ.
    destruct (zone_thread_gen A rb phF z CF0 HFILLX ltac:(rewrite PCr in Hz; lia) HZ) as [X|[_ X]]; cbn [ph_pop ph_setri ph_setcnt] in X; lia. }
  assert (PRE : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> exists b, m z = Some b).
  { intros z Hz. destruct (Z_le_dec (PCE A rb + 16) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 16 + 4 * k)) as [H2|H2]|].
    - assert (HZ : zoneR A rb phF z) by (unfold zoneR; cbn [ph_pop ph_setri ph_setcnt]; rewrite PX1; fold nv c k; do 5 right; left; lia).
      specialize (L2 z HZ). destruct (m z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z (NZ z Hz ltac:(lia))). apply PE0. lia.
    - rewrite (L1 z (NZ z Hz ltac:(lia))). apply PE0. lia. }
  assert (WR : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> wok_of segs (rm r) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r) (Z_to_bv 64 z) = Some x).
  { intros z Hz. destruct (PRE z Hz) as [b Hb]. unfold m in Hb. rewrite view_in in Hb by lia. eapply wok_rd_off_image2; [| |exact Hb]; lia. }
  idtac "xc:1".

  assert (Ha : SPA segs (JRp phF) (cE3a X2) r tp w).
  { unfold cE3a, addobjs, nxt.
    apply (SPA_carve_gen segs _ r X2 tp w pc_base 8 16 [mkCell (SLit 8) 8 (SVar V_SIZE)] (ss_next (ax_S X2)) H W3a (Pos.le_refl _)); rewrite ?EB; try lia.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val]; rewrite ?soff_lit_small by lia; lia.
    - rewrite EO. apply Forall_app. split; [apply BZ; left; rewrite PCr; lia|].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; lia.
    - intros off Hoff. apply WR. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. cbn [eval]. unfold V_SIZE. rewrite E148. specialize (D3 j Hj). cbn [c_addr c_w RtCells.c_val] in D3.
      rewrite <- (L1 _ (NZ (PCE A rb + 8 + Z.of_nat j) ltac:(cbn in Hj; lia) ltac:(cbn in Hj; lia))) in D3. unfold m in D3. rewrite view_in in D3 by (cbn in Hj; lia). exact D3.
    - unfold xwords_clear. rewrite XX2. intros rr y j []. }
  idtac "xc:2".

  pose proof (choffK_val r HGh) as ECH.
  assert (OBa : ss_objs (ax_S (cE3a X2)) = ss_objs (ax_S X2) ++ [O_pcs]) by reflexivity.
  assert (Hb : SPA segs (JRp phF) (cE3b X2) r tp w).
  { unfold cE3b, addobjs, nxt.
    apply (SPA_carve_gsym segs _ r (cE3a X2) tp w pc_base choffK (SLit 80) [mkCell choffK 4 vCHX] (ss_next (ax_S X2)) Ha W3b (Pos.le_refl _)); rewrite ?EB, ?ECH, ?soff_lit_small by lia; try lia.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val]; rewrite ?ECH; lia.
    - rewrite OBa, EO. apply Forall_app. split; [apply Forall_app; split|].
      + apply BZ. left. rewrite PCr. lia.
      + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; lia.
      + repeat apply Forall_cons; try apply Forall_nil. unfold O_pcs. rewrite obj_range_mk by lia. rewrite EB. unfold ranges_disjoint; cbn [fst snd]. lia.
    - intros off Hoff. replace (PCE A rb + off) with (PCE A rb + off) by lia. apply WR. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?ECH.
      intros j Hj. unfold vCHX. cbn [eval]. rewrite Q229.
      pose proof (L4 (k - 1) ltac:(cbn [ph_pop ph_setri ph_setcnt]; rewrite PX1; lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
      unfold m in Hc. rewrite view_in in Hc by (cbn in Hj; lia).
      replace (PCE A rb + (16 + 4 * (k - 1)) + Z.of_nat j) with (PCE A rb + 16 + 4 * (k - 1) + Z.of_nat j) by lia. rewrite Hc. do 3 f_equal.
      unfold gh_chx. fold nv c. replace (Z.to_nat (k - 1)) with (length (cs_cache (refill_cs c (cst_of A nv))) - 1)%nat by (clear -HLEN K1; lia). reflexivity.
    - unfold xwords_clear. cbn [ax_X cE3a addobjs ax_setS]. rewrite XX2. intros rr y j []. }
  idtac "xc:3".

  unfold cE3. apply (SPA_refacts segs _ r (cE3b X2) _ tp w Hb FB3).
  intros HF0. apply Forall_app. split; [|exact HF0].
  unfold F_x, vCHX. repeat apply Forall_cons; try apply Forall_nil. cbn [holds eval]. rewrite Q229.
  assert (Hg : 0 <= gh_chx A rb < 2 ^ 28).
  { apply HIDC. unfold gh_chx. fold nv c. apply nth_In. lia. }
  rewrite !u64_lit by lia. lia.
Qed.

Variable F : nat.
Variable XL : axst.
Variables L9 LZ : leafA.
Variable ic : nat.
Variable cells_f : list cell.
Let X1 : axst := ltac2:(tb__ "0|0|
S47S18VL9;A1Vic;A2").
Let X2 : axst := cE2 X1.
Let X3 : axst := cE3 X2.
Hypothesis R_9 : ltac2:(tb__ "0|1|
S0S24S1dS17A1M0A1S1bS2bVF;S1fS2aZ40e5cS20S2aA1A3VXL;S1eA5S21G0S1fS17VL9;S20S17A1A3A2A3").
Hypothesis LN_9 : ltac2:(tb__ "0|0|
S0S1cSeS16VXL;A1A1S25A3").
Hypothesis NX_9 : ltac2:(tb__ "0|0|
S0S1cS73S43S7S16VXL;A1A1A2S1eA3").
Hypothesis W_x1 : ltac2:(tb__ "0|0|
S0S1cS9S16VX1;A1A1S1eA3").
Hypothesis D_x1 : ltac2:(tb__ "0|4|
S0S24S22S1dS22S4S4A2M0A1M1S1dS6A1M2A2M3A1S81S16S18VL9;A1A1S16VX1;A1A2S21G3S26G1G2S1fG0S26S4S4S4aS4cA4S20G0A1A3S20S6A1A4A2A3").
Hypothesis NX_x1 : ltac2:(tb__ "0|0|
S0S1cS74S7S16VX1;A1A1S7S16S18VL9;A1A1A1A2S1eA3").
Hypothesis XX_1 : ax_X X1 = [].
Hypothesis IC_1 : ltac2:(tb__ "0|0|
S0S24S3A1S71S3S8S16VX1;A1A1Vic;A3S21S3S44A2A3").
Hypothesis OB_1 : ltac2:(tb__ "0|1|
S0S1dS3A1S8S16VX1;A1A1M0S23S3S3eS3S75S4bVX1;A1U2A2G0A3S1fS3S41S1fS3S5dVcells_f;A1S20S3A1A3A3A3A3").
Hypothesis RI_1 : ltac2:(tb__ "0|0|
S0S1cS46Vcells_f;Ve16;Ve24;Ve32;Ve48;A5S1eA3").
Hypothesis SK_2 : ltac2:(tb__ "0|1|
S0S1dS22S22S4S4A2S4A2M0A1S3dS3G0S50S8S16VX2;A1A1A4S3dS3G0S50S23S3S6eVW;A1S1fS3S62S1fS3S63S20S3A1A3A3A3A4A3").
Hypothesis XX_2 : ax_X X2 = [].
Hypothesis XF_2 : ltac2:(tb__ "0|0|
S70S6S6dVW;Vst;A2SbS16VX2;A1A1A3").
Hypothesis W_3a : ltac2:(tb__ "0|0|
S0S1cS9S16S45VX2;A1A1A1S1eA3").
Hypothesis W_3b : ltac2:(tb__ "0|0|
S0S1cS9S16S40VX2;A1A1A1S1eA3").
Hypothesis FB_3 : ltac2:(tb__ "0|1|
S0S1cS6fS6SdS7S16S40VX2;A1A1M0A1A1S23S6S42SbG0A1A3A3S1eA3").
Hypothesis R_z : ltac2:(tb__ "0|1|
S0S24S1dS17A1M0A1S1bS2bVF;S1fS2aZ3c614S20S2aA1A3VX3;S1eA5S21G0S1fS17VLZ;S20S17A1A3A2A3").
Hypothesis LN_z : ltac2:(tb__ "0|0|
S0S1cSeS16VX3;A1A1S25A3").
Hypothesis NX_z : ltac2:(tb__ "0|0|
S0S1cS73S43S7S16VX3;A1A1A2S1eA3").

Lemma exit_steps : ltac2:(tb__ "0|0|
S5S1dS39Q40A1A1S61S5VTR;S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fS4eVphX;A1A1A6S18VLZ;A1R1R3A5R2A2Fr';VTR;S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HZ.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x40e5c] XL [L9] phX r tp Q R_9 LN_9 NX_9).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L9) (ax_S X1) _ _ phX r1 tp Q W_x1 D_x1 NX_x1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    pose proof (r1_diffs A rb r1 (entry_cfacts _ _ _ _ _ _ _ HE) (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh) as D.
    unfold diffs_ok in *. apply Forall_cons; [|apply Forall_nil]. exact (Forall_inv (Forall_inv_tail D)). }
  change (ax_setS (la_state L9) (ax_S X1)) with X1.
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JRp (ph_setcnt phX)) X1 r2 tp) Q (fun w Hw => cnt_rebase X1 ic r1 tp w XX_1 IC_1 Hw)).
  intros r2.
  apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRp phF) X2 r3 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r2 [O_pcm; O_rif cells_f] (vms md tp ms)).
    apply (SPA_unobj_J (JRp (ph_setcnt phX)) (JRp phF) r2 X1 _ [O_pcm; O_rif cells_f] tp tr ms md OB_1 Hw).
    intros Hsm HJ. exact (ri_release (ax_S X1) _ cells_f r2 tp tr (vms md tp ms) (vmd md) md OB_1 RI_1 Hsm HJ). }
  intros r3.
  apply (tr_pre Kc TR KIT (SPA segs (JRp phF) X3 r3 tp)); [intros w Hw; exact (exit_carve X2 r3 tp w SK_2 XX_2 XF_2 W_3a W_3b FB_3 Hw)|].
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3c614] X3 [LZ] phF r3 tp Q R_z LN_z NX_z).
  intros L r4 [<-|[]] _. apply HZ.
Qed.
End EXIT.
End SpineMallocR4.

(* [comment removed for export] *)
Module SpineMallocSec3IE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S1cA1A1A2S1A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S15S1dSeS10S1bA1A1A2A1A1A2S1A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S1cZ1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S20G0G1A3G2A3A6S1A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S15S1dSeS10S1bA1A1A2Z1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S21G0G1A3G2A3A6S1A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_0h : ltac2:(tb__ "0|6|
S18S24SbS12Q40M0A1M1S4G1A1M2S14OF_;S1aVW;Vst;A2S25R6A1S28S1S11G0R5A2S19S11G0SdR6PcM3A2A2A1A3SbSbG2S29S11G0R9A2S19S11G0SdRaG3A2A2A1RaR3A4S13S8S16S8S26U0M4Vst;S1eS18R1LX;M5RdRcR4RaA8S1fR3R2A5R8A3F_;FtpY;FrhoY;Frho';SbS13S8S16S8S27G4Vst;S1eG5RbRaR9R8A8S23VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 0%nat) (st := st) (tmax := tmax) (hi := true) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
    (AX := fun X : AA => X) (AXg := fun X => eq_refl) (AXb := fun X => eq_refl)
    (E0 := E0c) (T0 := T0c) (SKT := SKT_0) (FCT := FCT_0) (AF0 := AF0_0)
    (ET1 := ET1c) (CT1 := CT1c) (CO1 := CO1c) (T1 := T1c) (ET2 := ET2c) (CT2 := CT2c) (CO2 := CO2c) (T2 := T2c) (s1 := s1c) (s2 := s2c) (R1 := R1c) (R2 := R2c)
    (NXT0 := NXT0_0) (NXD1 := NXD1_0) (ECert1 := ECert1_0) (ECert2 := ECert2_0)
    (WC1 := WC1_0) (DF1 := DF1_0) (NX1 := NX1_0) (HC1 := HC1_0) (SK1 := SK1_0) (FC1 := FC1_0) (XC1 := XC1_0) (HCO1 := HCO1_0) (WCO1 := WCO1_0)
    (He1 := He1_0) (Hchk1 := Hchk1_0) (HT1 := HT1_0) (FBC1 := FBC1_0) (FBT1 := FBT1_0) (NXC1 := NXC1_0)
    (WC2 := WC2_0) (DF2 := DF2_0) (NX2 := NX2_0) (HC2 := HC2_0) (SK2 := SK2_0) (FC2 := FC2_0) (XC2 := XC2_0) (HCO2 := HCO2_0) (WCO2 := WCO2_0)
    (He2 := He2_0) (Hchk2 := Hchk2_0) (HT2 := HT2_0) (FBC2 := FBC2_0) (FBT2 := FBT2_0) (NXC2 := NXC2_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineMallocSec3IE.

(* [comment removed for export] *)
Module SpineMallocSec3IEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S1dA1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S16S1eSfS11S1cA1A1A2A1A1A2S3A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S1dZ1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S21G0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S16S1eSfS11S1cA1A1A2Z1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S22G0G1A3G2A3A6S3A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_0l : ltac2:(tb__ "0|6|
S19S25ScS13Q40M0A1M1S5G1A1M2S15OF_;S1bVW;Vst;A2S26R6A1S29S4S12G0R5A2S1aS12G0SeR6PcM3A2A2A1A3ScScG2S2aS12G0R9A2S1aS12G0SeRaG3A2A2A1RaR3A4S14S9S17S9S27U0M4Vst;S1fS19R1LX;M5RdRcR4RaA8S20R3R2A5R8A3F_;FtpY;FrhoY;Frho';ScS14S9S17S9S28G4Vst;S1fG5RbRaR9R8A8S24VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 0%nat) (st := st) (tmax := tmax) (hi := false) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
    (AX := fun X : AA => X) (AXg := fun X => eq_refl) (AXb := fun X => eq_refl)
    (E0 := E0c) (T0 := T0c) (SKT := SKT_0) (FCT := FCT_0) (AF0 := AF0_0)
    (ET1 := ET1c) (CT1 := CT1c) (CO1 := CO1c) (T1 := T1c) (ET2 := ET2c) (CT2 := CT2c) (CO2 := CO2c) (T2 := T2c) (s1 := s1c) (s2 := s2c) (R1 := R1c) (R2 := R2c)
    (NXT0 := NXT0_0) (NXD1 := NXD1_0) (ECert1 := ECert1_0) (ECert2 := ECert2_0)
    (WC1 := WC1_0) (DF1 := DF1_0) (NX1 := NX1_0) (HC1 := HC1_0) (SK1 := SK1_0) (FC1 := FC1_0) (XC1 := XC1_0) (HCO1 := HCO1_0) (WCO1 := WCO1_0)
    (He1 := He1_0) (Hchk1 := Hchk1_0) (HT1 := HT1_0) (FBC1 := FBC1_0) (FBT1 := FBT1_0) (NXC1 := NXC1_0)
    (WC2 := WC2_0) (DF2 := DF2_0) (NX2 := NX2_0) (HC2 := HC2_0) (SK2 := SK2_0) (FC2 := FC2_0) (XC2 := XC2_0) (HCO2 := HCO2_0) (WCO2 := WCO2_0)
    (He2 := He2_0) (Hchk2 := Hchk2_0) (HT2 := HT2_0) (FBC2 := FBC2_0) (FBT2 := FBT2_0) (NXC2 := NXC2_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineMallocSec3IEL.

(* [comment removed for export] *)
Module SpineMallocSec3IELW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S1dA1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S16S1eSfS11S1cA1A1A2A1A1A2S3A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S1dZ1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S21G0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S16S1eSfS11S1cA1A1A2Z1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S22G0G1A3G2A3A6S3A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_2l : ltac2:(tb__ "0|6|
S19S25ScS13Q40M0A1M1S5G1A1M2S15OF_;S1bVW;Vst;A2S26R6A1S29S4S12G0R5A2S1aS12G0SeR6PcM3A2A2A1A3ScScG2S2aS12G0R9A2S1aS12G0SeRaG3A2A2A1RaR3A4S14S9S17S9S27U2M4Vst;S1fS19R1LX;M5RdRcR4RaA8S20R3R2A5R8A3F_;FtpY;FrhoY;Frho';ScS14S9S17S9S28G4Vst;S1fG5RbRaR9R8A8S24VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 2%nat) (st := st) (tmax := tmax) (hi := false) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
    (AX := fun X : AA => X) (AXg := fun X => eq_refl) (AXb := fun X => eq_refl)
    (E0 := E0c) (T0 := T0c) (SKT := SKT_0) (FCT := FCT_0) (AF0 := AF0_0)
    (ET1 := ET1c) (CT1 := CT1c) (CO1 := CO1c) (T1 := T1c) (ET2 := ET2c) (CT2 := CT2c) (CO2 := CO2c) (T2 := T2c) (s1 := s1c) (s2 := s2c) (R1 := R1c) (R2 := R2c)
    (NXT0 := NXT0_0) (NXD1 := NXD1_0) (ECert1 := ECert1_0) (ECert2 := ECert2_0)
    (WC1 := WC1_0) (DF1 := DF1_0) (NX1 := NX1_0) (HC1 := HC1_0) (SK1 := SK1_0) (FC1 := FC1_0) (XC1 := XC1_0) (HCO1 := HCO1_0) (WCO1 := WCO1_0)
    (He1 := He1_0) (Hchk1 := Hchk1_0) (HT1 := HT1_0) (FBC1 := FBC1_0) (FBT1 := FBT1_0) (NXC1 := NXC1_0)
    (WC2 := WC2_0) (DF2 := DF2_0) (NX2 := NX2_0) (HC2 := HC2_0) (SK2 := SK2_0) (FC2 := FC2_0) (XC2 := XC2_0) (HCO2 := HCO2_0) (WCO2 := WCO2_0)
    (He2 := He2_0) (Hchk2 := Hchk2_0) (HT2 := HT2_0) (FBC2 := FBC2_0) (FBT2 := FBT2_0) (NXC2 := NXC2_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineMallocSec3IELW2.

