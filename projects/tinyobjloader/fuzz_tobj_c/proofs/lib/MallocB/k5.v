(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall jq k1.

(* [comment removed for export] *)
Module CDepotCallS.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "pow"; "ltb"; "mul"; "opp"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "rw"; "SVar"; "SLit"; "sprop"; "ss_next"; "sstate"; "ss_facts"; "sv_eqb"; "ob_base"; "ob_hi"; "ob_lo"; "cell"; "obj_range"; "ss_objs"; "soff"; "holds"; "sprop_below"; "SAlu"; "SPUle"; "mkObj"; "rl"; "rm"; "DZero"; "SExt"; "c_off"; "eval"; "mkSS"; "ob_cells"; "ob_dflt"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "cons"; "pair"; "true"; "list"; "false"; "prod"; "S"; "nil"; "option"; "andb"; "fst"; "snd"; "orb"; "Some"; "app"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_depot"; "aa_geom"; "DG"; "ag_pab"; "ageom"; "aa_Km"; "ag_ctx"; "ag_thread"; "budget_ok_alloc"; "topG"; "aa_Kf"; "aa_V"; "aa_live"; "depot_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "WI"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "coveredbL"; "hi_lebL"; "lo_gebL"; "T5d"; "call_cellS"; "cov_exact"; "cov_itv"; "havS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"; "nocells"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "lt"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "V_DEPTH"; "malloc_depth"; "unwind_objs"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "isSome"; "rstS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS.DCS"; "site_factsS"; "AXK"; "dlink"; "zoneS"; "MAPO"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "JLD"; "DFP"; "JD"; "MAP1"; "MAP1N"; "STORE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP"; "KDP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Lists.ListDef"; "Forall";
"seq"; "firstn"; "skipn"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "import_okPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "omrg"; "osplit"; "lit63"; "oreb"; "F_call"; "rt_okD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sitv"; "set_objs"; "snorm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "bumpK"; "with_depot"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "LIVE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "DPRET"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl"; "sobjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition WI : nat := 2.
Definition X5f (X : axst) : axst := ax_add_facts F_call X.
Definition X5r (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|1|
S94S6eVX;A1S38S3dS37S10A2M0S39S37S10UbS15Vsz;A1A4S3fG0A1A3S3fS16A1A3").
Definition X5a (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S62VX;Vsz;A2S61S15Nf10A1A3").
Definition X5b (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S6bVX;Vsz;A2S3eS61A1S15N910A1A3").
Definition X5c (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S6cVX;Vsz;A2S3eS3eS61A1A1S15N848A1A3").
Definition X5s (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S6dVX;Vsz;A2S3eS3eS3eS61A1A1A1S15N50A1A3").

Definition T50 (T X : axst) : axst := ltac2:(tb__ "0|0|
SdeVT;S19S49VX;A1A1A2").
Definition T5a (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S64VT;VX;A2U0A2").
Definition T5b (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S65VT;VX;A2U1A2").
Definition permS (n : nat) : list nat := ltac2:(tb__ "0|1|
S46S37S38S37U9S38S37UaS38S37UbS38S37U0S38S37UcS38S37U1S38S37UdS38S37U2S38S37U3S38S37U4S38S37U5S38S37U6S38S37U7S38S37U8S3fS37A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb3UeM0Sd9Vn;G0A2A2A3").
Definition T5c (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|2|
S4cS66VT;VX;A2M0Sd1S49G0A1M1SddS20G1A1S63Vn;A1A2A2A2").
Definition T5m1 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S67Vn;VT;VX;A3S61A2").
Definition T5m2 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S68Vn;VT;VX;A3S61A2").
Definition T5m3 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S69Vn;VT;VX;A3S61A2").
Definition T5d (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S6aVn;VT;VX;A3S61A2").

Definition havS (n : positive) : list (nat * sv) := ltac2:(tb__ "0|1|
S38S3dS37S10A2M0S39S37S10UaS14Vn;A1A4S38G0S39S37S10U1S15Se1A1A4S38G0S39S37S10U5S14S7aVn;P1A2A1A4S38G0S39S37S10U6S14S7aVn;P2A2A1A4S38G0S39S37S10U7S14S7aVn;P3A2A1A4S38G0S39S37S10UbS14S7aVn;P4A2A1A4S38G0S39S37S10UcS14S7aVn;P5A2A1A4S38G0S39S37S10UdS14S7aVn;P6A2A1A4S38G0S39S37S10UeS14S7aVn;P7A2A1A4S38G0S39S37S10UfS14S7aVn;P8A2A1A4S38G0S39S37S10U10S14S7aVn;P9A2A1A4S38G0S39S37S10U11S14S7aVn;PaA2A1A4S38G0S39S37S10U1cS14S7aVn;PbA2A1A4S38G0S39S37S10U1dS14S7aVn;PcA2A1A4S38G0S39S37S10U1eS14S7aVn;PdA2A1A4S38G0S39S37S10U1fS14S7aVn;PeA2A1A4S3fG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition call_cellS (c : cell) : bool := ltac2:(tb__ "0|4|
S10S36Lx;S2bVc;A1S0S41S6Se0Sd2R1A1M0A2S48S41S6N848G0A2S8G0N50A2A2A1A2Lz;S1S3aLi;Sb6S10S10S3aLb;La;M1Lop;M2G2Sb7G1Lop;M3G3S36S2S10S3aLa;Lw;Lsgn;S1S10S0S3aLk;Li;Ll;X10x8").
Definition C5S (X : axst) : axst := ltac2:(tb__ "0|3|
S49VX;A1S18S40S12A1S4aLx;S8aS12S20R1A1S61A3S12S4cVX;S2dZ7ec58SdaS33R2A1S76S17R2A1M0A1A2S31R2A1S30R2A1S34R2A1S46S12Sb4S12S61S20R2A1M1A3S38S12S26S1bR1A1S1dR1A1S1cR1A1SeaS1eS3bS1eA1SecS1eA1S1eSe9S73R1A1M2A1Lc;S1eSebG2A1Lx;S2eR1A1A6S2fR1A1A5Sb5S12S3eS61A1G1A3A3A3S19R2A1S7aG0PfA2S32R2A1A9A2Lo;VX;X40x2TS0;").

Definition lo_gebL (facts : list sprop) (l l' : sv) : bool := ltac2:(tb__ "0|5|
S36S36L_;M0S1aVl;Vl';A2S3aS10S36Ll;Vl;S0G0Sc7R1A1S40S3dS0S0A2M1A1S36Lx;Sd0Vfacts;Vl';A2G1G1S36Lp;R1S0S0S6R1R4A2Lh';Lz;X3dx1Lp;S3cX40x2S3cX36x2La;S1S3cLi;Sb6S10S10S3cLb;La;M2Lop;M3G3Sb7G2Lop;M4G4S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll0;X10x8X36x2").
Definition hi_lebL (facts : list sprop) (h h' : sv) : bool := ltac2:(tb__ "0|5|
S36S36L_;M0S1aVh;Vh';A2S3aS10S36Lh;Vh;S0G0Sc7R1A1S40S3dS0S0A2M1A1S36Lx;Sd0Vfacts;Vh';A2G1G1S36Lp;R1S0S0S6R4R2A2Lz;Ll';X3dx1Lp;S3cX40x2S3cX36x2La;S1S3cLi;Sb6S10S10S3cLb;La;M2Lop;M3G3Sb7G2Lop;M4G4S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll;X10x8X36x2").
Lemma lo_gebL_sound : ltac2:(tb__ "0|0|
S11S3bS16A1S10S10Sb2S16S22R4A1R3A3ScS36S71R4R3R2A3S3aA3S3S21R6R3A2S21R6R4A2A2F_;F_;Fl';Fl;Ffacts;Frho;").
Proof.
  intros rho facts l l' HF H. apply (lo_geb_sound rho facts l l' HF). unfold lo_gebL in H. unfold lo_geb.
  destruct (sv_eqb l l'); [reflexivity|]. cbn [orb]. destruct l; try discriminate H. destruct (lit63 z); [exact H | discriminate H].
Qed.
Lemma hi_lebL_sound : ltac2:(tb__ "0|0|
S11S3bS16A1S10S10Sb2S16S22R4A1R3A3ScS36S70R4R3R2A3S3aA3S3S21R6R4A2S21R6R3A2A2F_;F_;Fh';Fh;Ffacts;Frho;").
Proof.
  intros rho facts h h' HF H. apply (hi_leb_sound rho facts h h' HF). unfold hi_lebL in H. unfold hi_leb.
  destruct (sv_eqb h h'); [reflexivity|]. cbn [orb]. destruct h; try discriminate H. destruct (lit63 z); [exact H | discriminate H].
Qed.
Definition cov_exact (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S36S36L_;M0S1aS1bVo;A1S1bVo';A1A2G0S1aS1dVo;A1S1dVo';A1A2S1aS1cVo;A1S1cVo';A1A2S3cX36x2S3cX36x2").
Definition cov_itv (facts : list sprop) (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S36S36L_;M0S1aS1bVo;A1S1bVo';A1A2G0S71Vfacts;S1dVo;A1S1dVo';A1A3S70Vfacts;S1cVo;A1S1cVo';A1A3S3cX36x2S3cX36x2").
Definition coveredbL (facts : list sprop) (R objs : list sobj) : bool := ltac2:(tb__ "0|0|
S87S12S12S36S36L_;S88S12S74R1A1Vobjs;A3S3aS88S12S75Vfacts;R1A2Vobjs;A3X36x2Lo;VR;A3").
Lemma coveredbL_sound : ltac2:(tb__ "0|6|
S3bS16A1S3bS12A1M0G0S11S12S4fQ40M1A1Sb2S16S22R3A1R6A3ScS36S6fR7R6R5A3S3aA3S86S12R4R7A3SbS3S42S0S0S1fR6R5A2M2A3S4eG1R4A2M3A2S4G3S43S0S0G2A3A2A2SeS12S12SbS86S12R1R9A3SbS3S42S0S0S1fR8R1A2M4A3S4eG1R6A2M5A2S4G5S43S0S0G4A3A2A2A2Lo';A2F_;F_;F_;F_;Fa;Fo;Frho;Fobjs;FR;Ffacts;").
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
ScS1Sd5VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
ScS36S7bSe2Vnx;A2S3aA3").

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
S52ScS3bS3dS0S0A2A1S5fVAX;R1A1A1S5fR1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
Se6VnW;Vst;Vnx;VBX;A4").

Definition AXK (G2 : DG) : AA -> AA := ltac2:(tb__ "0|0|
S52Sd7Sd8VAX;R1A1VG2;A2A1LX;").
Hypothesis Htmax : 1 <= tmax <= SZMAX.

Definition dlink (G2 : DG) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|3|
SbS1ScS4fQ40M0A1M1S13Vrho';R1A2S13Vrho;R1A2A3Fi;SbS1ScS3bS4fQ8A1M2A1S27Vrho';R1A2S27Vrho;R1A2A3Fl;G1SfSa5VG2;S4eG0R1A2A2A1ScS40G2A1S28Vrho';R2A2S28Vrho;R2A2A3F_;Fa;A2A2").

Variables (X5 C5 : axst).
Hypothesis NXE : ltac2:(tb__ "0|0|
ScS36S7bVGS;S17S49VX5;A1A1A2S3aA3").
Hypothesis FBE : ltac2:(tb__ "0|0|
ScS36S87S16S23S17S49VX5;A1A1A1Sc9A3S3aA3").
Hypothesis XE5 : ax_X X5 = [].
Hypothesis F192 : ltac2:(tb__ "0|1|
S89S16S38S16S25S15Z1A1S14Pc0A1M0A2S38S16S25G0S15Vtmax;A1A2S3fS16A1A3A3S19S49VX5;A1A1A3").
Hypothesis FDEP : ltac2:(tb__ "0|0|
S89S16S91S8fA1S19S49VX5;A1A1A3").

Hypothesis FUNW : ltac2:(tb__ "0|0|
S89S16S92VW;Vst;A2S19S49VX5;A1A1A3").
Hypothesis WX5r : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S35S49S62VX5;R2A2A1A1S3aA3F_;Fsz;").
Hypothesis DX5r : ltac2:(tb__ "0|4|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS40S3dS3bS3dS10S10A2M0A1M1S3bS16A1M2A2M3A1SdbS49S6eVX5;A1A1S49S62VX5;R2A2A1A2S45G3S39G1G2S38G0S39S10S10S2aS3cQ20S14Pc0A1A3S15R2A1A4S3fG0A1A3S3fS16A1A4A2A3F_;Fsz;").
Hypothesis SPL1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S62VX5;R2A2A1S61S15Nf10A1A3A2S3aA3F_;Fsz;").
Hypothesis SPL2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S6bVX5;R2A2A1S3eS61A1S15N910A1A3A2S3aA3F_;Fsz;").
Hypothesis SPL3 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S6cVX5;R2A2A1S3eS3eS61A1A1S15N848A1A3A2S3aA3F_;Fsz;").
Hypothesis SPL4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S6dVX5;R2A2A1S3eS3eS3eS61A1A1A1S15N50A1A3A2S3aA3F_;Fsz;").

Variables (s4 : Z -> wsub) (R4 : Z -> list sobj) (T4 : Z -> axst).
Let X4 (sz : Z) : axst := X5s X5 sz.
Hypothesis HER : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS40S3bS12A1M0A1Sc4VX4;R2A1S78R2A1Vs4;R2A1A3S45G0VR4;R2A1A2A3F_;Fsz;").
Hypothesis HT4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS4aSbfVs4;R2A1S78R2A1S77R2A1VX4;R2A1VR4;R2A1A5VT4;R2A1A3F_;Fsz;").
Hypothesis XX4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS3bS3dS10S10A2M0A1S4bVX4;R2A1A1S3fG0A1A3F_;Fsz;").
Hypothesis FBX4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S87S16S23S17S49VX4;R2A1A1M0A1A1S19G0A1A3S3aA3F_;Fsz;").
Hypothesis Hchk4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36Sc3VX4;R2A1S78R2A1Vs4;R2A1VR4;R2A1S38S4aS77R2A1S3fS4aA1A3A5S3aA3F_;Fsz;").
Hypothesis NX4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS1S17S49VX4;R2A1A1A1S17S49VX5;A1A1A3F_;Fsz;").
Hypothesis WG10 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10SacVs4;R2A1PaM0A2S24Sb8S14G0A1S15N910A1A3A3F_;Fsz;").
Hypothesis WG15 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10SacVs4;R2A1PfA2S15N600A1A3F_;Fsz;").
Hypothesis WG12 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10SacVs4;R2A1PcA2S24Sb8S14PaA1S15N848A1A3A3F_;Fsz;").

Variable EXo : list sobj.
Definition MAPO : sobj := ltac2:(tb__ "0|0|
S26S14Vnx;A1S15Z0A1S14Sd4A1S3fS1eA1S29A5").
Definition in_fambS (o : sobj) : bool := ltac2:(tb__ "0|4|
S44S44S44ScaVo;A1S88S12S12Se5S79Vo;A1S79R1A1A2Lo';M0S38S12Sa0VEXo;A3A3A2S41S1aS1bVo;A1S14PaA1A2S10S36Lx;S1dVo;A1S0S41S6N910R1A2S6R1Z0A2A2Llo;S1S41S7dR1S8eA2S1aS1cVo;A1S15Nf10A1A2A2Li;Sb6S10S10S3cLb;La;M1Lop;M2G2Sb7G1Lop;M3G3S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll;X10x8A2A2S88S12G0S90VW;A1A3A2").
Hypothesis FAM4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S87S12Sa1VR4;R2A1A3S3aA3F_;Fsz;").

Hypothesis EX_zone : ltac2:(tb__ "0|3|
S52S8cS11S4fQ40A1M0S11S3bG0A1S98S12S0S7eVsegs;VJG;VAX;R9R8R7R6A5VX5;R5R4R3A6S86S12R3VEXo;A3SbS3S42S0S0S1fR7R4A2M1A3R3A2S4R3S43S0S0G1A3A2A2SdSbS3ScdR4A2S4R4SccA2A2SbS3S56S54RcA1A1M2R4A2S4R4S5G2SceA2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Hypothesis NEWO : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS3bS12A1SbeS49S78R2A1A1S49S77R2A1A1A2S3fS12A1A3F_;Fsz;").
Hypothesis XPost : ltac2:(tb__ "0|1|
S0ScS3bS3dS10S10A2M0A1S4bS77R1A1A1S3fG0A1A3Fsz;").

Hypothesis FBT4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S87S16S23S17S49VT4;R2A1A1A1A1S19S49VX4;R2A1A1A1A3S3aA3F_;Fsz;").
Hypothesis XT4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS3bS3dS10S10A2M0A1S4bVT4;R2A1A1S3fG0A1A3F_;Fsz;").
Hypothesis RB1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbbS49S64VT4;R2A1VX4;R2A1A2A1U0A2A2S3aA3F_;Fsz;").
Hypothesis RB2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbbS49S65VT4;R2A1VX4;R2A1A2A1U1A2A2S3aA3F_;Fsz;").
Variable nobj : nat.
Hypothesis PERM_nd : ltac2:(tb__ "0|0|
ScS36SdcS63Vnobj;A1A1S3aA3").
Hypothesis PERM_lt : ltac2:(tb__ "0|0|
ScS36S87S37S37Se8R1Vnobj;A2Li;S63Vnobj;A1A3S3aA3").
Hypothesis PERM_cov : ltac2:(tb__ "0|0|
ScS36S87S37S37S88S37Se7R1A1S63Vnobj;A1A3Li;Sb3U0Vnobj;A2A3S3aA3").
Hypothesis PERM_len : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS37S47S12S20S49S66VT4;R2A1VX4;R2A1A2A1A1A2Vnobj;A3F_;Fsz;").
Hypothesis MRG1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S67Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Hypothesis MRG2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S68Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Hypothesis MRG3 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S69Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Hypothesis MRG4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S6aVnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Let T4d (sz : Z) : axst := ltac2:(tb__ "0|0|
S72Vnobj;VT4;Vsz;A1VX4;Vsz;A1A3").
Variable sd : Z -> wsub.
Hypothesis ENT5 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S4dVT4d;R2A1VC5;Vsd;R2A1A3S3aA3F_;Fsz;").
Hypothesis SID5 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36SaeVsd;R2A1VGS;A2S3aA3F_;Fsz;").
Hypothesis R4cov : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S6fS19S49VT4d;R2A1A1M0A1VR4;R2A1S20G0A1A3S3aA3F_;Fsz;").

Definition zoneS (T C pab ua L top a : Z) : Prop := ltac2:(tb__ "0|1|
SdSbSbS3ScfVa;A2S4Va;ScbA2A2SdS4Va;Sa9A2S3S5Sa7S9Z8Sa8A2A2Va;A2A2A2SdSbS3VT;Va;A2S4Va;S5VT;Z1000M0A2A2A2SdSbS3VC;Va;A2S4Va;S5VC;G0A2A2A2SdSbS3ScdVa;A2S4Va;SccA2A2SdSbS3Vpab;Va;A2S4Va;S5Vpab;SceA2A2A2SdSbS3Vua;Va;A2S4Va;S5Vua;VL;A2A2A2S3Vtop;Va;A2A2A2A2A2A2A2").

Definition site_factsS (A : AA) (rho : valuation) (a : word) (rhoE : valuation) (sz : Z) : Prop := ltac2:(tb__ "0|9|
S4eQ40M0S13Vrho;PcA2A2S0S4eG0Va;A2S0S82R2A1S0SbSbS3Z1Vsz;A2S3Vsz;Vtmax;A2A2SbS3S51G0S13VrhoE;S8eA2A2M1SaS8fA1A2SbSe4S54VA;A1M2A1SbScS4fG0A1M3S13VrhoE;Vnx;A2Va;A3SbScG3S13VrhoE;Sd4A2S50G0R1A2A3SbScG3S13VrhoE;P97A2S50G0S5aG2A1A2A3SbScG3S13VrhoE;P98A2S50G0S59G2A1A2A3SbS3S5cG2A1M4S5S4eG0S13VrhoE;PaA2A2G1A2A2SbSbS3Zfc01R3A2S4R3S7Z2M5Z27A2A2A2SbSbS3Z12000R1A2S3R1S5R3Z3007A2A2A2SbS3ScbR2A2SbS3S5R2R1A2Z7fffff800000A2SbS12S0S86S12R2VEXo;A3SbS3S42S0S0S1fVrhoE;R3A2M6A3R2A2S4R2S43S0S0G6A3A2A2SdSbS3ScdR3A2S4R3SccA2A2SbS3S56G2A1M7R3A2S4R3S5G7SceA2A2A2A2F_;F_;Fz;Fo;Sb2S12S12SbSbS3S5G4Z10A2S4eG0S2cVrhoE;S1bR1A1A2A2M8A2S3G8S7G5Z2fA2A2A2SbScS10S1dR1A1S15N10A1A3ScS10S1cR1A1S15Z0A1A3A2A2Lo;S90VW;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2TL;Tua;Tnv;").

Lemma R4_zoneS : ltac2:(tb__ "0|3|
S0S52S11S4fQ40M0A1S11S12S0S9cR6R5R4R3R7A5S86S12R3VR4;R8A1A3SbS3S42S0S0S1fR5R4A2M1A3R3A2S4R3S43S0S0G1A3A2A2S9fS5aS54R9A1M2A1S59G2A1S56G2A1S4eG0R7A2S82S4eG0S13R8PcA2A2A1S5cG2A1R4A7F_;F_;F_;Fz;Fo;FrhoE;Fa;Frho;FA;Fsz;").
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
S52S11S3bS4fQ40A1A1S84S0S0S0Sd6R7R6R5R4A4S3ScbR4A2S3dS0S0A2M0S86G0R1Sa3S53RaA1A1A3Sa2R2S39S0S0R7R6A4A2F_;Fbn;S54RaA1S57S9fS5aR1A1S59R1A1S56R1A1R7R6S5cR1A1R5A7SfSa5S53RcA1R6A2A1F_;TG;F_;F_;F_;Fz;FL;Fua;Fmd;Ftp;Frho;FAx;").
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

Lemma budget_A0 : ltac2:(tb__ "0|0|
S52S0S5bR2R1A2S5bVAX;Sd3R3R2A2A1Z0A2F_;Fnv;FA;").
Proof.
  intros A nv (HL & HR & HP). split; [|split].
  - rewrite AXV, AXKm, AXKf. cbn [aa_V aa_Km aa_Kf bumpV]. unfold limit_ok_alloc in *. rewrite Z.add_0_r. exact HL.
  - unfold sec_room, large_live in *. rewrite AXlive. cbn [aa_live bumpV]. exact HR.
  - apply (prim_room_same A (AX (bumpV A nv))); [rewrite AXlive; reflexivity | exact HP].
Qed.

Lemma dcS_facts : ltac2:(tb__ "0|2|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S98S7eVsegs;VJG;VAX;R7R6R5R4A5VX5;R3R2R1A6S9cR8R6R5R4S4eG0S13R4Pc0A2A2A5F_;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
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
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S98S7eVsegs;VJG;VAX;R7R6R5R4A5VX5;R3R2R1A6S7eVsegs;VJG;VAX;R8R7R6R5A5VX4;S4eG0S13R4Pc0A2A2A1R4R3R2A6F_;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w Hw. pose proof (dcS_facts A Kc rho a rhoE tp w Hw) as (Hsz & Fd1 & HG & _ & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *. destruct w as [tr [ms md]].
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG. unfold malloc_depth in Fd1.
  assert (Em3808 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-3856)))) = bv_unsigned (rw rhoE 10%positive) - 3856).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-3856))) with (2 ^ 64 - 3856) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
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
S52S11S4fQ40M0A1M1S11S0S9cR5R4R3R2R1A5S52S11S3bG1A1S84G1Sd6R5R4R3R2A4ScS57S54R6A1S54RcA1A3S3dS0S0A2M2S86G2R1Sa3S53R8A1A1A3Sa2R2S39S0S0S4eG0RdA2S82S4eG0S13RePcA2A2A1A4A2F_;Fbn;SadRbVR4;RaA1R4A3SfSa5S53R9A1S4eG0R5A2A2A1F_;F_;F_;F_;Fx;Fmdx;Ftpx;Frx;FAx;F_;Fsz;FrhoE;Fa;Frho;FA;").
Proof.
  intros A rho a rhoE sz SF Ax rx tpx mdx x HX EG HSEP (o & Ho & Hox).
  pose proof (R4_zoneS sz A rho a rhoE o (bv_unsigned x) SF Ho Hox) as HZ. rewrite <- EG in HZ.
  pose proof SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG & _).
  exact (zoneS_not_DFP Ax rx tpx mdx _ _ (bv_unsigned x) HX IMG HSEP HZ).
Qed.

Let A0 (A : AA) (rho : valuation) : AA := ltac2:(tb__ "0|0|
VAX;Sd3VA;S4eQ40S13Vrho;PcA2A2A2A1").
Lemma A0_geom : ltac2:(tb__ "0|0|
S52S11ScS57S54VA0;R2R1A2A1S54R2A1A3Frho;FA;").
Proof. intros A rho. unfold A0. rewrite AXg. reflexivity. Qed.
Lemma A0_depot : ltac2:(tb__ "0|0|
S52S11ScS60S53VA0;R2R1A2A1S53R2A1A3Frho;FA;").
Proof. intros A rho. unfold A0. rewrite AXd. reflexivity. Qed.

Lemma dcS_entry : ltac2:(tb__ "0|4|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S0S3bS85A1M2S95S84S9cRaR8R7R6R4A5S8dRaA1S7fVsegs;R8R7VX4;R6A1S39G2S96R5S97R4R3A2A4A5VJG;VAX;RdRcRbRaR9R8R6R4A9Sa6Sb1Sb0VA0;ReRcA2M3RdRaS4eG0RbA2S82S4eG0S13RcPcA2A2A1A5S53G3A1SabSaaRaVR4;R8A1S8bR5R9R6A3A3Vs4;R8A1A2R9R7R5A7F_;F_;F_;F_;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0.
  pose proof SF as (Hsz & Fd1 & HG & Enx & EMS & E151 & E152 & Htop & HN & SMB & IMG & HTOP & HEX). unfold malloc_depth in Fd1.
  pose proof HJ0 as (_ & _ & HA0 & HP0 & HK0 & _ & _ & _ & _ & HB0). cbn zeta in HA0, HP0, HB0. fold (A0 A rho) in HA0.
  pose proof (AInvA_budget (A0 A rho) rhoE tp md0 HA0) as (_ & _ & _ & HKm0 & _).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2272 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2320)))) = bv_unsigned (rw rhoE 10%positive) - 2320).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2320))) with (2 ^ 64 - 2320) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
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
S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S0S3bS85A1M3S95S84S11G2G3S95S84S9cRfRdRcRbR9A5S8dRfA1Sa4Sb1Sb0VA0;R11RfA2M4R10RdS4eG0ReA2S82S4eG0S13RfPcA2A2A1A5S53G4A1A3Sc0SabSaaReVR4;RcA1S8bR9RdRaA3A3Vs4;RcA1A2S11S7fVsegs;RfReVX4;RdA1S39G3S96RcS97RbRaA2A4A5VJG;VAX;R14R13R12R11R10RfRdRbA9SbcS17S49S78RfA1A1A1R3RbA3S7fVsegs;RcRbS77R10A1S39G3S96RaS97R9R8A2A4A5R6R5R12RdRcRbR9A6Sc2R14S8bRfR13R10A3VR4;R12A1Vs4;R12A1S78R12A1S77R12A1VX4;R12A1ReA8F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
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
S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S0S3bS85A1M3S95S84S11G2G3S95S84SafVW;Vst;A2S83VW;Vst;A2S9cR11RfReRdRbA5S8dR11A1Sa4Sb1Sb0VA0;R13R11A2M4R12RfS4eG0R10A2S82S4eG0S13R11PcM5A2A2A1A5S53G4A1A3Sc0SabSaaR10VR4;ReA1S8bRbRfRcA3A3Vs4;ReA1A2S11S7fVsegs;R11R10VX4;RfA1S39G3S96ReS97RdRcA2A4A5VJG;VAX;R16R15R14R13R12R11RfRdA9SbcS17S49S78R11A1A1A1R3RdA3S7fVsegs;ReRdS77R12A1S39G3S96RcS97RbRaA2A4A5R6R5R14RfReRdRbA6S11S98SbdR18S8bR13R17R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R2R12A9S7eVsegs;Sc1RaR9R18R13R12A5SbfVs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R3R12R2A6SeS55S55SeS11S11SeS11S11SbS3dS0S0A2M6S86G6R1Sa3R4A1A3Sa2R2S39S0S0S4eG0R20A2S82S4eG0S13R21G5A2A2A1A4A2F_;Fbn;SbS9eR3R1fR2A3S7eVsegs;VJG;S9dR3A1R21R20R2R1eA5VC5;R1R16R6A6A2A2LrhoX;A2Lrho'';A2LG2;A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
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
    - apply (HW rhoE rho5); [|exact HU0]. intros i Hi. apply RW5. apply GWS. unfold NF in Hi; unfold GW; lia.
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
S98OF_;S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S9bS0S3bS85A1M3S95S84S11G2G3S95S84SafVW;Vst;A2S83VW;Vst;A2S55S11S11G2S3dS0S0A2M4S86G4R1Sa3R5A1A3Sa2R2S39S0S0S4eG0R15A2S82S4eG0S13R16PcM5A2A2A1A4A2F_;Fbn;S9eR5R15R4A3S9aVsegs;R19S7eVsegs;VJG;S9dR6A1R18R17R5R15A5VC5;R4R3A5R12A4F_;F_;Ftp';FrhoX;Frho';FG2;S9cR13R11R10RfRcA5S8dR13A1Sa4Sb1Sb0VA0;R15R13A2M6R14R11S4eG0R12A2S82S4eG0S13R13G5A2A2A1A5S53G6A1A3Sc0SabSaaR12VR4;RfA1S8bRcR11RdA3A3Vs4;RfA1A2S11S7fVsegs;R13R12VX4;R10A1S39G3S96RfS97ReRdA2A4A5VJG;VAX;R18R17R16R15R14R13R10ReA9SbcS17S49S78R12A1A1A1R3ReA3S7fVsegs;RfReS77R13A1S39G3S96RdS97RcRbA2A4A5R6R5R16R10RfReRcA6SbSc2R18S8bR12R17R13A3VR4;R15A1Vs4;R15A1S78R15A1S77R15A1VX4;R15A1R11A8S11SbdR19S8bR13R18R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R1R12A9S9aVsegs;R1fS7eVsegs;Sc1R9R8R19R13R12A5SbfVs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R2R12A5R18A4F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dcS_exit_ok A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK n' Hg' w' Hw'.
  destruct (dcS_exit_core A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (G2 & rho'' & rhoX & Hsep & Hl & HC5).
  exact (Hcont G2 rho'' rhoX tpL Hsep Hl n' Hg' w' HC5).
Qed.

Lemma dcS_exitE : ltac2:(tb__ "0|7|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S98OF_;S0S3bS85A1M3S95S84S11G2G3S95S84SafVW;Vst;A2S83VW;Vst;A2S55S11S11G2S3dS0S0A2M4S86G4R1Sa3R5A1A3Sa2R2S39S0S0S4eG0R15A2S82S4eG0S13R16PcM5A2A2A1A4A2F_;Fbn;S9eR5R15R4A3S99Vsegs;S7eVsegs;VJG;S9dR6A1R18R17R5R15A5VC5;R4R3A5R12A3F_;F_;Ftp';FrhoX;Frho';FG2;S9cR13R11R10RfRcA5S8dR13A1Sa4Sb1Sb0VA0;R15R13A2M6R14R11S4eG0R12A2S82S4eG0S13R13G5A2A2A1A5S53G6A1A3Sc0SabSaaR12VR4;RfA1S8bRcR11RdA3A3Vs4;RfA1A2S11S7fVsegs;R13R12VX4;R10A1S39G3S96RfS97ReRdA2A4A5VJG;VAX;R18R17R16R15R14R13R10ReA9SbcS17S49S78R12A1A1A1R3ReA3S7fVsegs;RfReS77R13A1S39G3S96RdS97RcRbA2A4A5R6R5R16R10RfReRcA6SbSc2R18S8bR12R17R13A3VR4;R15A1Vs4;R15A1S78R15A1S77R15A1VX4;R15A1R11A8S11SbdR19S8bR13R18R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R1R12A9S99Vsegs;S7eVsegs;Sc1R9R8R19R13R12A5SbfVs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R2R12A5R18A3F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dcS_exit_ok A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK w' Hw'.
  destruct (dcS_exit_core A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (G2 & rho'' & rhoX & Hsep & Hl & HC5).
  exact (Hcont G2 rho'' rhoX tpL Hsep Hl w' HC5).
Qed.

Lemma dcS_nums : ltac2:(tb__ "0|4|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S3bS85A1S84VJG;VAX;R8R7R6R5R4R3R2R1A9S4eG0R6A2S0S82S4eG0S13R8PcA2A2A1S0SbS5bVA0;RbR9A2M2Z0M3A2SbS3G3S58G2A1A2SbS3G3R2A2SbS3G3R1A2SbS4S5R2R1A2S7Z2Z40A2A2Se3Vsegs;G2R7R6R4A5A2A2A2A2A2TL;Tua;F_;Fmd;Ftr;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp tr md HJ. cbn zeta.
  pose proof (JGs_nums nW st tmax nx Hnx AX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _).
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & _ & HB). cbn zeta in HA, HB. fold (A0 A rho) in HA.
  pose proof (AInvA_budget (A0 A rho) rhoE tp md HA) as (_ & _ & _ & HKm0 & _). pose proof (urange a) as Ra.
  split; [exact (budget_A0 A _ HB)|]. split; [exact HKm0|]. split; [lia|]. split; [lia|]. split; [lia | exact HA].
Qed.

Theorem depot_call_S : ltac2:(tb__ "0|4|
S98OF_;S52S8cS11S4fQ40M0A1M1S9bSafVW;Vst;A2S83VW;Vst;A2S8dR6A1S81Vsegs;R9S80R7A1A3SdfVsegs;RaS80R8A1A3S55S11S11S3bG1A1M2S3dS0S0A2M3S86G3R1Sa3R5A1A3Sa2R2S39S0S0S4eG0RdA2S82S4eG0S13RePcA2A2A1A4A2F_;Fbn;S9eR5RdR4A3S9aVsegs;R11S7eVsegs;VJG;S9dR6A1R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S11G2S9aVsegs;ReS7eVsegs;VJG;VAX;RdRcRbRaA5VX5;R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
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
S52S8cS11S4fQ40M0A1M1S98OF_;SafVW;Vst;A2S83VW;Vst;A2S8dR6A1S55S11S11S3bG1A1M2S3dS0S0A2M3S86G3R1Sa3R5A1A3Sa2R2S39S0S0S4eG0RbA2S82S4eG0S13RcPcA2A2A1A4A2F_;Fbn;S9eR5RbR4A3S99Vsegs;S7eVsegs;VJG;S9dR6A1ReRdR5RbA5VC5;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S11G2S99Vsegs;S7eVsegs;VJG;VAX;RbRaR9R8A5VX5;R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
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
End CDepotCallS.

(* [comment removed for export] *)
Module SpineCallocSec3IE.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S1aA1A1A2S1A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S15S1bSeS10S19A1A1A2A1A1A2S1A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S1aZ1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1eG0G1A3G2A3A6S1A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S15S1bSeS10S19A1A1A2Z1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1fG0G1A3G2A3A6S1A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_0h : ltac2:(tb__ "0|6|
S18S24SbS12Q40M0A1M1S4G1A1M2S14OF_;S21VW;Vst;A2S25R6A1S28S1S11G0R5A2S20S11G0SdR6PcM3A2A2A1A3SbSbG2S29S11G0R9A2S20S11G0SdRaG3A2A2A1RaR3A4S13S8S16S8S26U0M4Vst;S1cS18R1LX;M5RdRcR4RaA8S1dR3R2A5R8A3F_;FtpY;FrhoY;Frho';SbS13S8S16S8S27G4Vst;S1cG5RbRaR9R8A8S23VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
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
    [hw_discharge | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineCallocSec3IE.

(* [comment removed for export] *)
Module SpineCallocSec3IEL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S1bA1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S16S1cSfS11S1aA1A1A2A1A1A2S3A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S1bZ1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S1fG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S16S1cSfS11S1aA1A1A2Z1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S20G0G1A3G2A3A6S3A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_0l : ltac2:(tb__ "0|6|
S19S25ScS13Q40M0A1M1S5G1A1M2S15OF_;S22VW;Vst;A2S26R6A1S29S4S12G0R5A2S21S12G0SeR6PcM3A2A2A1A3ScScG2S2aS12G0R9A2S21S12G0SeRaG3A2A2A1RaR3A4S14S9S17S9S27U0M4Vst;S1dS19R1LX;M5RdRcR4RaA8S1eR3R2A5R8A3F_;FtpY;FrhoY;Frho';ScS14S9S17S9S28G4Vst;S1dG5RbRaR9R8A8S24VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
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
    [hw_discharge | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineCallocSec3IEL.

(* [comment removed for export] *)
Module SpineCallocSec3IELW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S1bA1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S16S1cSfS11S1aA1A1A2A1A1A2S3A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S1bZ1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S1fG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S16S1cSfS11S1aA1A1A2Z1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S20G0G1A3G2A3A6S3A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_1l : ltac2:(tb__ "0|6|
S19S25ScS13Q40M0A1M1S5G1A1M2S15OF_;S22VW;Vst;A2S26R6A1S29S4S12G0R5A2S21S12G0SeR6PcM3A2A2A1A3ScScG2S2aS12G0R9A2S21S12G0SeRaG3A2A2A1RaR3A4S14S9S17S9S27U1M4Vst;S1dS19R1LX;M5RdRcR4RaA8S1eR3R2A5R8A3F_;FtpY;FrhoY;Frho';ScS14S9S17S9S28G4Vst;S1dG5RbRaR9R8A8S24VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 1%nat) (st := st) (tmax := tmax) (hi := false) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
    (AX := fun X : AA => X) (AXg := fun X => eq_refl) (AXb := fun X => eq_refl)
    (E0 := E0c) (T0 := T0c) (SKT := SKT_0) (FCT := FCT_0) (AF0 := AF0_0)
    (ET1 := ET1c) (CT1 := CT1c) (CO1 := CO1c) (T1 := T1c) (ET2 := ET2c) (CT2 := CT2c) (CO2 := CO2c) (T2 := T2c) (s1 := s1c) (s2 := s2c) (R1 := R1c) (R2 := R2c)
    (NXT0 := NXT0_0) (NXD1 := NXD1_0) (ECert1 := ECert1_0) (ECert2 := ECert2_0)
    (WC1 := WC1_0) (DF1 := DF1_0) (NX1 := NX1_0) (HC1 := HC1_0) (SK1 := SK1_0) (FC1 := FC1_0) (XC1 := XC1_0) (HCO1 := HCO1_0) (WCO1 := WCO1_0)
    (He1 := He1_0) (Hchk1 := Hchk1_0) (HT1 := HT1_0) (FBC1 := FBC1_0) (FBT1 := FBT1_0) (NXC1 := NXC1_0)
    (WC2 := WC2_0) (DF2 := DF2_0) (NX2 := NX2_0) (HC2 := HC2_0) (SK2 := SK2_0) (FC2 := FC2_0) (XC2 := XC2_0) (HCO2 := HCO2_0) (WCO2 := WCO2_0)
    (He2 := He2_0) (Hchk2 := Hchk2_0) (HT2 := HT2_0) (FBC2 := FBC2_0) (FBT2 := FBT2_0) (NXC2 := NXC2_0);
    [hw_discharge | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineCallocSec3IELW1.

(* [comment removed for export] *)
Module SpineCallocSec3IEW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S1aA1A1A2S1A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S15S1bSeS10S19A1A1A2A1A1A2S1A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S1aZ1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1eG0G1A3G2A3A6S1A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S15S1bSeS10S19A1A1A2Z1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1fG0G1A3G2A3A6S1A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_1h : ltac2:(tb__ "0|6|
S18S24SbS12Q40M0A1M1S4G1A1M2S14OF_;S21VW;Vst;A2S25R6A1S28S1S11G0R5A2S20S11G0SdR6PcM3A2A2A1A3SbSbG2S29S11G0R9A2S20S11G0SdRaG3A2A2A1RaR3A4S13S8S16S8S26U1M4Vst;S1cS18R1LX;M5RdRcR4RaA8S1dR3R2A5R8A3F_;FtpY;FrhoY;Frho';SbS13S8S16S8S27G4Vst;S1cG5RbRaR9R8A8S23VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 1%nat) (st := st) (tmax := tmax) (hi := true) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
    (AX := fun X : AA => X) (AXg := fun X => eq_refl) (AXb := fun X => eq_refl)
    (E0 := E0c) (T0 := T0c) (SKT := SKT_0) (FCT := FCT_0) (AF0 := AF0_0)
    (ET1 := ET1c) (CT1 := CT1c) (CO1 := CO1c) (T1 := T1c) (ET2 := ET2c) (CT2 := CT2c) (CO2 := CO2c) (T2 := T2c) (s1 := s1c) (s2 := s2c) (R1 := R1c) (R2 := R2c)
    (NXT0 := NXT0_0) (NXD1 := NXD1_0) (ECert1 := ECert1_0) (ECert2 := ECert2_0)
    (WC1 := WC1_0) (DF1 := DF1_0) (NX1 := NX1_0) (HC1 := HC1_0) (SK1 := SK1_0) (FC1 := FC1_0) (XC1 := XC1_0) (HCO1 := HCO1_0) (WCO1 := WCO1_0)
    (He1 := He1_0) (Hchk1 := Hchk1_0) (HT1 := HT1_0) (FBC1 := FBC1_0) (FBT1 := FBT1_0) (NXC1 := NXC1_0)
    (WC2 := WC2_0) (DF2 := DF2_0) (NX2 := NX2_0) (HC2 := HC2_0) (SK2 := SK2_0) (FC2 := FC2_0) (XC2 := XC2_0) (HCO2 := HCO2_0) (WCO2 := WCO2_0)
    (He2 := He2_0) (Hchk2 := Hchk2_0) (HT2 := HT2_0) (FBC2 := FBC2_0) (FBT2 := FBT2_0) (NXC2 := NXC2_0);
    [hw_discharge | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineCallocSec3IEW1.

