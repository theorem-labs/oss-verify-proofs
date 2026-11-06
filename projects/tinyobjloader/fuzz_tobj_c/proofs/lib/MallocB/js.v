(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall jq jk.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.

(* [comment removed for export] *)
Module CDepotCallW.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "mul"; "opp"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SLit"; "sobj"; "sprop"; "rw"; "sstate"; "SVar"; "ss_next"; "ss_facts"; "SPUle"; "sv_eqb"; "SAlu"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "sprop_below"; "ss_objs"; "eval"; "swf"; "SExt"; "holds"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "cons"; "nat"; "nil"; "pair"; "prod"; "false"; "option"; "andb"; "orb"; "Some"; "app"; "None"; "fst"; "length"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW.DCW"; "X4"; "isSome"; "site_facts"; "X4r"; "osplit"; "permW"; "F_call"; "T4b"; "T4d"; "X4a"; "X4b"; "X4c"; "X4f"; "zoneR"; "R4_families"; "T40"; "T4a"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "in_famb"; "prim_fitb"; "rt_okD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_depot"; "ag_spacebeg"; "topG"; "ag_ctx"; "ag_thread"; "sec_chunk"; "ageom"; "DG"; "aa_live"; "aa_sec"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"; "nocells"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E4d"; "C5"; "upd"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "PIECES"; "V_CNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "V_DEPTH"; "malloc_depth"; "unwind_objs"; "J_alloc_preT"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "KEEPD"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "import_okPA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK"; "KD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "rz"; "ClassID"; "IMG_HI"; "IMG_LO"; "Sh"; "is_primary"; "kSpaceSize"; "needed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@LinuxProcessSemantics.Riscv.Instr";
"ALU_ADD"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "DFP"; "JLD"; "MAP1"; "MAP1N"; "STORE"; "dfp_static"; "DFPw"; "JD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "chk_of"; "cnt_of"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "geom_ok"; "inv3"; "primary_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "HD_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "pvals_ok"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl"; "sobjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE"; "HDE_stmt"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DCW.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.

Hypothesis HUS : stopJ_stable W st.

Hypothesis HUSr : ltac2:(tb__ "0|1|
S15S15S9Se0R1Sc2A2ScS68Q40A1S1aR3R2A2S1aR4R2A2A3F_;Fi;S89VW;Vst;R3A3M0G0F_;F_;Fr';Fr;").
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S8Sd9VCST;R1A2SfSbaR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S86VAInv;VW;Vst;VA;VKc;S1cPcA1A6").
Hypothesis Htmax : 1 <= tmax <= SZMAX.

Local Notation KEEPD := (CDepotCall.KEEPD CST XGL).

Definition F_call : list sprop := ltac2:(tb__ "0|3|
S2fS19S1fS17Z7fff7f800000A1M0S1cPaA1M1A2S2fS19S1fG0S21SafG1S17Nf10A1A3A2S2fS19S1fG0S21SafG1S17N848A1A3M2A2S2fS19S1fG2S17S7S4Z2Z40A2Z848A2A1A2S31S19A1A3A3A3A3").
Definition X4f : axst := ltac2:(tb__ "0|0|
Sd5S45S6eVW;Vst;Vtmax;A3A2").
Definition X4r (sz : Z) : axst := ltac2:(tb__ "0|1|
S70VW;Vst;Vtmax;S4bZ7e9e4S2fS33S30S16A2M0S32S30S16UbS17Vsz;A1A4S31G0A1A3S31S18A1S34S31S19A1A9").
Definition osplit (A : axst) (i : nat) (mid : sv) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9cS10VA;A1Vi;Vmid;A3S1bS13VA;R1A2LS';VA;X35x2").
Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
Definition X4a (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S42Vsz;A1U0S17Nf10A1A3").
Definition X4b (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S48Vsz;A1U1S17N910A1A3").
Definition X4c (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S49Vsz;A1U2S17N848A1A3").
Definition X4 (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S4aVsz;A1U3S17N50A1A3").
Hypothesis NXE : ltac2:(tb__ "0|0|
ScS2cSdfSc2S1dS10S6eVW;Vst;Vtmax;A3A1A1A2S2eA3").
Hypothesis FBE : ltac2:(tb__ "0|0|
ScS2cS8fS19S26S1dS10S6eVW;Vst;Vtmax;A3A1A1A1S45A3S2eA3").
Hypothesis XE4 : ltac2:(tb__ "0|1|
ScS2dS33S16S16A2M0A1S12S6eVW;Vst;Vtmax;A3A1S31G0A1A3").
Hypothesis F192 : ltac2:(tb__ "0|1|
S91S19S2fS19S1fS17Z1A1S1cPc0A1M0A2S2fS19S1fG0S17Vtmax;A1A2S31S19A1A3A3S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FDEP : ltac2:(tb__ "0|0|
S91S19S87S84A1S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FUNW : ltac2:(tb__ "0|0|
S91S19S88VW;Vst;A2S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FGEN4 : ltac2:(tb__ "0|0|
S91S19S71S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis YP4 : ltac2:(tb__ "0|0|
S90S19S1fS17Z1A1S1cS77A1A2S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis WX4r : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS29S10S42R2A1A1A1S2eA3F_;Fsz;").
Hypothesis DX4r : ltac2:(tb__ "0|4|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS35S33S2dS33S16S16A2M0A1M1S2dS19A1M2A2M3A1SccS10S4bA1S10S42R2A1A1A2S38G3S32G1G2S2fG0S32S16S16S2aS34Q20S1cPc0A1A3S17R2A1A4S31G0A1A3S31S19A1A4A2A3F_;Fsz;").
Hypothesis SPL1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S42R2A1A1U0S17Nf10A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S48R2A1A1U1S17N910A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL3 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S49R2A1A1U2S17N848A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S4aR2A1A1U3S17N50A1A3A2S2eA3F_;Fsz;").

Definition call_pack (X : axst) (sz : Z) : option (wsub * list sobj * axst) := ltac2:(tb__ "0|6|
S2fS33S9S16A2M0S32S9S16PfS17N600A1A4Sd1P1S10VX;A1S10S66Vsz;A1M1A1A3A3S2dG0A1M2S35S2dS18A1M3A1S35S33S33S99G3A2S11A2M4A1Lx;Sa2VX;G1R1A3G3S38S33S33G2G3A2M5S11A2S32G5S11S32G2G3R2R1A4S9eR2G1S65Vsz;A1VX;R1A5A4A2LR;S3aG4A1X35x2Ts;").

Variables (s4 : Z -> wsub) (R4 : Z -> list sobj) (T4 : Z -> axst).
Hypothesis HER : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS35S2dS18A1M0A1Sa2S3fR2A1S66R2A1Vs4;R2A1A3S38G0VR4;R2A1A2A3F_;Fsz;").
Hypothesis HT4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS11S9eVs4;R2A1S66R2A1S65R2A1S3fR2A1VR4;R2A1A5VT4;R2A1A3F_;Fsz;").
Hypothesis XX4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS33S16S16A2M0A1S12S3fR2A1A1S31G0A1A3F_;Fsz;").
Hypothesis FBX4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS19S26S1dS10S3fR2A1A1M0A1A1S1eG0A1A3S2eA3F_;Fsz;").
Hypothesis Hchk4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cSa3S3fR2A1S66R2A1Vs4;R2A1VR4;R2A1S2fS11S65R2A1S31S11A1A3A5S2eA3F_;Fsz;").
Hypothesis NX4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS9S1dS10S3fR2A1A1A1S1dS10S6eVW;Vst;Vtmax;A3A1A1A3F_;Fsz;").
Hypothesis WG10 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PaM0A2S21SafS1cG0A1S17N910A1A3A3F_;Fsz;").
Hypothesis WG15 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PfA2S17N600A1A3F_;Fsz;").
Hypothesis WG12 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PcA2S21SafS1cPaA1S17N848A1A3A3F_;Fsz;").

Definition R4_families : list sobj := ltac2:(tb__ "0|0|
S39S18SceS39S18S2fS18S72S2fS18S74S2fS18S73S2fS18S75S31S18A1A3A3A3A3S76A3A3").
Definition in_famb (o : sobj) : bool := ltac2:(tb__ "0|3|
S37S92S18S18SdaS67Vo;A1S67R1A1A2Lo';S39S18S4dS85VW;A1A3A3S36S20S22Vo;A1S1cPaA1A2S16S2cLx;S24Vo;A1S8S36S3N910R1A2S3R1Z0A2A2Llo;S9S36SdeR1S83A2S20S23Vo;A1S17Nf10A1A2A2Li;Sb0S16S16S34Lb;La;M0Lop;M1G1Sb1G0Lop;M2G2S2cSaS16S34La;Lw;Lsgn;S9S16S8S34Lk;Li;Ll;X16x8A2A2").
Hypothesis FAM4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS18S54VR4;R2A1A3S2eA3F_;Fsz;").
Hypothesis NEWO : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS18A1Sb4S10S66R2A1A1S10S65R2A1A1A2S31S18A1A3F_;Fsz;").
Hypothesis XPost : ltac2:(tb__ "0|1|
S8ScS2dS33S16S16A2M0A1S12S65R1A1A1S31G0A1A3Fsz;").

Hypothesis FBT4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS19S26S1dS10VT4;R2A1A1A1A1S1eS10S3fR2A1A1A1A3S2eA3F_;Fsz;").
Hypothesis XT4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS33S16S16A2M0A1S12VT4;R2A1A1S31G0A1A3F_;Fsz;").
Definition T40 (sz : Z) : axst := ltac2:(tb__ "0|0|
Sd6VT4;Vsz;A1S1eS10S3fVsz;A1A1A1A2").
Definition oreb (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9dS10VA;A1Vi;A2S1bS13VA;R1A2LS';VA;X35x2").
Definition omrg (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9bS10VA;A1Vi;A2S1bS13VA;R1A2LS';VA;X35x2").
Definition T4a (sz : Z) : axst := oreb (T40 sz) 0.
Definition T4b (sz : Z) : axst := oreb (T4a sz) 1.
Hypothesis RB1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9dS10S4eR2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis RB2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9dS10S4fR2A1A1U1A2A2S2eA3F_;Fsz;").
Definition permW (n : nat) : list nat := ltac2:(tb__ "0|1|
S39S30S2fS30U9S2fS30U0S2fS30UaS2fS30U1S2fS30UbS2fS30U2S2fS30U3S2fS30U4S2fS30U5S2fS30U6S2fS30U7S2fS30U8S31S30A1A3A3A3A3A3A3A3A3A3A3A3A3Sc1UcM0Sd0Vn;G0A2A2A3").
Variable nobj : nat.
Hypothesis PERM_nd : ltac2:(tb__ "0|0|
ScS2cSd2S44Vnobj;A1A1S2eA3").
Hypothesis PERM_lt : ltac2:(tb__ "0|0|
ScS2cS8fS30S30SddR1Vnobj;A2Li;S44Vnobj;A1A3S2eA3").
Hypothesis PERM_cov : ltac2:(tb__ "0|0|
ScS2cS8fS30S30S92S30SdcR1A1S44Vnobj;A1A3Li;Sc1U0Vnobj;A2A3S2eA3").
Hypothesis PERM_len : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS30S3cS18S27S10S46R2A1A1A1A2Vnobj;A3F_;Fsz;").
Definition T4c (sz : Z) : axst := ltac2:(tb__ "0|2|
S13S46Vsz;A1M0Sd4S10G0A1M1Sd3S27G1A1S44Vnobj;A1A2A2A2").
Definition T4m1 (sz : Z) : axst := omrg (T4c sz) 0.
Definition T4m2 (sz : Z) : axst := omrg (T4m1 sz) 0.
Definition T4m3 (sz : Z) : axst := omrg (T4m2 sz) 0.
Definition T4d (sz : Z) : axst := omrg (T4m3 sz) 0.
Hypothesis MRG1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S50R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S51R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG3 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S52R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S53R2A1A1U0A2A2S2eA3F_;Fsz;").
Variable sd : Z -> wsub.
Hypothesis ENT5 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS14S47R2A1S6fVW;Vst;Vtmax;A3Vsd;R2A1A3S2eA3F_;Fsz;").
Hypothesis SID5 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS9aVsd;R2A1Sc2A2S2eA3F_;Fsz;").

Hypothesis R4cov : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS94S1eS10S47R2A1A1M0A1VR4;R2A1S27G0A1A3S2eA3F_;Fsz;").

Definition rt_okD (o : sobj) : bool := ltac2:(tb__ "0|b|
S16S2cLx;M0S24Vo;A1S8G0S23Vo;A1S8S37S37S36S20S22Vo;A1M1S17Z0M2A1A2S36S36S36S3Sa9R2A2S3R2R1A2M3A2S3R1Sa8A2A2S37S3R1Sb9A2S3S1Sb7S5Z8Sb8A2A2R2A2A2A2A2S36S20G1S1cP97A1A2S36S36S3G2R2A2G3A2S3R1Z1000A2A2M4A2A2S36S20G1S1cP98A1A2G4A2A2Lhi;S9S34Li;M5Sb0S16S16S34Lb;La;M6Lop;M7G7Sb1G6Lop;M8G8S2cSaS16S34La;Lw;Lsgn;M9S9S16S8S34Lk;Li;Ll;MaX16x8Llo;G5G7G7G8G8G9GaX16x8").
Lemma RT_m1_okD : ltac2:(tb__ "0|0|
ScS2cS8fS18S56SceA3S2eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma obj_range_nocells : ltac2:(tb__ "0|0|
S15S18ScS33S8S8A2S25R2S67R1A1A2S25R2R1A2A3Fo;Frho;").
Proof. intros rho [b lo hi cs d]. reflexivity. Qed.

Definition zoneR (T C SB ab szc top a : Z) : Prop := ltac2:(tb__ "0|2|
SdSbSbS0Sa9Va;A2S2Va;Sa8A2A2SdS2Va;Sb9A2S0S1Sb7S5Z8Sb8A2A2Va;A2A2A2SdSbS0VT;Va;A2S2Va;S1VT;Z1000M0A2A2A2SdSbS0VC;Va;A2S2Va;S1VC;G0A2A2A2SdSbS0Vab;Va;A2S2Va;S1Vab;Vszc;A2M1A2A2SdSbS0SaaVab;A1Va;A2S2Va;SaaG1A1A2A2S0Vtop;Va;A2A2A2A2A2A2").

Lemma R4_zone : ltac2:(tb__ "0|a|
S8S15S57S18S8SbS0Z1M0R5A2S0R5Vtmax;A2A2S69Q40M1S1aR5PcA2A2S8ScfR6S5aS58R5A1A1SbdR1A1M2SbeR5R1A2Sa6R1A1Sa5G2A1R1A7SbS0G0SbfR6R2A2M3A2S0G3Z10M4A2A2ScS68G1A1M5S1aR8P97A2S6aG1S5dS58R7A1A1A2A3ScG5S1aR9P98A2S6aG1S5cS58R8A1A1A2A3ScG5S1aRaP95A2S6aG1SbfR9R5A2A2A3Sc3S58RaA1A1S0S5bS58RbA1A1S1S69G1S1aRcPaA2A2S6bG1S1aRcS83A2A2A2A2S0S6bG1S1aRdS83A2A2S6S84A1A2Sc0S18S18SbSbS0S1S5bS58ReA1A1G4A2S69G1S28RfS22R1A1A2A2M6A2S0G6S4Z2M7Z2fA2A2A2SbScS16S24R1A1S17N10A1A3ScS16S23R1A1S17Z0A1A3A2A2Lo;S85VW;A1A3S90S18RdVR4;R10A1A3SbS0S3bS8S8S25R10ReA2M8A3RdA2S2RdS3eS8S8G8A3A2A2S1S1S5aS58R10A1A1S5SbdRcA1S4G7Z20A2A2A2S5G4SbeR10RcA2A2A2S8S4cS5dS58R11A1M9A1S5cG9A1S5aG9A1R1Sa5SbdRdA1A1S5bG9A1RfA7Tab;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tnv;F_;Fa;Fo;FA;FrhoX;Fsz;").
Proof.
  intros sz rhoX A o a Hsz nv PV Hcnt E151 E152 E149 HG TOP DEP LNK Ho Ha ab.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T1 & T2 & _ & C1 & C2 & _ & _ & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (pv_ab rhoX _ _ _ _ _ _ PV) as Eab. pose proof (pv_ub rhoX _ _ _ _ _ _ PV) as Eub. pose proof (pv_ue rhoX _ _ _ _ _ _ PV) as Eue.
  pose proof (pv_bsh rhoX _ _ _ _ _ _ PV) as Ebsh. pose proof (pv_bu rhoX _ _ _ _ _ _ PV) as Ebu. pose proof (pv_lu rhoX _ _ _ _ _ _ PV) as Elu.
  pose proof (pv_lp rhoX _ _ _ _ _ _ PV) as Elp. pose proof (pv_lt rhoX _ _ _ _ _ _ PV) as Elt. pose proof (pv_bp rhoX _ _ _ _ _ _ PV) as Ebp.
  pose proof (pv_br rhoX _ _ _ _ _ _ PV) as Ebr. pose proof (pv_lr rhoX _ _ _ _ _ _ PV) as [Elr Blr]. pose proof (r8_facts rhoX _ _ _ _ _ _ PV) as R8F.
  cbn zeta in Eab, Eub, Eue, Ebsh, Ebu, Elu, Elp, Elt, Ebp, Ebr, Elr, Blr, R8F. fold ab in Eab, Eub, Eue, Ebsh, Ebu, Ebp, Ebr.
  set (T := ag_thread (aa_geom A)) in *. set (CTX := ag_ctx (aa_geom A)) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  set (szc := Size (cls_of nv)) in *. set (rzv := rz nv) in *. set (x := chk_of A nv) in *. set (c := cls_of nv) in *.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *. set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_le_mono nv (nv + 7) 8 ltac:(lia) ltac:(lia)) as Q1.
  assert (AB8 : ab mod 8 = 0).
  { apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(lia)) ltac:(tauto)) as [q Hq].
    exists (q * 2 ^ 13 + c * 2 ^ 29 + 2 * x). unfold ab. fold SB c x. lia. }
  assert (SHR : forall k, 0 <= k <= szc -> Sh ab <= Sh (ab + k) <= Sh (ab + szc)).
  { intros k Hk. unfold Sh. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
  assert (SHK : forall k, 0 <= k -> Sh (ab + k) = Sh ab + k / 8).
  { intros k Hk. unfold Sh. destruct (proj1 (Z.mod_divide ab 8 ltac:(lia)) AB8) as [q Hq]. rewrite Hq.
    replace (q * 8 + k) with (q * 8 + k) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_mul by lia. lia. }

  pose proof (proj1 (forallb_forall _ _) (FAM4 sz Hsz) o Ho) as Fo. unfold in_famb in Fo. apply orb_prop in Fo as [Fo|Fo].
  - apply existsb_exists in Fo as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoX o), Eo, (obj_range_nocells rhoX o') in Ha. clear Eo Ho o. rename o' into o.
    apply in_app_or in Ho' as [Ho'|HLK].
    2: {
      pose proof (proj1 (Forall_forall _ _) LNK o HLK) as (B & Elo & Ehi). destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in B, Elo, Ehi. subst olo ohi.
      rewrite obj_range_mk in Ha by (clear -B TG; lia). cbn [fst snd] in Ha. do 5 right. clear -Ha B. lia. }
    unfold R4_families in Ho'. apply in_app_or in Ho' as [HRT|Ho']; [|apply in_app_or in Ho' as [HPC|HPI]].
    +
      pose proof (proj1 (forallb_forall _ _) RT_m1_okD o HRT) as OK. unfold rt_okD in OK.
      destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in OK.
      destruct lo as [lo|i1|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate OK.
      destruct hi as [hi|i2|o2 a2 b2|o2 a2 b2|o2 a2 b2|o2 a2 b2|sg2 wd2 a2|l2 i2 k2]; try discriminate OK.
      apply orb_prop in OK as [OK|OK]; [apply orb_prop in OK as [OK|OK]|];
        apply andb_prop in OK as [EB OK]; apply sv_eqb_sound in EB; subst b.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply andb_prop in OK as [OK X1].
        apply Z.leb_le in OK. apply Z.leb_le in X1. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). cbn [fst snd eval] in Ha. rewrite u64_lit in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). left.
        unfold IMG_LO, IMG_HI, STORE, MAP1, MAP1N in *. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E151, u64_lit in Ha by lia. right. left. lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E152, u64_lit in Ha by lia. right. right. left. lia.
    +
      assert (EB : bv_unsigned (eval rhoX pc_base) = T + 0xd0 + 80 * c).
      { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
        rewrite (Z.mod_small (c * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. lia. }
      assert (ECH : soff rhoX choff = 16 + 4 * (cnt_of A nv - 1)).
      { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by (clear - Hcnt; lia).
        replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
        replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
        change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
        unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
      assert (ET : bv_unsigned (eval rhoX vT) = T). { unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia. }
      right. left. destruct HPC as [<-|[<-|[<-|[<-|[]]]]].
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcc] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcs] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pck] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB, ECH in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_st] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite ET in Ha. cbn [fst snd] in Ha. lia.
    +
      assert (ELL : soff rhoX LLe = 2 * (rzv / 16 * 2) / 2).
      { destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr].
        apply soff_of_val; [|first [clear - Brz Hqr; lia | lia]]. unfold LLe. cbn [eval]. unfold V_RZ. rewrite E150, srl_val, !u64_lit by lia. change (3 mod 64) with 3.
        rewrite Z.shiftr_div_pow2 by lia. rewrite Hqr. replace (qr * 16 / 2 ^ 3) with (2 * qr) by (apply Z.div_unique with 0; lia).
        replace (qr * 16 / 16) with qr by (apply Z.div_unique with 0; lia). first [clear - Hqr Brz; lia | lia]. }
      destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr]. rewrite Hqr in ELL.
      replace (qr * 16 / 16) with qr in ELL by (apply Z.div_unique with 0; lia). replace (2 * (qr * 2) / 2) with (2 * qr) in ELL by (apply Z.div_unique with 0; lia).
      assert (SHab : Sh (ab + rzv) = Sh ab + 2 * qr). { rewrite (SHK rzv) by lia. rewrite Hqr. replace (qr * 16 / 8) with (2 * qr) by (apply Z.div_unique with 0; lia). lia. }
      destruct HPI as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold obj_range, obj_lo_of, obj_hi_of in Ha;
        cbn [ob_base ob_lo ob_hi O_H O_UB O_T O_L O_U O_P O_R] in Ha; rewrite ?soff_lit_small in Ha by lia.
      * rewrite Eab in Ha. rewrite (soff_of_val rhoX (SVar V_RZ) rzv) in Ha by (cbn [eval]; unfold V_RZ; rewrite ?E150; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eub in Ha. rewrite (soff_of_val rhoX (SVar 12) nv) in Ha by (cbn [eval]; rewrite ?E12; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eue in Ha. rewrite (soff_of_val rhoX LTe _ Elt) in Ha by lia. cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Ebsh, ELL in Ha. cbn [fst snd] in Ha. do 4 right. left. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono rzv szc 8 ltac:(lia) ltac:(lia)). assert (rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia). lia.
      * rewrite Ebu in Ha. rewrite (soff_of_val rhoX LUe (nv / 8) Elu) in Ha by (first [clear - Bn Q0; lia | lia]). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono (rzv + nv) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr in M at 1. replace ((qr * 16 + nv) / 8) with (2 * qr + nv / 8) in M by (rewrite <- (Z.div_add_l (2 * qr)) by lia; f_equal; lia).
        lia.
      * rewrite Ebp in Ha. rewrite (soff_of_val rhoX LPe lp Elp) in Ha by (unfold lp; destruct (Z.eq_dec _ _); lia). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        pose proof (Z.div_le_mono (rzv + r8) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr, Q84 in M. fold lp in M.
        replace ((qr * 16 + (8 * (nv / 8) + (if Z.eq_dec (nv mod 8) 0 then 0 else 8))) / 8) with (2 * qr + nv / 8 + lp) in M.
        2:{ unfold lp. destruct (Z.eq_dec _ _); apply Z.div_unique with 0; lia. }
        unfold lp in *. destruct (Z.eq_dec _ _); lia.
      * rewrite Ebr in Ha. rewrite (soff_of_val rhoX LRe _ Elr) in Ha by (destruct R8F as (Q81 & Q82 & Q83 & Q84); pose proof (Z.div_le_upper_bound (szc - rzv - r8) 8) as DUB8; first [clear - Blr Bsz Brz Bn Q82 Q83 DUB8; lia | lia]).
        cbn [fst snd] in Ha. do 4 right. left. rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        assert (Y1 : r8 / 8 + (szc - rzv - r8) / 8 <= (szc - rzv) / 8).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le r8 8 ltac:(lia)). pose proof (Z.mul_div_le (szc - rzv - r8) 8 ltac:(lia)). lia. }
        pose proof (Z.div_le_mono (szc - rzv) szc 8 ltac:(lia) ltac:(lia)) as Y2. pose proof (Z.div_pos r8 8 ltac:(lia) ltac:(lia)) as Y3.
        assert (Y4 : rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia).
        assert (Y5 : (szc - rzv) / 8 + 2 * qr <= szc / 8).
        { rewrite <- Y4. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (szc - rzv) 8 ltac:(lia)). pose proof (Z.mul_div_le rzv 8 ltac:(lia)). lia. }
        lia.
  -
    apply andb_prop in Fo as [Fb Fl]. apply sv_eqb_sound in Fb.
    destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in Fb, Fl. subst b.
    pose proof (urange (rw rhoX 10%positive)) as R10. pose proof (srange (rw rhoX V_DEPTH)) as R15.
    do 5 right. unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
    destruct lo as [lo|i|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate Fl.
    +
      apply andb_prop in Fl as [Fl Fl2]. apply Z.leb_le in Fl. apply Z.leb_le in Fl2. cbn [fst snd] in Ha.
      rewrite soff_lit_small in Ha by lia. unfold malloc_depth in DEP. lia.
    + apply andb_prop in Fl as [Fi Fl]. apply Pos.eqb_eq in Fi. subst i. apply sv_eqb_sound in Fl. subst hi. rewrite soff_lit_small in Ha by lia.
      unfold soff in Ha. cbn [eval] in Ha. change 15%positive with V_DEPTH in Ha. cbn [fst snd] in Ha. lia.
Qed.

Definition prim_fitb (n : Z) : bool := ltac2:(tb__ "0|0|
S37S3dSabVn;A1A1S3S1Vn;Sa6Vn;A1A2Sa5Sa7SadVn;A1A1A1A2A2").
Lemma prim_fitb_all : ltac2:(tb__ "0|1|
S8SbS0Z1M0R1A2S2R1S1G0Z10000A2A2A2ScS2cS55R2A1S2eA3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok prim_fitb 1 65536); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prim_fit : ltac2:(tb__ "0|0|
S8S0Z1R1A2ScS2cSabR2A1S2eA3S0S1R3Sa6R3A1A2Sa5Sa7SadR3A1A1A1A2F_;F_;Fn;").
Proof.
  intros n Hn HP. destruct (Z_lt_le_dec n (1 + 65536)) as [L|L].
  - pose proof (prim_fitb_all n ltac:(lia)) as H. unfold prim_fitb in H. rewrite HP in H. cbn [negb orb] in H. apply Z.leb_le in H. exact H.
  - exfalso. unfold is_primary, needed, kMaxSize, kChunkHeader2Size in HP. apply Z.leb_le in HP.
    pose proof (round_up_ge8 (Z.max n 16)). unfold rz in HP. rewrite Z.shiftl_mul_pow2 in HP by (unfold rz_log; repeat destruct (_ <=? _); lia).
    assert (0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; [lia | unfold rz_log; repeat destruct (_ <=? _); lia]). lia.
Qed.

Lemma live_user_zone : ltac2:(tb__ "0|2|
Sd8S57S8S8S8Sc3S58R4A1A1Sc4R5A1Sc5R7R6A2Sc6R8R7A2S90S33S8S8A2S32S8S8R7R6A4S61R8A1A3S0Z1R7A2SbS0R9R7A2S2R7S1R9R8A2A2A2SdSbS0S5aS58RbA1A1M0R8A2S2R8S1S1G0SacA2Z1000A2A2A2SeS5eS5eSbS90S5eR1S62RcA1A3SbS0S63R1A1M1R9A2S2R9S1G1S64R1A1A2A2A2A2Lch;A2A2F_;F_;F_;F_;F_;F_;F_;Fz;Fn;Fb;FA;Fm;").
Proof.
  intros m A b n z HG HI3 HP HS Hin Hn Hz. destruct HI3 as (_ & LIV3 & _).
  destruct (LIV3 b n Hin) as [EP|(ch & Hch & Eb & Esz)].
  - left. pose proof (primary_cls n ltac:(lia) EP) as Hc. pose proof (prim_fit n ltac:(lia) EP) as FIT. pose proof (rz_bound n) as RZ.
    destruct HP as (_ & _ & _ & P4).
    destruct (P4 _ Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
    destruct (LV b n Hin EP eq_refl) as (R1 & R2 & R3).
    pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
    pose proof (Size_pos _ Hc) as SP.
    set (c := ClassID (needed n)) in *. clearbody c.
    unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in R1, R3. rewrite kSpaceSize_val.
    nia.
  - right. exists ch. split; [exact Hch|]. destruct HS as (HS1 & _). destruct (In_nth_error _ _ Hch) as (i & Hi).
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & D11 & D12 & _).
    assert (RU : forall x, x <= round_up x PG) by (intros x; unfold round_up, PG; pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)); lia).
    pose proof (RU (sc_size ch)). pose proof (round_up_ge8 n). unfold PG in *. lia.
Qed.

Lemma DFP_split : ltac2:(tb__ "0|0|
S60S8Sb5R2R1A2SdSbaR2A1SbbR3R2A2A2F_;Fa;FG;").
Proof. intros G a [H|[H|H]]; [left; exact H | right; right; left; exact H | right; right; right; exact H]. Qed.

Lemma keep_not_DFP : ltac2:(tb__ "0|0|
S57S15S2dS68Q40A1A1S6cS8Sc7R5R4R3R2A4S93VCST;VXGL;R6R2A4SfSb5S59R7A1R3A2A1F_;F_;Fa;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md a HX HK HD.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HK as [HC|HSH].
  - destruct (client_addr_cases CST A a _ HF HC) as [ST|[(b & n & Hbn & Hab)|[FR|[HCa|FL]]]].
    + apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | lia | apply (NS (topG (aa_geom A)) (2 ^ 47)); [lia | unfold MAP1, MAP1N; lia]].
    + destruct (Hsep b n Hbn) as (N1 & _).
      destruct (live_user_zone _ A b n a HG HI3 HP HS Hbn N1 Hab) as [SP|(ch & Hch & Hz)].
      * apply (GOAL _ (fun H => ZN (or_intror (or_introl H))) SP). eapply NS; [exact SP | unfold MAP1, MAP1N; lia].
      * apply (GOAL (exists ch, In ch (aa_sec A) /\ sc_map_beg ch <= a < sc_map_beg ch + sc_map_size ch)).
        -- intros H. apply ZN. do 7 right. left. exact H.
        -- exists ch. exact (conj Hch Hz).
        -- destruct (In_nth_error _ _ Hch) as (i & Hi). destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _).
           pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as CB. eapply NS; [exact Hz | unfold IMG_HI in CB; unfold MAP1, MAP1N; lia].
    + destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      eapply NS; [exact Hx | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
    + destruct (HCST _ HCa) as [X _]. apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | | exact (HCSTD a HCa)].
      split; [exact X|]. intros [Hs _]. exact (HCSTD a HCa Hs).
    + destruct FL as (c & p & Hc & Hp & _ & Ex). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M. rewrite <- Ex in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      apply (NS a (a + 1)); [lia | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
  - pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep HSH) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | |];
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; [lia|].
    eapply NS; [split; [apply Z.le_refl | apply Z.lt_succ_diag_r] | unfold MAP1, MAP1N; lia].
Qed.

Lemma zoneR_not_DFP : ltac2:(tb__ "0|0|
S57S15S2dS68Q40A1A1S6cS8S8S8Sc7R7R6R5R4A4S58R8A1S5fS0S5aR1A1R5A2S0S1R6R5A2S1S5aR2A1SacA2A2S0Z0R6A2S2S1R8R7A2S4Z2Z2fA2A2S4cS5dR5A1S5cR5A1S5aR5A1R9R8S5bR5A1R7A7SfSb5S59ReA1R8A2A1F_;F_;F_;F_;F_;TG;F_;Fa;Fszc;Fab;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md ab szc a HX G Hab1 Hab2 Hsz Hab3 HZ HD. subst G.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, Hab2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZA|[ZS|ZK]]]]].
  - apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range a Hs). lia.
    + intros Hs. pose proof (dstat_range a Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (ag_spacebeg (aa_geom A) <= a < ag_spacebeg (aa_geom A) + kSpaceSize + 4096)); [intros H; apply ZN; right; left; exact H | rewrite kSpaceSize_val; lia |].
    apply (NS (ag_spacebeg (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
  - pose proof (Sh_in_band ab ltac:(lia)) as B1. pose proof (Sh_in_band (ab + szc) ltac:(lia)) as B2.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | lia |].
    apply (NS SHADOW_BAND_LO (a + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma SPA_updR : ltac2:(tb__ "0|5|
S7bS15S11S8S2dS33S30S16A2A1S2dS68Q40A1A1S8aS2dS33S16S16A2A1M0S2dS19A1M1ScS2cS29S10S70VW;Vst;Vtmax;R7R6R5S31S18A1M2S34S31S19A1M3A9A1A1S2eA3ScS35S33G0G1A2M4A1SccS10R8A1S10S70VW;Vst;Vtmax;R8R7R6G2S34G3A9A1A2S38G4S32G0G1R3R2A4A2A3ScdRaR4A2Sc0S19S2bRbA1R4A3S78Vsegs;RdRbRcR8R7A6S78Vsegs;ReS70VW;Vst;Vtmax;RcRbRaG2S34G3A9RdR9R8A6F_;F_;F_;F_;F_;Fnf;Fd;Fw;FtpY;Fru;Fpc;FE;FrhoY;FJx;").
Proof. intros Jx rhoY E pc ru tpY w d nf Hw Hd Hok Hnf HE. unfold CertCallocSP.upd. eapply SPA_restate; [exact Hw | exact Hd | reflexivity | exact Hok | exact Hnf | exact HE]. Qed.

Definition site_facts (A : AA) (rho rhoE : valuation) (sz : Z) : Prop := ltac2:(tb__ "0|c|
SbSbS0Z1M0Vsz;A2S0Vsz;Vtmax;A2A2SbS0S6bQ40M1S1aVrhoE;S83A2A2M2S6S84A1A2SbSc3S58VA;A1M3A1SbScS68G1A1M4S1aVrhoE;PcM5A2M6S1aVrho;G5A2A3SbS69G1G6A2S8SbScfVrhoE;S5aG3A1SbdR1A1M7SbeVA;R1A2Sa6R1A1Sa5G7A1R1A7SbSbS0G0SbfVA;R1A2M8A2S0G8Z10M9A2A2ScG4S1aVrhoE;P95A2S6aG1G8A2A3A2A2Tnv;SbScG4S1aVrhoE;P97A2S6aG1S5dG3A1A2A3SbScG4S1aVrhoE;P98A2S6aG1S5cG3A1A2A3SbS0S5bG3A1MaS1S69G1S1aVrhoE;PaA2A2G2A2A2Sc0S18S18SbSbS0S1GaG9A2S69G1S28VrhoE;S22R1A1A2A2MbA2S0GbS4Z2Z2fA2A2A2SbScS16S24R1A1S17N10A1A3ScS16S23R1A1S17Z0A1A3A2A2Lo;S85VW;A1A3A2A2A2A2A2A2A2A2").

Lemma dc_facts : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40M0A1A1S8aS78Vsegs;S8eVW;Vst;R6R5R4A5S6eVW;Vst;Vtmax;A3R3R2R1A6S41R7R5R4S69G0S1aR4Pc0A2A2A4F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof Hag as (Hagw & Hagl & Hagm).
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB. unfold top_high in Htop.
  pose proof (JG_rigid nW st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
  assert (FACT : forall p, In p (ss_facts (ax_S (E4d W st tmax))) -> holds rhoE p).
  { intros p Hp. exact (fact_of_state nW st A Kc rho rhoE tp _ _ p Hw Hp). }
  pose proof (FACT _ (F192 _ (or_introl eq_refl))) as Fs1. pose proof (FACT _ (F192 _ (or_intror (or_introl eq_refl)))) as Fs2.
  cbn [holds eval] in Fs1, Fs2. rewrite u64_lit in Fs1 by lia. rewrite u64_lit in Fs2 by (unfold SZMAX in Htmax; lia).
  pose proof (FACT _ (FDEP _ ltac:(unfold pre_facts, F_depth; cbn [app]; do 2 right; left; reflexivity))) as Fd1.
  cbn [holds eval branch_taken] in Fd1. unfold bv_lts in Fd1. apply negb_true_iff in Fd1. apply Z.ltb_ge in Fd1.
  change (bv_signed (Z_to_bv 64 (- malloc_depth))) with (- malloc_depth) in Fd1.
  pose proof (proj1 HA) as HG.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  pose proof (cnt_pos_of_fact nW st A Kc rho rhoE tp _ _ Hw YP4) as Hcnt.
  pose proof (JGb_pvals nW st A Kc rho rhoE tp _ _ (conj (proj1 Hw) (JG_JGb nW st A Kc rho rhoE tp tr md (proj2 Hw))) FGEN4 Hcnt) as PV.
  cbn zeta in PV. rewrite <- E12 in PV, Hcnt, E149.
  pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & _).
  assert (Hcnt16 : 1 <= cnt_of A (bv_unsigned (rw rhoE 12%positive)) <= 16).
  { split; [exact Hcnt|]. pose proof (pc_entry_facts segs A rhoE tp md _ HA Bn Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & X & _). exact X. }
  split; [lia|]. split; [exact Fd1|]. split; [exact HG|]. split; [exact E12|]. split; [exact (conj PV (conj Hcnt16 E149))|].
  split; [exact E151|]. split; [exact E152|]. split; [exact Htop|].
  pose proof (topG_range (aa_geom A)) as TGr. pose proof (srange (rw rhoE V_DEPTH)) as R15. unfold malloc_depth in Fd1.
  apply (unwind_objs_above W rhoE (topG (aa_geom A))); [|clear -Htop Fd1; lia | clear -TGr; lia].
  apply Forall_forall. intros p Hp. apply FACT. apply FUNW.
  unfold unwind_factsS. destruct st; [apply chain_pre_in; exact Hp|]. destruct W as [|l0 W0']; [destruct Hp | exact Hp].
Qed.

Lemma dc_site : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40M0A1A1S8aS78Vsegs;S8eVW;Vst;R6R5R4A5S6eVW;Vst;Vtmax;A3R3R2R1A6S78Vsegs;S8eVW;Vst;R7R6R5A5S3fS69G0S1aR4Pc0A2A2A1R4R3R2A6F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. pose proof (dc_facts A Kc rho rhoE tp w Hw) as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *. destruct w as [tr [ms md]].
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG. unfold malloc_depth in Fd1.

  assert (Em3808 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-3856)))) = bv_unsigned (rw rhoE 10%positive) - 3856).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-3856))) with (2 ^ 64 - 3856) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HwF : SPA segs (JG W st A Kc rho) X4f rhoE tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hw)]. unfold X4f. apply (smatchA_add_facts segs rhoE tp F_call _ _ (proj1 Hw)); [|exact FBE]. unfold F_call.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?Em3808, ?Em2112; cbn [eval]; rewrite ?u64_lit by lia; lia. }

  assert (HwR : SPA segs (JG W st A Kc rho) (X4r sz) rhoE tp (tr, mkCfg ms md)).
  { unfold X4r. eapply SPA_updR; [exact (WX4r sz Hsz) | exact (DX4r sz Hsz) | | constructor | exact HwF].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd eval].
    apply bv_eq. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. rewrite u64_lit by (unfold SZMAX in Htmax; lia).
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by (unfold SZMAX in Htmax; lia). reflexivity. }

  assert (OS : forall (Jx : jpredA) X i mid, isSome (split_obj_at (ax_S X) i mid) = true ->
            SPA segs Jx X rhoE tp (tr, mkCfg ms md) -> SPA segs Jx (osplit X i mid) rhoE tp (tr, mkCfg ms md)).
  { intros Jx X i mid Hs HX. unfold osplit. destruct (split_obj_at (ax_S X) i mid) as [S'|] eqn:E; [|exact HX]. eapply (SPA_split segs); [exact E | exact HX]. }
  unfold X4. apply OS; [exact (SPL4 sz Hsz)|]. unfold X4c. apply OS; [exact (SPL3 sz Hsz)|]. unfold X4b. apply OS; [exact (SPL2 sz Hsz)|].
  unfold X4a. apply OS; [exact (SPL1 sz Hsz)| exact HwR].
Qed.

Lemma dc_R4 : ltac2:(tb__ "0|2|
S57S15S15S8S41R4R3R2R1A4S57S15S2dS68Q40M0A1M1A1S6cG1Sc7R5R4R3R2A4ScS5fS58R6A1S58RbA1A3S98RaVR4;R9A1R3A3SfSb5S59R8A1S69G0R4A2A2A1F_;F_;F_;Fa;Fmdx;Ftpx;Frx;FAx;F_;Fsz;FrhoE;Frho;FA;").
Proof.
  intros A rho rhoE sz (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK) Ax rx tpx mdx a HX EG (o & Ho & Hoa) HD.
  cbn zeta in PV. pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (R4_zone sz rhoE A o (bv_unsigned a) Hsz PV Hcnt16 E151 E152 E149 HG Htop Fd1 LNK Ho Hoa) as HZ. cbn zeta in HZ. rewrite <- EG in HZ.
  refine (zoneR_not_DFP Ax rx tpx mdx _ _ (bv_unsigned a) HX _ _ _ _ HZ HD); rewrite ?EG; rewrite ?kSpaceSize_val; lia.
Qed.

Lemma dc_entry : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40A1A1S8S2dS6dA1M0S7eS6cS41R9R7R6R4A4S82R9A1S79Vsegs;R8R7S3fR6A1S32G0S7fR5S80R4R3A2A4A5S8eVW;Vst;RcRbRaR9R8R6R4A9SbcSaeSa4RdRcRaA3S59RdA1S96S95RaVR4;R8A1S7dR5R9R6A3A3Vs4;R8A1A2R9R7R5A7F_;F_;F_;F_;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 [Hag0 HJ0].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK). unfold malloc_depth in Fd1.
  pose proof HJ0 as (HA0 & HK0 & _ & _ & HB0 & HN0 & _). cbn [eval] in HB0, HN0.
  pose proof (AInvA_budget A rhoE tp md0 HA0) as (_ & _ & _ & HKm0 & _).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2272 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2320)))) = bv_unsigned (rw rhoE 10%positive) - 2320).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2320))) with (2 ^ 64 - 2320) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  - apply (KD_intro A Kc rhoE _ HB0 HKm0 tp tr0 md0 HA0 HK0). unfold TOPr, V_DEPTH. cbn [rw rho_sub rho_absorb].
    rewrite (WG10 sz Hsz), (WG15 sz Hsz), (WG12 sz Hsz), !eval_absorb, Em2272, Em2112.
    change (bv_signed (eval rhoE (SLit (-1536)))) with (-1536). lia.
  - destruct (AInvA_X A rhoE tp md0 HA0) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot A) rhoE _ md0 tp); [|exact HD0]. intros a Ha. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin. apply (dc_R4 A rho rhoE sz SF A rhoE tp md0 _ HX0 eq_refl Hin). rewrite u64_lit by exact Hr. exact Ha.
Qed.

Lemma dc_exit_ok : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS41ReRcRbR9A4S82ReA1Sb6SaeSa4R10RfRdA3S59R10A1A3S9fS96S95ReVR4;RcA1S7dR9RdRaA3A3Vs4;RcA1A2S15S79Vsegs;RfReS3fRdA1S32G1S7fRcS80RbRaA2A4A5S8eVW;Vst;R13R12R11R10RfRdRbA9Sb2S1dS10S66RfA1A1A1R3RbA3S79Vsegs;RcRbS65R10A1S32G1S7fRaS80R9R8A2A4A5R6R5R12RdRcRbR9A6Sa1R14S7dRfR13R10A3VR4;R12A1Vs4;R12A1S66R12A1S65R12A1S3fR12A1ReA8F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL.
  pose proof SF as (Hsz & _). subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros a Hin. apply HRM. pose proof HKD' as (HXK & _). exact (dc_R4 A rho rhoE sz SF _ rhoE tpL md' a HXK eq_refl Hin).
  - intros o' oR Ho' HoR. rewrite (NEWO sz Hsz) in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite (XPost sz) in Hr. destruct Hr.
  - intros r a j Hr. rewrite (XX4 sz Hsz) in Hr. destruct Hr.
Qed.

Lemma dc_exit_core : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS41ReRcRbR9A4S82ReA1Sb6SaeSa4R10RfRdA3S59R10A1A3S9fS96S95ReVR4;RcA1S7dR9RdRaA3A3Vs4;RcA1A2S15S79Vsegs;RfReS3fRdA1S32G1S7fRcS80RbRaA2A4A5S8eVW;Vst;R13R12R11R10RfRdRbA9Sb2S1dS10S66RfA1A1A1R3RbA3S79Vsegs;RcRbS65R10A1S32G1S7fRaS80R9R8A2A4A5R6R5R12RdRcRbR9A6S15S8aSb3R16S7dR11R15R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R2R10A9S78Vsegs;Sa0RaR9R16R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R3R10R2A6SeS57S57SeS15S15SeS15S15SbSc9R1eR3A2SbScaS93VCST;VXGL;R1eA3R1cR2A3S78Vsegs;Sc8VW;Vst;R3R1dR2A5S6fVW;Vst;Vtmax;A3R1R14R6A6A2A2LrhoX;A2Lrho'';A2LA';A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL rho' w' HLK [Hsm' HJ'].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK).
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as (HA0 & HK0 & Htp0 & HU0 & _ & HN0 & Htop0). cbn [eval] in HN0. unfold top_high in Htop0.
  pose proof (HER sz Hsz) as ER. pose proof (HT4 sz Hsz) as ET4.
  subst JL.
  destruct (entails_frA_sound segs (X4 sz) (PreD sz) (s4 sz) (R4 sz) rhoE tp tr0 ms0 md0 ER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as (HX2 & HK2 & HL2 & HT2).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  rewrite ET4 in Hsm'.
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S (X4 sz)))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. rewrite (NX4 sz Hsz). apply Pos.leb_le. exact NXE. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (X4 sz)))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros p Hp.
    exact (proj1 (holds_agree_vals _ rhoE rho' p Hag' (proj1 (forallb_forall _ _) (FBX4 sz Hsz) p Hp)) (proj1 (Forall_forall _ _) Hfacts4 p Hp)). }
  assert (HT40 : SPA segs (J_ofPA (JLD segsA (KD A Kc rhoE) (aa_depot A)) (rho_sub (rho_absorb rhoE (R4 sz) (vms md0 tp ms0)) (s4 sz)) tp rhoL tpL) (T40 sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T40. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact (FBT4 sz Hsz) | intros _; exact HF4]. }

  assert (AXr : forall X i, ax_X (oreb X i) = ax_X X) by (intros X i; unfold oreb; destruct (rebase_obj_at _ _); reflexivity).
  assert (AXm : forall X i, ax_X (omrg X i) = ax_X X) by (intros X i; unfold omrg; destruct (merge_objs_at _ _); reflexivity).
  assert (AX40 : ax_X (T40 sz) = []) by (unfold T40, ax_with_facts; cbn [ax_X ax_setS]; exact (XT4 sz Hsz)).
  assert (OR : forall (Jx : jpredA) X i, isSome (rebase_obj_at (ax_S X) i) = true -> ax_X X = [] ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (oreb X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX0 HX. unfold oreb. destruct (rebase_obj_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_rebase segs); [exact E | exact HX0 | exact HX]. }
  assert (OM : forall (Jx : jpredA) X i, isSome (merge_objs_at (ax_S X) i) = true ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (omrg X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX. unfold omrg. destruct (merge_objs_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_merge segs); [exact E | exact HX]. }
  match type of HT40 with SPA _ ?Jx _ _ _ _ => set (JP := Jx) in HT40 end.
  assert (HT4b : SPA segs JP (T4b sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4b. apply OR; [exact (RB2 sz Hsz) | unfold T4a; rewrite AXr; exact AX40 |]. unfold T4a. apply OR; [exact (RB1 sz Hsz) | exact AX40 | exact HT40]. }

  assert (HT4c : SPA segs JP (T4c sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4c. apply (SPA_select segs); [exact HT4b | exact PERM_nd | |].
    - intros i Hi. rewrite (PERM_len sz Hsz). apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt i Hi).
    - intros i Hi. rewrite (PERM_len sz Hsz) in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }

  assert (HT4d : SPA segs JP (T4d sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4d. apply OM; [exact (MRG4 sz Hsz)|]. unfold T4m3. apply OM; [exact (MRG3 sz Hsz)|]. unfold T4m2. apply OM; [exact (MRG2 sz Hsz)|].
    unfold T4m1. apply OM; [exact (MRG1 sz Hsz)| exact HT4c]. }
  assert (AX4d : ax_X (T4d sz) = []).
  { unfold T4d, T4m3, T4m2, T4m1. rewrite !AXm. unfold T4c. cbn [ax_X ax_setS]. unfold T4b, T4a. rewrite !AXr. exact AX40. }
  clear HT40 HT4b HT4c OR OM.

  assert (RNG : forall o, In o (R4 sz) -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (X4 sz)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := bumpK (with_depot A G2)).
  set (rho5 := rho_absorb rho' (R4 sz) (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho) (rl rho) (rm rho5)).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' (R4 sz) a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' (R4 sz) a <-> in_ranges rhoE (R4 sz) a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (R4DFP : forall a, in_ranges rhoE (R4 sz) a -> ~ DFP G2 (bv_unsigned a)).
  { intros a Hin. exact (dc_R4 A rho rhoE sz SF A' rhoE tpL md2 a HX2 eq_refl Hin). }
  assert (KEY : forall a, ~ DFP G2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (KEYin : forall a, in_ranges rhoE (R4 sz) a -> rm rho5 a = rm rhoE a).
  { intros a Hi. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE a) Hi)). }
  assert (BAND : forall Ax rx tpx mdx a, AInvX Ax rx tpx mdx -> SHADOW_BAND_LO <= a < SHADOW_BAND_HI -> ~ DFP (aa_depot Ax) a).
  { intros Ax rx tpx mdx a HX HB' HD. pose proof HX as (HGx & _ & _ & HRest & _ & HI3x & _). destruct HRest as (_ & _ & _ & HSx & _).
    assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSx as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HSx as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw Ax a HGx HI3x HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HB'; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; exact HB' | exact Hws]. }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE (R4 sz) (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros a Ha. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 a)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 a) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Ha. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X A rhoE tp md0 HA0) as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A'. cbn [aa_depot aa_Km aa_Kf bumpK with_depot]. lia. }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (HJGb5 : JGb W st A' Kc rho'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold A'. refine (eq_trans (rhoM_of_AK A G2 rho rho'' (fun j => eq_refl _) i) _). rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rhoM_of. rewrite rl_rho_sets. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l), <- (Hagl l).
        unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
      + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
    - split; [exact HA5|]. split; [exact HK2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact (HUSr rhoE rho5 RW5 HU0)|]. split; [exact I|].
      split; [cbn [eval]; rewrite (RW5 12%positive) by (unfold GW; lia); exact HN0|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }

  assert (HT5 : SPA segs (JGb W st A' Kc rho'') (T4d sz) rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT4d)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact AX4d | | exact HT4d | exact HJGb5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT (R4cov sz Hsz) Ho Ha). }
  pose proof (SPA_entails segs (JGb W st A' Kc rho'') GW (T4d sz) (C5 W st tmax) _ rho5 tpL _ (ENT5 sz Hsz) (SID5 sz Hsz)
                (JGb_stable nW st A' Kc rho'' HUS HKc) HT5) as HC5.
  exists A', rho'', (rho_sub rho5 (sd sz)). split; [|split; [|exact HC5]].
  - unfold depot_onlyK, A'. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf bumpK with_depot].
    repeat split; reflexivity.
  - split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros a Hk. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; reflexivity|].
      exact (keep_not_DFP A' rhoE tpL md2 (bv_unsigned a) HX2 Hk).
    + intros a HBa Hdef. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; exact Hdef|].
      exact (BAND A' rhoE tpL md2 (bv_unsigned a) HX2 HBa).
Qed.

Lemma dc_exit : ltac2:(tb__ "0|2|
S8aOF_;S57S81S15S15S2dS68Q40A1A1M0S8bS8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS57S15S15G0Sc9R13R4A2ScaS93VCST;VXGL;R14A3R12R4A3S8dVsegs;R16S78Vsegs;Sc8VW;Vst;R6R14R5A5S6fVW;Vst;Vtmax;A3R4R3A5R10A4F_;F_;Ftp';FrhoX;Frho';FA';S41R10ReRdRaA4S82R10A1Sb6SaeSa4R12R11RfA3S59R12A1A3S9fS96S95R10VR4;RdA1S7dRaRfRbA3A3Vs4;RdA1A2S15S79Vsegs;R11R10S3fReA1S32G1S7fRdS80RcRbA2A4A5S8eVW;Vst;R15R14R13R12R11ReRcA9Sb2S1dS10S66R10A1A1A1R3RcA3S79Vsegs;RdRcS65R11A1S32G1S7fRbS80RaR9A2A4A5R6R5R14ReRdRcRaA6SbSa1R16S7dR10R15R11A3VR4;R13A1Vs4;R13A1S66R13A1S65R13A1S3fR13A1RfA8S15Sb3R17S7dR11R16R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R1R10A9S8dVsegs;R1cS78Vsegs;Sa0R9R8R17R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R2R10A5R16A4F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK n' Hg' w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl n' Hg' w' HC5).
Qed.

Lemma dc_exitE : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8aOF_;S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS57S15S15G0Sc9R13R4A2ScaS93VCST;VXGL;R14A3R12R4A3S8cVsegs;S78Vsegs;Sc8VW;Vst;R6R14R5A5S6fVW;Vst;Vtmax;A3R4R3A5R10A3F_;F_;Ftp';FrhoX;Frho';FA';S41R10ReRdRaA4S82R10A1Sb6SaeSa4R12R11RfA3S59R12A1A3S9fS96S95R10VR4;RdA1S7dRaRfRbA3A3Vs4;RdA1A2S15S79Vsegs;R11R10S3fReA1S32G1S7fRdS80RcRbA2A4A5S8eVW;Vst;R15R14R13R12R11ReRcA9Sb2S1dS10S66R10A1A1A1R3RcA3S79Vsegs;RdRcS65R11A1S32G1S7fRbS80RaR9A2A4A5R6R5R14ReRdRcRaA6SbSa1R16S7dR10R15R11A3VR4;R13A1Vs4;R13A1S66R13A1S65R13A1S3fR13A1RfA8S15Sb3R17S7dR11R16R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R1R10A9S8cVsegs;S78Vsegs;Sa0R9R8R17R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R2R10A5R16A3F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl w' HC5).
Qed.

Theorem depot_call_HD : ltac2:(tb__ "0|0|
S8aOF_;S57S81S15S8bS82R3A1S7cVsegs;R6S7aR4A1A3Sd7Vsegs;R7S7aR5A1A3ScbVnW;Vst;Vtmax;S93VCST;VXGL;R7A3R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho Q HKc Hokl Hokpl rhoE tp Hcont n HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_soundPA segs ok (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  -
    intros rho1 tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    refine (seg_D_sound2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t tr0 ms0 md0 msv' HKG HMI Hh Hp Hs. exact (Hokl r t tr0 ms0 md0 msv' (KD_Kc A Kc rhoE G r t tr0 md0 HKG) HMI Hh Hp Hs).
    + intros G r t tr0 ms0 md0 x8 HKG Hp Hok. exact (Hokpl r t tr0 ms0 md0 x8 (KD_Kc A Kc rhoE G r t tr0 md0 HKG) Hp Hok).
  -
    intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  -
    intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exit ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact HgQ.
  - exact Hw4.
Qed.

Theorem depot_call_HDE : ltac2:(tb__ "0|0|
S57S81S15S8aOF_;S82R3A1SdbVnW;Vst;Vtmax;S93VCST;VXGL;R5A3R5R4R3R2A8F_;FQ;Frho;FKc;FA;").
Proof.
  intros A Kc rho Q HKc rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_completePA segs (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    exact (seg_D_complete2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exitE A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact Hw4.
Qed.
End DCW.
End CDepotCallW.

(* [comment removed for export] *)
Module SpineMallocSecOK.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "sprop"; "SVar"; "reg_sv"; "ss_facts"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_sec"; "DG"; "sec_chunk"; "aa_geom"; "aa_Km"; "aa_fs_busy"; "aa_live"; "ageom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "app"; "length"; "option"; "nil"; "true"; "bool"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "ulink"; "UStopLeOrPc"; "mem_keptA"; "ustop"; "AE_A"; "Posts_malloc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGsC"; "clsP"; "slink"; "JGs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "CS1"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_fam"; "F_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SecLinks.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OK.
Variable nW : nat. Variable st : ustop. Variable nx : positive. Variable hi : bool.
Let W : list ulink := Wcan nW.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S14S5cVCST;R1A2S5cS6bR2A2S27F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S14S5cVCST;R1A2S26S44R2A1A1F_;Fa;").
Let JGs : ltac2:(tb__ "0|0|
SbSbF_;SbS31S2S17Q40A1S2eFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S51VnW;Vst;Vnx;A3").
Let JGsC : ltac2:(tb__ "0|0|
SbSbF_;SbS31S2S17Q40A1S2eFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S4eVnW;Vst;Vnx;A3").
Let Posts (A : AA) (Kc : KcA) : ltac2:(tb__ "0|0|
S19S1bS5fS58A2A1") := ltac2:(tb__ "0|0|
S38S37S69S0A1VCST;VXGL;VW;Vst;VA;VKc;A8").

Variables (E1 D2 T4a T4b C5a C5b : axst).

Hypothesis HG12 : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S19G1A1M2S2aS30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4fVhi;S16G0R6A2S2fS16G0S3R7PcM3A2A2A1A3S2S2G2S50S16G0RaA2S2fS16G0S3RbG3A2A2A1RbR3A4S28S0RfS2bS0VJGs;SbR1LX;M4ReRdR4RbA5VD2;R3R2A5R9A4F_;FtpY;FrhoY;Frho';S2S28S0RdS2bS0VJGsC;G4RcRbRaR9A5VE1;R1R8A5R7A4FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG3 : ltac2:(tb__ "0|7|
S29OF_;SbS31S2S17Q40M0A1M1S2aS30VW;Vst;A2S32R5A1S2dS0R8S2cR6A1A3S4bS0R9S2cR7A1A3S3eS3dS40S1eSeScR9A1A2A1Z1A2S41Z2Z14A2A2S14S25S3cS4dS16G0R8A2A1M2R1A2S3eR1S3dG2S3fS2fS16G0S3R9PcM3A2A2A1Z8A2A2A2A2S26S24S1fS17Q8A1M4A1S4RaS18G0R2A2A2S1cG4A1A3A1F_;Fz;S2S2S19G1A1M5S60SfReA1S16G0RbA2S2fS16G0S3RcG3A2A2A1RcR3A5S28S0R10S2bS0VJGs;SbS5dR1A1LX;RfReR4RcA5VT4a;R3R2A5RbA4F_;FtY;FrY;Frho'';S2G5S28S0RfS2bS0VJGs;SbR1LX;M6ReRdRcRbA5VT4b;R2R1A5RaA4FtY;FrY;S2G5S28S0R10S2bS0VJGs;G6RfReRdRcA5VD2;R2R1A5RbA4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41a : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S2aS24S36Vst;S34A3S24S19S33A1VW;S20S33A1A3F_;S30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4bS0RaS2cR8A1A3SdS2S2S19G1A1M2S1bS14S14A2M3S45G3R1S43R5A1A3S42R2S1aS14S14S16G0RdA2S2fS16G0S3RePcA2A2A1A4A2F_;Fbn;S48R5RdR4A3S28S0R11S2bS0VJGs;S47SbS5dR1A1LX;M4R6A2R10RfR5RdA5VC5a;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S28S0ReS2bS0VJGs;G4RdRcRbRaA5VT4a;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41b : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S2aS24S36Vst;S34A3S24S19S33A1VW;S20S33A1A3F_;S30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4bS0RaS2cR8A1A3SdS2S2S19G1A1M2S1bS14S14A2M3S45G3R1S43R5A1A3S42R2S1aS14S14S16G0RdA2S2fS16G0S3RePcA2A2A1A4A2F_;Fbn;S48R5RdR4A3S28S0R11S2bS0VJGs;S47SbR1LX;M4R6A2R10RfR5RdA5VC5b;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S28S0ReS2bS0VJGs;G4RdRcRbRaA5VT4b;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HTLa : ltac2:(tb__ "0|8|
S29OF_;SbS31S2S2S17Q40M0A1M1S19G1A1M2SdS30VW;Vst;A2S32R7A1S2dS0RaS2cR8A1A3S15S24G1S3R8R1A2S3R9R1A2A3Fi;S15S24S19S17Q8A1M3A1S5R9R1A2S5RaR1A2A3Fl;S35VCST;VXGL;RcRcS4RaA1S4R9A1A6S3cS40S1eSeScRdA1A2A1S10RdA1A2S1bS14S14A2M4S45G4R1S43R9A1A3S42R2S1aS14S14S16G0RcA2M5S2fS16G0S3RdPcA2A2A1M6A4A2F_;Fbn;S14S25S3cS4dG5A1M7R1A2S3eR1S3dG7S3fG6Z8A2A2A2A2S26S24S1fG3A1S4ReS18G0R2A2A2S1cG3A1A3A1F_;Fz;S2G2S28S0R13S2bS0VJGs;S47SbS5dR1A1LX;RcA2R12R11RfReA5VC5a;R2R1A5S57S0S56R10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Hypothesis HTLb : ltac2:(tb__ "0|8|
S29OF_;SbS31S2S2S17Q40M0A1M1S19G1A1M2SdS30VW;Vst;A2S32R7A1S2dS0RaS2cR8A1A3S15S24G1S3R8R1A2S3R9R1A2A3Fi;S15S24S19S17Q8A1M3A1S5R9R1A2S5RaR1A2A3Fl;S35VCST;VXGL;RcRcS4RaA1S4R9A1A6S3cS40S1eSeScRdA1A2A1S10RdA1A2S1bS14S14A2M4S45G4R1S43R9A1A3S42R2S1aS14S14S16G0RcA2M5S2fS16G0S3RdPcA2A2A1M6A4A2F_;Fbn;S14S25S3cS4dG5A1M7R1A2S3eR1S3dG7S3fG6Z8A2A2A2A2S26S24S1fG3A1S4ReS18G0R2A2A2S1cG3A1A3A1F_;Fz;S2G2S28S0R13S2bS0VJGs;S47SbR1LX;RcA2R12R11RfReA5VC5b;R2R1A5S57S0S56R10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").

Lemma c5_pure : ltac2:(tb__ "0|7|
SbSbF_;SdSbS31S2S2S2S2S17Q40M0A1M1S2S19G1A1S19S53A1S52SbS24S13SfReR1A1A1SfR1A1A3FX;SbS24S19SeA1ScRfR1A1A1ScR1A1A3FX;SbS24S19S1bS14S14A2M2A1M3S12R10R1A1A1S12R1A1A3FX;SbS24S19G3A1S11R11R1A1A1S11R1A1A3FX;S16G0R9A2S14S2fS16G0S3RePcM4A2A2A1S14S50R2R1RfReA4S60SfR12A1R3R2RfReA5S48R14RfReA3G2S45G2R1S43R16A1A3S42R2S1aS14S14R7R6A4A2F_;Fbn;VJGs;S47R17R16A2R15R14R10RfReRdRcRbA9S25S35VCST;VXGL;R16R16S4R14A1S4R11A1A6S25S14S25S3cS4dR8A1M5R1A2S3eR1S3dG5S3fS2fS16G0S3R12G4A2A2A1Z8A2A2A2A2S26S24S1fS17Q8A1M6A1S4R13S18G0R2A2A2S1cG6A1A3A1F_;Fz;S25S15S24G1S3R12R1A2S3R15R1A2A3Fi;S25S15S24S19G6A1S5R12R1A2S5R15R1A2A3Fl;G2S45G2R1S43R18A1A3S42R2S1aS14S14R9S2fS16G0S3R13G4A2A2A1A4A2F_;Fbn;A2A2A2A2F_;F_;F_;F_;F_;TL;Tua;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho3;Frho2;Frho1;Frho;FKc;FA;FG2;FBX;").
Proof.
  intros BX G2 A Kc rho rho1 rho2 rho3 a r tp tr md BXg BXs BXl BXf ua L SL1 SL4 DL HDB HJ.
  assert (E12 : rw rho3 12%positive = rw rho 12%positive).
  { destruct SL1 as (W1 & _). destruct SL4 as (W2 & _). destruct DL as (W3 & _). rewrite W3, W2. apply W1. }
  unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.JGs in HJ. rewrite E12 in HJ. fold L in HJ. cbn zeta in HJ.
  destruct HJ as (_ & _ & HA & HPD & _ & _ & _ & Hnv & _).
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  set (As := AXK BX G2 (bumpV A nv)) in *.
  assert (Eg : aa_geom As = aa_geom A) by (unfold As, AXK; cbn [aa_geom bumpK with_depot]; rewrite BXg; reflexivity).
  assert (Es : aa_sec As = aa_sec A) by (unfold As, AXK; cbn [aa_sec bumpK with_depot]; rewrite BXs; reflexivity).
  assert (El : aa_live As = aa_live A) by (unfold As, AXK; cbn [aa_live bumpK with_depot]; rewrite BXl; reflexivity).
  assert (Ef : aa_fs_busy As = aa_fs_busy A) by (unfold As, AXK; cbn [aa_fs_busy bumpK with_depot]; rewrite BXf; reflexivity).
  assert (Ed : aa_depot As = G2) by reflexivity.
  assert (HPDs : pendS As ua L md).
  { destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB).
    unfold pendS. rewrite Eg, Es, Ed. repeat (split; [assumption|]). exact HDB. }
  rewrite <- Eg in SL4. rewrite <- Ed in DL.
  destruct (links_kept CST XGL HCST HXGL HCSTS HCSTD As r tp md nv ua rho rho1 rho2 rho3 HA Hnv HPDs SL1 SL4 DL) as (HK & RD & HW & HL).
  rewrite E12. fold nv L.
  split; [|split; [exact RD|split; [exact HW|split; [exact HL|exact HDB]]]].
  -
    assert (CA : forall x, client_addrA CST As x <-> client_addrA CST A x).
    { intros x. unfold client_addrA, client_mut_addrA, aa_frames. rewrite Eg, El, Ef. reflexivity. }
    assert (CS : forall x, client_shadowA CST XGL As x <-> client_shadowA CST XGL A x).
    { intros x. unfold client_shadowA. split; (intros [(y & Hy & E)|H]; [left; exists y; split; [apply CA; exact Hy | exact E] | right; exact H]). }
    destruct HK as [K1 K2]. split.
    + intros x Bx Hx. apply K1; [exact Bx|]. destruct Hx as [(C1 & C2 & NE)|(C1 & C2 & Hd)]; [left | right]; (split; [|split]); try assumption; first [apply CA | apply CS]; assumption.
    + intros x j Hx Hj Hd. apply (K2 x j); [|exact Hj|exact Hd]. destruct Hx as [[C1 C2]|GX]; [left; split; apply CA; assumption | right; exact GX].
Qed.

Lemma d2_pure : ltac2:(tb__ "0|2|
SbS31S2S17Q40A1M0S2S19G0A1S19S53A1S52VJGs;SbR1LX;R8R7R6R5R4R3R2R1A9S25S3eS3dS40S1eSeScR9A1A2A1M1Z1A2S41Z2Z14A2A2S3cG1S10R9A1A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.JGs in HJ. cbn zeta in HJ.
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & _ & HBO).
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  split.
  - pose proof (AInvA_sec_bound segsA _ r tp md HA) as SB. cbn [aa_sec bumpV] in SB.
    assert (E : large_live (bumpV A nv) = large_live A) by reflexivity. rewrite E in SB.
    pose proof (budget_ok_alloc_room A nv HBO) as RM. unfold sec_room, SEC_SLACK in RM. clear -SB RM. lia.
  - destruct HA as (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HLd).
    destruct HLd as (_ & _ & _ & _ & _ & _ & _ & _ & L9 & _). cbn [aa_sec aa_Km bumpV] in L9. exact L9.
Qed.

Theorem sec_ok_chain : ltac2:(tb__ "0|2|
S29OF_;SbS31S2S17Q40M0A1M1S19G1A1S24S36Vst;S34A3S24S19S33A1VW;S20S33A1A3F_;S30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4bS0RaS2cR8A1A3S4fVhi;S16G0R7A2S2fS16G0S3R8PcA2A2A1A3S2S28S0RdS2bS0VJGsC;SbR1LX;RcRbRaR9A5VE1;R1R8A5S57S0S56RaR8VPosts;RcRbA2A5A4FrhoX;F_;F_;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HW HUS HKc Hokl Hokpl HC rhoX.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  apply (HG12 ok A Kc rho a tp _ HUS HKc Hokl HC). intros rho1 rhoY tpY SL1.
  apply (triple_pre_pure segsA ok _ _ (Z.of_nat (length (aa_sec A)) + 1 < 2 ^ 20 /\ Z.of_nat (length (aa_sec A)) <= aa_Km A)).
  { intros [tr [ms md]] Hw. exact (d2_pure A Kc rho1 a rhoY tpY tr md (proj2 Hw)). }
  intros [HRM HL9].
  assert (E1r : rw rho1 12%positive = rw rho 12%positive) by (destruct SL1 as (W1 & _); apply W1).
  assert (RD1 : forall z, Sh ua <= z < Sh ua + L / 8 -> rm rho1 (Z_to_bv 64 z) <> None) by (destruct SL1 as (_ & _ & _ & D1); exact D1).
  apply (HG3 ok A Kc rho1 a _ HUS HKc Hokl Hokpl HRM); [rewrite E1r; exact RD1 | |].
  -
    rewrite E1r. fold ua L. intros rho2 rY tY SL4.
    assert (E2r : rw rho2 12%positive = rw rho 12%positive) by (destruct SL4 as (W2 & _); rewrite W2; exact E1r).
    apply (HG41a ok A Kc rho2 a _ HW HUS HKc Hokl Hokpl). rewrite E2r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure (fun X : AA => bumpP X) G2 A Kc rho rho1 rho2 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 SL4 DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLa ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
  -
    intros rY tY.
    apply (HG41b ok A Kc rho1 a _ HW HUS HKc Hokl Hokpl). rewrite E1r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure (fun X : AA => X) G2 A Kc rho rho1 rho1 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 (slink4_refl (aa_geom A) ua L rho1 RD1) DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLb ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
Qed.
End OK.

Section GRANT.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S24S15S5bVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S24S22S6cS1Vnx;A2S21A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S24SaS8S5eS59VW;Vst;Vtmax;A3A1ZbA2S7S5aA1A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S46S6S1dS6S1dS6S1dS6S1dS6S3bVW;Vst;A2S3aS39A1A3S66A3S68A3S67Vtmax;Z8A2A3S9S5eS59VW;Vst;Vtmax;A3A1A1A3").

Lemma grant_Jo : ltac2:(tb__ "0|3|
SbS31S2S2S19S17Q40A1M0A1S19S53A1M1S4aS52G0S30VW;Vst;A2S32R9A1S4cS0R8R7S59VW;Vst;Vtmax;A3S1aG1S61R6S62R5R4A2A4A5S6aVW;Vst;RcRbRaR9R8R7R5A9S63S49R7U0A2S49R7U3A2R6S49R7U1M2A2R5A5S4eVnW;Vst;Vnx;SbR1LX;ReRdRcR6S65RbVnx;R6A3RaR9S55S64S54R7A1S49R8G2A2R6A3R7A2AcF_;F_;F_;F_;F_;Fa;Fmd;Fms;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr ms md a HUS HKc Hsp HJG Hpl.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & _ & E142 & _).
  assert (Hnv : 64513 <= nv < 2 ^ 39).
  { pose proof (proj1 (Forall_forall _ _) (smatch_pendingA_facts segsA rhoX tp _ _ Hsp) (SPUle (SLit (rzf_lo 8)) (SVar 12))
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn [In]; left; reflexivity)) as F.
    destruct HJG as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  pose proof (mmap_len_sym segsA rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11
                ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  apply (JGsC_of_Sec nW st tmax nx Hnx (fun X : AA => X) A Kc rho a _ tp tr _ (fun X => eq_refl)). pose proof Hnx as Hnx'. unfold W in Hnx'.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.JGs. rewrite Hnx'.
  assert (NXG' : Pos.leb GW (nxS W st tmax) = true) by (rewrite Hnx; exact NXG).
  pose proof (JGsC_grant W st tmax A Kc rho rhoX tp tr md a (ms_gpr ms 1) (ms_gpr ms 0) (ms_gpr ms 3) HUS HKc HJG
                (smatch_pendingA_MI segsA rhoX tp _ tr ms md Hsp) Hnv HnZ Hpl NXG') as H.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.JGs in H. rewrite Hnx in H. exact H.
Qed.

Lemma cls_split : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S5fS2S19G1A1S2aS4fS21S16G0R5A2S2fS16G0S3R6PcM2A2A2A1A3S28S0RaS2bS0S4eVnW;Vst;Vnx;SbR1LX;M3R9R8R7R6A8R5R4R3A5R2A4F_;S4fS23S16G0R6A2S2fS16G0S3R7G2A2A2A1A3S28S0RbS2bS0S4eVnW;Vst;Vnx;G3RaR9R8R7A8R6R5R4A5R3A4M4F_;G4F_;F_;FQ;Ftp;FrhoX;FE;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a E rhoX tp Q HH HL.
  apply (triple_pre_pure segsA ok _ _ (clsP true (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))
                                       \/ clsP false (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))))).
  - intros [tr [ms md]] Hw. pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as [HJ _]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.JGs in HJ. cbn zeta in HJ. destruct HJ as (_ & _ & _ & HPD & _).
    destruct HPD as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & _ & _ & PDB).
    unfold clsP. destruct PDB as [X|X]; [right; exact X | left; exact X].
  - intros [X|X]; [exact (HH X) | exact (HL X)].
Qed.
End GRANT.
End SpineMallocSecOK.

(* [comment removed for export] *)
Module SpineCallocR11.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "reg_sv"; "eval"; "ss_facts"; "valuation"; "ss_objs"; "swf"; "sprop_below"; "ss_lenient"; "ss_pc"; "sv_below"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "list"; "nil"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "GR"; "rMS"; "sMS"; "O_pcm"; "O_ri"; "beg1"; "beg2"; "cX"; "idx_rot"; "nobj"; "relM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "ge"; "le"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "ghosts"; "mlink"; "F0"; "U0"; "entryR"; "frozen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP"; "ph_set"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineCallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "rigids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR9"; "O_piece"; "O_shp"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocR10"; "a2_e"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocR10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition a0_e (eb : sv) : sv := SAlu ALU_AND eb (SLit 18446744073709547520).

Lemma a0_val : ltac2:(tb__ "0|1|
SfS8S22S0S22S34Q40M0SdR3R2A2A2R1A3S0S22S38R2Z1000A2Z0A3S0S33G0A1SdR5S4dR4A1A2SdR5R4A2A3F_;F_;FB;Feb;Fr;").
Proof.
  intros r eb B EB HM. unfold a0_e. cbn [eval]. apply bv_eq. rewrite and_val. replace (bv_unsigned (Z_to_bv 64 18446744073709547520)) with 18446744073709547520 by reflexivity.
  rewrite EB. apply land_m4096_id; [|exact HM]. rewrite <- EB. apply urange.
Qed.

Section ADDR.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S50VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S42VA;Vrb;Vr;A3").

Lemma beg1_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2cA2A2S45VA;Vrb;A2A3").
Proof.
  unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _ & (_ & AU0 & MU1 & _) & _ & _ & (G12 & G13 & G14 & TG) & _).
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). destruct GH as (_ & _ & _ & _ & Q224 & _).
  unfold beg1, rb_e, vMU, vSB, V_CLS, U0, region_beg, kRegionSize. cbn [eval]. rewrite !add_val, sll_val, E155, E158, Q224, !u64_lit by lia.
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma beg2_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2dA2A2S44VA;Vrb;A2A3").
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
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S46VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S21S4aVp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S49VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SfS47Vrb;R1A2S42VA;Vrb;R2A3S0S22S34Q40SdR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S37S35S5dS5cVA;A1A1M0Z100000000A2VB;A2S1S37S35VB;Z40000A2S35G0Z2000000000A2A2S0S22S38VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM_c : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S43VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S36S40R2R3A2Z40000A2F_;Fmd;Ftp;").
Hypothesis HROOM_r : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S43VA;Vrb;Vtp0;Vmd0;S48Vp;U1Vph;A3R2R1A7S36S40R2R3A2Z8000A2F_;Fmd;Ftp;").

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
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2S4VLX;A1A1S2VCX;A1A2S1cG3S1eG1G2S16G0S1eS8S8S4dVeb;A1Veb;A4S1aG0A1A3S1aS9A1A4A2A3").

Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VCX;A1A1A4S23S7G0S32S1fS7S4fVW;A1S16S7S4bS16S7S4cS16S7S2aS16S7S2bS1aS7A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S54S9S4eVW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCX;A1A1A2S18A3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S1dS3aA1S59S25S14S2VCX;A1A1A2S1cS3aS3bA2A3").
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
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VEM;A1A1A4S23S7G0S32S1fS7S4fVW;A1S16S7S4bS16S7S4cS16S7S2aS16S7S2bS16S7S51Veb;A1S1aS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S54S9S4eVW;Vst;A2SeS2VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S17S11S2VCMR;A1A1S18A3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2VEM;A1S2VCMR;A1A2S1cG3S1eG1G2S16G0S1eS8S8S5fVeb;A1SbZ8000A1A4S1aG0A1A3S1aS9A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S17S11S2VCMC;A1A1S18A3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S1dS19S7A1M0A1S5bVCMC;S3cS29VCMC;A1A3S1cG0S28VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S17S5aVCMC;S3cS29VCMC;A1S28VCMC;A1S23S3S6S4S3dA4A5S18A3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S17S26S57SaS2VCMC;A1A1A2S18A3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCMC;A1A1A2S18A3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S17S53S9S12SaS2VCMC;A1M0A1A1SeG0A1A3S18A3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S17S53S9S12SaS2S5eVCMC;S29VCMC;A1S28VCMC;A1A3A1A1A1SeS2VCMC;A1A1A3S18A3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S17S58S2fVDM;A1A1S18A3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S19S7A1S10S2VRM;A1A1M0S1fS7S24S7S55S30VDM;A1U2A2G0A3S16S7S51Veb;A1S16S7S52Veb;A1S1aS7A1A3A3A3A3").

Theorem piece_full : ltac2:(tb__ "0|1|
SfS19S33Q40A1A1M0S56SfG0VTR;S3fS25S41VA;VKc;Vrb;Vtp0;Vmd0;S48Vp;U3Vph;A3A6S31VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S3fS25S41VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
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
End SpineCallocR11.

(* [comment removed for export] *)
Module SpineMallocR6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "eval"; "rw"; "rm"; "SAlu"; "SLit"; "SPBranch"; "SPNot"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "lt"; "add"; "mul"; "to_nat"; "pow"; "sub"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "false"; "true"; "nil"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "entryR"; "ph0"; "FAb"; "frozen"; "ghosts"; "ph_fill"; "gh_nf"; "phase"; "gh_new"; "ph_cnt"; "ph_pop"; "ph_ri"; "rlink"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cs_cache"; "class_state"; "cs_free_array"; "aa_cache_inited"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "kchunks"; "refillA"; "take_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "ulink"; "mem_keptA"; "ustop"; "UStopLeOrPc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "cnt_of"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "cR0"; "vAU"; "vK"; "vMFA"; "vMU"; "vNF"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4"; "ph_setcnt"; "ph_setri"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1"; "r0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6.ARMN"; "e16N"; "e_srcN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6.ASMN"; "exitT"; "phFN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6"; "e16N"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma entry_fa : ltac2:(tb__ "0|3|
S34S1S16S32Q40M0A1A1S2fS16S42A1S44S1S22R7R6R5R4R3R2R1A7S33G0S3R7PcA2A2S0S46R1A1S0S47RaR2A2S36S55SdS4RaA1A2S52ScS0ScSeZ0M1R1A2S10R1SfS17S0S37R3A1M2A2A1A2A2S53R3S54S11S24ReRdA2S12Z4R2A2A2U4S50S0S13R2A1S37R4A1G1A4A3A2F_;Fidx;S0S49S0R1G2A3ScSeG1R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;A2Tm0;Tcs;Tc;Tnv;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE nv c cs m0.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & S1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _).
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MS : forall z, ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize + 4096 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C9 & _ & N7 & _).
  split.
  - intros idx Hidx j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    assert (NE : nth_error (cs_free_array cs) (Z.to_nat idx) = Some (nth (Z.to_nat idx) (cs_free_array cs) 0)) by (apply nth_error_nth'; lia).
    pose proof (C9 _ _ NE j Hj) as Hc. cbn [c_addr c_w RtCells.c_val] in Hc. rewrite Z2Nat.id in Hc by lia.
    unfold FAb. fold nv c. rewrite MS in Hc; [exact Hc|]. rewrite kSpaceSize_val. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. clear -Hidx Hj MF0 C1. lia.
  - intros x Hx. destruct (N7 x ltac:(apply in_or_app; left; exact Hx)) as (X1 & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia. lia.
Qed.

Section ARMN.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S22VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let k : Z := kchunks c.
Let fa : list Z := cs_free_array cs.

Hypothesis HNP : ltac2:(tb__ "0|0|
SeVk;SfS17S0Vfa;A2A1A2").

Lemma N_refill_cs : ltac2:(tb__ "0|0|
SbS36S3cVc;Vcs;A2S3fS13Vk;A1Vcs;A2A3").
Proof. unfold refill_cs, needs_populate. fold k fa. replace (Z.of_nat (length fa) <? k) with false by (symmetry; apply Z.ltb_ge; exact HNP). reflexivity. Qed.

Lemma N_HCACHE : ltac2:(tb__ "0|0|
SbS16S0A1S35S3cVc;Vcs;A2A1S51S0S13S15SfS17S0Vfa;A2A1Vk;A2A1Vfa;A3A3").
Proof.
  rewrite N_refill_cs. unfold take_cs. cbn [cs_cache]. fold fa. f_equal.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HLEN : ltac2:(tb__ "0|0|
SbS0SfS17S0S35S3cVc;Vcs;A2A1A2A1Vk;A3").
Proof.
  rewrite N_HCACHE, length_skipn.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HIDS : ltac2:(tb__ "0|0|
S0S49S0R1Vfa;A3ScSeZ0R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;").
Proof. exact (proj2 (entry_fa _ _ _ _ _ _ _ HE)). Qed.

Lemma N_HIDC : ltac2:(tb__ "0|0|
S0S49S0R1S35S3cVc;Vcs;A2A1A3ScSeZ0R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;").
Proof. intros x Hx. rewrite N_HCACHE in Hx. apply N_HIDS. rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length fa) - k)) fa). apply in_or_app. right. exact Hx. Qed.

Definition e_srcN : sv := ltac2:(tb__ "0|0|
S5S61S5cS5S62S5S63S5bS58A3S6Z2A1A3A3").
Definition e16N : sv := SAlu ALU_SUB vNF vK.

Lemma N_HSRCP : ltac2:(tb__ "0|1|
S1S25Vrb;R1A2S26VA;Vrb;R2A3SbS32Q40M0A1S2R3S69A2S31G0S11S24VA;Vrb;A2S12Z4S15SfS17S0Vfa;A2A1Vk;A2A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct HGh as (_ & Q221 & _ & _ & _ & _ & Q226 & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _). fold k in K1. fold fa in MF0.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384) by (unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c; lia).
  unfold e_srcN, vFA, vNF, vK. cbn [eval]. rewrite Q221, Q226, Q227. apply bv_eq.
  rewrite add_val, sll_val, sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k), (u64_lit (FAb A rb)) by lia.
  change (2 mod 64) with 2. rewrite (Z.mod_small (Z.of_nat (length fa) - k)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HRIv : ltac2:(tb__ "0|2|
S1S25Vrb;R1A2S26VA;Vrb;R2A3S3cVc;Vcs;A2S36ScSbS32Q40M0A1M1S2R4S68A2S31G0SfS17S0S37R1A1A2A1A2A3ScSbG1S2R4S59A2S31G0S3aR1A1A2A3ScSbG1S2R4S57A2S31G0S39R1A1A2A3SbG1S2R4S5aA2S31G0S3bR1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Proof.
  intros r HFz HGh csR. unfold csR. rewrite N_refill_cs. unfold take_cs. cbn [cs_free_array cs_mapped_free_array cs_allocated_user cs_mapped_user]. fold fa.
  destruct HGh as (_ & Q221 & Q222 & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c cs in Q222, Q223, Q224. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _). fold k in K1. fold fa in MF0.
  split; [|split; [exact Q222 | split; [exact Q223 | exact Q224]]].
  unfold e16N, vNF, vK. cbn [eval]. rewrite Q221, Q227. apply bv_eq. rewrite sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k) by lia.
  rewrite firstn_length_le by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HSRC : ltac2:(tb__ "0|1|
S0S52ScSeZ0M0R2A2SeR2Vk;A2A2S2eVA;Vrb;S4eS23R3A2S55SdS4Vrb;A1A2R2A5S0ScSeG0R1A2S10R1SfS17S0Vfa;A2A1A2A2S53R5S54S11S24VA;Vrb;A2S12Z4R2A2A2U4S50S0S13R2A1Vfa;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Proof.
  intros i m Hi (L1 & _) idx Hidx.
  eapply cell_ok_agree_range; [|exact (proj1 (entry_fa _ _ _ _ _ _ _ HE) idx Hidx)]. cbn [c_addr c_w]. intros z Hz. apply L1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & PS1) & _). fold k in K1. fold fa in MF0.
  change (Z.of_nat 4) with 4 in Hz. unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
  unfold zoneR, phK, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb]. unfold PCE. fold nv c.
  intros [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; lia.
Qed.
End ARMN.

Section ASMN.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S34S40S16S1cS66S4dA2A1F_;F_;").
Variables (W : list ulink) (st : ustop).
Variables (E3 E3P LP LJ XL LZ : axst).
Notation AInvS := (AInvA segs).
Hypothesis HWs : ltac2:(tb__ "0|0|
SbS44Vst;S45A3SbS16S42A1VW;S1bS42A1A3F_;").
Hypothesis FJ : ltac2:(tb__ "0|0|
S49S9S8S7S64S5bS58A3A1SaS65VLJ;A1A1A3").

Definition prefixT : Prop := ltac2:(tb__ "0|2|
S34S40S1S16S32Q40A1A1M0S2fS1dS1dOF_;F_;S4aR5R1A2S41R6A1S1S1G0S1dS22RcRaR9R8VW;Vst;R4A7S1R9S20SdS21ReRdRcRbRaS23A6VLP;R1R4A5R3A2Fr';S1RaS20SdS21RfReRdRcRbS23A6M1VLJ;R1R5A5R4A2Fr';RaS20SdG1S56VE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition popT (e_src : sv) : Prop := ltac2:(tb__ "0|9|
S34S40S1S16S32Q40M0A1M1A1M2S2fS1dS1dOF_;F_;S4aR5R1A2S41R6A1S1S22R9R7R6R5VW;Vst;R1A7S29ScSbS0S2cR1A1Z0M3A3ScSbS18S2bR1A1S19A3SbS18S2dR1A1S19A3A2A2S16S0A1M4S33G0S3RbPcA2A2S0S46R1A1S0S3dR1A1S0SfS17S0R4A2A1S0S0S52ScSeG3R2A2M5SeR2R4A2A2S2eR14R12S4eRaR3A2S55SdS4R12A1A2R2A5S0ScSeG3R1A2S10R1R6A2A2S53R5S54S11S24R17R15A2S12Z4M6R2A2A2U4S50S0S13R2A1RbG3A4A3A2F_;Fidx;F_;F_;Fm;Fi;SeR3R2A2SeS12G6R3A2Z20000000A2S10G3S27RaA1A2ScSeG3S28R15R13A2M7A2ScSbS0S11G7S2aR15R13A2M8A2R5A3SeS27RbA1G8A2A2A2F_;S0S49S0R1RaA3ScG5S10R2S14Z2Z1cA2A2A2F_;Fx;SbG4S35S3cR8S47R16R9A2A2A1S51S0S13S15R6R7A2A1RaA3A3S1S25R16R1A2S26R19R17R2A3SbG1S2R3Ve_src;A2S31G0S11S24R1aR18A2S12G6S15RaRbA2A2A2A2A3F_;F_;Fr;S1G2S1dS1R17S20SdS21R1cR1bR1aR19R18S4eR12RdA2A6VXL;R1R3A5R2A2Fr';R17S20SdS21R1cR1bR1aR19R18R12A6VLJ;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;TnfP;Tk;Tc;Tnv;FfaP;FPH0;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition entryT : Prop := ltac2:(tb__ "0|2|
S34S40S1S1S16S32Q40M0A1A1S1fSbS18S38R6A1S1aA3SbS0S48R7S33G0S3R5PcA2A2A2Z0A3S20SdS4fVW;Vst;R8R7R6A5VE3;R5R4R3A6ScS22R9R6R5S60S1eR4A1A1M1VW;Vst;R7A7S20SdS21R9R8R6R5G1S23A6S56VE3;A1S67R9R6A2R5R4A6A2F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Definition exitT (e16 e24 e32 e48 : sv) : Prop := ltac2:(tb__ "0|7|
S34S40S1S16S32Q40M0A1M1A1M2S2fS1dS1dOF_;F_;S4aR5R1A2S41R6A1S1S22R9R7R6R5VW;Vst;R1A7S29S33G0S3R9PcA2A2S0S46R1A1S0S3dR1A1S0ScSbS0S2cR4A1R1A3ScSbS18S2bR4A1S19A3SbS18S2dR4A1S19A3A2A2S10Z0M3S27R5A1A2ScSeG3S28R10ReA2M4A2ScSeS12Z4S11G4S2aR10ReA2M5A2A2Z20000000A2SeS27R6A1G5A2A2A2F_;SbS18S38R10A1S1aA3S1S25R10R1A2S26R13R11R2A3S3cR8S47R14R9A2A2M6S36ScSbG1S2R4Ve16;A2S31G0SfS17S0S37R1A1A2A1A2A3ScSbG1S2R4Ve24;A2S31G0S3aR1A1A2A3ScSbG1S2R4Ve32;A2S31G0S39R1A1A2A3SbG1S2R4Ve48;A2S31G0S3bR1A1A2A3A2A2A2TcsR;F_;F_;Fr;SbS0SfS17S0S35S3cR6S47R12R7A2A2A1A2A1R5A3S0S49S0R1S35G6A1A3ScSeG3R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;S1G2S1dS1R13S20SdS21R18R17R16R15R14S5fS5eReA1A1A6VLZ;R1R3A5R2A2Fr';R13S20SdS21R18R17R16R15R14ReA6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;Tk;Tc;Tnv;FphX;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition backT : Prop := ltac2:(tb__ "0|4|
S34S40S1S16S32Q40M0A1A1M1S2fS1dS1dOF_;F_;S4aR5R1A2S1S22R8R6R5R4VW;Vst;R1A7S29S33G0S3R8PcA2A2S0S46R1A1S0S1G1S16S30A1M2S2fS21R10RfReRdRcR7R4R3R2R1AaS5dSdS3eR11R6A2R5R4R2A5F_;Fmd;Ftr;Ftp;Fr;S1G1G2S2fS21R11R10RfReRdR8R4R3R2R1AaS43VCST;VXGL;R12S3eR12R7A2M3S4R10A1S4R5A1A6F_;Fmd;Ftr;Ftp;Fr;SbS0SfS17S0S35S3cR3S47ReR4A2A2A1A2A1S3dR3A1A3S1G1S1RdS20SdS4fVW;Vst;G3R11R3A5VE3P;R1R2A5S4cSdS4bR3R2VPFam;G3R11A2A5A2FrX;Ftp';Frho';S1G1RdS20SdS21R12R11R10RfReR9A6VLZ;R2R1A5S4cSdS4bRbRfVPFam;R12R11A2A5A2Ftp;Fr;F_;F_;F_;F_;Tc;Tnv;FphF;FHE;Frho;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_entry : entryT.
Hypothesis H_prefix : prefixT.
Hypothesis H_pop : popT e_srcN.
Hypothesis H_exit : ltac2:(tb__ "0|0|
S6aS6cS59S57S5aA4").
Hypothesis H_back : backT.

Definition phFN (k : Z) : phase := ltac2:(tb__ "0|0|
S5fS5eS4eS23Vk;A2A1A1").

Theorem refill_N : ltac2:(tb__ "0|4|
S34S40S1S16S32Q40M0A1A1M1S1dS1dOF_;F_;S4aR4R1A2S41R5A1SbS18S38R7A1S1aA3SbS0S48R8S33G0S3R6PcM2A2A2A2Z0A3S4cSdS4bR7R6VPFam;R9R8A2A5S1dS1S2fS22RcR2R9R1VW;Vst;RaA7SeS3dS46S33G0S3R3G2A2A2A1A1S28RdR3A2A2S1G1S16S30A1S2fS21R12R11R8RfR7S6bS3dS46S33G0S3R8G2A2A2A1A1A1R4R3R2R1AaScS5dSdS3eR13S46S33G0S3R9G2A2A2A1A2M3R5R4R2A5S43VCST;VXGL;R13G3S4R9A1S4R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S34S1G1S1RbS20SdS4fVW;Vst;R4ReR3A5VE3P;R1R2A5S4cSdS4bR3R2VPFam;R4ReA2A5A2FrX;Ftp';Frho';FA';S1S2fS1S22RfR3RcR2VW;Vst;RdA7RcS20SdS21R10RfR4RdR3S23A6VLP;R2RdA5R7A2F_;Fr';Fmd0;Frb;S1RaS20SdS4fVW;Vst;ReRdRcA5VE3;R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc Hini Hcnt Q HREB HPOP HPOPUL rhoE.
  apply (tr_cutP Kc TR KIT Model _ (fun md0 => entryR A rhoE tp md0 W st rho) (fun md0 => SPA segs (JR A Kc rhoE tp md0 ph0) (cR0 E3) (r0_of A rhoE) tp) Q).
  { intros w Hw. exists (cfg_model (w_cfg w)). exact (H_entry A Kc rho rhoE tp w Hini Hcnt Hw). }
  intros md0 HE.
  apply (H_prefix A Kc rhoE tp md0 TR KIT HKc rho _ tp Q HE); [intros r'; exact (HPOPUL rhoE md0 r' HE)|].
  intros r1.

  apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FJ) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (kchunks (cls_of (bv_unsigned (rw rhoE 12%positive))) <= gh_nf A rhoE)).
  { intros w [_ (HFz & HGh & _)]. destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. destruct (Z.ltb_spec (Z.of_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rhoE 12%positive)))))) (kchunks (cls_of (bv_unsigned (rw rhoE 12%positive))))) as [X|X]; [exfalso; apply BF; reflexivity | exact X]. }
  intros HNP. unfold gh_nf in HNP.
  set (nv := bv_unsigned (rw rhoE 12%positive)) in *. set (c := cls_of nv) in *. set (k := kchunks c) in *.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & _ & _ & (_ & MF0) & _).
  apply (H_pop A Kc rhoE tp md0 TR KIT HKc rho HE ph0 (conj eq_refl (conj eq_refl eq_refl)) (cs_free_array (cst_of A nv))
           (N_HSRC A rhoE tp md0 W st rho HE) HNP ltac:(lia) ltac:(cbn; intros X; exfalso; lia)
           (N_HIDS A rhoE tp md0 W st rho HE) (N_HCACHE A rhoE tp md0 W st rho HE HNP) (N_HSRCP A rhoE tp md0 W st rho HE HNP)).
  intros r2.
  apply (H_exit A Kc rhoE tp md0 TR KIT HKc rho HE (phK ph0 k) (conj eq_refl (conj eq_refl eq_refl)) ltac:(cbn; intros X; exfalso; lia) Hini
           (N_HRIv A rhoE tp md0 W st rho HE HNP) (N_HLEN A rhoE tp md0 W st rho HE HNP) (N_HIDC A rhoE tp md0 W st rho HE HNP)).
  intros r3.
  apply (H_back A Kc rhoE tp md0 TR KIT rho HE (phFN k)
           (fun r t tr md HJ => proj1 (HREB rhoE md0 HE HNP r t tr md HJ)) (fun r t tr md HJ => proj2 (HREB rhoE md0 HE HNP r t tr md HJ))
           (N_HLEN A rhoE tp md0 W st rho HE HNP) (HPOP (refillA A c))).
Qed.
End ASMN.
End SpineMallocR6.

(* [comment removed for export] *)
Module SpineMallocSec6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "prod"; "option"; "pair"; "Some"; "app"; "None"; "nat"; "fst"; "snd"; "S"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ageom"; "aa_ptr_committed"; "aa_sec"; "sec_chunk"; "ag_pab"; "DG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "sprop"; "ss_next"; "ss_facts"; "eval"; "rw"; "holds"; "obj_range"; "sprop_below"; "swf"; "SLit"; "SVar"; "rm"; "ss_objs"; "DUnknown"; "SPBranch"; "SPNot"; "cell"; "mkObj"; "ranges_disjoint"; "sstate"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "entailsA"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "ulink"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "LQA"; "jpredA"; "stableA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "div"; "sub"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "kPtrArrayCommit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "secneeded"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "O_1"; "O_2"; "carveS"; "BR"; "Pret_ms"; "O_blk"; "O_w"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "M48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "range_noband"; "SKEL0"; "JGs"; "noband"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "L3"; "O_3"; "B3"; "B4"; "F_A"; "F_B"; "F_par"; "O_3b"; "a2e8"; "perm7"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "a0e7"; "a2e6"; "a2e7"; "osplit"; "END8"; "O_4z"; "PGST"; "UE9"; "fx8"; "sel7"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NCH"; "V_NRES"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC6.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S3cS9fVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S5S7dSb3Vnx;A2S6A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S7bVnW;Vst;Vnx;VBX;A4").

Lemma run_band : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S1S52S63R2A2S53R2S62A2A2F_;Fz;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ z Hz.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. unfold IMG_HI in IMG.
  pose proof (Sh_in_band ua ltac:(clear -IMG HTOP SMB; lia)) as B1. pose proof (Sh_in_band (ua + L) ltac:(clear -IMG HTOP SMB; lia)) as B2.
  assert (DS : Sh ua + L / 8 <= Sh (ua + L)).
  { unfold Sh. assert (ua / 8 + L / 8 <= (ua + L) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le ua 8). pose proof (Z.mul_div_le L 8). lia. }
  clear -Hz B1 B2 DS. lia.
Qed.

Lemma ex1_band : ltac2:(tb__ "0|2|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bVJG;RaR9R8R7R6R5R4R3R2A9S1S52S10S3bS3bS25R6S6eVnx;A1A2M1A3R2A2S53R2S11S3bS3bG1A3A2A2S1S52S63R3A2S53R3S62A2A2F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z HJ Hz.
  pose proof (site1_bounds nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (EB & _ & LE).
  unfold O_1, L1 in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EB in Hz.
  apply (run_band BX A Kc rho a r tp tr md HJ z). clear -Hz LE. lia.
Qed.

Lemma ex2_band : ltac2:(tb__ "0|2|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bVJG;RaR9R8R7R6R5R4R3R2A9S1S52S10S3bS3bS25R6S6fVnx;A1A2M1A3R2A2S53R2S11S3bS3bG1A3A2A2S1S52S63R3A2S53R3S62A2A2F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z HJ Hz.
  pose proof (site2_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & EB & _ & EL & LR). cbn zeta in EB, EL, LR.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & _ & _ & ENS & _). cbn zeta in HN, SMB, ENS.
  unfold O_2, obj_range, obj_lo_of, obj_hi_of in Hz. cbn [ob_base ob_lo ob_hi fst snd] in Hz.
  rewrite soff_lit_small in Hz by lia. rewrite (soff_of_val r L2 _ EL) in Hz by (clear -LR; lia). rewrite EB in Hz.
  apply (run_band BX A Kc rho a r tp tr md HJ z).
  assert (0 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (apply Z.div_pos; [rewrite ENS; pose proof (round_up_ge' (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)); lia | lia]).
  clear -Hz LR H. lia.
Qed.

Lemma exblk_pab : ltac2:(tb__ "0|3|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bS14S0S16S15RbR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RcR1A1A1S18R1A1A3FX;S14S0S3bS17RdR1A1A1S51S17R1A1S65A2A3FX;VJG;RdRcRbRaR9R8R7R6R5A9S24R9S2dS9bS29S9dA1S29S9eA1A3A2S1S52S10S3bS3bS25RaS73A2M1A3R6A2S53R6S11S3bS3bG1A3A2A2S1S52S1aS15RfA1A1M2R7A2S53R7S51G2S64A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z BXg BXs BXp HJ HBR Hz.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  destruct HJ as (_ & _ & HA & _). pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. cbn zeta in X.
  destruct X as (P1 & P2 & P3 & P4 & P5 & P6 & _).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  assert (C17 : c mod 2 ^ 17 = 0).
  { pose proof (Z.mod_add c 1 (2 ^ 17) ltac:(lia)) as MA. rewrite <- MA. rewrite <- P6. f_equal. }
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite C17, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  cbn [holds eval] in HBR. rewrite E147, E146 in HBR. fold c in HBR.
  assert (C0 : 0 <= c).
  { destruct (Z_lt_le_dec c 0) as [Hneg|]; [exfalso | assumption].
    assert (Ec : c = - 2 ^ 17) by (clear -X Hneg P5 NN; lia).
    assert (En : Z.of_nat (length (aa_sec A)) = 0) by (clear -Ec P5 NN; lia).
    rewrite En, Ec in HBR. vm_compute in HBR. discriminate HBR. }
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(clear -P5; lia) ltac:(clear -P5; lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HBR by (clear -DP DM NN P5; lia). apply Z.eqb_eq in HBR.
  assert (HcN : 8 * Z.of_nat (length (aa_sec A)) = c) by (rewrite HBR; clear -X8; lia).
  assert (R64 : 0 <= ag_pab G + Z.of_nat (length (aa_sec A)) * 8 < 2 ^ 64) by (clear -P1 P2 TG HcN P5 NN; lia).
  assert (EBw : bv_unsigned (eval r Bw) = ag_pab G + c).
  { unfold Bw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G. rewrite !u64_lit by (clear -P1 P2 TG NN HcN P5; lia).
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (Z.of_nat (length (aa_sec A)) * 8)) by (clear -NN HcN P5; lia). rewrite (Z.mod_small _ _ R64). clear -HcN. lia. }
  unfold O_blk in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EBw in Hz. clear -Hz P5 C0. lia.
Qed.

Lemma exw_pab : ltac2:(tb__ "0|3|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bS14S0S16S15RbR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RcR1A1A1S18R1A1A3FX;S14S0S3bS17RdR1A1A1S17R1A1A3FX;VJG;RdRcRbRaR9R8R7R6R5A9S24R9S2eS2dS9bS29S9dA1S29S9eA1A3A1A2S1S52S10S3bS3bS25RaS74A2M1A3R6A2S53R6S11S3bS3bG1A3A2A2S1S52S1aS15RfA1A1M2R7A2S53R7S51G2S64A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z BXg BXs BXp HJ HBR Hz.
  pose proof (site_b nW st tmax nx Hnx Pret_ms Pret_ms Pret_ms Pret_ms eq_refl eq_refl BX A Kc rho a r tp tr md BXg BXs BXp HJ HBR) as (EBw & B1 & B2 & B3 & _). cbn zeta in EBw, B1, B2, B3.
  unfold O_w in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EBw in Hz. clear -Hz B1 B2 B3. lia.
Qed.

Lemma pab_noband : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S3bS1S52S1aS15RbA1A1M1R1A2S53R1S51G1S64A2A2A2S7cR2A1F_;Fz;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ z Hz. destruct HJ as (_ & _ & HA & _).
  pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg in X. cbn [aa_geom bumpV] in X. cbn zeta in X. destruct X as (_ & _ & _ & P4 & _).
  unfold noband. clear -P4 Hz. lia.
Qed.
Lemma pxa_noband : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RbR1A1A1S18R1A1A3FX;S14S0S3bS17RcR1A1A1S51S17R1A1S65A2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S4fS1fS24R8A1S7S1fS2dS9bS29S9dA1S29S9eA1A3S8S1fA1A3A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57S7S1cS73S8S1cA1A3A4A3S4fS1cS1cS79S25RcR1A2A1Lo;R2A3F_;Fl;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF l EE. apply Forall_inv in HF.
  destruct l as [|o [|o' l']]; try (cbn in EE; discriminate EE). assert (Es : skel o = skel O_blk) by (cbn in EE; congruence).
  apply Forall_cons; [|apply Forall_nil]. rewrite (obj_range_skel r o O_blk Es). intros z Hz.
  exact (pab_noband BX A Kc rho a r tp tr md BXg HJ z (exblk_pab BX A Kc rho a r tp tr md z BXg BXs BXp HJ HF Hz)).
Qed.
Lemma pxb_noband : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RbR1A1A1S18R1A1A3FX;S14S0S3bS17RcR1A1A1S17R1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S4fS1fS24R8A1S7S1fS2eS2dS9bS29S9dA1S29S9eA1A3A1S8S1fA1A3A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57S7S1cS74S8S1cA1A3A4A3S4fS1cS1cS79S25RcR1A2A1Lo;R2A3F_;Fl;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF l EE. apply Forall_inv in HF.
  destruct l as [|o [|o' l']]; try (cbn in EE; discriminate EE). assert (Es : skel o = skel O_w) by (cbn in EE; congruence).
  apply Forall_cons; [|apply Forall_nil]. rewrite (obj_range_skel r o O_w Es). intros z Hz.
  exact (pab_noband BX A Kc rho a r tp tr md BXg HJ z (exw_pab BX A Kc rho a r tp tr md z BXg BXs BXp HJ HF Hz)).
Qed.

Section G41.
Variable BX : AA -> AA.
Variables (T4 U4 X5 C5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S5S27S34VU4;A1A1S6A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VT4;A1S34VU4;A1A2ScG3SbG1G2S8G0A1Sb2Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S3cS20S34VU4;A1A1S20S34VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S35S37VT4;S34VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bSb1S8S3bA1A3VGS;S7S35VU4;S8S35A1M0A3S7S35VX5;G0A3A6S6A3").

Hypothesis HDS : ltac2:(tb__ "0|4|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3Sa5Vsegs;RaS49R8A1A3S1bS1dS1dS4G1A1M2S9S3bS3bA2M3S5fG3R1SacR5A1A3SabR2SbS3bS3bS3dG0RdA2S66S3dG0S23RePcA2A2A1A4A2F_;Fbn;SaaR5RdR4A3S5aVsegs;R11S48Vsegs;VJG;Sa9VBX;R6A2R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S1dG2S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VX5;R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").

Theorem sec_g41 : ltac2:(tb__ "0|4|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3Sa5Vsegs;RaS49R8A1A3S1bS1dS1dS4G1A1M2S9S3bS3bA2M3S5fG3R1SacR5A1A3SabR2SbS3bS3bS3dG0RdA2S66S3dG0S23RePcA2A2A1A4A2F_;Fbn;SaaR5RdR4A3S5aVsegs;R11S48Vsegs;VJG;Sa9VBX;R6A2R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S1dG2S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VT4;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU4 nW st tmax nx Hnx T4 U4 WU4 DU4 NXU4 HU4 BX A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [DPENT] GS [U4] [X5] (JG BX A Kc rho a) ok Q tX Hokf HST Cert5); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  exact (HDS ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rE tX).
Qed.
End G41.

Lemma diamond_hold : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S3S4fS1fS24R6A1M1S86Vnx;A1A3S4fS1fG1S87Vnx;A1A3A2F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _ & _ & E155 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  destruct HJ as (_ & _ & HA & HP & _). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & SSP & _).
  pose proof (proj1 HA) as HG. rewrite BXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (RSB : 0 <= SB < 2 ^ 64) by (clear -S1 S2 TG; lia).
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  destruct SSP as [SA|SB'].
  - left. unfold F_A. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E142, E155, add_val. fold ua L SB.
    rewrite (u64_lit L RL), (u64_lit SB RSB). rewrite Z.mod_small by (clear -IMG HTOP SMB; lia). exact SA.
  - right. unfold F_B. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E155, add_val. fold ua SB.
    rewrite (u64_lit SB RSB). rewrite u64_lit by lia. rewrite Z.mod_small by (clear -S1 S2 TG; lia). clear -SB'. lia.
Qed.

Lemma site3_vals : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S1S0S3bS3dG0S22R5S84Vnx;A1A2A2S51S61S3dG0R6A2A1Z200A2A3S1S0G1S22R5S92Vnx;A1A2S22R5S82A2M2A3S0S3bS3dG0G2A2Z100A3A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & _). cbn zeta in *.
  pose proof (urange a) as Ra. unfold PG in AL. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (D1 : (ua + 4096) / 8 = ua / 8 + 512) by (replace (ua + 4096) with (ua + 512 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  assert (D2 : (ua + 6136) / 8 = ua / 8 + 767) by (replace (ua + 6136) with (ua + 767 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  split; [|split].
  - unfold B3. cbn [eval]. rewrite Enx, add_val, srl_val, add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra HTOP SMB; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU; lia). lia.
  - unfold a2e6, L3. cbn [eval]. rewrite Enx. apply bv_eq.
    rewrite sub_val, add_val, !srl_val, !add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6136)) by (clear -Ra HTOP SMB; lia).
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1, D2.
    rewrite (Z.mod_small (ua / 8 + 767 + 1)) by (clear -DP DU; lia). replace (ua / 8 + 767 + 1 - (ua / 8 + 512)) with 256 by lia. reflexivity.
  - unfold L3. cbn [eval]. apply u64_lit. lia.
Qed.

Section G43.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").

Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A C5B Y6A Y6B E6 CT6 CO6 T6 : axst) (sA sB s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S7eVT6;S21S34VCO6;A1A1A2").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0S35S6dS86Vnx;A1VC5;A2VC5A;A3").
Hypothesis HC5B : ltac2:(tb__ "0|0|
S0S35S6dS87Vnx;A1VC5;A2VC5B;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VC5;A1A1A1S86Vnx;A1A3S6A3").
Hypothesis FBB : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VC5;A1A1A1S87Vnx;A1A3S6A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VC5A;S8S35A1M0A3S7S35VY6A;G0A3A6S6A3").
Hypothesis Cert6B : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VC5B;S8S35A1M0A3S7S35VY6B;G0A3A6S6A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S5S39VY6A;VE6;VsA;A3S6A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S5Sa3VsA;VGS;A2S6A3").
Hypothesis E6B : ltac2:(tb__ "0|0|
S0S5S39VY6B;VE6;VsB;A3S6A3").
Hypothesis I6B : ltac2:(tb__ "0|0|
S0S5Sa3VsB;VGS;A2S6A3").

Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S5S27S34VCT6;A1A1S6A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VE6;A1S34VCT6;A1A2ScG3SbG1G2S7G0SbS1eS1eS92Vnx;A1S82A4S8G0A1A3S8S1fA1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S3cS20S34VCT6;A1A1S20S34VE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0S35S37VE6;S34VCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VCT6;A1A1A4S4eS1cG0S57SdS1cS7S1cS6fVnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0S35S70VCT6;S30S84Vnx;A1S28Z0A1S82S8S2fA1S2cA5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S5S27S34VCO6;A1A1S6A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VCO6;S69Vs6;A3ScG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S5S7fVCO6;S69Vs6;VR6;S4eS36S35S38S6aA4A5S6A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S35S81Vs6;S69S72VCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VCO6;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT6;A1A1A1S21S34VCO6;A1A1A3S6A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VCO6;A1A1A2S6A3").

Lemma RS6 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S48Vsegs;VJG;VBX;R8R7R6R5A5VE6;R4R3R2A6S48Vsegs;VJG;VBX;R9R8R7R6A5VCT6;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC6.
  eapply SPA_restate; [exact WC6 | exact DF6 | exact NX6 | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  exact (proj1 (proj2 (site3_vals BX A Kc rho a rhoX tp tr md (proj2 Hw)))).
Qed.

Lemma HBL6 : ltac2:(tb__ "0|b|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VCT6;R3R2R1A6S1S52S61S3dG0R5A2A1M2S3dG0S22R4S84Vnx;A1M3A2A2M4A2S1S52S51G4S3dG0S22R4S82A2A2A2S51G2S54S66S3dG0S23R6PcA2A2A1Z8A2A2A2S1S4S1cA1M5S0S4S9S9S1eS1eA2S1eA2M6A1M7S4eS1cG6S57R1A4M8S4eS1cG6S57S7S1cS6fVnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A4A3S4fS1cS1cS31S25R7R1A2SbS3bS3bS3dG0S22R7G3A2A2M9S51G9S3dG0S22R7S82A2A2A2A4A2Lo;R2A3MaF_;Fl;G5S0G7G8S4eS1cG6S57VPX;A4A3GaF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. pose proof (SPA_facts_hold segs _ rhoX CT6 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB & _ & EL). rewrite EB, EL.
  destruct (site2_vals nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (_ & EB2 & _ & EL2 & BL2 & _). cbn zeta in EB2, EL2, BL2.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  assert (V512 : 512 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (rewrite ENS; apply Z.div_le_lower_bound; clear -R8B HN; lia).
  assert (L9216 : 9216 <= secmapsize (bv_unsigned (rw rho 12%positive)) / 8) by (apply Z.div_le_lower_bound; clear -SMB; lia).
  split; [lia|]. split; [clear -L9216; lia|]. split.
  - intros l2 EE. destruct l2 as [|o [|o' [|o'' l2']]]; try (cbn in EE; discriminate EE).
    assert (Es : skel o = skel (O_2 nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_1 nx)) by (cbn in EE; congruence).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite (obj_range_skel rhoX o (O_2 nx) Es). unfold O_2, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX L2 _ EL2) by (clear -BL2; lia). rewrite EB2.
      unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -V512. lia.
    + rewrite (obj_range_skel rhoX o' (O_1 nx) Es'). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
  - intros l2 EE. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX6 p Hp))).
    pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
    eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
    destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
    destruct (Z_le_gt_dec (snd (obj_range rhoX o)) (Sh (bv_unsigned a) + 512)) as [|G1]; [right; right; left; lia|].
    destruct (Z_le_gt_dec (Sh (bv_unsigned a) + 512 + 256) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
    exfalso. set (x := Z.max (fst (obj_range rhoX o)) (Sh (bv_unsigned a) + 512)).
    pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x; clear -L9216 G1 G2 NE; lia)) as Bx.
    unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g43 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VC5;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }

  assert (TAIL : forall rE tE, triple segs ok (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ms_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl RS6 HBL6 SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             ok A Kc rho rho a tE Q HW HUS HKc Hokl SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }

  apply (triple_conseq (P:=fun w => SPA segs (JG BX A Kc rho a) C5A rX tX w \/ SPA segs (JG BX A Kc rho a) C5B rX tX w)
           (SPA segs (JG BX A Kc rho a) C5 rX tX) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { destruct w as [tr [ms md]]. destruct (diamond_hold BX A Kc rho a rX tX tr md BXg (proj2 Hw)) as [FA|FB]; [left; rewrite <- HC5A | right; rewrite <- HC5B].
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) FA FBA).
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_B nx) _ _ (proj1 Hw) FB FBB). }
  apply triple_disj.
  - apply (cfg_soundA segs 4000%nat [MSENT] GS [C5A] [Y6A] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6A); [|left; reflexivity].
    intros E rE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | intros w Hw; right; exact Hw |].
    apply TAIL.
  - apply (cfg_soundA segs 4000%nat [MSENT] GS [C5B] [Y6B] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6B); [|left; reflexivity].
    intros E rE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6B E6 sB rE tX w HUS HKc E6B I6B Hw) | intros w Hw; right; exact Hw |].
    apply TAIL.
Qed.
End G43.

Lemma ms_call : ltac2:(tb__ "0|8|
S14S14F_;S35S35S35S35S4S36A1M0Sa4S4S1cA1M1S0G0R3S7S36S3aR4Sb0A2S8S36A1A3A3S5bOF_;M2S4cS1dS4S3eQ40A1M3A1M4S4aVsegs;R4R3A3S4dVsegs;Sa2R4A3S5aVsegs;R6S48Vsegs;R5RcR4R3A5S4bVsegs;R5Sa2R4R3RaA6A4F_;F_;Ftp;Frho;FJx;Fok;S0S3cS20S34R7A1A1Sa2A3S0SaG1A1S80RaR8R5A3ScG1R4A2A3S0S5S7fRbR9R6R5S4eS36S35S38R7A4A5S6A3S0S35S81R7RaR9RcR6A5RbA3S0S5S5dS1fS26S20S34RdA1M5A1A1M6S21G5A1A3S6A3S0S5S5dS1fG6S21S34ReA1A1A3S6A3S0S5S7dVGS;S20S34RfA1A1A2S6A3G2S14S40S1dG3G4S5cS67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S1dG4S5aVsegs;RcS48Vsegs;VJG;R1dRbRaR9R8A5M7S7eR1bS21S34R1cA1A1A2R2R1A5R6A4FtpY;FrhoY;S1dS5aVsegs;RcS48Vsegs;G7R1cR1R7A5R6A4FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;F_;F_;F_;F_;F_;F_;F_;F_;F_;FR;Fs;FPosts;FPret;FPre;FT;FCM;FBX;").
Proof.
  intros BX CM T Pre Pret Posts s R HPosts Hsum NPre He Hchk HT FBC FBT NXC ok A Kc rho a tp Q HUS HKc Hokf HD rhoX.
  pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JG BX A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segs ok Jf).
  { intros r t tr ms md msv' HJ HMI Hh Hp Hs. exact (Hokf rhoX t tr ms md msv' (JG_K nW st nx BX A Kc rho a _ _ _ _ HJ) HMI Hh Hp Hs). }
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (triple_pre_pure segs ok _ _ (Forall (holds rhoX) (ss_facts (ax_S CM)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CM tp w Hw). }
  intros HFC.
  apply (call_soundA segs ok (JG BX A Kc rho a) Jf Jf (JG BX A Kc rho a) CM Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.

Lemma F_g7_hold : ltac2:(tb__ "0|1|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1S8dVnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). unfold PG in *. lia. }
  unfold F_g7, RUE. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite and_val, !add_val, Enx, E12, !u64_lit in H by lia. fold ua nv in H.
  rewrite (Z.mod_small (ua + 6144)) in H by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) in H by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (Z.mod_small (ua + 6144 + nv + 7)) in H by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (land_m8E nW st tmax nx Hnx) in H by (clear -Ra HTOP LB HN SMB; lia). pose proof (Z.mod_pos_bound (ua + 6144 + nv + 7) 8 ltac:(lia)) as MB. clear -H MB HTOP LB Ra HN SMB. lia.
Qed.

Lemma site7_vals : ltac2:(tb__ "0|9|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S23R7PcA2A2S3bS3dG0R7A2S3bS68R2A1S3bS66R3A1S3bS1S0G1S22R9S91Vnx;A1A2S22R9S71Vnx;A1A2M2A3S1S0G1S22R9S93Vnx;A1A2S22R9S90A2M3A3S1S0S3bS3dG0G2A2S51S51S61R3A1S54R2Z8M4A2M5A2Z100M6A2A3S1S0S3bS3dG0G3A2S55S55S54R1G4A2M7G5A2G6A2A3S1S52Z200M8G5A2S52S51G5G8A2G7A2A2A2A2A2A2TMS;TVNS;Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (site2_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & EL2 & BL2 & _).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  set (VNS := secneeded nv) in *. set (MS := secmapsize nv) in *. unfold IMG_HI in IMG.
  assert (V8 : VNS mod 8 = 0) by (rewrite ENS, Z.add_mod, R8M by lia; reflexivity).
  assert (M8 : MS mod 8 = 0).
  { pose proof (Z.div_mod MS 4096 ltac:(lia)) as X. unfold PG in SMM. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (MS / 4096)) with ((512 * (MS / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (VB : 68609 <= VNS <= nv + 4103) by (rewrite ENS; clear -R8B HN; lia).
  assert (MB : VNS + 4096 <= MS <= VNS + 8191).
  { rewrite EMS. unfold PG. pose proof (round_up_ge' VNS 4096 ltac:(lia)) as H. clear -H. lia. }
  pose proof (Z.div_mod VNS 8 ltac:(lia)) as DV. pose proof (Z.div_mod MS 8 ltac:(lia)) as DM. pose proof (Z.div_mod ua 8 ltac:(lia)) as DA.
  rewrite V8 in DV. rewrite M8 in DM. rewrite A8 in DA.
  assert (SHB : Sh ua + MS / 8 < 2 ^ 45) by (unfold Sh, SHADOW_OFF; clear -TOP DM DA Ra MB VB; lia).

  assert (ERUE : bv_unsigned (eval r (RUE nx)) = ua + 2048 + VNS).
  { unfold RUE. cbn [eval]. rewrite Enx, E12, and_val, !add_val, !u64_lit by lia. fold ua nv.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP MB VB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) by (clear -Ra TOP MB VB HN; lia).
    rewrite (Z.mod_small (ua + 6144 + nv + 7)) by (clear -Ra TOP MB VB HN; lia). rewrite (land_m8E nW st tmax nx Hnx) by (clear -Ra TOP MB VB HN; lia).
    rewrite ENS. unfold round_up. replace (ua + 6144 + nv + 7) with (nv + 8 - 1 + (ua / 8 + 768) * 8) by (clear -DA; lia). rewrite Z_mod_plus_full.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)) as X. clear -X DA. lia. }
  assert (EA0 : bv_unsigned (eval r (a0e7 nx)) = Sh ua + VNS / 8 + 256).
  { unfold a0e7. cbn [eval]. change (eval r (RUE nx)) with (eval r (RUE nx)). rewrite add_val, srl_val. cbn [eval] in ERUE. rewrite ERUE.
    rewrite !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (ua + 2048 + VNS) with ((ua / 8 + 256 + VNS / 8) * 8) by (clear -DA DV; lia). rewrite Z.div_mul by lia.
    unfold Sh, SHADOW_OFF in *. rewrite Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EB : bv_unsigned (eval r (BR nx)) = Sh ua + VNS / 8 + 256).
  { unfold BR, shS, vMAPn. cbn [eval]. rewrite Enx, E141.
    rewrite !add_val. rewrite !srl_val. rewrite !u64_lit by (unfold SHADOW_OFF in *; lia).
    fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF in *. rewrite !Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EL : bv_unsigned (eval r L3b) = MS / 8 - VNS / 8 - 256).
  { unfold L3b. cbn [eval]. rewrite add_val. cbn [eval] in EL2. rewrite EL2, u64_lit by lia. rewrite Z.mod_small by (clear -BL2; lia). lia. }
  assert (EA2 : bv_unsigned (eval r (a2e7 nx)) = MS / 8 - VNS / 8 - 256).
  { unfold a2e7. cbn [eval]. cbn [eval] in ERUE. rewrite E141, Enx.
    rewrite !sub_val, !add_val, !srl_val, !add_val, !sub_val, !add_val, and_val, add_val. rewrite ERUE.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite !u64_lit by lia. fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (VNS + 4095)) by lia. rewrite (land_m4096E nW st tmax nx Hnx) by lia.
    assert (ERU : VNS + 4095 - (VNS + 4095) mod 4096 + 4096 = MS).
    { rewrite EMS. unfold round_up, PG. pose proof (Z.div_mod (VNS + 4096 - 1) 4096 ltac:(lia)). replace (VNS + 4095) with (VNS + 4096 - 1) by lia. lia. }
    set (RPG := VNS + 4095 - (VNS + 4095) mod 4096) in *.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra TOP MB VB; lia).

    rewrite (Z.add_mod_idemp_l (ua + 4096 - (ua + 2048 + VNS))) by lia.
    rewrite (Z.add_mod_idemp_r (ua + 2048 + VNS)) by lia.
    replace (ua + 2048 + VNS + (ua + 4096 - (ua + 2048 + VNS) + RPG)) with (ua + MS) by (clear -ERU; lia).
    rewrite (Z.mod_small (ua + MS)) by (clear -Ra TOP MB VB; lia).
    replace ((ua + MS + (2 ^ 64 - 8)) mod 2 ^ 64) with (ua + MS - 8).
    2:{ replace (ua + MS + (2 ^ 64 - 8)) with (ua + MS - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. clear -Ra TOP MB VB IMG. lia. }
    replace (ua + MS - 8) with ((MS / 8 + ua / 8 - 1) * 8) by (clear -DA DM; lia). rewrite Z.div_mul by lia.
    replace (ua + 2048 + VNS) with ((ua / 8 + 256 + VNS / 8) * 8) by (clear -DA DV; lia). rewrite Z.div_mul by lia.
    rewrite (Z.mod_small (MS / 8 + ua / 8 - 1 + 1)) by (clear -DA DM DV MB Ra VB TOP IMG; lia). rewrite Z.mod_small by (clear -DA DM DV MB Ra VB TOP IMG; lia). lia. }
  split; [apply bv_eq; rewrite EA0, EB; reflexivity|]. split; [apply bv_eq; rewrite EA2, EL; reflexivity|].
  split; [exact EB|]. split; [exact EL|]. split; [clear -DV VB; lia | clear -DV DM MB; lia].
Qed.

Section G44.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D6 U7 ET7 CT7 CO7 CR7 CS7 CM7 T7 : axst) (s7 : wsub) (R7 : list sobj) (n7 : nat).
Let D7 : axst := ltac2:(tb__ "0|0|
S7eVT7;S21S34VCM7;A1A1A2").
Hypothesis WU7 : ltac2:(tb__ "0|0|
S0S5S27S34VU7;A1A1S6A3").
Hypothesis DU7 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VD6;A1S34VU7;A1A2ScG3SbG1G2S8G0A1S8dVnx;A1A4A2A3").
Hypothesis NXU7 : ltac2:(tb__ "0|0|
S0S3cS20S34VU7;A1A1S20S34VD6;A1A1A3").
Hypothesis HU7 : ltac2:(tb__ "0|0|
S0S35S37VD6;S34VU7;A1A2VU7;A3").
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VU7;S8S35A1M0A3S7S35VET7;G0A3A6S6A3").
Hypothesis WC7 : ltac2:(tb__ "0|0|
S0S5S27S34VCT7;A1A1S6A3").
Hypothesis DF7 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VET7;A1S34VCT7;A1A2ScG3SbG1G2S7G0SbS1eS1eS91Vnx;A1S71Vnx;A1A4S7G0SbS1eS1eS93Vnx;A1S90A4S8G0A1A3A3S8S1fA1A4A2A3").
Hypothesis NX7 : ltac2:(tb__ "0|0|
S0S3cS20S34VCT7;A1A1S20S34VET7;A1A1A3").
Hypothesis HC7 : ltac2:(tb__ "0|0|
S0S35S37VET7;S34VCT7;A1A2VCT7;A3").
Hypothesis SK7 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VCT7;A1A1A4S4eS1cG0S57SdS1cS7S1cS83Vnx;A1S7S1cS6fVnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC7 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VCT7;A1A1A3").
Hypothesis FX7 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VCT7;A1A1A3").
Hypothesis XC7 : ax_X CT7 = [].
Hypothesis HCO7 : ltac2:(tb__ "0|0|
S0S35S70VCT7;S30S71Vnx;A1S28Z0A1S28Z100A1S8S2fA1S2cA5A2VCO7;A3").
Hypothesis WCO7 : ltac2:(tb__ "0|0|
S0S5S27S34VCO7;A1A1S6A3").

Hypothesis RB7 : ltac2:(tb__ "0|0|
S0S5Sa6S32SafS34VCO7;A1U1A2A2S6A3").
Hypothesis HCR7 : ltac2:(tb__ "0|0|
S0S35Sa8VCO7;U1A2VCR7;A3").
Hypothesis LEN7 : ltac2:(tb__ "0|0|
S0SfS13S1cS2bS34VCR7;A1A1A2Vn7;A3").
Hypothesis PERM_nd7 : ltac2:(tb__ "0|0|
S0S5SadS8bVn7;A1A1S6A3").
Hypothesis PERM_lt7 : ltac2:(tb__ "0|0|
S0S5S5dSfSfSb5R1Vn7;A2Li;S8bVn7;A1A3S6A3").
Hypothesis PERM_cov7 : ltac2:(tb__ "0|0|
S0S5S5dSfSfS60SfSb4R1A1S8bVn7;A1A3Li;S50U0Vn7;A2A3S6A3").
Hypothesis HCS7 : ltac2:(tb__ "0|0|
S0S35S9aVCR7;A1VCS7;A3").
Hypothesis MRG7 : ltac2:(tb__ "0|0|
S0S5Sa6S32SaeS34VCS7;A1U1A2A2S6A3").
Hypothesis HCM7 : ltac2:(tb__ "0|0|
S0S35Sa7VCS7;U1A2VCM7;A3").
Hypothesis He7 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VCM7;S69Vs7;A3ScG0VR7;A2A3").
Hypothesis Hchk7 : ltac2:(tb__ "0|0|
S0S5S7fVCM7;S69Vs7;VR7;S4eS36S35S38S6aA4A5S6A3").
Hypothesis HT7 : ltac2:(tb__ "0|0|
S0S35S81Vs7;S69S72VCM7;VR7;A5VT7;A3").
Hypothesis FBC7 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VCM7;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT7 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT7;A1A1A1S21S34VCM7;A1A1A3S6A3").
Hypothesis NXC7 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VCM7;A1A1A2S6A3").

Lemma RSU7 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VD6;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VU7;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU7.
  eapply SPA_restate; [exact WU7 | exact DU7 | exact NXU7 | constructor | | exact Hw].
  exact (F_g7_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma prep7 : ltac2:(tb__ "0|4|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S3bS1S52S61S3dG0R6A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R7PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR8S3fG0R2A2A2SeG3A1A3A1F_;Fz;S48Vsegs;VJG;VBX;R9R8R7R6A5VET7;R5R4R3A6S48Vsegs;VJG;VBX;RaR9R8R7A5VCM7;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW RUNDEF Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (EA0 & EA2 & EB & EL & V512 & VM). cbn zeta in EB, EL, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site2_vals nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (_ & EB2 & _ & EL2 & BL2 & _). cbn zeta in EB2, EL2, BL2.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).

  assert (HC : SPA segs (JG BX A Kc rho a) CT7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HC7. eapply SPA_restate; [exact WC7 | exact DF7 | exact NX7 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [exact EA0|]. apply Forall_cons; [exact EA2 | apply Forall_nil]. }
  pose proof (SPA_facts_hold segs _ rhoX CT7 tp _ HC) as HF.

  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (E256 : bv_unsigned (eval rhoX (SLit 256)) = 256) by (cbn [eval]; apply u64_lit; lia).
  assert (HCO : SPA segs (JG BX A Kc rho a) CO7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCO7. apply (carve_piece nW st tmax nx Hnx BX CT7 (BR nx) (SLit 256) A Kc rho rho a rhoX tp _ SL HC); [rewrite HCO7; exact WCO7 | exact XC7 | | |].
    - rewrite EB. clear -V512. lia.
    - rewrite EB, E256. clear -VM. lia.
    - rewrite EB, E256. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
      apply (pieces_disjoint nW st tmax nx Hnx BX BXg CT7 [O_3 nx; O_2 nx; O_1 nx] PX A Kc rho a rhoX tp _ _ _ HW HC SK7 FC7).
      + apply (RB (Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256)). clear -V512 VM. lia.
      + pose proof (RB (Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256 + 256 - 1) ltac:(clear -V512 VM; lia)). lia.
      + intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 l2']]]]; try (cbn in EE; discriminate EE).
        assert (Es : skel o = skel (O_3 nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_2 nx)) by (cbn in EE; congruence).
        assert (Es'' : skel o'' = skel (O_1 nx)) by (cbn in EE; congruence).
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * rewrite (obj_range_skel rhoX o (O_3 nx) Es). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
          unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
        * rewrite (obj_range_skel rhoX o' (O_2 nx) Es'). unfold O_2, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
          rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX L2 _ EL2) by (clear -BL2; lia). rewrite EB2.
          unfold ranges_disjoint. cbn [fst snd]. right. right. right. lia.
        * rewrite (obj_range_skel rhoX o'' (O_1 nx) Es''). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
          unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
      + intros l2 EE.
        assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX7 p Hp))).
        pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
        eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
        set (lo := Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256) in *.
        destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
        destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
        destruct (Z_le_gt_dec (lo + 256) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
        exfalso. set (x := Z.max (fst (obj_range rhoX o)) lo).
        pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x, lo in *; clear -V512 VM G1 G2 NE; lia)) as Bx.
        unfold noband in NBx. clear -NBx Bx. lia. }

  assert (XCO : ax_X CO7 = []) by (rewrite <- HCO7; exact XC7).
  assert (HCR : SPA segs (JG BX A Kc rho a) CR7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCR7. unfold oreb. destruct (rebase_obj_at (ax_S CO7) 1) as [S'|] eqn:E; [|exact HCO]. eapply (SPA_rebase segs); [exact E | exact XCO | exact HCO]. }
  assert (HCS : SPA segs (JG BX A Kc rho a) CS7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCS7. unfold sel7. rewrite LEN7. apply (SPA_select segs); [exact HCR | exact PERM_nd7 | |].
    - intros i Hi. rewrite LEN7. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt7 i Hi).
    - intros i Hi. rewrite LEN7 in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov7 i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }
  rewrite <- HCM7. unfold omrg. destruct (merge_objs_at (ax_S CS7) 1) as [S'|] eqn:E; [|exact HCS]. eapply (SPA_merge segs); [exact E | exact HCS].
Qed.

Theorem sec_g44 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VD7;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VD6;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU7 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT] GS [U7] [ET7] (JG BX A Kc rho a) ok Q tX Hokf HST Cert7); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (prep7 A Kc rho a rE tX w HW RUNDEF Hw) | intros w Hw; right; exact Hw |].
  exact (ms_call BX CM7 T7 Pre_memsetA Pret_ms Posts_memsetA s7 R7 eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
           He7 Hchk7 HT7 FBC7 FBT7 NXC7 ok A Kc rho a tX Q HUS HKc Hokl HCONT rE).
Qed.
End G44.

Lemma site8_vals : ltac2:(tb__ "0|5|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S23R7PcM2A2A2S3bS3dG0R7A2S3bS1S0S3bS3dG0S22R7S85Vnx;A1A2A2S51S61R1A1Z300A2A3S1S0S3bS3dG0S22R7S8aVnx;A1A2A2S54R2Z8M3A2A3S1S0S3bS3dG0S22R7S33S9cS29G2A1S28S78A1A3A2A2S55R2S56R2G3A2A2M4A3S0S3bS3dG0S22R7S95Vnx;A1A2A2S55S51S51R1Z1800A2G4A2G3A2A3A2A2A2Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA.
  pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  assert (EN8 : bv_unsigned (eval r (SAlu ALU_AND (SVar 12) (SLit M48))) = nv - nv mod 8).
  { cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). fold nv. apply land_M48. clear -HN. lia. }
  assert (EE : bv_unsigned (eval r (END8 nx)) = ua + 6144 + (nv - nv mod 8) - 8).
  { unfold END8. cbn [eval] in EN8 |- *. rewrite add_val, add_val, EN8, add_val, Enx, !u64_lit by lia. fold ua.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + (nv - nv mod 8))) by (clear -Ra TOP SMB HN MN; lia).
    replace (ua + 6144 + (nv - nv mod 8) + (2 ^ 64 - 8)) with (ua + 6144 + (nv - nv mod 8) - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
    apply Z.mod_small. clear -Ra TOP SMB HN MN IMG. lia. }
  assert (D1 : (ua + 6144) / 8 = ua / 8 + 768) by (replace (ua + 6144) with (ua + 768 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  split; [|split; [|split; [exact EN8 | exact EE]]].
  - unfold B4. cbn [eval]. rewrite Enx, add_val, srl_val, add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU; lia). lia.
  - unfold a2e8. cbn [eval]. cbn [eval] in EE. rewrite sub_val, add_val, !srl_val, EE, add_val, Enx, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    replace (ua + 6144 + (nv - nv mod 8) - 8) with ((ua / 8 + 767 + nv / 8) * 8) by (clear -DA DN; lia). rewrite Z.div_mul by lia.
    pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
    rewrite (Z.mod_small (ua / 8 + 767 + nv / 8 + 1)) by (clear -DP DU NP NU; lia).
    replace (ua / 8 + 767 + nv / 8 + 1 - (ua / 8 + 768)) with (nv / 8) by lia. apply Z.mod_small. clear -NP NU. lia.
Qed.

Lemma F_g8_hold : ltac2:(tb__ "0|1|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1S8eVnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & EL & EN8 & EE). cbn zeta in EL, EN8, EE.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  pose proof (urange a) as Ra. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
  unfold F_g8. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - cbn [holds branch_taken]. unfold bv_ltu. apply Z.ltb_lt. rewrite EL. cbn [eval]. rewrite u64_lit by lia. clear -NP NU. lia.
  - cbn [holds branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H. rewrite EE in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H Ra TOP SMB HN MN LB. lia.
  - cbn [holds branch_taken]. intros H. unfold bv_eqb in H. apply Z.eqb_eq in H. rewrite EN8 in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H HN MN. lia.
Qed.

Section G45.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D7 U8 ET8 CT8 CO8 T8 : axst) (s8 : wsub) (R8 : list sobj).
Let D8 : axst := ltac2:(tb__ "0|0|
S7eVT8;S21S34VCO8;A1A1A2").
Hypothesis WU8 : ltac2:(tb__ "0|0|
S0S5S27S34VU8;A1A1S6A3").
Hypothesis DU8 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VD7;A1S34VU8;A1A2ScG3SbG1G2S8G0A1S8eVnx;A1A4A2A3").
Hypothesis NXU8 : ltac2:(tb__ "0|0|
S0S3cS20S34VU8;A1A1S20S34VD7;A1A1A3").
Hypothesis HU8 : ltac2:(tb__ "0|0|
S0S35S37VD7;S34VU8;A1A2VU8;A3").
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VU8;S8S35A1M0A3S7S35VET8;G0A3A6S6A3").
Hypothesis WC8 : ltac2:(tb__ "0|0|
S0S5S27S34VCT8;A1A1S6A3").
Hypothesis DF8 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VET8;A1S34VCT8;A1A2ScG3SbG1G2S8G0A1S99Vnx;A1A4A2A3").
Hypothesis NX8 : ltac2:(tb__ "0|0|
S0S3cS20S34VCT8;A1A1S20S34VET8;A1A1A3").
Hypothesis HC8 : ltac2:(tb__ "0|0|
S0S35S37VET8;S34VCT8;A1A2VCT8;A3").
Hypothesis SK8 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VCT8;A1A1A4S4eS1cG0S57SdS1cS7S1cS89Vnx;A1S7S1cS83Vnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC8 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VCT8;A1A1A3").
Hypothesis FX8 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VCT8;A1A1A3").
Hypothesis XC8 : ax_X CT8 = [].
Hypothesis HCO8 : ltac2:(tb__ "0|0|
S0S35S70VCT8;S30S85Vnx;A1S28Z0A1S8aVnx;A1S8S2fA1S2cA5A2VCO8;A3").
Hypothesis WCO8 : ltac2:(tb__ "0|0|
S0S5S27S34VCO8;A1A1S6A3").
Hypothesis He8 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VCO8;Sa0Vs8;A3ScG0VR8;A2A3").
Hypothesis Hchk8 : ltac2:(tb__ "0|0|
S0S5S7fVCO8;Sa0Vs8;VR8;S4eS36S35S38Sa1A4A5S6A3").
Hypothesis HT8 : ltac2:(tb__ "0|0|
S0S35S81Vs8;Sa0S75VCO8;VR8;A5VT8;A3").
Hypothesis FBC8 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VCO8;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT8 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT8;A1A1A1S21S34VCO8;A1A1A3S6A3").
Hypothesis NXC8 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VCO8;A1A1A2S6A3").

Lemma RSU8 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VD7;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VU8;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU8.
  eapply SPA_restate; [exact WU8 | exact DU8 | exact NXU8 | constructor | | exact Hw].
  exact (F_g8_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma RS8 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S48Vsegs;VJG;VBX;R8R7R6R5A5VET8;R4R3R2A6S48Vsegs;VJG;VBX;R9R8R7R6A5VCT8;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC8.
  eapply SPA_restate; [exact WC8 | exact DF8 | exact NX8 | constructor | | exact Hw].
  destruct (site8_vals BX A Kc rho a rhoX tp tr md (proj2 Hw)) as (_ & EL & _). cbn zeta in EL.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md (proj2 Hw)) as (HN & _). cbn zeta in HN.
  unfold fx8. apply Forall_cons; [|apply Forall_nil]. cbn [holds]. rewrite EL. cbn [eval]. rewrite u64_lit by lia.
  pose proof (Z.div_lt_upper_bound (bv_unsigned (rw rho 12%positive)) 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU. clear -NU. lia.
Qed.

Lemma HBL8 : ltac2:(tb__ "0|c|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VCT8;R3R2R1A6S1S52S61S3dG0R5A2A1M2S3dG0S22R4S85Vnx;A1M3A2A2M4A2S1S52S51G4S3dG0S22R4S8aVnx;A1M5A2A2A2S51G2S54S66S3dG0S23R6PcA2A2A1Z8A2A2A2S1S4S1cA1M6S0S4S9S9S1eS1eA2S1eA2M7A1M8S4eS1cG7S57R1A4M9S4eS1cG7S57S7S1cS89Vnx;A1S7S1cS83Vnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3A4A3S4fS1cS1cS31S25R7R1A2SbS3bS3bS3dG0S22R7G3A2A2MaS51GaS3dG0S22R7G5A2A2A2A4A2Lo;R2A3MbF_;Fl;G6S0G8G9S4eS1cG7S57VPX;A4A3GbF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. pose proof (SPA_facts_hold segs _ rhoX CT8 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site8_vals BX A Kc rho a rhoX tp tr md HJ) as (EB & EL & _). cbn zeta in EB, EL. rewrite EB, EL.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.

  assert (NV8 : nv / 8 <= secneeded nv / 8 - 512).
  { rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by lia. rewrite Z.div_add by lia.
    pose proof (Z.div_le_mono nv (round_up nv 8) 8 ltac:(lia) ltac:(clear -R8B; lia)). lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP.
  split; [lia|]. split; [clear -NV8 VM; lia|]. split.
  - intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 l2']]]]; try (cbn in EE; discriminate EE).
    assert (Es : skel o = skel (O_3b nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_3 nx)) by (cbn in EE; congruence).
    assert (Es'' : skel o'' = skel (O_1 nx)) by (cbn in EE; congruence).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + rewrite (obj_range_skel rhoX o (O_3b nx) Es). unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. rewrite EBR. unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -NV8. lia.
    + rewrite (obj_range_skel rhoX o' (O_3 nx) Es'). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
    + rewrite (obj_range_skel rhoX o'' (O_1 nx) Es''). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
  - intros l2 EE. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX8 p Hp))).
    pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
    eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
    set (lo := Sh (bv_unsigned a) + 768) in *.
    destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
    destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
    destruct (Z_le_gt_dec (lo + nv / 8) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
    exfalso. set (x := Z.max (fst (obj_range rhoX o)) lo).
    pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x, lo in *; fold nv; clear -NV8 VM G1 G2 NE NP; lia)) as Bx.
    unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g45 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VD8;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VD7;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  eapply triple_conseq; [intros w Hw; exact (RSU8 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT] GS [U8] [ET8] (JG BX A Kc rho a) ok Q tX Hokf HST Cert8); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  apply (ms_step nW st tmax nx Hnx NXG BX BXg ET8 CT8 CO8 T8 (B4 nx) (a2e8 nx) [O_3b nx; O_3 nx; O_1 nx] PX Pre_mszA Pret_mz Posts_mszA s8 R8 eq_refl
           (fun ok0 Jx r0 t0 Ho Hs => memsetZ_sumA ok0 Jx Ho Hs r0 t0) eq_refl RS8 HBL8 SK8 FC8 XC8 HCO8 WCO8 He8 Hchk8 HT8 FBC8 FBT8 NXC8
           ok A Kc rho rho a tX Q HW HUS HKc Hokl SL).
  intros rhoY tpY. exact (HCONT rhoY tpY).
Qed.
End G45.

Lemma site9_vals : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S23R7PcA2A2S3bS3dG0R7A2S3bS1S0S3bS3dG0S22R7S98Vnx;A1A2A2S51S51R1Z1800A2S55R2S56R2Z8M2A2A2A2A3S0S3bS3dG0S22R7S8cVnx;A1A2A2S51S51S61R1A1Z300A2S54R2G2A2A2A3A2Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & _ & EN8 & _). cbn zeta in EN8.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA.
  pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  assert (EU : bv_unsigned (eval r (UE9 nx)) = ua + 6144 + (nv - nv mod 8)).
  { unfold UE9. cbn [eval] in EN8 |- *. rewrite add_val, EN8, add_val, Enx, !u64_lit by lia. fold ua.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). apply Z.mod_small. clear -Ra TOP SMB HN MN LB. lia. }
  split; [exact EU|].
  unfold BP9. cbn [eval]. cbn [eval] in EU. rewrite add_val, srl_val, EU, !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (ua + 6144 + (nv - nv mod 8)) with ((ua / 8 + 768 + nv / 8) * 8) by (clear -DA DN; lia). rewrite Z.div_mul by lia.
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
  unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU NP NU; lia). lia.
Qed.

Lemma F_g9_hold : ltac2:(tb__ "0|1|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1S8fVnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site9_vals BX A Kc rho a r tp tr md HJ) as (EU & _). cbn zeta in EU.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  pose proof (urange a) as Ra. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g9. apply Forall_cons; [|apply Forall_nil]. cbn [holds branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite EU in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H Ra TOP SMB HN MN LB. lia.
Qed.

Lemma nmod8_of_par : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S1S24R5S88A2S0S3bS56S3dG0S23R8PcA2A2Z8A2Z0A3M2F_;S24R5S2eS88A1A2S2G2A1F_;A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & _ & EN8 & _). cbn zeta in EN8.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & _).
  assert (EQ : branch_taken BC_EQ (eval r (SVar 12)) (eval r (SAlu ALU_AND (SVar 12) (SLit M48))) = (bv_unsigned (rw rho 12%positive) mod 8 =? 0)).
  { cbn [branch_taken]. unfold bv_eqb. rewrite EN8. cbn [eval]. rewrite E12.
    pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)) as MN.
    destruct (Z.eqb_spec (bv_unsigned (rw rho 12%positive) mod 8) 0) as [E|NE]; [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia]. }
  unfold F_par. cbn [holds]. rewrite EQ. split.
  - intros H. apply Z.eqb_eq in H. exact H.
  - intros H E. apply H. apply Z.eqb_eq. exact E.
Qed.

Section G46.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D8 U9 E9f E9p CO9p E9q : axst).
Hypothesis WU9 : ltac2:(tb__ "0|0|
S0S5S27S34VU9;A1A1S6A3").
Hypothesis DU9 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VD8;A1S34VU9;A1A2ScG3SbG1G2S8G0A1S8fVnx;A1A4A2A3").
Hypothesis NXU9 : ltac2:(tb__ "0|0|
S0S3cS20S34VU9;A1A1S20S34VD8;A1A1A3").
Hypothesis HU9 : ltac2:(tb__ "0|0|
S0S35S37VD8;S34VU9;A1A2VU9;A3").
Hypothesis Cert9 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S7S3bS97S8S3bA1A3A3VGS;S7S35VU9;S8S35A1M0A3S7S35VE9f;S7S35VE9p;G0A3A3A6S6A3").
Hypothesis SK9 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VE9p;A1A1A4S4eS1cG0S57SdS1cS7S1cS96Vnx;A1S7S1cS89Vnx;A1S7S1cS83Vnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC9 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VE9p;A1A1A3").
Hypothesis FX9 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VE9p;A1A1A3").
Hypothesis FP9 : ltac2:(tb__ "0|0|
S5fS1fS2eS88A1S21S34VE9p;A1A1A3").
Hypothesis XC9 : ax_X E9p = [].
Hypothesis HCO9 : ltac2:(tb__ "0|0|
S0S35S70VE9p;S30S8cVnx;A1S28Z0A1S28Z1A1S8S2fA1S2cA5A2VCO9p;A3").
Hypothesis WCO9 : ltac2:(tb__ "0|0|
S0S5S27S34VCO9p;A1A1S6A3").
Hypothesis Cert9q : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VCO9p;S8S35A1M0A3S7S35VE9q;G0A3A6S6A3").

Lemma RSU9 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VD8;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VU9;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU9.
  eapply SPA_restate; [exact WU9 | exact DU9 | exact NXU9 | constructor | | exact Hw].
  exact (F_g9_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma prep9 : ltac2:(tb__ "0|4|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S3bS1S52S61S3dG0R6A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R7PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR8S3fG0R2A2A2SeG3A1A3A1F_;Fz;S48Vsegs;VJG;VBX;R9R8R7R6A5VE9p;R5R4R3A6S48Vsegs;VJG;VBX;RaR9R8R7A5VCO9p;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW RUNDEF Hw. pose proof (SPA_facts_hold segs _ rhoX E9p tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site9_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & EB). cbn zeta in EB.
  destruct (site8_vals BX A Kc rho a rhoX tp tr md HJ) as (EB4 & EL4 & _). cbn zeta in EB4, EL4.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (proj2 (nmod8_of_par BX A Kc rho a rhoX tp tr md HJ) (proj1 (Forall_forall _ _) HF _ FP9)) as NM8.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.

  assert (NV8 : secneeded nv / 8 = nv / 8 + 1 + 512).
  { rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by lia. rewrite Z.div_add by lia. f_equal.
    unfold round_up. rewrite Z.div_mul by lia. pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
    symmetry. apply Z.div_unique with (nv mod 8 - 1); lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP.
  assert (SL : slink (bv_unsigned a) (secmapsize nv) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (E1 : bv_unsigned (eval rhoX (SLit 1)) = 1) by (cbn [eval]; apply u64_lit; lia).
  rewrite <- HCO9. apply (carve_piece nW st tmax nx Hnx BX E9p (BP9 nx) (SLit 1) A Kc rho rho a rhoX tp _ SL Hw); [rewrite HCO9; exact WCO9 | exact XC9 | | |].
  - rewrite EB. clear -NP. lia.
  - rewrite EB, E1. fold nv. clear -NV8 VM. lia.
  - rewrite EB, E1. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    apply (pieces_disjoint nW st tmax nx Hnx BX BXg E9p [O_4z nx; O_3b nx; O_3 nx; O_1 nx] PX A Kc rho a rhoX tp _ _ _ HW Hw SK9 FC9).
    + apply (RB (Sh (bv_unsigned a) + 768 + nv / 8)). fold nv. clear -NV8 VM NP. lia.
    + pose proof (RB (Sh (bv_unsigned a) + 768 + nv / 8) ltac:(fold nv; clear -NV8 VM NP; lia)). lia.
    + intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 [|o4 l2']]]]]; try (cbn in EE; discriminate EE).
      assert (Es : skel o = skel (O_4z nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_3b nx)) by (cbn in EE; congruence).
      assert (Es'' : skel o'' = skel (O_3 nx)) by (cbn in EE; congruence). assert (Es3 : skel o3 = skel (O_1 nx)) by (cbn in EE; congruence).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * rewrite (obj_range_skel rhoX o (O_4z nx) Es). unfold O_4z, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX (a2e8 nx) _ EL4) by (pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)); fold nv; lia). rewrite EB4.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. fold nv. lia.
      * rewrite (obj_range_skel rhoX o' (O_3b nx) Es'). unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite soff_lit_small by lia. rewrite EBR. unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -NV8. lia.
      * rewrite (obj_range_skel rhoX o'' (O_3 nx) Es''). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -NP. lia.
      * rewrite (obj_range_skel rhoX o3 (O_1 nx) Es3). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -NP. lia.
    + intros l2 EE.
      assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX9 p Hp))).
      pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
      eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
      set (lo := Sh (bv_unsigned a) + 768 + nv / 8) in *.
      destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
      destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
      destruct (Z_le_gt_dec (lo + 1) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
      exfalso. pose proof (Ho lo ltac:(lia)) as NBx. pose proof (RB lo ltac:(unfold lo; fold nv; clear -NV8 VM NP; lia)) as Bx.
      unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g46 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VE9f;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VE9q;R2R1A5R9A4FtpY;FrhoY;S1dG4S5aVsegs;RfS48Vsegs;VJG;VBX;ReRdRcRbA5VD8;R2R1A5RaA4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCF HCQ rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU9 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT; PGST] GS [U9] [E9f; E9p] (JG BX A Kc rho a) ok Q tX Hokf HST Cert9); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[<-|[]]].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HCF rE tX)].
  - eapply triple_conseq; [intros w Hw; exact (prep9 A Kc rho a rE tX w HW RUNDEF Hw) | intros w Hw; right; exact Hw |].
    apply (cfg_soundA segs 4000%nat [MSENT] GS [CO9p] [E9q] (JG BX A Kc rho a) ok Q tX Hokf HST Cert9q); [|left; reflexivity].
    intros E rE' HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HCQ rE' tX)].
Qed.
End G46.

Section G47.
Variable BX : AA -> AA.
Variables (E S9a S9b T9 : axst) (iM : nat) (s9 : wsub) (R9 : list sobj).
Let D9 : axst := ltac2:(tb__ "0|0|
S7eVT9;S21S34VS9b;A1A1A2").
Hypothesis HS9a : ltac2:(tb__ "0|0|
S0S35S94VE;ViM;S28Z1800A1A3VS9a;A3").
Hypothesis HS9b : ltac2:(tb__ "0|0|
S0S35S94VS9a;S12ViM;A1S28Z2800A1A3VS9b;A3").
Hypothesis He9 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VS9b;S69Vs9;A3ScG0VR9;A2A3").
Hypothesis Hchk9 : ltac2:(tb__ "0|0|
S0S5S7fVS9b;S69Vs9;VR9;S4eS36S35S38S6aA4A5S6A3").
Hypothesis HT9 : ltac2:(tb__ "0|0|
S0S35S81Vs9;S69S72VS9b;VR9;A5VT9;A3").
Hypothesis FBC9 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VS9b;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT9 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT9;A1A1A1S21S34VS9b;A1A1A3S6A3").
Hypothesis NXC9 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VS9b;A1A1A2S6A3").

Lemma prepF : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VE;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VS9b;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw.
  assert (Ha : SPA segs (JG BX A Kc rho a) S9a rhoX tp w).
  { rewrite <- HS9a. unfold osplit. destruct (split_obj_at (ax_S E) iM (SLit 6144)) as [S'|] eqn:E1; [|exact Hw]. eapply (SPA_split segs); [exact E1 | exact Hw]. }
  rewrite <- HS9b. unfold osplit. destruct (split_obj_at (ax_S S9a) (S iM) (SLit 10240)) as [S'|] eqn:E2; [|exact Ha]. eapply (SPA_split segs); [exact E2 | exact Ha].
Qed.

Theorem sec_g47 : ltac2:(tb__ "0|2|
S5bOF_;S14S40S1dS3eQ40A1M0S5cS67VW;Vst;A2S44R5A1S4aVsegs;R8S49R6A1A3S1dS4G0A1M1S5aVsegs;RbS48Vsegs;VJG;VBX;RaR9R8R7A5VD9;R2R1A5R6A4FtpY;FrhoY;S1dG1S5aVsegs;RcS48Vsegs;VJG;VBX;RbRaR9R8A5VE;R2R1A5R7A4FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HUS HKc Hokl HCONT rX tX.
  eapply triple_conseq; [intros w Hw; exact (prepF A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  exact (ms_call BX S9b T9 Pre_memsetA Pret_ms Posts_memsetA s9 R9 eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
           He9 Hchk9 HT9 FBC9 FBT9 NXC9 ok A Kc rho a tX Q HUS HKc Hokl HCONT rX).
Qed.
End G47.
End SEC6.
End SpineMallocSec6.

(* [comment removed for export] *)
Module SpineMallocSec4IE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4I.run3]); [exact SpineMallocSec4I.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4I.run3a]); [exact SpineMallocSec4I.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4I.run4a]); [exact SpineMallocSec4I.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4I.run4b]); [exact SpineMallocSec4I.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_0h : ltac2:(tb__ "0|8|
S1dS3aS10S18Q40M0A1M1S1bOF_;S25VW;Vst;A2S3bR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S39S17G0R6A2A1M2R1A2S34R1S33G2S35S24S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S24S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U0M6Vst;S22S1dS3cR1A1LX;RdRcR4RaA8S2aR3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S2bR2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineMallocSec4IE.

