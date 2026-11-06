(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk br bp q0.

(* [comment removed for export] *)
Module SegQS_loop.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "pair"; "prod"; "bool"; "list"; "nil"; "true"; "app"; "fst"; "length"; "option"; "Some"; "S"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "sprop"; "eval"; "SLit"; "SAlu"; "SVar"; "rw"; "holds"; "rm"; "SPUle"; "ss_objs"; "SPBranch"; "SPNot"; "rl"; "SPUlt"; "SPAlign"; "agree_below"; "soff"; "sprop_below"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_sec"; "sc_map_beg"; "topG"; "AA"; "aa_geom"; "ag_spacebeg"; "sc_map_size"; "ag_ctx"; "ag_thread"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "pow"; "div"; "modulo"; "sub"; "opp"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "Forall2"; "nth_error"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "nth"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "qsenv"; "zloS"; "fam_ok"; "N1"; "ZD_fixS"; "ZD_rtiS"; "ZD_sec1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "NPRE"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop"; "KEEPV"; "lfL"; "ZD_ref"; "zhiX"; "REF1"; "a3_of"; "ENVQ"; "F2X"; "LF"; "NSC"; "NX"; "UX"; "ZUL"; "EQF"; "F_lenX"; "LT1"; "LT2"; "T_exit"; "T_first"; "T_loop"; "ZDNX"; "ZDU"; "hv_of"; "r16_of"; "zbX"; "BSX"; "F_hX"; "M_exit"; "M_first"; "M_loop"; "zbL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vCHV"; "vMS"; "VS0"; "vPTR"; "SC"; "VSC"; "vPAB"; "vEND"; "vIDX"; "vNCH"; "vNEAR"; "LA"; "SX"; "vLAST"; "BSHS"; "LENS"; "LL"; "vH"; "vLIDX"; "F2"; "OBJ2"; "O_chS"; "TOPMAX"; "TsPL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "vIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_ADD"; "ALU_SRL"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "forallb2"; "same_rng"; "dspec"; "keepN"; "dobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop.Loop"; "SCANI"; "XVALS"; "ZUXl"; "zbE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world";
"@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "Sh"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "LOW_SHADOW_BEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "carve_okq"; "DQI0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "mkST"; "s_Cd"; "s_ok"; "uobj"; "ro_cond"; "s_okU"; "unk_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop.Env"; "zbL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan"; "best"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "sec_foot"; "@Stdlib.Arith.PeanoNat.Nat"; "even"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "FRM"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib F0A_zones.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition zbX (T CTX TOP h SHH C6 C7 LST C9 : Z) (z : nat) : Z := ltac2:(tb__ "0|0|
S0SfLz;Vz;Z0S0S0SfLn;R1VT;S0S0SfLn0;R1VCTX;S0S0SfLn1;R1VTOP;S0S0SfLn2;R1VSHH;S0S0SfLn3;R1Vh;S0S0SfLn4;R1VC6;S0S0SfLn5;R1VC7;S0S0SfLn6;R1VLST;S0VC9;Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition zhiX (ms : Z) (z : nat) : Z :=
  match z with 0%nat => 0x646000 | 1%nat => 4096 | 2%nat => 4096 | 3%nat => 2 ^ 64 | 4%nat => 17592186048512 | 5%nat => ms | 6%nat => 8 | 7%nat => 8 | 8%nat => 32 | _ => 8 end.

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
S1eVhv;A1S17S8S1aS1S1aS6bR1A1S1S1aS25S24Sa1R1S1cZ0A1A3A1S1S1aS22R1S99A2S1S1aS27S99S5aR1S7eA2M0A2S1S1aS28Vhv;ZcM1A2S1S1aS28PcbG1A2S1S1aS22S1cZ12000A1S7eA2S1S1aS22S7eS1cS93A1M2A2S1S1aS22S1cZ646000A1R1A2S1S1aS22G0G2A2S1S1aS22S5aS7eR1A2G2A2S6S1aA1M3A3A3A3A3A3A3A3A3A3A3A3S8S1aS77Vf;R1A2S4S5S1aA1Ll;Vl;G3S1S1aS27S85S5aS86S1cN1A1A2A2G3A3X4x2A3A3ThT;").
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
  assert (R : 0x646000 <= PAB + 8 * Z.of_nat j /\ PAB + 8 * Z.of_nat j + 8 <= 2 ^ 47) by (clear -P1 P2 P3 LT TG; lia).
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
S18S17SfSfS5S3S3SfS0A2M0S17A2M1A1M2SfS11S43Q40M3A1M4S1bR6R5A2S42G3R1A2M5A3S12S38Z0R2A2S3aR2S3dZ2Z3eA2M6A2A2S38S41G6A1R6A2S38R7R6A2S3aR7G6A2S38Z646000M7S39R6R9A2A2Sd0RaR9R8A3SfS12S38S39R9RcA2R1A2S3aR1S39R9RbA2A2A2S14SfSfS14S0S0S14SfSfS12S12S12S38S39RdR3A2M8R5A2S3aR5S39G8S3cR2A1A2M9A2A2S12S38G7G8A2S38G9G6A2A2A2S96S95S4aS21R12A1A2S97G8R2R1A3A2A2Lval;A2Lk;A2Loff;A2F_;Fz;S4dG1G1G1OLc;R1G0S17G0OLp;R2SfS0S14SfSfS12S11G4S1bR14R4A2G5A3S96S95S4aS21R14A1A2S97S39RfR3A2R2R1A3A2A2Lval;A2Lk;Loff;X3x1Le;Lp;X3x1Lc;RaA3SbdRfS2S3S3S17SfA2MaSfA2G2S2GaSfS2S17SfReRdA4RcA4RbA4A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbz;Fcs;Fhi;Flo;Fb;Fr;").
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
  assert (HR : 0x646000 <= h /\ h + msz < 2 ^ 47) by (clear -IH HTG TG; lia).
  split; [|split; [|split; [|split]]].
  -
    unfold UX, unk_ok. rewrite soff_lit_small by (clear; lia). rewrite (soff_LENS r4 vMS msz EM ltac:(clear -MS HR; lia)), (eval_BSHS r4 hT h EH ltac:(clear -HR MS; lia)).
    pose proof (Sh_in_band h ltac:(clear -HR MS; lia)) as B1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
    pose proof (Z.div_pos msz 8 ltac:(clear -MS; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -HR IH MS; lia)).
    rewrite u64_lit by (clear -B1; lia).
    split; [clear -H; lia|]. split; [clear -H H0; lia|]. split; [clear -B1; lia|]. split; [clear -B1 H0; lia|].
    intros x Hx. rewrite <- (Sh_add8 h msz (proj1 M8) (proj2 M8)) in Hx. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (h + msz) ltac:(clear -HR IH MS; lia)) as B2. unfold HIGH_SHADOW_END in B2.
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
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (h + msz) ltac:(clear -HR IH MS; lia)) as B2. unfold HIGH_SHADOW_END in B2. rewrite (Sh_add8 h msz (proj1 M8) (proj2 M8)) in B2.
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
  assert (HR : 0x646000 <= h /\ h + msz <= 140737479966720 /\ 73728 <= msz) by (clear -IH HTG TG MS; lia).
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
    + apply (hle r4 _ (SVar hv) 0x646000 h (elit r4 _) EH); clear -HR; lia.
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
Module SpineCallocOvA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "rw"; "ss_next"; "valuation"; "SLit"; "sobj"; "swf"; "SVar"; "sprop_below"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "Pre_callocI"; "KcA"; "L_calloc_null"; "JL_calloc_null"; "Kc_ok"; "unwind_stopJ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv"; "stRo_S"; "EXo"; "s_o"; "stKo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "rho_ce"; "sa_c"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo"; "FACTSo"; "P0o"; "sb_o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineCallocOv"; "JGe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocIo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineCallocOv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OVA.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S27S2fVCST;R1A2S2fS51R2A2S5F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S27S2fVCST;R1A2S2fS56R2A2S5F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.

Hypothesis HUS : stopJ_stable W st.
Hypothesis Wa : ltac2:(tb__ "0|0|
S3S8S18S40VW;Vst;A2A1S9A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S3SfScS7ScS12S12A2M0A1M1S7S11A1M2A2M3A1S49S1S1dS1cVW;Vst;A3A1S40VW;Vst;A2A2SeG3SbG1G2SdG0SbS12S12S19P18A1S16S4aA1A4SaG0A1A3SaS11A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S3S8S18S54VW;Vst;A2A1S9A3").
Hypothesis Fbo : ltac2:(tb__ "0|0|
S3S8S26S11S1aS4dA1S52VW;Vst;A2A3S9A3").
Hypothesis RN : ltac2:(tb__ "0|0|
S3S7S17A1S3bVW;Vst;A2S10S17S4eS44S50S17S4fS3aA4A3A3").
Hypothesis WRn : ltac2:(tb__ "0|0|
S3S8S18S36VW;Vst;A2A1S9A3").
Hypothesis DKRn : ltac2:(tb__ "0|4|
S3SfScS7ScS12S12A2M0A1M1S7S11A1M2A2M3A1S49S1S39VW;Vst;A2A1S36VW;Vst;A2A2SeG3SbG1G2SdG0SbS12S12S16S4aA1S19P18A1A4SaG0A1A3SaS11A1A4A2A3").
Hypothesis NXRn : ltac2:(tb__ "0|0|
S3S28S14S36VW;Vst;A2A1S14S1S39VW;Vst;A2A1A1A3").
Hypothesis ENTn : ltac2:(tb__ "0|0|
S3S8S2S3cVW;Vst;A2S1fS1cVW;Vst;A3S38VW;Vst;A2A3S9A3").
Hypothesis IDn : ltac2:(tb__ "0|0|
S3S8S4cS38VW;Vst;A2S30A2S9A3").

Variable cuts : list axst.
Hypothesis HCUT : ltac2:(tb__ "0|2|
S2eS15S22VW;Vst;S3fR2R1A2A3S6S7S11A1M0G0S4S25S0S33R1S53VW;Vst;A2M1A2Vcuts;A3S4S45S11S1bS3fR4R3A2A1R1A3S3S8S26S11S1aS14S1G1A1A1A1R1A3S9A3A2A2Lsx;A2F_;Frho;FA;").
Hypothesis CertO : ltac2:(tb__ "0|0|
S3S8S34S4bUfa0SaS27A1S3dVcuts;SdS0S37VW;Vst;A2SaS0A1A3A6S9A3").

Lemma ov_front : ltac2:(tb__ "0|1|
S2eS1eS15S7S24Q40M0A1A1S46S41S43Z2Z40A2S42S23G0S13R3PcA2A2S23G0S13R3PdA2A2A2A2S29Vsegs;S3eVW;Vst;R6R5A4S1dS1cVW;Vst;A3R4R3R2A6S6S0S0S4S25S0R1Vcuts;A3S29Vsegs;S55VnW;Vst;R8R7R6A5R1S3fR8R6A2R5R4A6A2LC;A2F_;F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w HOV Hw.
  pose proof (c_instantiate_ov law_die W st A Kc rho tp w HUS Wa Da Wb Fbo HOV Hw) as H1.
  destruct (HCUT A rho (proj1 (proj2 (proj2 (proj2 (proj2 H1)))))) as (sx & Hin & Hh & Hb).
  exists (ax_add_facts sx (P0o W st)). split; [exact Hin|].
  apply (SPA_withG_intro segs (Jc W st A Kc) GW _ (rho_ce A rho) tp w).
  exact (SPA_add_facts' segs (Jc W st A Kc) (rho_ce A rho) (P0o W st) sx tp w Hh Hb H1).
Qed.

Theorem calloc_ov : ltac2:(tb__ "0|2|
S46OF_;S2eS1eS15S7S24Q40M0A1A1S7ScS0S2cA2M1A1S21R4A1S2bVsegs;R7S2aR5A1A3S25G1SbS0S2cS1fS1cVW;Vst;A3S20VAInv;VCST;VXGL;R7R6A5A4R3A3S41S43Z2Z40A2S42S23G0S13R6PcA2A2S23G0S13R6PdA2A2A2A2S48Vsegs;RaS29Vsegs;S3eVW;Vst;R9R8A4S1dS1cVW;Vst;A3R7R6A5S2dVsegs;S30R7R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts HKc Hokl HPin HOV.
  apply triple_conseq with (P := fun w => exists C, In C cuts /\ SPA segs (JGe nW st A Kc rho) C (rho_ce A rho) tp w) (Q := LQPA segs NF rho tp Posts);
    [intros w Hw; exact (ov_front A Kc rho tp w HOV Hw) | intros w Hw; exact Hw |].
  intros n Hg w (C & HinC & HwC). revert n Hg w HwC.
  change (triple segs ok (SPA segs (JGe nW st A Kc rho) C (rho_ce A rho) tp) (LQPA segs NF rho tp Posts)).
  apply (cfg_soundA segs 4000%nat [] GW cuts [EXo W st] (JGe nW st A Kc rho) ok (LQPA segs NF rho tp Posts) tp).
  - intros r t tr ms md msv' [_ HJ]. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK.
  - exact (JGe_stable nW st A Kc rho HUS HKc).
  - exact CertO.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
    intros w Hw. exact (ov_null_finish nW st CST XGL HCST HXGL HCSTM HCSTS RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoE Posts HKc HPin Hw).
  - exact HinC.
Qed.

Hypothesis NXcuts : ltac2:(tb__ "0|0|
S0S25S0R1Vcuts;A3S57S3dS14S1R2A1A1A2F_;FC;").
Hypothesis ECertO : ltac2:(tb__ "0|2|
S3S8S35S4bUfa0SaS27A1S3dS44S0S31S0S32R1Z1S16Z0M0A1M1A3Lc;Vcuts;A4SdS31S32S37VW;Vst;A2G0G1A3SaS31A1A3A6S9A3").
Theorem ecalloc_ov : ltac2:(tb__ "0|2|
S2eS1eS15S7S24Q40M0A1A1S7ScS0S2cA2M1A1S21R4A1S25G1SbS0S2cS1fS1cVW;Vst;A3S20VAInv;VCST;VXGL;R6R5A5A4R2A3S41S43Z2Z40A2S42S23G0S13R5PcA2A2S23G0S13R5PdA2A2A2A2S47Vsegs;S29Vsegs;S3eVW;Vst;R8R7A4S1dS1cVW;Vst;A3R6R5A5S2dVsegs;S30R6R5R4A5A3F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts HKc HPin HOV w Hw0.
  destruct (ov_front A Kc rho tp w HOV Hw0) as (C & HinC & HwC). clear Hw0. revert w HwC.
  change (etriple segs (SPA segs (JGe nW st A Kc rho) C (rho_ce A rho) tp) (LQPA segs NF rho tp Posts)).
  apply (ecfg_cut 4000%nat [] GW (map (fun c => mkVNA c 1 (SLit 0)) cuts) [mkVNA (EXo W st) 0 (SLit 0)] (JGe nW st A Kc rho) (LQPA segs NF rho tp Posts) tp C _
           (JGe_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. apply in_map_iff in Hn. destruct Hn as (c & <- & Hc). cbn [vna_state]. exact (NXcuts c Hc).
  - exact ECertO.
  - intros E rhoE HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
    intros w Hw. exact (ov_null_finish nW st CST XGL HCST HXGL HCSTM HCSTS RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoE Posts HKc HPin Hw).
  - apply in_map_iff. exists C. split; [reflexivity | exact HinC].
Qed.
End OVA.
End SpineCallocOvA.

(* [comment removed for export] *)
Module SpineMallocR5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cls_keptA"; "cs_cache"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cls"; "aa_fs_busy"; "aa_geom"; "aa_live"; "class_fresh"; "class_state"; "ageom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "prod"; "true"; "nat"; "nil"; "orb"; "cons"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "sv"; "SVar"; "mkVal"; "rl"; "sv_eqb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "KcA"; "JL_malloc_ok"; "AE_A"; "JL_malloc_null"; "client_addrA"; "client_shadowA"; "ulink"; "L_malloc_ok"; "Posts_malloc"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5"; "rho_after"; "same_client"; "posts_conv"; "sx_okb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "rhoM_of"; "chk_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "refill_cs"; "kchunks"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vCHX"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "of_nat"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "to_nat"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5.PCONV"; "PF_malloc"; "PF_ok"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition sx_okb (s : wsub) : bool := ltac2:(tb__ "0|0|
S60S18S18S56R1A1S12S1aS1aS25S37Vs;R1A2S22R1A1A2S54R1P95A2A2S54R1P9fA2A2Ti;Ln;S5cU1U9fA2A3").
Lemma sx_ok_id : ltac2:(tb__ "0|0|
S38S12S0S15S3fR2A1S17A3S55R2S29A2S2S0S12R3P95A3A1S2S0S12R4P9fA3A1S0S21S37R6R5A2S22R5A1A3F_;F_;F_;F_;Fi;Fs;").
Proof.
  intros s i H Hi H1 H2. unfold sx_okb in H.
  pose proof (proj1 (forallb_forall _ _) H (Pos.to_nat i) ltac:(apply in_seq; unfold GW in Hi; lia)) as X. cbv beta zeta in X. rewrite Pos2Nat.id in X.
  apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|].
  - apply sv_eqb_sound in X. exact X.
  - apply Pos.eqb_eq in X. contradiction.
  - apply Pos.eqb_eq in X. contradiction.
Qed.

Definition rho_after (rho r : valuation) : valuation := ltac2:(tb__ "0|0|
S23S20Vrho;A1S24Vrho;A1S1fVr;A1A3").

Lemma rhoM_refill : ltac2:(tb__ "0|0|
S4S1eS1eS11S12S2S0S12R1P95A3A1S2S0S12R2P9fA3A1S0S26Q40A1S20S46S4bR7R4A2S3cR6R5A2A2R3A2S20S46R7R6A2R3A2A3F_;F_;Fi;Fc;Fr;Frho;FA;").
Proof.
  intros A rho r c i H1 H2. unfold rhoM_of, rho_sets. cbn [rw rho_set_rw rho_after aa_geom refillA aa_ptr_committed aa_sec].
  repeat match goal with |- context [Pos.eqb i ?kk] => destruct (Pos.eqb_spec i kk); [try reflexivity; try contradiction|] end.
  reflexivity.
Qed.

Lemma cnt_of_refill : ltac2:(tb__ "0|1|
S4S11S4eS59S44R1A1A1S14SfSaR2A1A2A2S0S11S48S4bR3S44R2A1M0A2R2A2S58S14S11S6S4cG0S45R3R2A2A2A1A2A1A3F_;Fn;FA;").
Proof. intros A n H. unfold cnt_of, cst_of, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact H. reflexivity. Qed.
Lemma chk_of_refill : ltac2:(tb__ "0|1|
S4S11S4eS59S44R1A1A1S14SfSaR2A1A2A2S0S11S47S4bR3S44R2A1M0A2R2A2S6S4cG0S45R3R2A2A2A1S13S11A1S5bS11S5aS14S11R1A2U1A2R1Z0A4Tl;A3F_;Fn;FA;").
Proof. intros A n H. unfold chk_of, cst_of, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact H. reflexivity. Qed.

Definition same_client (A Ar : AA) : Prop := ltac2:(tb__ "0|1|
S1S0S10ScVAr;A1ScVA;A1A3S1S0S13S16S11S11A2A1M0SdVAr;A1SdVA;A1A3S1S0S13G0A1SbVAr;A1SbVA;A1A3S1S0S11S9VAr;A1S9VA;A1A3S1S0S11S8VAr;A1S8VA;A1A3S0S11S7VAr;A1S7VA;A1A3A2A2A2A2A2").

Definition posts_conv (CST XGL : list (Z * Z)) (PFam : AA -> KcA -> list (axst * jpostA)) : Prop := ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1G1S4fS3dR8R7A2S2aVCST;VXGL;R9R8S1fR6A1S1fR5A1A6S4S5RaR1S27G0S20R8PcM2A2A2A3S5RcR2S27G0S20R9G2A2A2A3F_;FA';S3aS28S36S3cR8R7A2R6VPFam;RaR9A2R4A6S3aS28S36R9R6VPFam;RcRaA2R5A6F_;F_;F_;F_;Fw;Ftp0;Ftp;Fr;Frho;FKc;FAr;FA;").

Section PCONV.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (W : list ulink) (st : ustop).

Lemma client_same : ltac2:(tb__ "0|0|
S4S4S3dR2R1A2S11S3S2fVCST;R3R1A3S2fVCST;R4R1A3A2Fa;F_;FAr;FA;").
Proof.
  intros A Ar (EG & EL & EF & _) a. unfold client_addrA, client_mut_addrA, aa_frames. rewrite EG, EL, EF. reflexivity.
Qed.
Lemma shadow_same : ltac2:(tb__ "0|0|
S4S4S3dR2R1A2S11S3S30VCST;VXGL;R3R1A4S30VCST;VXGL;R4R1A4A2Fa;F_;FAr;FA;").
Proof.
  intros A Ar HS a. unfold client_shadowA. split; (intros [(x & Hx & E)|H]; [left; exists x; split; [apply (client_same A Ar HS); exact Hx | exact E] | right; exact H]).
Qed.

Lemma mem_kept_trans : ltac2:(tb__ "0|2|
S4S4S4S26Q40A1S1cS26Q8A1A1F_;M0G0G0S3dR6R5A2S2aVCST;VXGL;R7R6R4R3A6M1G1S2aVCST;VXGL;R9R7R6R4A6F_;F_;F_;Fm2;Fm1;Fm0;FA';FAr;FA;").
Proof.
  intros A Ar A' m0 m1 m2 HS [K1 K2] [K1' K2']. split.
  - intros a Ha [(H1 & H2 & H3)|(H1 & H2 & H3)].
    + pose proof (proj2 (client_same A Ar HS a) H1) as H1r.
      rewrite (K1' a Ha (or_introl (conj H1r (conj H2 H3)))). exact (K1 a Ha (or_introl (conj H1 (conj H1r H3)))).
    + pose proof (proj2 (shadow_same A Ar HS a) H1) as H1r.
      assert (E1 : m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) by exact (K1 a Ha (or_intror (conj H1 (conj H1r H3)))).
      assert (D1 : m1 (Z_to_bv 64 a) <> None) by (rewrite E1; exact H3).
      rewrite (K1' a Ha (or_intror (conj H1r (conj H2 D1)))). exact E1.
  - intros x j Hx Hj Hd.
    assert (Hxr : client_addrA CST A x /\ client_addrA CST Ar x \/ in_rangesZ XGL x).
    { destruct Hx as [[X1 X2]|X]; [left; split; [exact X1 | apply (client_same A Ar HS); exact X1] | right; exact X]. }
    apply (K2' x j); [destruct Hx as [[X1 X2]|X]; [left; split; [apply (client_same A Ar HS); exact X1 | exact X2] | right; exact X] | exact Hj|].
    exact (K2 x j Hxr Hj Hd).
Qed.

Lemma conv_null : ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1S1eG1S13S41A1S40S3dRaR9A2S2aVCST;VXGL;RbRaS1fR8A1S1fR7A1A6S4S5RcR1S27G0S20RaPcM2A2A2A3S5ReR2S27G0S20RbG2A2A2A3F_;FA';G1S2eVAInv;VCST;VXGL;RdRcS3cRbRaA2R1R8R7R6R5AbS2eVAInv;VCST;VXGL;RfRdRcRaR9R8R7R6AbF_;Ftpx;F_;F_;F_;Fmd;Ftr;Ftp';Frho';Ftp0;Fr;Frho;FKc;FAr;FA;").
Proof.
  intros A Ar Kc rho r tp0 rho' tp' tr md HS HM0 HCK tpx (A' & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10).
  pose proof HS as (EG & EL & EF & EV & EKm & EKf). cbn [rho_after rw rm] in J4, J8, J10.
  exists A'. split; [exact J1|]. split; [rewrite J2; exact EL|]. split; [rewrite J3; unfold aa_frames; rewrite EF; reflexivity|].
  split; [rewrite J4, EV; reflexivity|]. split; [rewrite J5, EKm; reflexivity|]. split; [rewrite J6; exact EKf|]. split; [rewrite J7; exact EG|].
  split; [exact (mem_kept_trans A Ar A' _ _ _ HS HM0 J8)|]. split; [exact J9 | exact (HCK A' J10)].
Qed.
Lemma conv_ok : ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1S1eG1S13S41A1S40S3dRaR9A2S2aVCST;VXGL;RbRaS1fR8A1S1fR7A1A6S4S5RcR1S27G0S20RaPcM2A2A2A3S5ReR2S27G0S20RbG2A2A2A3F_;FA';G1S2cVAInv;VCST;VXGL;RdRcS3cRbRaA2R1R8R7R6R5AbS2cVAInv;VCST;VXGL;RfRdRcRaR9R8R7R6AbF_;Ftpx;F_;F_;F_;Fmd;Ftr;Ftp';Frho';Ftp0;Fr;Frho;FKc;FAr;FA;").
Proof.
  intros A Ar Kc rho r tp0 rho' tp' tr md HS HM0 HCK tpx (A' & l1 & l2 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
  pose proof HS as (EG & EL & EF & EV & EKm & EKf). cbn [rho_after rw rm] in J2, J5, J9, J11.
  exists A', l1, l2. split; [exact J1|]. split; [exact J2|]. split; [rewrite <- EL; exact J3|]. split; [rewrite J4; unfold aa_frames; rewrite EF; reflexivity|].
  split; [rewrite J5, EV; reflexivity|]. split; [rewrite J6, EKm; reflexivity|]. split; [rewrite J7; exact EKf|]. split; [rewrite J8; exact EG|].
  split; [exact (mem_kept_trans A Ar A' _ _ _ HS HM0 J9)|]. split; [exact J10 | exact (HCK A' J11)].
Qed.

Definition PF_malloc : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|0|
S4S2bS33S2dVAInv;VCST;VXGL;VW;Vst;R2R1A8LKc;LA;").
Definition PF_ok : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|1|
S4S2bS1bS16S49S3bA2M0S1dS49S3bS32S2dVW;Vst;A3S2cVAInv;VCST;VXGL;R2R1A5A4S19G0A1A3LKc;LA;").
Lemma posts_conv_malloc : ltac2:(tb__ "0|0|
S3eVCST;VXGL;S5eA3").
Proof.
  intros A Ar Kc rho r tp tp0 w HS HM0 HCK (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PF_malloc, Posts_malloc in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
  - exists (L_malloc_null AE_A W st), (JL_malloc_null AInv CST XGL A Kc), rho', tp'.
    split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_null A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
  - exists (L_malloc_ok AE_A W st), (JL_malloc_ok AInv CST XGL A Kc), rho', tp'.
    split; [right; left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_ok A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
Qed.
Lemma posts_conv_ok : ltac2:(tb__ "0|0|
S3eVCST;VXGL;S5fA3").
Proof.
  intros A Ar Kc rho r tp tp0 w HS HM0 HCK (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PF_ok in Hin. destruct Hin as [E|[]]; injection E as <- <-.
  exists (L_malloc_ok AE_A W st), (JL_malloc_ok AInv CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_ok A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
Qed.
End PCONV.

Section FINAL.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S4S2bS13S16S49S3bA2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S3eVCST;VXGL;VPFam;A3").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S35Vst;S34A3S0S13S31A1VW;S19S31A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S43VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let Ar : AA := refillA A c.
Variable phF : phase.

Hypothesis HREB : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S13S41A1S40S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS5dS28VAr;R5R4R2A5F_;Fmd;Ftr;Ftp;Fr;").
Hypothesis HMK : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S13S41A1S40S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS2aVCST;VXGL;VA;VAr;S1fVrb;A1S1fR5A1A6F_;Fmd;Ftr;Ftp;Fr;").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S11S58S14S11S6S4cVc;S45VA;Vnv;A2A2A1A2A1S4dVc;A1A3").

Lemma refill_fresh : ltac2:(tb__ "0|0|
S11S1S57Z1R1A2S57R1Z1eA2A2S2S0S11R2Vc;A3A1SeVA;R3A2SeVAr;R4A2F_;F_;F_;Fc';").
Proof.
  intros c' Hc' Hne Hf. unfold class_fresh, Ar, refillA in *. cbn [aa_cls].
  rewrite nth_list_upd_other; [exact Hf|]. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _). lia.
Qed.

Lemma JG_after : ltac2:(tb__ "0|0|
S38S1eS13S26Q40A1A1S13S41A1S40S0S15S3fR5A1S17A3S0S21S37R6P95A2S52A3S0S21S37R7P9fA2S51A3S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;R7R6R5R4AaS53VW;Vst;VAr;VKc;S3cVrho;R8A2S39R8R9A2R7R6R5A9F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fs_x;").
Proof.
  intros s_x r tp tr md HSX H149 H159 HJ. pose proof HJ as (HFz & HGh & HK' & _ & _).
  pose proof HE as (Hag & HA & Htp & HU & HB & Hnv & Htop & Hcnt & _). destruct Hag as (Hagw & Hagl & Hagm). destruct HFz as [Fw Fl].
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (RWid : forall i, (i < GW)%positive -> i <> 149%positive -> i <> 159%positive -> rw (rho_sub r s_x) i = rw (rhoM_of A rho) i).
  { intros i Hi H1 H2. cbn [rho_sub rw]. rewrite (sx_ok_id s_x i HSX Hi H1 H2). cbn [eval]. rewrite <- (Fw i) by (unfold GW in Hi; lia). symmetry. apply Hagw. exact Hi. }
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _ & Q229). fold nv c in Q227.
  assert (HL32 : (Z.to_nat (cls_of nv) < length (aa_cls A))%nat).
  { pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (L32 & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv in CF. destruct CF as ((_ & C1 & _) & _). rewrite L32. lia. }
  split.
  -
    split; [|split].
    + intros i Hi. destruct (Pos.eq_dec i 149) as [->|N1]; [|destruct (Pos.eq_dec i 159) as [->|N2]].
      * cbn [rho_sub rw]. rewrite H149. unfold vK. cbn [eval]. rewrite Q227.
        change (rw (rhoM_of Ar (rho_after rho r)) 149%positive) with (Z_to_bv 64 (cnt_of Ar (bv_unsigned (rw rho 12%positive)))).
        rewrite <- E12. fold nv. unfold Ar, c. rewrite (cnt_of_refill A nv HL32). fold c. rewrite HLEN. reflexivity.
      * cbn [rho_sub rw]. rewrite H159. unfold vCHX. cbn [eval]. rewrite Q229.
        change (rw (rhoM_of Ar (rho_after rho r)) 159%positive) with (Z_to_bv 64 (chk_of Ar (bv_unsigned (rw rho 12%positive)))).
        rewrite <- E12. fold nv. unfold Ar, c. rewrite (chk_of_refill A nv HL32). reflexivity.
      * rewrite (RWid i Hi N1 N2). apply rhoM_refill; assumption.
    + intros l. unfold rhoM_of. rewrite rl_rho_sets. cbn [rho_after rl rho_sub]. rewrite <- Fl. rewrite <- Hagl. unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
    + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
  -
    assert (R12 : rw (rho_sub r s_x) 12%positive = rw rb 12%positive) by (rewrite (RWid 12%positive) by (unfold GW; lia); apply Hagw; unfold GW; lia).
    split; [|split; [exact HK'|split; [|split; [|split; [|split]]]]].
    + apply (AInvA_view Ar r (rho_sub r s_x) tp md (HREB r tp tr md HJ)). intros a. reflexivity.
    + unfold tp_ok in *. rewrite (RWid 24%positive) by (unfold GW; lia). rewrite (Hagw 24%positive) by (unfold GW; lia). exact Htp.
    + unfold unwind_stopJ. destruct W as [|l W']; [exact I|]. destruct st; [exact I|]. discriminate (HW eq_refl).
    + cbn [eval]. rewrite R12. fold nv. exact HB.
    + cbn [eval]. rewrite R12. fold nv. lia.
    + unfold top_high in *. rewrite (RWid 10%positive) by (unfold GW; lia). rewrite (RWid V_DEPTH) by (unfold GW, V_DEPTH; lia).
      rewrite (Hagw 10%positive) by (unfold GW; lia). rewrite (Hagw V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma posts_after : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S4fS2aVCST;VXGL;VA;VAr;S1fVrho;A1S1fR3A1A6S3aS28S36S3cVrho;R4A2R3VPFam;VAr;VKc;A2R2A6S3aS28S36Vrho;Vtp0;VPFam;VA;VKc;A2R3A6F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w HM0 H.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((Hnv & C1 & _) & _).
  pose proof HE as (HagE & _). destruct HagE as (Hagw & _ & _).
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (Ecls : ClassID (needed (bv_unsigned (rw rho 12%positive))) = c) by (rewrite <- E12; fold nv; exact (proj1 (cls_needed nv Hnv))).
  apply (HPF A Ar Kc rho r tp tp0 w); [repeat split; reflexivity | exact HM0 | | exact H].
  intros A' HCK c' Hc' Hn Hf. apply (HCK c' Hc' Hn). apply refill_fresh; [exact Hc'| |exact Hf].
  destruct Hn as [Hn|Hn]; [rewrite <- E12 in Hn; fold nv in Hn; lia | rewrite Ecls in Hn; exact Hn].
Qed.

Variables (E3P EZ : axst) (s_x : wsub).
Hypothesis ENT_x : ltac2:(tb__ "0|0|
S0S15S4aVEZ;VE3P;Vs_x;A3S17A3").
Hypothesis SX_x : sx_okb s_x = true.
Hypothesis S149_x : ltac2:(tb__ "0|0|
S0S21S37Vs_x;P95A2S52A3").
Hypothesis S159_x : ltac2:(tb__ "0|0|
S0S21S37Vs_x;P9fA2S51A3").

Hypothesis HPOP : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S1eVTR;S50S28S53VW;Vst;VAr;VKc;R3A5VE3P;R1R2A5S3aS28S36R3R2VPFam;VAr;VKc;A2A5A2FrX;Ftp';Frho';").

Theorem refill_back : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1VTR;S50S28S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;A6VEZ;R2R1A5S3aS28S36Vrho;Vtp0;VPFam;VA;VKc;A2A5A2Ftp;Fr;").
Proof.
  intros r tp.
  assert (Erm : rm rb = rm rho).
  { destruct HE as ((_ & _ & Hm) & _). apply functional_extensionality. intros a. rewrite <- (Hm a). unfold rhoM_of. rewrite rm_rho_sets. reflexivity. }
  apply (tr_pure Kc TR KIT (mem_keptA CST XGL A Ar (rm rho) (rm r))).
  { intros w [_ HJ]. rewrite <- Erm. exact (HMK r tp _ _ HJ). }
  intros HM0.
  apply (tr_post Kc TR KIT _ _ _ (fun w Hw => posts_after r tp w HM0 Hw)).
  apply (tr_pre Kc TR KIT (SPA segs (JG W st Ar Kc (rho_after rho r)) E3P (rho_sub r s_x) tp)); [|apply HPOP].
  intros w Hw. apply (SPA_entails_J (JRp phF) (JG W st Ar Kc (rho_after rho r)) EZ E3P s_x r tp w ENT_x); [|exact Hw].
  intros HJ. exact (JG_after s_x r tp _ _ SX_x S149_x S159_x HJ).
Qed.
End FINAL.
End SpineMallocR5.

(* [comment removed for export] *)
Module SecLinks.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "None"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ageom"; "AA"; "aa_depot"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "slink"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.RebuildS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Links.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0SaVCST;R1A2SaS23R2A2S5F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0SaVCST;R1A2S4S21R2A1A1F_;Fa;").

Lemma slink4_refl : ltac2:(tb__ "0|2|
S16S0S0S6S0S2SbS15R4A1M0R1A2ScR1SdG0SeR3Z8A2A2A2A2S4S3S14S10Q8A1M1A1S7R3S11Q40R2A2A2S12G1A1A3A1F_;Fz;S1aR5R4R3R2R2A5F_;Fr;FL;Fua;FG;").
Proof. intros G ua L r RD. split; [reflexivity|]. split; [reflexivity|]. split; [intros a; left; reflexivity | exact RD]. Qed.

Theorem links_kept : ltac2:(tb__ "0|4|
S17S6S13S10Q40M0A1M1A1S1bS0S0S6S6S6S6S1fS1cRaR9R8R7A5S2SbZfc01R7A2ScR7SfZ2Z27A2A2A2S19RcA1S16S22R9A1S0S20ReR9R1RbA4S24RaR2R9R8A4S1aR4RbR3R9R8A5S1dS18R11A1R9R8A3S2S1eVCST;VXGL;R12R12S7RcA1S7R9A1A6S2S0S2SbS15ReA1M2R1A2ScR1SdG2SeR6Z8A2A2A2A2S4S3S14S10Q8A1M3A1S7RbS11G0R2A2A2S12G3A1A3A1F_;Fz;S2S1S3G1S9RaR1A2S9RdR1A2A3Fi;S1S3S13G3A1S8RaR1A2S8RdR1A2A3Fl;A2A2A2F_;F_;F_;F_;TL;TG;F_;F_;Frho3;Frho2;Frho1;Frho0;Fua;Fnv;Fmd;Ftp;Fr;FAs;").
Proof.
  intros A r tp md nv ua rho0 rho1 rho2 rho3 HA Hnv. cbn zeta. intros HPD (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2) (W3 & L3 & M3).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A _ HG Hsep HI3 HPR HSR SS SX) as LFN.
  unfold sepZ in SF, ST. cbn [fst snd] in SF, ST. rewrite FS_total_val in SF.
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }

  assert (RUNB : forall z, Sh ua <= z < Sh ua + L / 8 -> 2147446784 <= z < 17594333495296).
  { intros z Hz. rewrite <- ESHL in Hz.
    pose proof (sh_run_band2 ua (ua + L) z ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia) Hz) as BY.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. exact BY. }
  idtac "lk:0".

  assert (NOC : forall a, client_addrA CST A a -> ~ rtint G a /\ ~ (ua <= a < ua + L)).
  { intros a Hcl.
    destruct (client_addr_cases CST A a _ HF Hcl) as [S|[Lv|[FR|[C|FL]]]].
    - fold G in S. split; [|clear -S PDT; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X S ACV; lia | clear -X S P2; lia].
    - destruct Lv as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2.
      pose proof (rz_bound n) as RZ.
      pose proof (LFN b n a Hbn ltac:(left; clear -Hx RZ; lia)) as NZ.
      pose proof (live_foot _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as (X1 & X2 & _).
      pose proof (live_foot_pab _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as X3. fold G T in X2, X3.
      split; [|intros X; apply NZ; left; exact X].
      intros [X|X]; [unfold SEC_INST, IMG_HI in *; clear -X X1; lia | exact (X3 X)].
    - destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. fold G in Hx.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -Hx M SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X Hx M; lia | unfold kPtrArrayReserve in X; clear -X Hx M PF; lia].
    - destruct (HCST _ C) as [X0 _]. unfold IMG_LO, IMG_HI in X0.
      split; [|unfold IMG_HI in UI; clear -X0 UI; lia].
      intros [X|X].
      + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold SEC_INST in *.
        exists 0xeddd8, (0xee044 - 0xeddd8). split; [left; reflexivity | clear -X; lia].
      + unfold IMG_HI in P1. clear -X X0 P1. lia.
    - destruct FL as (c & p & Hcp & Hp & _ & Ea). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Ea. unfold fs_flags in M, Ea. rewrite FS_kFlagsOffset_val in M, Ea. unfold IMG_HI in M.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -M Ea SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X M Ea; lia | unfold kPtrArrayReserve in X; clear -X M Ea PF; lia]. }
  idtac "lk:1".

  destruct (AInvA_X A r tp md HA) as (HXd & _ & _).
  assert (NOD : forall a, KEEPD CST XGL A a -> ~ DFP (aa_depot A) a).
  { intros a HK. exact (keep_not_DFP UStopLe CST XGL HCST HXGL HCSTD A r tp md a HXd HK). }
  assert (BAND : forall a, 2147446784 <= a < 17594333495296 -> ~ DFP (aa_depot A) a).
  { intros a HB' HD.
    assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSR as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HSR as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact HB' | exact Hws]. }

  assert (BRT : forall a, 2147446784 <= a < 17594333495296 -> ~ rtint G a).
  { intros a HB' [X|X]; [unfold SEC_INST in X; clear -X HB'; lia |].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P3. clear -X HB' P3. lia. }
  idtac "lk:2".

  assert (NOS : forall a, client_shadowA CST XGL A a -> 2147446784 <= a < 17594333495296 /\ ~ (Sh ua <= a < Sh ua + L / 8)).
  { intros a C1. pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
    split; [clear -B0; lia|]. intros X.
    assert (XIN : forall x, a = Sh x -> 0 <= x -> ua <= x < ua + L).
    { intros x -> Hx0. unfold Sh in X. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL.
      pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
      pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MX. clear -X DL DU DX MX. lia. }
    destruct C1 as [(y & Cy & Ey)|(y & Gy & Ey)].
    - destruct (client_addr_bounds CST HCST A y _ HG HF Hsep Cy) as [By _]. pose proof (XIN y Ey ltac:(clear -By; lia)) as YIN.
      exact (proj2 (NOC y Cy) YIN).
    - destruct (HXGL y Gy) as [Y1 Y2]. pose proof (XIN y Ey ltac:(clear -Y1; unfold IMG_LO in *; lia)) as YIN. clear -YIN Y2 UI. lia. }
  idtac "lk:3".

  assert (DEFB : forall z, 2147446784 <= z < 17594333495296 -> rm rho0 (Z_to_bv 64 z) <> None -> rm rho3 (Z_to_bv 64 z) <> None).
  { intros z Hz Hd.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Hz; lia).
    assert (H1 : rm rho1 (Z_to_bv 64 z) <> None).
    { destruct (M1 (Z_to_bv 64 z)) as [E|[(N & _)|(_ & N)]]; [rewrite E; exact Hd | exact (False_ind _ (Hd N)) | exact N]. }
    assert (H2 : rm rho2 (Z_to_bv 64 z) <> None).
    { destruct (M2 (Z_to_bv 64 z)) as [E|[(N & _)|[(_ & N)|N]]]; [rewrite E; exact H1 | exact (False_ind _ (H1 N)) | exact N |].
      rewrite EZ in N. exact (False_ind _ (BRT z Hz N)). }
    rewrite (M3 (Z_to_bv 64 z)); [exact H2|]. rewrite EZ. exact (BAND z Hz). }
  idtac "lk:4".
  split; [|split; [|split]].
  - split.
    + intros a Ba Hcl.
      assert (EZ : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Ba; lia).
      assert (KD : KEEPD CST XGL A a) by (destruct Hcl as [(C1 & _)|(C1 & _)]; [left; exact C1 | right; exact C1]).
      rewrite (M3 (Z_to_bv 64 a)) by (rewrite EZ; exact (NOD a KD)).
      destruct Hcl as [(C1 & _ & NE)|(C1 & _ & Hd)].
      * destruct (NOC a C1) as (N1 & N2).
        destruct (client_addr_bounds CST HCST A a _ HG HF Hsep C1) as [_ NB].
        assert (NRUN : ~ (Sh ua <= a < Sh ua + L / 8)) by (intros X; pose proof (RUNB a X) as Y; clear -Y NB; lia).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|(N & _)]]; [exact E | | ]; rewrite EZ in N; exfalso;
            [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N)]. }
        rewrite <- E1.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|[(N & _)|N]]]; [exact E | | | ]; rewrite EZ in N; exfalso;
          [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N) | exact (N1 N)].
      * destruct (NOS a C1) as (B0 & NRUN).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(N & _)|(N & _)]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N))]. }
        rewrite <- E1. rewrite <- E1 in Hd.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(N & _)|[(N & _)|N]]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N)) |].
        rewrite EZ in N. exact (False_ind _ (BRT a B0 N)).
    + intros x j Hx Hj Hdef.
      assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
      { destruct Hx as [[C1 C2]|GX].
        - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
        - destruct (HXGL x GX) as [X0 X1]. unfold IMG_LO, IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
      unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
      destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1' & W2' & W3').
      unfold word_byte in *. apply DEFB; [|exact Hdef]. clear -W3' Bx Hj. lia.
  - intros z Hz. pose proof (RUNB z Hz) as Bz.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Bz; lia).
    rewrite (M3 (Z_to_bv 64 z)); [exact (D2 z Hz)|]. rewrite EZ. exact (BAND z Bz).
  - intros i. rewrite W3, W2. apply W1.
  - intros l. rewrite L3, L2. apply L1.
Qed.
End Links.
End SecLinks.

(* [comment removed for export] *)
Module SpineMallocSec5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "true"; "prod"; "Some"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "sv"; "holds"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU"; "F_g4"; "DPENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC5.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S15S21VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S6S25S22Vnx;A2S9A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S24VnW;Vst;Vnx;VBX;A4").

Lemma F_g4_hold : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S5S1dA1S1cVJG;R9R8R7R6R5R4R3R2R1A9S1bSfS12R5A1S17Vnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & ENS & _).
  destruct HJ as (_ & _ & _ & HP & _ & _ & _ & Hnv & _). cbn zeta in Hnv.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  destruct HP as (_ & _ & _ & (D1 & D2 & D3 & _) & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (secmapsize_bounds nv ltac:(lia)) as (MB1 & MB2).
  assert (NSV : secneeded nv = (nv + 8 - 1) / 8 * 8 + 4096) by reflexivity.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)) as MBd.
  pose proof (urange a) as Ra.
  unfold F_g4. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite !add_val, ENS, Enx, E12, !u64_lit in H by lia. fold nv in H.
  rewrite (Z.mod_small (bv_unsigned a + 4096)) in H by lia. rewrite (Z.mod_small (bv_unsigned a + 6144)) in H by lia.
  rewrite !Z.mod_small in H by lia. lia.
Qed.

Section G41.
Variables (T4 U4 X5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S6S13S1VU4;A1A1S9A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0ScSaS5SaS11S11A2M0A1M1S5SfA1M2A2M3A1S1fS1VT4;A1S1VU4;A1A2SbG3SdG1G2S8G0A1S17Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S15S10S1VU4;A1A1S10S1VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S2S3VT4;S1VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S6S20S23Ufa0S7S14S18S8S14A1A3VGS;S7S2VU4;S8S2A1M0A3S7S2VX5;G0A3A6S9A3").

Lemma RSU4 : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S1eS16Vsegs;VJG;R8R7R6R5R4A5VT4;R3R2R1A6S16Vsegs;VJG;R9R8R7R6R5A5VU4;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU4.
  eapply SPA_restate; [exact WU4 | exact DU4 | exact NXU4 | constructor | | exact Hw].
  exact (F_g4_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.
End G41.
End SEC5.
End SpineMallocSec5.

(* [comment removed for export] *)
Module SpineMallocSecE2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "ax_X"; "ax_base"; "shadow_addr"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "list"; "app"; "prod"; "pair"; "option"; "length"; "None"; "Some"; "false"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "ss_next"; "sobj"; "SLit"; "reg_sv"; "SVar"; "rw"; "ss_facts"; "eval"; "ss_objs"; "SPBranch"; "rm"; "swf"; "sprop_below"; "SPNot"; "obj_range"; "ranges_disjoint"; "ro_addr"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_sec"; "aa_geom"; "sec_chunk"; "aa_ptr_committed"; "budget_bound"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "of_nat"; "pow"; "div"; "ge"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "genL"; "Bw"; "F_l2"; "F_g3"; "O_1"; "O_2"; "x11e3"; "O_blk"; "O_w"; "a0e3"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NCH"; "V_NRES"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"; "JGo"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "alloc_top"; "m_vmmaps"; "map_contains"; "region_free"; "vm_forget_range"; "vm_maps"; "vm_reserved"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "SKEL0"; "JGs"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac rr X := intros; eapply X; revgoals; [> eassumption ..].

Section SEC4E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1bS73VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0ScS57S8bVnx;A2SdA3").
Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S3dS0S43S3fVAX;R1A1A1S3fR1A1A3FX;").
Hypothesis AXs : ltac2:(tb__ "0|0|
S3dS0SfS40A1S3eVAX;R1A1A1S3eR1A1A3FX;").
Hypothesis AXp : ltac2:(tb__ "0|0|
S3dS0S1aS41VAX;R1A1A1S41R1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S3dS0S1aS42VAX;R1A1A1S42R1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S84VnW;Vst;Vnx;VBX;A4").
Let slink : Z -> Z -> valuation -> valuation -> Prop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.slink.
Let AXP : AA -> AA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4.AXP AX.
Let JGo : ltac2:(tb__ "0|0|
S3dS45S1cS3bQ40A1S38Fa;Frho;FKc;FA;") := ltac2:(tb__ "0|0|
S76VnW;Vst;Vnx;VAX;A4").

Lemma ecfg_2 : ltac2:(tb__ "0|3|
SfS1aA1S5S5S5S38S55OF_;SfS3bQ40A1A1S1cS39Vsegs;VGS;R4A3S0ScS57VGS;S1fS4R8A1A1A2SdA3S0ScS34S56Ufa0RaVGS;SbS32S33R9Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33R8G0G1A3SbS32S33R7G0G1A3G2A3A3A6SdA3S1cS54Vsegs;S37Vsegs;R8RaR1R6A5R7A3Frho';S1cS54Vsegs;S37Vsegs;R9RaR1R7A5R8A3Frho';S54Vsegs;S37Vsegs;R9RcR6R7A5R8A3F_;F_;F_;F_;F_;Frho;Ftp;FQ;FJx;FE2;FE1;FC;Fcutpcs;").
Proof.
  intros cutpcs C E1 E2 Jx Q tp rho HST NXC HC HE1 HE2.
  apply (ecfg_cutG 4000%nat cutpcs GS [mkVNA C 1 (SLit 0)] [mkVNA E1 0 (SLit 0); mkVNA E2 0 (SLit 0)] Jx Q tp C rho HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. apply Pos.leb_le. exact NXC.
  - exact HC.
  - intros E' rho' HinE. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE1 rho')].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE2 rho')].
  - left. reflexivity.
Qed.

Section G3E.

Variables (D2 U2 X3a X3b CS3 G3 X3a3 L3a L3b CO3b T4a T4b Y4a0 Y4a1 Y4b0 Y4b1 : axst).
Variables (sLa sLb s4a0 s4a1 s4b0 s4b1 : wsub).

Hypothesis WU2 : ltac2:(tb__ "0|0|
S0ScS2aS4VU2;A1A1SdA3").
Hypothesis DU2 : ltac2:(tb__ "0|4|
S0S13S11SfS11S1dS1dA2M0A1M1SfS1eA1M2A2M3A1S82S4VD2;A1S4VU2;A1A2S16G3S12G1G2SeG0A1S5dA4A2A3").
Hypothesis NXU2 : ltac2:(tb__ "0|0|
S0S1bS1fS4VU2;A1A1S1fS4VD2;A1A1A3").
Hypothesis HU2 : ltac2:(tb__ "0|0|
S0S5S7VD2;S4VU2;A1A2VU2;A3").

Hypothesis Cert3 : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ7050cSbS1aZ40f5cSeS1aA1A3A3VGS;SbS5VU2;SeS5A1M0A3SbS5VX3a;SbS5VX3b;G0A3A3A6SdA3").

Hypothesis WC3 : ltac2:(tb__ "0|0|
S0ScS2aS4VCS3;A1A1SdA3").
Hypothesis DC3 : ltac2:(tb__ "0|4|
S0S13S11SfS11S1dS1dA2M0A1M1SfS1eA1M2A2M3A1S82S4VX3a;A1S4VCS3;A1A2S16G3S12G1G2SbG0S12S1dS1dS63S5bA4SeG0A1A3SeS1eA1A4A2A3").
Hypothesis NXC3 : ltac2:(tb__ "0|0|
S0S1bS1fS4VCS3;A1A1S1fS4VX3a;A1A1A3").
Hypothesis HC3 : ltac2:(tb__ "0|0|
S0S5S7VX3a;S4VCS3;A1A2VCS3;A3").
Hypothesis FX3a : ltac2:(tb__ "0|0|
S67S1eS10S1eSbS1eS28S6eS23S71A1S23S72A1A3SeS1eA1A3S5dA3S25S4VX3a;A1A1A3").
Hypothesis IC3 : ltac2:(tb__ "0|0|
S0S13S6fA1S87S56S30S4VCS3;A1A1A2S16S6fS70A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1Z11A2S21ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZaA2S5bA3").
Hypothesis BBw : ltac2:(tb__ "0|0|
S0ScS31S1fS4VCS3;A1A1S5bA2SdA3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZbA2S21Z20000A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZcA2S21Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZdA2S21Z32A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZeA2S21ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZfA2S21Z0A1A3").
Hypothesis XC3 : ax_X CS3 = [].
Hypothesis SK3 : ltac2:(tb__ "0|2|
S0SfS11S11S1dS1dA2S1dA2M0A1S6aS20G0S6bS27S4VCS3;A1A1A4S6aS20G0S6bS10S20SbS20S5fVnx;A1SbS20S5eVnx;A1SeS20A1M1A3A3S10S20S83VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC3 : ltac2:(tb__ "0|0|
S67S1eS10S1eS4bVW;Vst;A2S4aS49A1A3S25S4VCS3;A1A1A3").
Hypothesis FCS3 : ltac2:(tb__ "0|0|
S67S1eS10S1eSbS1eS28S6eS23S71A1S23S72A1A3SeS1eA1A3S5dA3S25S4VCS3;A1A1A3").
Hypothesis NXS3 : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VCS3;A1A1A2SdA3").

Hypothesis HG3 : ltac2:(tb__ "0|1|
S0S5S7VCS3;S86S4VCS3;A1M0S5bS10S20S27G0A1SbS20S61SeS20A1A3A3S1fG0A1A4A2VG3;A3").

Hypothesis Cert3a : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ40f5cSeS1aA1A3VGS;SbS5VG3;SeS5A1M0A3SbS5VX3a3;G0A3A6SdA3").

Hypothesis ELa : ltac2:(tb__ "0|0|
S0ScS6VX3a3;S5aVX3a3;A1VsLa;A3SdA3").
Hypothesis IDa : ltac2:(tb__ "0|0|
S0ScS58VsLa;VGS;A2SdA3").
Hypothesis GLa : ltac2:(tb__ "0|0|
S0S1dS59VsLa;S1fS4VX3a3;A1A1A2S60A3").
Hypothesis FBLa : ltac2:(tb__ "0|0|
S0ScS69S1eS2bS1fS4S5aVX3a3;A1A1A1A1S5cS1fS4VX3a3;A1A1A1A3SdA3").
Hypothesis HL3a : ltac2:(tb__ "0|0|
S0S5S36S5cS1fS4VX3a3;A1A1A1S5aVX3a3;A1A2VL3a;A3").
Hypothesis ELb : ltac2:(tb__ "0|0|
S0ScS6VX3b;S5aVX3b;A1VsLb;A3SdA3").
Hypothesis IDb : ltac2:(tb__ "0|0|
S0ScS58VsLb;VGS;A2SdA3").
Hypothesis GLb : ltac2:(tb__ "0|0|
S0S1dS59VsLb;S1fS4VX3b;A1A1A2S60A3").
Hypothesis FBLb : ltac2:(tb__ "0|0|
S0ScS69S1eS2bS1fS4S5aVX3b;A1A1A1A1S5cS1fS4VX3b;A1A1A1A3SdA3").
Hypothesis HL3b : ltac2:(tb__ "0|0|
S0S5S36S5cS1fS4VX3b;A1A1A1S5aVX3b;A1A2VL3b;A3").

Hypothesis HCOb : ltac2:(tb__ "0|0|
S0S5S64VL3b;S62A2VCO3b;A3").
Hypothesis WCOb : ltac2:(tb__ "0|0|
S0ScS2aS4VCO3b;A1A1SdA3").
Hypothesis XCb : ax_X L3b = [].
Hypothesis SKb : ltac2:(tb__ "0|2|
S0SfS11S11S1dS1dA2S1dA2M0A1S6aS20G0S6bS27S4VL3b;A1A1A4S6aS20G0S6bS10S20SbS20S5fVnx;A1SbS20S5eVnx;A1SeS20A1M1A3A3S10S20S83VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FCb : ltac2:(tb__ "0|0|
S67S1eS10S1eS4bVW;Vst;A2S4aS49A1A3S25S4VL3b;A1A1A3").
Hypothesis FXb : ltac2:(tb__ "0|0|
S67S1eSbS1eS2cS28S6eS23S71A1S23S72A1A3A1SeS1eA1A3S25S4VL3b;A1A1A3").

Hypothesis Cert4a : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ3c480SeS1aA1A3VGS;SbS5VL3a;SeS5A1M0A3SbS5VY4a0;SbS5VY4a1;G0A3A3A6SdA3").
Hypothesis E4a0 : ltac2:(tb__ "0|0|
S0ScS6VY4a0;VT4a;Vs4a0;A3SdA3").
Hypothesis I4a0 : ltac2:(tb__ "0|0|
S0ScS58Vs4a0;VGS;A2SdA3").
Hypothesis E4a1 : ltac2:(tb__ "0|0|
S0ScS6VY4a1;VT4a;Vs4a1;A3SdA3").
Hypothesis I4a1 : ltac2:(tb__ "0|0|
S0ScS58Vs4a1;VGS;A2SdA3").
Hypothesis Cert4b : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ3c480SeS1aA1A3VGS;SbS5VCO3b;SeS5A1M0A3SbS5VY4b0;SbS5VY4b1;G0A3A3A6SdA3").
Hypothesis E4b0 : ltac2:(tb__ "0|0|
S0ScS6VY4b0;VT4b;Vs4b0;A3SdA3").
Hypothesis I4b0 : ltac2:(tb__ "0|0|
S0ScS58Vs4b0;VGS;A2SdA3").
Hypothesis E4b1 : ltac2:(tb__ "0|0|
S0ScS6VY4b1;VT4b;Vs4b1;A3SdA3").
Hypothesis I4b1 : ltac2:(tb__ "0|0|
S0ScS58Vs4b1;VGS;A2SdA3").

Hypothesis NXEU2 : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VU2;A1A1A2SdA3").
Hypothesis NXEG3 : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VG3;A1A1A2SdA3").
Hypothesis NXEL3a : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VL3a;A1A1A2SdA3").
Hypothesis NXECOb : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VCO3b;A1A1A2SdA3").
Hypothesis ECert3 : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ7050cSbS1aZ40f5cSeS1aA1A3A3VGS;SbS32S33VU2;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VX3a;G0G1A3SbS32S33VX3b;G0G1A3G2A3A3A6SdA3").
Hypothesis ECert3a : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ40f5cSeS1aA1A3VGS;SbS32S33VG3;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VX3a3;G0G1A3G2A3A6SdA3").
Hypothesis ECert4a : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ3c480SeS1aA1A3VGS;SbS32S33VL3a;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VY4a0;G0G1A3SbS32S33VY4a1;G0G1A3G2A3A3A6SdA3").
Hypothesis ECert4b : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ3c480SeS1aA1A3VGS;SbS32S33VCO3b;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VY4b0;G0G1A3SbS32S33VY4b1;G0G1A3G2A3A3A6SdA3").

Lemma RSU' : ltac2:(tb__ "0|1|
S3dS45S1cS3bQ40A1M0S1cSfG0A1S55S4dS4cS4fS14S40S3eR7A1A2A1Z1A2S50Z2Z14A2A2S37Vsegs;VJG;VAX;R8R7R6R5A5VD2;R4R3R2A6S37Vsegs;VJG;VAX;R9R8R7R6A5VU2;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU. Qed.
Lemma RS3' : ltac2:(tb__ "0|1|
S3dS45S1cS3bQ40A1M0S1cSfG0A1S55S37Vsegs;VJG;VAX;R7R6R5R4A5VX3a;R3R2R1A6S37Vsegs;VJG;VAX;R8R7R6R5A5VCS3;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RS3. Qed.
Lemma ens_oblig' : ltac2:(tb__ "0|c|
S3dS45S1cS3bQ40M0A1M1S1cSfG1A1S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S48R6A1S4dS4cS4fS14S40S3eR8A1A2A1Z1A2S50Z2Z14A2A2SfS79A1M2S77S78S89Vsegs;R8R7VCS3;S12G2S6cR3S6dR2R1A2A4A5VJG;VAX;RdRcRbRaR9R8R4R2A9S26RaS5bA2G1S3aG0R1A2M3S1aZ20000S1aS1S0S1aS53R2Z1000A2Z0M4A3S1S4dG4R2A2S1S4eS4cR2R1A2M5S7aS7bR6A1M6A1A2S1S0ScS7dS80G6A1R3S3cG0R1A2M7A3SdA3S1S0ScS7cS7fG6A1M8R3G7A3SdA3S1S4eS88G8R2G5A3R1A2S1S52S8aR6RcA2R1A2S1S20S68S20R1S27S4VCS3;A1A1A3S2eS2dRfR2A2S12S1aS1aR4S4cR4R3A2A4A2F_;Fo;S1G1S1S4eR3G3A2S4dG3S4cR3R2A2A2A2S0ScS2fVsegs;R2A2S17A3F_;Fx;S1S11S1dS1dA2M9S1aS68G9R2S8VCS3;A1A3S1S4eS3aG0S26R10S18S1dS1dR3A3A2A2MaR2A2S4dR2S4cGaS3aG0S26R10S19S1dS1dR3A3A2A2A2A2A2S2S1S4eR6S3aG0SaS3aG0S26R11S9VCS3;A1A2A2R3A2A2MbA2S4dGbS4cR6R5A2A2A2A1F_;F_;Fy;Frr;VJGo;R11R10RfReRdRcR8S7eR2G5S81S85G6R3G7A3R6A2A3A8A2A2A2A2A2A2A2A2A2A2Tnlit;Tua;Ta0;F_;F_;Fmd;Fms;Ftr;F_;F_;F_;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr ens_oblig. Qed.
Lemma ensure_post' : ltac2:(tb__ "0|6|
S3dS45S1cS3bQ40M0A1M1S1cSfG1A1SfS79A1M2S77S78S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S1aS1S4eS74S3aG0R8A2A1M3R1A2S4dR1S4cG3S51S65S3aG0S24R9PcM4A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M5A1S29RaS3cG0R2A2A2S15G5A1A3A1F_;Fz;S37Vsegs;VJGo;RbRaR9R8A4VG3;R7R6S12G2S6cR5S6dR4R3A2A4A6S3S1cS1cS3S1cS1cS1S75S3fReA1S3aG0RbA2S65S3aG0S24RcG4A2A2A1RcR1A5S37Vsegs;VJG;VAXP;ReRdR1RbA5VG3;R2R9S12G2S6cR8S6dR7R6A2A4A6A2Lrho'';A2Lr2;A2F_;F_;F_;Fmd';Fms;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. rr ensure_post. Qed.
Lemma carve_w' : ltac2:(tb__ "0|1|
S3dS45S1cS3bQ40A1M0S1cSfG0A1S55S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S37Vsegs;VJG;VAX;R8R7R6R5A5VL3b;R4R3R2A6S37Vsegs;VJG;VAX;R9R8R7R6A5VCO3b;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. rr carve_w. Qed.

Lemma epath_b : ltac2:(tb__ "0|2|
S3dS45S1cS3bQ40A1M0S55OF_;S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S66VW;Vst;A2S48R6A1S1cSfG0A1M1S54Vsegs;S37Vsegs;VJG;VAX;RaR9R8R7A5VT4b;R2R1A5R6A3FtY;FrY;S1cG1S54Vsegs;S37Vsegs;VJG;VAX;RbRaR9R8A5VX3b;R2R1A5R7A3Ftp;Fr;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCb r tp.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) CO3b (rho_sub r sLb) tp));
    [intros w Hw; exact (carve_w' A Kc rho a _ tp w HW (gen_x11 nW st tmax nx Hnx NXG AX A Kc rho a X3b L3b sLb r tp w HUS HKc ELb IDb GLb FBLb HL3b Hw))|].
  apply (ecfg_2 [0x3c480] CO3b Y4b0 Y4b1 (JG AX A Kc rho a) Q tp _ HST NXECOb ECert4b); intros rE.
  - apply (etc_pre (SPA segs (JG AX A Kc rho a) T4b (rho_sub rE s4b0) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AX A Kc rho a Y4b0 T4b s4b0 rE tp w HUS HKc E4b0 I4b0 Hw) | apply HCb].
  - apply (etc_pre (SPA segs (JG AX A Kc rho a) T4b (rho_sub rE s4b1) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AX A Kc rho a Y4b1 T4b s4b1 rE tp w HUS HKc E4b1 I4b1 Hw) | apply HCb].
Qed.

Lemma epath_a : ltac2:(tb__ "0|6|
S3dS45S1cS3bQ40M0A1M1S55OF_;S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S66VW;Vst;A2S48R6A1S4dS4cS4fS14S40S3eR8A1A2A1Z1A2S50Z2Z14A2A2S1aS1S4eS74S3aG0R7A2A1M2R1A2S4dR1S4cG2S51S65S3aG0S24R8PcM3A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M4A1S29R9S3cG0R2A2A2S15G4A1A3A1F_;Fz;S1cS1cSfG1A1M5S75S3fRdA1S3aG0RaA2S65S3aG0S24RbG3A2A2A1RbR3A5S54Vsegs;S37Vsegs;VJG;VAXP;ReRdR4RbA5VT4a;R3R2A5RaA3F_;FtY;FrY;Frho'';S1cG5S54Vsegs;S37Vsegs;VJG;VAX;RdRcRbRaA5VX3a;R2R1A5R9A3Ftp;Fr;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc Hok RUNDEF HCa r tp.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) CS3 r tp)); [intros w Hw; exact (RS3' A Kc rho a r tp w Hw)|].
  assert (HST' : stableA segs (ss_next (ax_S CS3)) (JG AX A Kc rho a)).
  { eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact NXS3. }
  eapply etriple_seq.
  { apply (etriple_fixed_commitA segs (JG AX A Kc rho a) (JGo A Kc rho a) CS3 r tp Bw 131072 HST' IC3 R17 R10 BBw R11 R12 R13 R14 R15 eq_refl ltac:(lia)).
    exact (ens_oblig' A Kc rho a r tp HW HKc Hok). }
  fold O_blk. rewrite HG3.
  apply (etc_pre (fun w => exists r2 rho'', slink4 (aa_geom A) (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho'' /\ SPA segs (JG AXP A Kc rho'' a) G3 r2 tp w));
    [intros w Hw; destruct w as [tr [ms md]]; exact (ensure_post' A Kc rho a r tp tr ms md HW RUNDEF Hw)|].
  apply etriple_ex; intros r2. apply etriple_ex; intros rho''.
  apply (etriple_pre_pure segs _ _ (slink4 (aa_geom A) (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho'')); [intros w [SL _]; exact SL|]. intros SL.
  apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) G3 r2 tp)); [intros w [_ Hw]; exact Hw|].
  pose proof (JGs_stable nW st tmax nx Hnx NXG AXP A Kc rho'' a HUS HKc) as HST2.
  apply (ecfg_1 nx [0x40f5c] G3 X3a3 (JG AXP A Kc rho'' a) Q tp r2 HST2 NXEG3 ECert3a). intros rE.
  apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) L3a (rho_sub rE sLa) tp));
    [intros w Hw; exact (gen_x11 nW st tmax nx Hnx NXG AXP A Kc rho'' a X3a3 L3a sLa rE tp w HUS HKc ELa IDa GLa FBLa HL3a Hw)|].
  apply (ecfg_2 [0x3c480] L3a Y4a0 Y4a1 (JG AXP A Kc rho'' a) Q tp _ HST2 NXEL3a ECert4a); intros rE'.
  - apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) T4a (rho_sub rE' s4a0) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AXP A Kc rho'' a Y4a0 T4a s4a0 rE' tp w HUS HKc E4a0 I4a0 Hw) | apply HCa; exact SL].
  - apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) T4a (rho_sub rE' s4a1) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AXP A Kc rho'' a Y4a1 T4a s4a1 rE' tp w HUS HKc E4a1 I4a1 Hw) | apply HCa; exact SL].
Qed.

Theorem esec_g3 : ltac2:(tb__ "0|6|
S3dS45S1cS3bQ40M0A1M1S55OF_;S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S66VW;Vst;A2S48R6A1S4dS4cS4fS14S40S3eR8A1A2A1Z1A2S50Z2Z14A2A2S1aS1S4eS74S3aG0R7A2A1M2R1A2S4dR1S4cG2S51S65S3aG0S24R8PcM3A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M4A1S29R9S3cG0R2A2A2S15G4A1A3A1F_;Fz;S1cS1cSfG1A1M5S75S3fRdA1S3aG0RaA2S65S3aG0S24RbG3A2A2A1RbR3A5S54Vsegs;S37Vsegs;VJG;VAXP;ReRdR4RbA5VT4a;R3R2A5RaA3F_;FtY;FrY;Frho'';S1cG5S54Vsegs;S37Vsegs;VJG;VAX;RdRcRbRaA5VT4b;R2R1A5R9A3FtY;FrY;S1cG5S54Vsegs;S37Vsegs;VJG;VAX;ReRdRcRbA5VD2;R2R1A5RaA3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (WU2, DU2, NXU2, HU2, Cert3, WC3, DC3, NXC3, HC3, FX3a, IC3, R17, R10, BBw, R11, R12, R13, R14, R15, XC3, SK3, FC3, FCS3, NXS3, HG3, Cert3a, ELa, IDa, GLa, FBLa, HL3a, ELb, IDb, GLb, FBLb, HL3b, HCOb, WCOb, XCb, SKb, FCb, FXb, Cert4a, E4a0, I4a0, E4a1, I4a1, Cert4b, E4b0, I4b0, E4b1, I4b1, NXEU2, NXEG3, NXEL3a, NXECOb, ECert3, ECert3a, ECert4a, ECert4b)); clear USED.
  intros A Kc rho a Q HW HUS HKc Hok RUNDEF HCa HCb rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) U2 rX tX)); [intros w Hw; exact (RSU' A Kc rho a rX tX w Hok Hw)|].
  apply (ecfg_2 [0x7050c; 0x40f5c] U2 X3a X3b (JG AX A Kc rho a) Q tX rX HST NXEU2 ECert3); intros rE.
  - exact (epath_a A Kc rho a Q HW HUS HKc Hok RUNDEF HCa rE tX).
  - exact (epath_b A Kc rho a Q HW HUS HKc HCb rE tX).
Qed.
End G3E.
End SEC4E.
End SpineMallocSecE2.

