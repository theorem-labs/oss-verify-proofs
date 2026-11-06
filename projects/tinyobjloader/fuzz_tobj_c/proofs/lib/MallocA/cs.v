(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca F0A_cLN0 dg F0A_cLN1 dk F0A_cN0 F0A_cN1.

(* [comment removed for export] *)
Module CDepotCallIW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "Wcan"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.CDepotCallMW1"; "T4_i"; "nobj_i"; "s4_i"; "R4_i"; "sd_i"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "list"; "nat"; "prod"; "cons"; "Some"; "option"; "pair"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "ss_facts"; "sstate"; "ss_next"; "SVar"; "sobj"; "ss_objs"; "SPUle"; "sprop_below"; "SAlu"; "rw"; "valuation"; "SExt"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW"; "omrg"; "X4"; "isSome"; "X4r"; "oreb"; "permW"; "T4d"; "T40"; "T4a"; "T4b"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "X4a"; "X4b"; "X4c"; "X4f"; "F_call"; "in_famb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E4d"; "C5"; "F_gen"; "V_CNT"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"; "SZMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.CDepotCallIW1.INST"; "pm__22"; "pm__23"; "pm__24"; "pm__13"; "pm__14"; "pm__15"; "pm__16"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__29"; "pm__30"; "pm__31"; "pm__32"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__0"; "pm__1"; "pm__10"; "pm__11"; "pm__12"; "pm__2"; "pm__3"; "pm__37"; "pm__38"; "pm__39"; "pm__4"; "pm__5"; "pm__6"; "pm__7"; "pm__8"; "pm__9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "coveredb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.CDepotCallMW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Ltac memo_rw t M := lazymatch goal with |- context [t] => pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta | _ => fail "memo_rw: stage term not found" t end.
Ltac vmc := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NXE_i : ltac2:(tb__ "0|0|
S0S15S8cS81S26S4S45S9U1A1Vst;Vtmax;A3A1A1A2S16A3").
Proof.  memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.
Lemma FBE_i : ltac2:(tb__ "0|0|
S0S15S49S22S2bS26S4S45S9U1A1Vst;Vtmax;A3A1A1A1S43A3S16A3").
Proof.  memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.
Lemma XE4_i : ltac2:(tb__ "0|1|
S0S18S1aS21S21A2M0A1S5S45S9U1A1Vst;Vtmax;A3A1S17G0A1A3").
Proof.  memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.
Lemma F192_i : ltac2:(tb__ "0|1|
S4aS22S1bS22S2aS23Z1A1S27Pc0A1M0A2S1bS22S2aG0S23Vtmax;A1A2S17S22A1A3A3S24S4S45S9U1A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.
Lemma FDEP_i : ltac2:(tb__ "0|0|
S4aS22SbSaA1S24S4S45S9U1A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.
Lemma FUNW_i : ltac2:(tb__ "0|1|
S4aS22ScS9U1A1M0Vst;A2S24S4S45G0Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.
Lemma FGEN4_i : ltac2:(tb__ "0|0|
S4aS22S47S24S4S45S9U1A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.
Lemma YP4_i : ltac2:(tb__ "0|0|
S4bS22S2aS23Z1A1S27S48A1A2S24S4S45S9U1A1Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E4d (Wcan 1) st tmax) mE. vmc. Qed.

Ltac PM_sub0 t := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSPW1.CallocMemoSPW1_subst t.
Ltac PM_all0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSPW1.CallocMemoSPW1_all.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X4f] in (X4f 1%nat UStopLeOrPc 3) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S3S42U1S8Z3A3S71A3"). Proof. cbv delta [X4f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X4f 1%nat UStopLeOrPc 3) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 1%nat UStopLeOrPc 3 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S3S34U1S8Z3Z1A4S72A3"). Proof. cbv delta [X4r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X4r 1%nat UStopLeOrPc 3 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 1%nat UStopLeOrPc 3 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|0|
S0S3S34U1S8Z3Z2A4S76A3"). Proof. cbv delta [X4r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X4r 1%nat UStopLeOrPc 3 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 1%nat UStopLeOrPc 3 3) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|1|
S0S3S34U1S8Z3M0G0A4S77A3"). Proof. cbv delta [X4r pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X4r 1%nat UStopLeOrPc 3 3) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 1%nat UStopLeOrPc 3 1) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|0|
S0S3S3fU1S8Z3Z1A4S7bA3"). Proof. cbv delta [X4a pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X4a 1%nat UStopLeOrPc 3 1) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 1%nat UStopLeOrPc 3 2) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S3S3fU1S8Z3Z2A4S7cA3"). Proof. cbv delta [X4a pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X4a 1%nat UStopLeOrPc 3 2) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 1%nat UStopLeOrPc 3 3) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|1|
S0S3S3fU1S8Z3M0G0A4S7dA3"). Proof. cbv delta [X4a pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X4a 1%nat UStopLeOrPc 3 3) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 1%nat UStopLeOrPc 3 1) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S3S40U1S8Z3Z1A4S7eA3"). Proof. cbv delta [X4b pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X4b 1%nat UStopLeOrPc 3 1) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 1%nat UStopLeOrPc 3 2) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|0|
S0S3S40U1S8Z3Z2A4S7fA3"). Proof. cbv delta [X4b pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X4b 1%nat UStopLeOrPc 3 2) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 1%nat UStopLeOrPc 3 3) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|1|
S0S3S40U1S8Z3M0G0A4S80A3"). Proof. cbv delta [X4b pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X4b 1%nat UStopLeOrPc 3 3) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 1%nat UStopLeOrPc 3 1) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|0|
S0S3S41U1S8Z3Z1A4S73A3"). Proof. cbv delta [X4c pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X4c 1%nat UStopLeOrPc 3 1) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 1%nat UStopLeOrPc 3 2) in let t := eval cbv beta zeta in t in let t := PM_sub11 t in exact t).
Lemma pm__11_eq : ltac2:(tb__ "0|0|
S0S3S41U1S8Z3Z2A4S74A3"). Proof. cbv delta [X4c pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (X4c 1%nat UStopLeOrPc 3 2) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 1%nat UStopLeOrPc 3 3) in let t := eval cbv beta zeta in t in let t := PM_sub12 t in exact t).
Lemma pm__12_eq : ltac2:(tb__ "0|1|
S0S3S41U1S8Z3M0G0A4S75A3"). Proof. cbv delta [X4c pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (X4c 1%nat UStopLeOrPc 3 3) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac:(let t := eval cbv delta [X4] in (X4 1%nat UStopLeOrPc 3 1) in let t := eval cbv beta zeta in t in let t := PM_sub13 t in exact t).
Lemma pm__13_eq : ltac2:(tb__ "0|0|
S0S3S32U1S8Z3Z1A4S5cA3"). Proof. cbv delta [X4 pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (X4 1%nat UStopLeOrPc 3 1) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac:(let t := eval cbv delta [X4] in (X4 1%nat UStopLeOrPc 3 2) in let t := eval cbv beta zeta in t in let t := PM_sub14 t in exact t).
Lemma pm__14_eq : ltac2:(tb__ "0|0|
S0S3S32U1S8Z3Z2A4S5dA3"). Proof. cbv delta [X4 pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (X4 1%nat UStopLeOrPc 3 2) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac:(let t := eval cbv delta [X4] in (X4 1%nat UStopLeOrPc 3 3) in let t := eval cbv beta zeta in t in let t := PM_sub15 t in exact t).
Lemma pm__15_eq : ltac2:(tb__ "0|1|
S0S3S32U1S8Z3M0G0A4S5eA3"). Proof. cbv delta [X4 pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (X4 1%nat UStopLeOrPc 3 3) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac2:(tb__ "0|0|
S58SeZ1A1S24S4S5cA1A1A2").
Lemma pm__16_eq : ltac2:(tb__ "0|0|
S0S3S38U1S8Z3SeZ1A5S5fA3"). Proof. cbv delta [T40 pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (T40 1%nat UStopLeOrPc 3 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac2:(tb__ "0|0|
S58SeZ2A1S24S4S5dA1A1A2").
Lemma pm__17_eq : ltac2:(tb__ "0|0|
S0S3S38U1S8Z3SeZ2A5S60A3"). Proof. cbv delta [T40 pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (T40 1%nat UStopLeOrPc 3 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac2:(tb__ "0|0|
S58SeZ3A1S24S4S5eA1A1A2").
Lemma pm__18_eq : ltac2:(tb__ "0|1|
S0S3S38U1S8Z3M0SeG0A5S61A3"). Proof. cbv delta [T40 pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (T40 1%nat UStopLeOrPc 3 T4_i 3) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac2:(tb__ "0|0|
S35S5fU0A2").
Lemma pm__19_eq : ltac2:(tb__ "0|0|
S0S3S39U1S8Z3SeZ1A5S62A3"). Proof. cbv delta [T4a pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (T4a 1%nat UStopLeOrPc 3 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac2:(tb__ "0|0|
S35S60U0A2").
Lemma pm__20_eq : ltac2:(tb__ "0|0|
S0S3S39U1S8Z3SeZ2A5S63A3"). Proof. cbv delta [T4a pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (T4a 1%nat UStopLeOrPc 3 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
S35S61U0A2").
Lemma pm__21_eq : ltac2:(tb__ "0|1|
S0S3S39U1S8Z3M0SeG0A5S64A3"). Proof. cbv delta [T4a pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T4a 1%nat UStopLeOrPc 3 T4_i 3) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
S35S62U1A2").
Lemma pm__22_eq : ltac2:(tb__ "0|0|
S0S3S3aU1S8Z3SeZ1A5S59A3"). Proof. cbv delta [T4b pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T4b 1%nat UStopLeOrPc 3 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
S35S63U1A2").
Lemma pm__23_eq : ltac2:(tb__ "0|0|
S0S3S3aU1S8Z3SeZ2A5S5aA3"). Proof. cbv delta [T4b pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T4b 1%nat UStopLeOrPc 3 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
S35S64U1A2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S3S3aU1S8Z3M0SeG0A5S5bA3"). Proof. cbv delta [T4b pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T4b 1%nat UStopLeOrPc 3 T4_i 3) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|1|
S6S59S57S4S59A1M0S53S29G0A1S36SfA1A2A2A2").
Lemma pm__25_eq : ltac2:(tb__ "0|0|
S0S3S3bU1S8Z3SeSfZ1A6S65A3"). Proof. cbv delta [T4c pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T4c 1%nat UStopLeOrPc 3 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|1|
S6S5aS57S4S5aA1M0S53S29G0A1S36SfA1A2A2A2").
Lemma pm__26_eq : ltac2:(tb__ "0|0|
S0S3S3bU1S8Z3SeSfZ2A6S66A3"). Proof. cbv delta [T4c pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T4c 1%nat UStopLeOrPc 3 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Definition pm__27 : axst := ltac2:(tb__ "0|1|
S6S5bS57S4S5bA1M0S53S29G0A1S36SfA1A2A2A2").
Lemma pm__27_eq : ltac2:(tb__ "0|1|
S0S3S3bU1S8Z3M0SeSfG0A6S67A3"). Proof. cbv delta [T4c pm__27]; cbv beta zeta. PM_all27. reflexivity. Qed.
Ltac PM_sub28 t := let t := lazymatch (eval pattern (T4c 1%nat UStopLeOrPc 3 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__27) end in PM_sub27 t.
Ltac PM_all28 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__27_eq; PM_all27.
Definition pm__28 : axst := ltac2:(tb__ "0|0|
S31S65U0A2").
Lemma pm__28_eq : ltac2:(tb__ "0|0|
S0S3S3cU1S8Z3SeSfZ1A6S68A3"). Proof. cbv delta [T4m1 pm__28]; cbv beta zeta. PM_all28. reflexivity. Qed.
Ltac PM_sub29 t := let t := lazymatch (eval pattern (T4m1 1%nat UStopLeOrPc 3 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__28) end in PM_sub28 t.
Ltac PM_all29 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__28_eq; PM_all28.
Definition pm__29 : axst := ltac2:(tb__ "0|0|
S31S66U0A2").
Lemma pm__29_eq : ltac2:(tb__ "0|0|
S0S3S3cU1S8Z3SeSfZ2A6S69A3"). Proof. cbv delta [T4m1 pm__29]; cbv beta zeta. PM_all29. reflexivity. Qed.
Ltac PM_sub30 t := let t := lazymatch (eval pattern (T4m1 1%nat UStopLeOrPc 3 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__29) end in PM_sub29 t.
Ltac PM_all30 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__29_eq; PM_all29.
Definition pm__30 : axst := ltac2:(tb__ "0|0|
S31S67U0A2").
Lemma pm__30_eq : ltac2:(tb__ "0|1|
S0S3S3cU1S8Z3M0SeSfG0A6S6aA3"). Proof. cbv delta [T4m1 pm__30]; cbv beta zeta. PM_all30. reflexivity. Qed.
Ltac PM_sub31 t := let t := lazymatch (eval pattern (T4m1 1%nat UStopLeOrPc 3 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__30) end in PM_sub30 t.
Ltac PM_all31 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__30_eq; PM_all30.
Definition pm__31 : axst := ltac2:(tb__ "0|0|
S31S68U0A2").
Lemma pm__31_eq : ltac2:(tb__ "0|0|
S0S3S3dU1S8Z3SeSfZ1A6S6bA3"). Proof. cbv delta [T4m2 pm__31]; cbv beta zeta. PM_all31. reflexivity. Qed.
Ltac PM_sub32 t := let t := lazymatch (eval pattern (T4m2 1%nat UStopLeOrPc 3 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__31) end in PM_sub31 t.
Ltac PM_all32 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__31_eq; PM_all31.
Definition pm__32 : axst := ltac2:(tb__ "0|0|
S31S69U0A2").
Lemma pm__32_eq : ltac2:(tb__ "0|0|
S0S3S3dU1S8Z3SeSfZ2A6S6cA3"). Proof. cbv delta [T4m2 pm__32]; cbv beta zeta. PM_all32. reflexivity. Qed.
Ltac PM_sub33 t := let t := lazymatch (eval pattern (T4m2 1%nat UStopLeOrPc 3 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__32) end in PM_sub32 t.
Ltac PM_all33 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__32_eq; PM_all32.
Definition pm__33 : axst := ltac2:(tb__ "0|0|
S31S6aU0A2").
Lemma pm__33_eq : ltac2:(tb__ "0|1|
S0S3S3dU1S8Z3M0SeSfG0A6S6dA3"). Proof. cbv delta [T4m2 pm__33]; cbv beta zeta. PM_all33. reflexivity. Qed.
Ltac PM_sub34 t := let t := lazymatch (eval pattern (T4m2 1%nat UStopLeOrPc 3 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__33) end in PM_sub33 t.
Ltac PM_all34 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__33_eq; PM_all33.
Definition pm__34 : axst := ltac2:(tb__ "0|0|
S31S6bU0A2").
Lemma pm__34_eq : ltac2:(tb__ "0|0|
S0S3S3eU1S8Z3SeSfZ1A6S6eA3"). Proof. cbv delta [T4m3 pm__34]; cbv beta zeta. PM_all34. reflexivity. Qed.
Ltac PM_sub35 t := let t := lazymatch (eval pattern (T4m3 1%nat UStopLeOrPc 3 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__34) end in PM_sub34 t.
Ltac PM_all35 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__34_eq; PM_all34.
Definition pm__35 : axst := ltac2:(tb__ "0|0|
S31S6cU0A2").
Lemma pm__35_eq : ltac2:(tb__ "0|0|
S0S3S3eU1S8Z3SeSfZ2A6S6fA3"). Proof. cbv delta [T4m3 pm__35]; cbv beta zeta. PM_all35. reflexivity. Qed.
Ltac PM_sub36 t := let t := lazymatch (eval pattern (T4m3 1%nat UStopLeOrPc 3 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__35) end in PM_sub35 t.
Ltac PM_all36 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__35_eq; PM_all35.
Definition pm__36 : axst := ltac2:(tb__ "0|0|
S31S6dU0A2").
Lemma pm__36_eq : ltac2:(tb__ "0|1|
S0S3S3eU1S8Z3M0SeSfG0A6S70A3"). Proof. cbv delta [T4m3 pm__36]; cbv beta zeta. PM_all36. reflexivity. Qed.
Ltac PM_sub37 t := let t := lazymatch (eval pattern (T4m3 1%nat UStopLeOrPc 3 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__36) end in PM_sub36 t.
Ltac PM_all37 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__36_eq; PM_all36.
Definition pm__37 : axst := ltac2:(tb__ "0|0|
S31S6eU0A2").
Lemma pm__37_eq : ltac2:(tb__ "0|0|
S0S3S37U1S8Z3SeSfZ1A6S78A3"). Proof. cbv delta [T4d pm__37]; cbv beta zeta. PM_all37. reflexivity. Qed.
Ltac PM_sub38 t := let t := lazymatch (eval pattern (T4d 1%nat UStopLeOrPc 3 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__37) end in PM_sub37 t.
Ltac PM_all38 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__37_eq; PM_all37.
Definition pm__38 : axst := ltac2:(tb__ "0|0|
S31S6fU0A2").
Lemma pm__38_eq : ltac2:(tb__ "0|0|
S0S3S37U1S8Z3SeSfZ2A6S79A3"). Proof. cbv delta [T4d pm__38]; cbv beta zeta. PM_all38. reflexivity. Qed.
Ltac PM_sub39 t := let t := lazymatch (eval pattern (T4d 1%nat UStopLeOrPc 3 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__38) end in PM_sub38 t.
Ltac PM_all39 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__38_eq; PM_all38.
Definition pm__39 : axst := ltac2:(tb__ "0|0|
S31S70U0A2").
Lemma pm__39_eq : ltac2:(tb__ "0|1|
S0S3S37U1S8Z3M0SeSfG0A6S7aA3"). Proof. cbv delta [T4d pm__39]; cbv beta zeta. PM_all39. reflexivity. Qed.
Ltac PM_sub40 t := let t := lazymatch (eval pattern (T4d 1%nat UStopLeOrPc 3 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__39) end in PM_sub39 t.
Ltac PM_all40 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__39_eq; PM_all39.
Lemma WX4r_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S30S4S34U1Vst;Vtmax;R2A4A1A1S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX4r_i : ltac2:(tb__ "0|5|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S1dS1aS18S1aS21S21A2M0A1M1S18S22A1M2A2M3A1S84S4S42U1M4Vst;Vtmax;A3A1S4S34G4Vst;Vtmax;R2A4A1A2S1cG3S1eG1G2S1bG0S1eS21S21S2fS1fQ20S27Pc0A1A3S23R2A1A4S17G0A1A3S17S22A1A4A2A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4eS4S34U1Vst;Vtmax;R2A4A1U0S23Nf10A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4eS4S3fU1M0Vst;Vtmax;R2A4A1G0S23N910A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4eS4S40U1Vst;Vtmax;R2A4A1U2S23N848A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4eS4S41U1Vst;Vtmax;R2A4A1U3S23N50A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HER_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S1dS18S28A1M0A1S87S32U1Vst;Vtmax;R2A4S51R2A1S10R2A1A3S1cG0S11R2A1A2A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S3S88S10R2A1S51R2A1S50R2A1S32U1Vst;Vtmax;R2A4S11R2A1A5SeR2A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S1aS21S21A2M0A1S5S32U1Vst;Vtmax;R2A4A1S17G0A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S22S2bS26S4S32U1Vst;Vtmax;R2A4A1M0A1A1S24G0A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S86S32U1Vst;Vtmax;R2A4S51R2A1S10R2A1S11R2A1S1bS3S50R2A1S17S3A1A3A5S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S14S26S4S32U1M0Vst;Vtmax;R2A4A1A1S26S4S45S9G0A1Vst;Vtmax;A3A1A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S21S55S10R2A1PaM0A2S2cS82S27G0A1S23N910A1A3A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc ]. Qed.
Lemma WG15_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S21S55S10R2A1PfA2S23N600A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc ]. Qed.
Lemma WG12_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S21S55S10R2A1PcA2S2cS82S27PaA1S23N848A1A3A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc ]. Qed.
Lemma FAM4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S28S44U1A1S11R2A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc ]. Qed.
Lemma NEWO_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S28A1S85S4S51R2A1A1S4S50R2A1A1A2S17S28A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc ]. Qed.
Lemma XPost_i : ltac2:(tb__ "0|1|
S13S0S18S1aS21S21A2M0A1S5S50R1A1A1S17G0A1A3Fsz;").
Proof. intros sz. reflexivity. Qed.
Lemma FBT4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S22S2bS26S4SeR2A1A1A1A1S24S4S32U1Vst;Vtmax;R2A4A1A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S1aS21S21A2M0A1S5SeR2A1A1S17G0A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc ]. Qed.
Lemma RB1_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4fS4S38U1Vst;Vtmax;SeR2A5A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4fS4S39U1M0Vst;Vtmax;SeR2A5A1G0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nd_i : ltac2:(tb__ "0|0|
S0S15S54S36SfA1A1S16A3").
Proof.   vmc. Qed.
Lemma PERM_lt_i : ltac2:(tb__ "0|0|
S0S15S49S19S19S8bR1SfA2Li;S36SfA1A3S16A3").
Proof.   vmc. Qed.
Lemma PERM_cov_i : ltac2:(tb__ "0|0|
S0S15S49S19S19S4cS19S8aR1A1S36SfA1A3Li;S83U0SfA2A3S16A3").
Proof.   vmc. Qed.
Lemma PERM_len_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S19S20S28S29S4S3aU1Vst;Vtmax;SeR2A5A1A1A2SfA3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4dS4S3bU1Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4dS4S3cU1Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4dS4S3dU1Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S33S25S4dS4S3eU1Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S7S37U1M0Vst;Vtmax;SeSfR2A6S46S9G0A1Vst;Vtmax;A3S12R2A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S56S12R2A1S81A2S16A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc ]. Qed.
Lemma R4cov_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S89S24S4S37U1Vst;Vtmax;SeSfR2A6A1M0A1S11R2A1S29G0A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all40; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Htmax_i : ltac2:(tb__ "0|0|
S1S2Z1Vtmax;A2S2Vtmax;S52A2A2").
Proof. unfold SZMAX. subst tmax. lia. Qed.
Lemma HUS_i : stopJ_stable (Wcan 1) st.
Proof. exact (stopJ_w_stable _ _ stopJ_w_1pc). Qed.
Lemma HUSr_i : ltac2:(tb__ "0|1|
S2eS2eS14S8dR1S81A2S0S8eQ40A1S2dR3R2A2S2dR4R2A2A3F_;Fi;SdS9U1A1Vst;R3A3M0G0F_;F_;Fr';Fr;").
Proof. exact (stopJ_w_ge _ _ GW stopJ_w_1pc ltac:(unfold NF, GW; lia)). Qed.

End INST.
End CDepotCallIW1.

(* [comment removed for export] *)
Module CDepotCallHW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@Corelib.Init.Logic"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "HD_stmt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.CDepotCallMW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.CDepotCallIW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.

Theorem depot_call_HD_1 : ltac2:(tb__ "0|1|
S1S2S0S0A2A1M0G0SeR2A1S10R2A1S0SfR5R1A2S3S11R2A1A1F_;Fa;S4OF_;SdSbS6S5ScR3A1S8SaR6S7R4A1A3S12SaR7S7R5A1A3S14U1Vst;Vtmax;S9RdRcR7A3R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HD 1%nat st tmax HUS_i HUSr_i CST XGL HCST HXGL HCSTD Htmax_i NXE_i FBE_i XE4_i F192_i FDEP_i FUNW_i FGEN4_i YP4_i WX4r_i DX4r_i SPL1_i SPL2_i SPL3_i SPL4_i
           s4_i R4_i T4_i HER_i HT4_i XX4_i FBX4_i Hchk4_i NX4_i WG10_i WG15_i WG12_i FAM4_i NEWO_i XPost_i FBT4_i XT4_i RB1_i RB2_i
           nobj_i PERM_nd_i PERM_lt_i PERM_cov_i PERM_len_i MRG1_i MRG2_i MRG3_i MRG4_i sd_i ENT5_i SID5_i R4cov_i).
Qed.

Theorem depot_call_HDE_1 : ltac2:(tb__ "0|1|
S1S2S0S0A2A1M0G0SeR2A1S10R2A1S0SfR5R1A2S3S11R2A1A1F_;Fa;SdSbS6S4OF_;ScR3A1S13U1Vst;Vtmax;S9RaR9R5A3R5R4R3R2A8F_;FQ;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HDE 1%nat st tmax HUS_i HUSr_i CST XGL HCST HXGL HCSTD Htmax_i NXE_i FBE_i XE4_i F192_i FDEP_i FUNW_i FGEN4_i YP4_i WX4r_i DX4r_i SPL1_i SPL2_i SPL3_i SPL4_i
           s4_i R4_i T4_i HER_i HT4_i XX4_i FBX4_i Hchk4_i NX4_i WG10_i WG15_i WG12_i FAM4_i NEWO_i XPost_i FBT4_i XT4_i RB1_i RB2_i
           nobj_i PERM_nd_i PERM_lt_i PERM_cov_i PERM_len_i MRG1_i MRG2_i MRG3_i MRG4_i sd_i ENT5_i SID5_i R4cov_i).
Qed.
End INST.
End CDepotCallHW1.

(* [comment removed for export] *)
Module F0A_aLN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "bool"; "pair"; "prod"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN0"; "Erc_LN0"; "ED_LN0_1"; "ED_LN0_2"; "TD_LN0_1"; "TD_LN0_2"; "P0_LN0"; "PMID_LN0"; "exits1_LN0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "QFN"; "contN"; "econtN"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cLN0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dg.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALN0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_LN0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S40S8S3eS40R2S2dA3S1fVsegs;R11S24Vsegs;S31G1S1SeR10RfRdA6R3R2RcA5RbA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0 UStopLe true S1c_LN0_1 C2_LN0_1 EfD_LN0_1 ED_LN0_1 run2_LN0_1 D2_LN0_1 W2_LN0_1 NX2_LN0_1 EQ2_LN0_1 RUN2_LN0_1 L2_LN0_1 AXD_LN0_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 0 UStopLe TD_LN0_1 TDr_LN0_1 CD_LN0 Eps_LN0 Ebg_LN0 Erc_LN0 run3_LN0 AXDr_LN0_1 ENTD_LN0_1 RUN3_LN0 L3_LN0 NX3_LN0 SMF_LN0 CertR_LN0
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 0 UStopLe true S1c_LN0_2 C2_LN0_2 EfD_LN0_2 ED_LN0_2 run2_LN0_2 D2_LN0_2 W2_LN0_2 NX2_LN0_2 EQ2_LN0_2 RUN2_LN0_2 L2_LN0_2 AXD_LN0_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 0 UStopLe TD_LN0_2 TDr_LN0_2 CD_LN0 Eps_LN0 Ebg_LN0 Erc_LN0 run3_LN0 AXDr_LN0_2 ENTD_LN0_2 RUN3_LN0 L3_LN0 NX3_LN0 SMF_LN0 CertR_LN0
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_LN0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S40S8S3eS40R2S2dA3S1eVsegs;S24Vsegs;S31G1S1SeRfReRcA6R3R2RbA5RaA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0 UStopLe true S1c_LN0_1 C2_LN0_1 EfD_LN0_1 ED_LN0_1 run2_LN0_1 D2_LN0_1 W2_LN0_1 NX2_LN0_1 EQ2_LN0_1 RUN2_LN0_1 L2_LN0_1 AXD_LN0_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 0 UStopLe TD_LN0_1 TDr_LN0_1 CD_LN0 Eps_LN0 Ebg_LN0 Erc_LN0 run3_LN0 AXDr_LN0_1 ENTD_LN0_1 RUN3_LN0 L3_LN0 NX3_LN0 SMF_LN0 NXB_LN0 ECertR_LN0
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 0 UStopLe true S1c_LN0_2 C2_LN0_2 EfD_LN0_2 ED_LN0_2 run2_LN0_2 D2_LN0_2 W2_LN0_2 NX2_LN0_2 EQ2_LN0_2 RUN2_LN0_2 L2_LN0_2 AXD_LN0_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 0 UStopLe TD_LN0_2 TDr_LN0_2 CD_LN0 Eps_LN0 Ebg_LN0 Erc_LN0 run3_LN0 AXDr_LN0_2 ENTD_LN0_2 RUN3_LN0 L3_LN0 NX3_LN0 SMF_LN0 NXB_LN0 ECertR_LN0
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_LN0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S8S1fVsegs;RfS24Vsegs;S31G1S1SeReRdRbA6S2bR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG.
  apply (f0_s1c 0 UStopLe true P0_LN0 exits1_LN0 Cert1_LN0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG).
Qed.
Theorem efree_spine_LN0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S8S1eVsegs;S24Vsegs;S31G1S1SeRdRcRaA6S2bR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG.
  apply (ef0_s1c 0 UStopLe true P0_LN0 exits1_LN0 NX0_LN0 ECert1_LN0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG).
Qed.

Theorem free_spine_m_LN0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S8S1fVsegs;RfS24Vsegs;S31G1S1SeReRdRbA6S2cR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG.
  apply (f0_s1c 0 UStopLe true PMID_LN0 exits1_LN0 Cert1m_LN0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG).
Qed.
Theorem efree_spine_m_LN0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S8S1eVsegs;S24Vsegs;S31G1S1SeRdRcRaA6S2cR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG.
  apply (ef0_s1c 0 UStopLe true PMID_LN0 exits1_LN0 NX0m_LN0 ECert1m_LN0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S44VCST;R1A2S1bS45R2A1A1F_;Fa;").

Theorem hdf_LN0_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S1dS25SaR2S23R10A1A3S41SaR3S23R11A1A3S2fU0S1S35VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S27S29R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG NVN 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN0_1 TD_LN0_1 (sD_of ED_LN0_1 1) RD_LN0_1 HeD_LN0_1 HchkD_LN0_1 HTD_LN0_1 DCHK_LN0_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN0_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S30U0S1S35VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S27S29R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 0 (rd_okG NVN 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN0_1 TD_LN0_1 (sD_of ED_LN0_1 1) RD_LN0_1 HeD_LN0_1 HchkD_LN0_1 HTD_LN0_1 DCHK_LN0_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.
Theorem hdf_LN0_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S1dS25SaR2S23R10A1A3S41SaR3S23R11A1A3S2fU0S1S35VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S28S2aR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG NVN 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN0_2 TD_LN0_2 (sD_of ED_LN0_2 2) RD_LN0_2 HeD_LN0_2 HchkD_LN0_2 HTD_LN0_2 DCHK_LN0_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN0_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S30U0S1S35VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S28S2aR1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 0 (rd_okG NVN 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN0_2 TD_LN0_2 (sD_of ED_LN0_2 2) RD_LN0_2 HeD_LN0_2 HchkD_LN0_2 HTD_LN0_2 DCHK_LN0_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.

Theorem free_lo_N_0 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S25SaR9S23R7A1A3S41SaRaS23R8A1A3S21S22R6R5A2S33A2S19SfS17RbA1SeA3S20S32R7A2S0S14S36RfRdRbRaR2R1A6S19S0S15R2A1S34A3S2eRfS13R11RfRdRcR4R3A6A2S3cG1S35VCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S26RcA8F_;F_;F_;Fjv;Ft;S1fSaRfS24SaS5S37SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN false (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate false 0 UStopLe NVN VFN Wa_LN0 Da_LN0 Wb_LN0 Wc_LN0 Wd_LN0 Fb_LN0 XI_LN0 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_LN0 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_LN0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_N_0 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S21S22R4R3A2S33A2S19SfS17R9A1SeA3S20S32R5A2S0S14S36RdRbR9R8R2R1A6S19S0S15R2A1S34A3S2eRdS13RfRdRbRaR4R3A6A2S3dG1S35VCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S26RaA7F_;F_;F_;Fjv;Ft;S1eSaS24SaS5S37SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN false (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate false 0 UStopLe NVN VFN Wa_LN0 Da_LN0 Wb_LN0 Wc_LN0 Wd_LN0 Fb_LN0 XI_LN0 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_LN0 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_LN0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S44VCST;R1A2S1aS1bS1aS21S39R2A2S20R2S3aA2A2A1S1bS1aS21Z180e88R2A2S20R2Z180e8cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_N_0 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S25SaR9S23R7A1A3S41SaRaS23R8A1A3S21S22R6R5A2S33A2S19SfS17RbA1S12A3S20S32R7A2S8S0S14S43R10S13R10ReRcRbR2R1A6R3A3S36S38R11A1R4RdRcR3R2A6S19S0S15R3A1S34A3S2eR6S13S38R13A1R6RfReR5R4A6A2S3cG1S35VCST;VXGL;S38R14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S26S3bVCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS24SaS5S37SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Certi_0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 0 UStopLe NVN VFN Wbm_LN0 Wcm_LN0 Wdm_LN0 Fb_LN0 XIm_LN0 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_LN0 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_LN0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_N_0 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S21S22R4R3A2S33A2S19SfS17R9A1S12A3S20S32R5A2S8S0S14S43ReS13ReRcRaR9R2R1A6R3A3S36S38RfA1R4RbRaR3R2A6S19S0S15R3A1S34A3S2eR6S13S38R11A1R6RdRcR5R4A6A2S3dG1S35VCST;VXGL;S38R12A1M2A3G2R11S13G2R7ReRdR6R5A6S26S3bVCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS24SaS5S37SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.ECerti_0A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid false 0 UStopLe NVN VFN Wbm_LN0 Wcm_LN0 Wdm_LN0 Fb_LN0 XIm_LN0 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_LN0 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_LN0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALN0.
End F0A_aLN0.

(* [comment removed for export] *)
Module F0A_aLN1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "pair"; "prod"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "aa_internal_inited"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN1"; "Erc_LN1"; "ED_LN1_1"; "ED_LN1_2"; "ED_LN1_3"; "TD_LN1_1"; "TD_LN1_2"; "TD_LN1_3"; "P0_LN1"; "PMID_LN1"; "exits1_LN1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "QFN"; "contN"; "econtN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cLN1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dk.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALN1.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_LN1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S44S8S3dS44R2S34A3S1fVsegs;R12S21Vsegs;S26G1S1SeR11R10ReA6R3R2RdA5RcA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1 UStopLe true S1c_LN1_1 C2_LN1_1 EfD_LN1_1 ED_LN1_1 run2_LN1_1 D2_LN1_1 W2_LN1_1 NX2_LN1_1 EQ2_LN1_1 RUN2_LN1_1 L2_LN1_1 AXD_LN1_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_LN1_1 TDr_LN1_1 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_1 ENTD_LN1_1 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 CertR_LN1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 1 UStopLe true S1c_LN1_2 C2_LN1_2 EfD_LN1_2 ED_LN1_2 run2_LN1_2 D2_LN1_2 W2_LN1_2 NX2_LN1_2 EQ2_LN1_2 RUN2_LN1_2 L2_LN1_2 AXD_LN1_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_LN1_2 TDr_LN1_2 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_2 ENTD_LN1_2 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 CertR_LN1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 1 UStopLe true S1c_LN1_3 C2_LN1_3 EfD_LN1_3 ED_LN1_3 run2_LN1_3 D2_LN1_3 W2_LN1_3 NX2_LN1_3 EQ2_LN1_3 RUN2_LN1_3 L2_LN1_3 AXD_LN1_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_LN1_3 TDr_LN1_3 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_3 ENTD_LN1_3 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 CertR_LN1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_LN1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S44S8S3dS44R2S34A3S1eVsegs;S21Vsegs;S26G1S1SeR10RfRdA6R3R2RcA5RbA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1 UStopLe true S1c_LN1_1 C2_LN1_1 EfD_LN1_1 ED_LN1_1 run2_LN1_1 D2_LN1_1 W2_LN1_1 NX2_LN1_1 EQ2_LN1_1 RUN2_LN1_1 L2_LN1_1 AXD_LN1_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_LN1_1 TDr_LN1_1 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_1 ENTD_LN1_1 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 NXB_LN1 ECertR_LN1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_LN1_2 C2_LN1_2 EfD_LN1_2 ED_LN1_2 run2_LN1_2 D2_LN1_2 W2_LN1_2 NX2_LN1_2 EQ2_LN1_2 RUN2_LN1_2 L2_LN1_2 AXD_LN1_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_LN1_2 TDr_LN1_2 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_2 ENTD_LN1_2 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 NXB_LN1 ECertR_LN1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_LN1_3 C2_LN1_3 EfD_LN1_3 ED_LN1_3 run2_LN1_3 D2_LN1_3 W2_LN1_3 NX2_LN1_3 EQ2_LN1_3 RUN2_LN1_3 L2_LN1_3 AXD_LN1_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_LN1_3 TDr_LN1_3 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_3 ENTD_LN1_3 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 NXB_LN1 ECertR_LN1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_LN1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S8S1fVsegs;R10S21Vsegs;S26G1S1SeRfReRcA6S32R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG.
  apply (f0_s1c 1 UStopLe true P0_LN1 exits1_LN1 Cert1_LN1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG).
Qed.
Theorem efree_spine_LN1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S8S1eVsegs;S21Vsegs;S26G1S1SeReRdRbA6S32R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG.
  apply (ef0_s1c 1 UStopLe true P0_LN1 exits1_LN1 NX0_LN1 ECert1_LN1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG).
Qed.

Theorem free_spine_m_LN1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S8S1fVsegs;R10S21Vsegs;S26G1S1SeRfReRcA6S33R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG.
  apply (f0_s1c 1 UStopLe true PMID_LN1 exits1_LN1 Cert1m_LN1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG).
Qed.
Theorem efree_spine_m_LN1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S8S1eVsegs;S21Vsegs;S26G1S1SeReRdRbA6S33R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG.
  apply (ef0_s1c 1 UStopLe true PMID_LN1 exits1_LN1 NX0m_LN1 ECert1m_LN1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S46VCST;R1A2S1bS47R2A1A1F_;Fa;").

Theorem hdf_LN1_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2cS2fR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_1 TD_LN1_1 (sD_of ED_LN1_1 1) RD_LN1_1 HeD_LN1_1 HchkD_LN1_1 HTD_LN1_1 DCHK_LN1_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN1_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2cS2fR1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_1 TD_LN1_1 (sD_of ED_LN1_1 1) RD_LN1_1 HeD_LN1_1 HchkD_LN1_1 HTD_LN1_1 DCHK_LN1_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.
Theorem hdf_LN1_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2dS30R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_2 TD_LN1_2 (sD_of ED_LN1_2 2) RD_LN1_2 HeD_LN1_2 HchkD_LN1_2 HTD_LN1_2 DCHK_LN1_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN1_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2dS30R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_2 TD_LN1_2 (sD_of ED_LN1_2 2) RD_LN1_2 HeD_LN1_2 HchkD_LN1_2 HTD_LN1_2 DCHK_LN1_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.
Theorem hdf_LN1_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2eS31R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_3 TD_LN1_3 (sD_of ED_LN1_3 3) RD_LN1_3 HeD_LN1_3 HchkD_LN1_3 HTD_LN1_3 DCHK_LN1_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN1_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2eS31R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_3 TD_LN1_3 (sD_of ED_LN1_3 3) RD_LN1_3 HeD_LN1_3 HchkD_LN1_3 HTD_LN1_3 DCHK_LN1_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.

Theorem free_lo_N_1 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S22SaR9S20R7A1A3S43SaRaS20R8A1A3S28S29R6R5A2S37A2S19S11S18RbA1SeA3S27S36R7A2S0S14S35RfRdRbRaR2R1A6S19S0S15R2A1S38A3S25RfS13R11RfRdRcR4R3A6A2S41G1S2aVCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S2bRcA8F_;F_;F_;Fjv;Ft;S1fSaRfS21SaS5S39SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN false (Wcan 1) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate false 1 UStopLe NVN VFN Wa_LN1 Da_LN1 Wb_LN1 Wc_LN1 Wd_LN1 Fb_LN1 XI_LN1 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_LN1 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_LN1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_N_1 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S28S29R4R3A2S37A2S19S11S18R9A1SeA3S27S36R5A2S0S14S35RdRbR9R8R2R1A6S19S0S15R2A1S38A3S25RdS13RfRdRbRaR4R3A6A2S42G1S2aVCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S2bRaA7F_;F_;F_;Fjv;Ft;S1eSaS21SaS5S39SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN false (Wcan 1) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate false 1 UStopLe NVN VFN Wa_LN1 Da_LN1 Wb_LN1 Wc_LN1 Wd_LN1 Fb_LN1 XI_LN1 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_LN1 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_LN1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S46VCST;R1A2S1aS1bS1aS28S3bR2A2S27R2S3cA2A2A1S1bS1aS28Z180e88R2A2S27R2Z180e8cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_N_1 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S22SaR9S20R7A1A3S43SaRaS20R8A1A3S28S29R6R5A2S37A2S19S11S18RbA1S12A3S27S36R7A2S8S0S14S45R10S13R10ReRcRbR2R1A6R3A3S35S3aR11A1R4RdRcR3R2A6S19S0S15R3A1S38A3S25R6S13S3aR13A1R6RfReR5R4A6A2S41G1S2aVCST;VXGL;S3aR14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S2bS40VCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS21SaS5S39SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Certi_1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 1) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 1 UStopLe NVN VFN Wbm_LN1 Wcm_LN1 Wdm_LN1 Fb_LN1 XIm_LN1 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_LN1 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_LN1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_N_1 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S28S29R4R3A2S37A2S19S11S18R9A1S12A3S27S36R5A2S8S0S14S45ReS13ReRcRaR9R2R1A6R3A3S35S3aRfA1R4RbRaR3R2A6S19S0S15R3A1S38A3S25R6S13S3aR11A1R6RdRcR5R4A6A2S42G1S2aVCST;VXGL;S3aR12A1M2A3G2R11S13G2R7ReRdR6R5A6S2bS40VCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS21SaS5S39SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.ECerti_1A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 1) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid false 1 UStopLe NVN VFN Wbm_LN1 Wcm_LN1 Wdm_LN1 Fb_LN1 XIm_LN1 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_LN1 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_LN1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALN1.
End F0A_aLN1.

(* [comment removed for export] *)
Module F0A_aN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "bool"; "pair"; "prod"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN0"; "Erc_N0"; "ED_N0_1"; "ED_N0_2"; "TD_N0_1"; "TD_N0_2"; "P0_N0"; "PMID_N0"; "exits1_N0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "QFN"; "contN"; "econtN"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cN0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dg.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AN0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_N0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S40S8S3eS40R2S2dA3S1fVsegs;R11S24Vsegs;S31G1S1SeR10RfRdA6R3R2RcA5RbA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0 UStopLe true S1c_N0_1 C2_N0_1 EfD_N0_1 ED_N0_1 run2_N0_1 D2_N0_1 W2_N0_1 NX2_N0_1 EQ2_N0_1 RUN2_N0_1 L2_N0_1 AXD_N0_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 0 UStopLe TD_N0_1 TDr_N0_1 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_1 ENTD_N0_1 RUN3_N0 L3_N0 NX3_N0 SMF_N0 CertR_N0
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 0 UStopLe true S1c_N0_2 C2_N0_2 EfD_N0_2 ED_N0_2 run2_N0_2 D2_N0_2 W2_N0_2 NX2_N0_2 EQ2_N0_2 RUN2_N0_2 L2_N0_2 AXD_N0_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 0 UStopLe TD_N0_2 TDr_N0_2 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_2 ENTD_N0_2 RUN3_N0 L3_N0 NX3_N0 SMF_N0 CertR_N0
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_N0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S40S8S3eS40R2S2dA3S1eVsegs;S24Vsegs;S31G1S1SeRfReRcA6R3R2RbA5RaA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0 UStopLe true S1c_N0_1 C2_N0_1 EfD_N0_1 ED_N0_1 run2_N0_1 D2_N0_1 W2_N0_1 NX2_N0_1 EQ2_N0_1 RUN2_N0_1 L2_N0_1 AXD_N0_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 0 UStopLe TD_N0_1 TDr_N0_1 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_1 ENTD_N0_1 RUN3_N0 L3_N0 NX3_N0 SMF_N0 NXB_N0 ECertR_N0
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 0 UStopLe true S1c_N0_2 C2_N0_2 EfD_N0_2 ED_N0_2 run2_N0_2 D2_N0_2 W2_N0_2 NX2_N0_2 EQ2_N0_2 RUN2_N0_2 L2_N0_2 AXD_N0_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 0 UStopLe TD_N0_2 TDr_N0_2 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_2 ENTD_N0_2 RUN3_N0 L3_N0 NX3_N0 SMF_N0 NXB_N0 ECertR_N0
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_N0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S8S1fVsegs;RfS24Vsegs;S31G1S1SeReRdRbA6S2bR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG.
  apply (f0_s1c 0 UStopLe true P0_N0 exits1_N0 Cert1_N0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG).
Qed.
Theorem efree_spine_N0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S8S1eVsegs;S24Vsegs;S31G1S1SeRdRcRaA6S2bR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG.
  apply (ef0_s1c 0 UStopLe true P0_N0 exits1_N0 NX0_N0 ECert1_N0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG).
Qed.

Theorem free_spine_m_N0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S8S1fVsegs;RfS24Vsegs;S31G1S1SeReRdRbA6S2cR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG.
  apply (f0_s1c 0 UStopLe true PMID_N0 exits1_N0 Cert1m_N0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG).
Qed.
Theorem efree_spine_m_N0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S8S1eVsegs;S24Vsegs;S31G1S1SeRdRcRaA6S2cR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG.
  apply (ef0_s1c 0 UStopLe true PMID_N0 exits1_N0 NX0m_N0 ECert1m_N0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S44VCST;R1A2S1bS45R2A1A1F_;Fa;").

Theorem hdf_N0_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S1dS25SaR2S23R10A1A3S41SaR3S23R11A1A3S2fU0S1S35VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S27S29R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG NVN 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_1 TD_N0_1 (sD_of ED_N0_1 1) RD_N0_1 HeD_N0_1 HchkD_N0_1 HTD_N0_1 DCHK_N0_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_N0_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S30U0S1S35VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S27S29R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 0 (rd_okG NVN 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_1 TD_N0_1 (sD_of ED_N0_1 1) RD_N0_1 HeD_N0_1 HchkD_N0_1 HTD_N0_1 DCHK_N0_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.
Theorem hdf_N0_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S1dS25SaR2S23R10A1A3S41SaR3S23R11A1A3S2fU0S1S35VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S28S2aR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG NVN 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_2 TD_N0_2 (sD_of ED_N0_2 2) RD_N0_2 HeD_N0_2 HchkD_N0_2 HTD_N0_2 DCHK_N0_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_N0_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S30U0S1S35VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S28S2aR1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 0 (rd_okG NVN 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_2 TD_N0_2 (sD_of ED_N0_2 2) RD_N0_2 HeD_N0_2 HchkD_N0_2 HTD_N0_2 DCHK_N0_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.

Theorem free_hi_N_0 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S25SaR9S23R7A1A3S41SaRaS23R8A1A3S21S33S22R6Z10A2A2S19SfS17RbA1SeA3S20S32R7A2S0S14S36RfRdRbRaR2R1A6S19S0S15R2A1S34A3S2eRfS13R11RfRdRcR4R3A6A2S3cG1S35VCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S26RcA8F_;F_;F_;Fjv;Ft;S1fSaRfS24SaS5S37SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN true (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate true 0 UStopLe NVN VFN Wa_N0 Da_N0 Wb_N0 Wc_N0 Wd_N0 Fb_N0 XI_N0 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_N0 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_N0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_N0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_N_0 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S21S33S22R4Z10A2A2S19SfS17R9A1SeA3S20S32R5A2S0S14S36RdRbR9R8R2R1A6S19S0S15R2A1S34A3S2eRdS13RfRdRbRaR4R3A6A2S3dG1S35VCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S26RaA7F_;F_;F_;Fjv;Ft;S1eSaS24SaS5S37SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN true (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate true 0 UStopLe NVN VFN Wa_N0 Da_N0 Wb_N0 Wc_N0 Wd_N0 Fb_N0 XI_N0 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_N0 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_N0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_N0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S44VCST;R1A2S1aS1bS1aS21S39R2A2S20R2S3aA2A2A1S1bS1aS21Z180e88R2A2S20R2Z180e8cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_N_0 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S25SaR9S23R7A1A3S41SaRaS23R8A1A3S21S33S22R6Z10A2A2S19SfS17RbA1S12A3S20S32R7A2S8S0S14S43R10S13R10ReRcRbR2R1A6R3A3S36S38R11A1R4RdRcR3R2A6S19S0S15R3A1S34A3S2eR6S13S38R13A1R6RfReR5R4A6A2S3cG1S35VCST;VXGL;S38R14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S26S3bVCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS24SaS5S37SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Certi_0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 0 UStopLe NVN VFN Wbm_N0 Wcm_N0 Wdm_N0 Fb_N0 XIm_N0 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_N0 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_N0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_N0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_N_0 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S21S33S22R4Z10A2A2S19SfS17R9A1S12A3S20S32R5A2S8S0S14S43ReS13ReRcRaR9R2R1A6R3A3S36S38RfA1R4RbRaR3R2A6S19S0S15R3A1S34A3S2eR6S13S38R11A1R6RdRcR5R4A6A2S3dG1S35VCST;VXGL;S38R12A1M2A3G2R11S13G2R7ReRdR6R5A6S26S3bVCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS24SaS5S37SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A.ECerti_0A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid true 0 UStopLe NVN VFN Wbm_N0 Wcm_N0 Wdm_N0 Fb_N0 XIm_N0 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_N0 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_N0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_N0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End AN0.
End F0A_aN0.

(* [comment removed for export] *)
Module F0A_aN1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "pair"; "prod"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "aa_internal_inited"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN1"; "Erc_N1"; "ED_N1_1"; "ED_N1_2"; "ED_N1_3"; "TD_N1_1"; "TD_N1_2"; "TD_N1_3"; "P0_N1"; "PMID_N1"; "exits1_N1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "QFN"; "contN"; "econtN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cN1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dk.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AN1.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_N1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S44S8S3dS44R2S34A3S1fVsegs;R12S21Vsegs;S26G1S1SeR11R10ReA6R3R2RdA5RcA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1 UStopLe true S1c_N1_1 C2_N1_1 EfD_N1_1 ED_N1_1 run2_N1_1 D2_N1_1 W2_N1_1 NX2_N1_1 EQ2_N1_1 RUN2_N1_1 L2_N1_1 AXD_N1_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_N1_1 TDr_N1_1 CD_N1 Eps_N1 Ebg_N1 Erc_N1 run3_N1 AXDr_N1_1 ENTD_N1_1 RUN3_N1 L3_N1 NX3_N1 SMF_N1 CertR_N1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 1 UStopLe true S1c_N1_2 C2_N1_2 EfD_N1_2 ED_N1_2 run2_N1_2 D2_N1_2 W2_N1_2 NX2_N1_2 EQ2_N1_2 RUN2_N1_2 L2_N1_2 AXD_N1_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_N1_2 TDr_N1_2 CD_N1 Eps_N1 Ebg_N1 Erc_N1 run3_N1 AXDr_N1_2 ENTD_N1_2 RUN3_N1 L3_N1 NX3_N1 SMF_N1 CertR_N1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 1 UStopLe true S1c_N1_3 C2_N1_3 EfD_N1_3 ED_N1_3 run2_N1_3 D2_N1_3 W2_N1_3 NX2_N1_3 EQ2_N1_3 RUN2_N1_3 L2_N1_3 AXD_N1_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_N1_3 TDr_N1_3 CD_N1 Eps_N1 Ebg_N1 Erc_N1 run3_N1 AXDr_N1_3 ENTD_N1_3 RUN3_N1 L3_N1 NX3_N1 SMF_N1 CertR_N1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_N1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S44S8S3dS44R2S34A3S1eVsegs;S21Vsegs;S26G1S1SeR10RfRdA6R3R2RcA5RbA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1 UStopLe true S1c_N1_1 C2_N1_1 EfD_N1_1 ED_N1_1 run2_N1_1 D2_N1_1 W2_N1_1 NX2_N1_1 EQ2_N1_1 RUN2_N1_1 L2_N1_1 AXD_N1_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_N1_1 TDr_N1_1 CD_N1 Eps_N1 Ebg_N1 Erc_N1 run3_N1 AXDr_N1_1 ENTD_N1_1 RUN3_N1 L3_N1 NX3_N1 SMF_N1 NXB_N1 ECertR_N1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_N1_2 C2_N1_2 EfD_N1_2 ED_N1_2 run2_N1_2 D2_N1_2 W2_N1_2 NX2_N1_2 EQ2_N1_2 RUN2_N1_2 L2_N1_2 AXD_N1_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_N1_2 TDr_N1_2 CD_N1 Eps_N1 Ebg_N1 Erc_N1 run3_N1 AXDr_N1_2 ENTD_N1_2 RUN3_N1 L3_N1 NX3_N1 SMF_N1 NXB_N1 ECertR_N1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_N1_3 C2_N1_3 EfD_N1_3 ED_N1_3 run2_N1_3 D2_N1_3 W2_N1_3 NX2_N1_3 EQ2_N1_3 RUN2_N1_3 L2_N1_3 AXD_N1_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_N1_3 TDr_N1_3 CD_N1 Eps_N1 Ebg_N1 Erc_N1 run3_N1 AXDr_N1_3 ENTD_N1_3 RUN3_N1 L3_N1 NX3_N1 SMF_N1 NXB_N1 ECertR_N1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_N1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S8S1fVsegs;R10S21Vsegs;S26G1S1SeRfReRcA6S32R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG.
  apply (f0_s1c 1 UStopLe true P0_N1 exits1_N1 Cert1_N1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG).
Qed.
Theorem efree_spine_N1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S8S1eVsegs;S21Vsegs;S26G1S1SeReRdRbA6S32R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG.
  apply (ef0_s1c 1 UStopLe true P0_N1 exits1_N1 NX0_N1 ECert1_N1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG).
Qed.

Theorem free_spine_m_N1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S8S1fVsegs;R10S21Vsegs;S26G1S1SeRfReRcA6S33R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG.
  apply (f0_s1c 1 UStopLe true PMID_N1 exits1_N1 Cert1m_N1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG).
Qed.
Theorem efree_spine_m_N1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S8S1eVsegs;S21Vsegs;S26G1S1SeReRdRbA6S33R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG.
  apply (ef0_s1c 1 UStopLe true PMID_N1 exits1_N1 NX0m_N1 ECert1m_N1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S46VCST;R1A2S1bS47R2A1A1F_;Fa;").

Theorem hdf_N1_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2cS2fR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N1_1 TD_N1_1 (sD_of ED_N1_1 1) RD_N1_1 HeD_N1_1 HchkD_N1_1 HTD_N1_1 DCHK_N1_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_N1_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2cS2fR1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N1_1 TD_N1_1 (sD_of ED_N1_1 1) RD_N1_1 HeD_N1_1 HchkD_N1_1 HTD_N1_1 DCHK_N1_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.
Theorem hdf_N1_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2dS30R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N1_2 TD_N1_2 (sD_of ED_N1_2 2) RD_N1_2 HeD_N1_2 HchkD_N1_2 HTD_N1_2 DCHK_N1_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_N1_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2dS30R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N1_2 TD_N1_2 (sD_of ED_N1_2 2) RD_N1_2 HeD_N1_2 HchkD_N1_2 HTD_N1_2 DCHK_N1_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.
Theorem hdf_N1_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2eS31R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N1_3 TD_N1_3 (sD_of ED_N1_3 3) RD_N1_3 HeD_N1_3 HchkD_N1_3 HTD_N1_3 DCHK_N1_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_N1_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2eS31R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N1_3 TD_N1_3 (sD_of ED_N1_3 3) RD_N1_3 HeD_N1_3 HchkD_N1_3 HTD_N1_3 DCHK_N1_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.

Theorem free_hi_N_1 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S22SaR9S20R7A1A3S43SaRaS20R8A1A3S28S37S29R6Z10A2A2S19S11S18RbA1SeA3S27S36R7A2S0S14S35RfRdRbRaR2R1A6S19S0S15R2A1S38A3S25RfS13R11RfRdRcR4R3A6A2S41G1S2aVCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S2bRcA8F_;F_;F_;Fjv;Ft;S1fSaRfS21SaS5S39SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN true (Wcan 1) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate true 1 UStopLe NVN VFN Wa_N1 Da_N1 Wb_N1 Wc_N1 Wd_N1 Fb_N1 XI_N1 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_N1 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_N1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_N1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_N1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_N_1 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S28S37S29R4Z10A2A2S19S11S18R9A1SeA3S27S36R5A2S0S14S35RdRbR9R8R2R1A6S19S0S15R2A1S38A3S25RdS13RfRdRbRaR4R3A6A2S42G1S2aVCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S2bRaA7F_;F_;F_;Fjv;Ft;S1eSaS21SaS5S39SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN true (Wcan 1) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate true 1 UStopLe NVN VFN Wa_N1 Da_N1 Wb_N1 Wc_N1 Wd_N1 Fb_N1 XI_N1 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_N1 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_N1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_N1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_N1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S46VCST;R1A2S1aS1bS1aS28S3bR2A2S27R2S3cA2A2A1S1bS1aS28Z180e88R2A2S27R2Z180e8cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_N_1 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S22SaR9S20R7A1A3S43SaRaS20R8A1A3S28S37S29R6Z10A2A2S19S11S18RbA1S12A3S27S36R7A2S8S0S14S45R10S13R10ReRcRbR2R1A6R3A3S35S3aR11A1R4RdRcR3R2A6S19S0S15R3A1S38A3S25R6S13S3aR13A1R6RfReR5R4A6A2S41G1S2aVCST;VXGL;S3aR14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S2bS40VCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS21SaS5S39SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Certi_1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 1) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 1 UStopLe NVN VFN Wbm_N1 Wcm_N1 Wdm_N1 Fb_N1 XIm_N1 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_N1 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_N1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_N1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_N1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_N_1 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S28S37S29R4Z10A2A2S19S11S18R9A1S12A3S27S36R5A2S8S0S14S45ReS13ReRcRaR9R2R1A6R3A3S35S3aRfA1R4RbRaR3R2A6S19S0S15R3A1S38A3S25R6S13S3aR11A1R6RdRcR5R4A6A2S42G1S2aVCST;VXGL;S3aR12A1M2A3G2R11S13G2R7ReRdR6R5A6S2bS40VCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS21SaS5S39SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.ECerti_1A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 1) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 1) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid true 1 UStopLe NVN VFN Wbm_N1 Wcm_N1 Wdm_N1 Fb_N1 XIm_N1 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_N1 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_N1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_N1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_N1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End AN1.
End F0A_aN1.

