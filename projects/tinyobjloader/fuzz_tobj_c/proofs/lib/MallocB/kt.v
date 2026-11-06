(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf F0A_cLN0 lo F0A_cLN2.

(* [comment removed for export] *)
Module CDepotCallIW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "Wcan"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.CDepotCallMW1"; "T4_i"; "nobj_i"; "s4_i"; "R4_i"; "sd_i"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "list"; "nat"; "prod"; "cons"; "Some"; "option"; "pair"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "ss_facts"; "sstate"; "ss_next"; "SVar"; "sobj"; "ss_objs"; "SPUle"; "sprop_below"; "SAlu"; "rw"; "valuation"; "SExt"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW"; "omrg"; "X4"; "isSome"; "X4r"; "oreb"; "permW"; "T4d"; "T40"; "T4a"; "T4b"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "X4a"; "X4b"; "X4c"; "X4f"; "F_call"; "in_famb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E4d"; "C5"; "F_gen"; "V_CNT"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"; "SZMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kt.CDepotCallIW1.INST"; "pm__22"; "pm__23"; "pm__24"; "pm__13"; "pm__14"; "pm__15"; "pm__16"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__29"; "pm__30"; "pm__31"; "pm__32"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__0"; "pm__1"; "pm__10"; "pm__11"; "pm__12"; "pm__2"; "pm__3"; "pm__37"; "pm__38"; "pm__39"; "pm__4"; "pm__5"; "pm__6"; "pm__7"; "pm__8"; "pm__9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "coveredb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.CDepotCallMW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
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

Ltac PM_sub0 t := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.CallocMemoSPW1_subst t.
Ltac PM_all0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.CallocMemoSPW1_all.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@Corelib.Init.Logic"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "HD_stmt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.CDepotCallMW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kt.CDepotCallIW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
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
Module F0T_aNT.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "andb"; "false"; "cons"; "nil"; "negb"; "prod"; "orb"; "pair"; "length"; "option"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_lenient"; "ss_next"; "sv"; "ss_objs"; "swf"; "SVar"; "sv_below"; "SLit"; "sobj"; "sprop"; "ss_facts"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "Wcan"; "AE_A"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "sub"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "aa_internal_inited"; "topG"; "aa_Kf"; "aa_Km"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kt.F0T_aNT"; "MT_NT"; "m1_NT"; "MX_NT"; "MH0_NT"; "m2_NT"; "m3_NT"; "m4_NT"; "okbm_NT"; "okbp_NT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cNT"; "ED_NT"; "Erc_NT"; "PMID_NT"; "TD_NT"; "S1c_NT"; "P0_NT"; "LT_NT"; "l1_NT"; "EX_NT"; "LH0_NT"; "l2_NT"; "l3_NT"; "l4_NT"; "RD_NT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "PostDv"; "PreDv"; "sDv_of"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln"; "QFNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "contN"; "econtN"; "entry_pureN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "JT"; "objs_le"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "carve_link_state";
"@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cNT.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma RUN1p_DUMMY_NT : True. Proof. exact I. Qed.
Definition RUN1p_NT := RUN1_NT. Definition RUN2p_NT := RUN2f_NT. Definition RUN3p_NT := RUN3f_NT. Definition RUN4p_NT := RUN4f_NT.
Definition okbp_NT := l1okb_NT. Definition chkp_NT := chk_NT. Definition H0eqp_NT := LH0eq_NT. Definition SIDEp_NT := SIDE_NT. Definition OBNDp_NT := OBND_NT.
Lemma splitp_NT : ltac2:(tb__ "0|9|
S1S1S2S0S7S13A1M0S59SbS13A1M1A3A1S1S2S0G0S5cG1A3A1S1S2S0G0S5dG1A3A1S2S0G0S5eG1A3A1A2A2A2S1S0S5S51S59A1S6A3S1S0S5S90S10S13S6bS69S59A2A2U1A2S6A3S1S0S5S67S13S13SeS3fS15R1A1M2S58A2S3fG2S5aA2A2LL;S5cA3S6A3S1S0S5S1dS14S8eS58S1eS6aA1M3A2A1A1S6A3S1S0S5S1fS1aS14S58A1M4A1M5G3A2S6A3S1S0S5S67S13S8dS58S5aS6aA3S5dA3S6A3S1S0S5S67S13S13S3fG2S56A2LL;S5eA3S6A3S1S1S70S29S1aS14S57A1M6A1A2S1S70S29S1aS14S5bA1M7A1A2S1S70S29G5A2S70S29S1aS14S5aA1M8A1A2A2A2A2S1S0S5S19G6A1S9A3S1S0S5S19G7A1S9A3S1S0S5S19G4A1S9A3S0S5S19G8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkp_NT as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okp_NT : ltac2:(tb__ "0|1|
S13S68S13R1S59A3S3S0S16S15R2A1M0S5bA3S0S5S3fG0S56A2S6A3A2F_;FL;").
Proof.
  destruct splitp_NT as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_NT)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqp_NT. destruct (atpc LOOPH l1_NT) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.
Lemma Wai_NT : ltac2:(tb__ "0|0|
S0S5S1dS89S2dU0A1S2aA2A1S6A3"). Proof. vmr. Qed.
Lemma Dai_NT : ltac2:(tb__ "0|4|
S0S11SdS7SdS1bS1bA2M0A1M1S7S22A1M2A2M3A1S9dS14S75S2eA1A1S89S2dU0A1S2aA2A2S12G3SfG1G2SaG0SfS1bS1bS1eP18A1S20Sa1A1A4SbG0A1A3SbS22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_NT : ltac2:(tb__ "0|0|
S0S5S1dS8bS2dU0A1S2aA2A1S6A3"). Proof. vmr. Qed.
Lemma Wci_NT : ltac2:(tb__ "0|0|
S0S5S1dS8cS2dU0A1S2aA2A1S6A3"). Proof. vmr. Qed.
Definition Certi_NT__runs : ltac2:(tb__ "0|0|
S7S11S7S13A1A1A1") := ltac2:(tb__ "0|0|
S9eS28Ubb8S86S88U0S2aA2A4").
Lemma Certi_NT : ltac2:(tb__ "0|1|
S0S5S95S28Ubb8S86S29S88U0M0S2aA2SaS16S87S2dG0A1S2aA2SbS16A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_NT__runs); [unfold Certi_NT__runs; reflexivity | vmr]. Qed.
Lemma ECerti_NT : ltac2:(tb__ "0|2|
S0S5S96S28Ubb8S86S29S8aU0M0S2aA2SaS94S97S87S2dG0A1S2aA2Z0M1S20G1A1A3SbS94A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_NT__runs); [unfold Certi_NT__runs; reflexivity | vmr]. Qed.
Definition m1_NT : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_NT.
Definition MH0_NT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_NT) DUMMY).
Definition m2_NT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_NT.
Definition MH1_NT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_NT) DUMMY).
Definition MT_NT : axst := Eval vm_compute in LT_ofg MH1_NT F0_NT.
Definition MX_NT : axst := Eval vm_compute in EX_ofg MH1_NT F0_NT.
Definition m3_NT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_NT (SVar pFR)).
Definition m4_NT : list leafA := Eval vm_compute in runA FUELF [CASX] MX_NT.
Lemma RUN1m_NT : ltac2:(tb__ "0|0|
S0S7S13A1S83S40SaS4S69SaS4S41SbS4A1A3A3S54A3S4aA3"). Proof. Time vmr. Qed.
Lemma RUN2m_NT : ltac2:(tb__ "0|0|
S0S7S13A1S83S40SaS4S69SaS4S6cSbS4A1A3A3S4cA3S4dA3"). Proof. Time vmr. Qed.
Lemma RUN3m_NT : ltac2:(tb__ "0|0|
S0S7S13A1S83S40SaS4S69SaS4S6cSbS4A1A3A3S8fS49S1eS6aA1A2A3S4eA3"). Proof. Time vmr. Qed.
Lemma RUN4m_NT : ltac2:(tb__ "0|0|
S0S7S13A1S83S40SaS4S41SbS4A1A3S4bA3S4fA3"). Proof. Time vmr. Qed.
Definition okbm_NT (l : list leafA) : bool := ltac2:(tb__ "0|1|
S67S13S13SeS33S24S14S15R1A1M0A1A1S69A2S3fG0S56A2A2LL;Vl;A3").
Lemma chkm_NT : ltac2:(tb__ "0|a|
S0S5S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8ScS7S13A1M0S5Lx;M1S4aS6S13G0S9Ll0;Ll;M2X7x2A1ScG1S4dS6G2X7x2A1A2ScG1S4eS6G2X7x2A1A2ScG1S4fS6G2X7x2A1A2S50S4aA1A2S90S10S13S6bS69S4aA2A2U1A2A2S67S13S13SeS3fS15R1A1M3S49A2S3fG3S4bA2A2LL;S4dA3A2S1dS14S8eS49S1eS6aA1M4A2A1A1A2S1fS1aS14S49A1M5A1M6G4A2A2S67S13S8dS49S4bS6aA3S4eA3A2S67S13S13S3fG3S56A2LL;S4fA3A2S71S29S1aS14S54A1M7A1A2A2S71S29S1aS14S4cA1M8A1A2A2S71S29G6A2A2S71S29S1aS14S4bA1M9A1A2A2ScS19G7A1A1A2ScS19G8A1A1A2ScS19G5A1A1A2ScS19G9A1A1A2S6A3").
Proof. Time vmr. Qed.
Lemma H0eqm_NT : ltac2:(tb__ "0|0|
S0S16S15S92S13U0S6bS69S4aA2S84A4A1S4cA3"). Proof. vmr. Qed.
Lemma SIDEm_NT : ltac2:(tb__ "0|0|
S0S5S82S54S49A2S6A3"). Proof. Time vmr. Qed.
Lemma OBNDm_NT : ltac2:(tb__ "0|1|
S0S7SdSdS1bS1bA2S1bA2M0A1S91S21G0S81S1cS14S49A1A1A4S91S21G0S81S1cS14S54A1A1A4A3"). Proof. Time vmr. Qed.
Lemma splitm_NT : ltac2:(tb__ "0|9|
S1S1S2S0S7S13A1M0S4aSbS13A1M1A3A1S1S2S0G0S4dG1A3A1S1S2S0G0S4eG1A3A1S2S0G0S4fG1A3A1A2A2A2S1S0S5S50S4aA1S6A3S1S0S5S90S10S13S6bS69S4aA2A2U1A2S6A3S1S0S5S67S13S13SeS3fS15R1A1M2S49A2S3fG2S4bA2A2LL;S4dA3S6A3S1S0S5S1dS14S8eS49S1eS6aA1M3A2A1A1S6A3S1S0S5S1fS1aS14S49A1M4A1M5G3A2S6A3S1S0S5S67S13S8dS49S4bS6aA3S4eA3S6A3S1S0S5S67S13S13S3fG2S56A2LL;S4fA3S6A3S1S1S70S29S1aS14S54A1M6A1A2S1S70S29S1aS14S4cA1M7A1A2S1S70S29G5A2S70S29S1aS14S4bA1M8A1A2A2A2A2S1S0S5S19G6A1S9A3S1S0S5S19G7A1S9A3S1S0S5S19G4A1S9A3S0S5S19G8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_NT as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okm_NT : ltac2:(tb__ "0|1|
S13S68S13R1S4aA3S3S0S16S15R2A1M0S4cA3S0S5S3fG0S56A2S6A3A2F_;FL;").
Proof.
  destruct splitm_NT as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_NT)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqm_NT. destruct (atpc LOOPH m1_NT) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ANT.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Lemma spine_tail_NT : ltac2:(tb__ "0|2|
S4OF_;S42OF_;S34S2bS18S18S7S26Q40M0A1A1S43S2cR5A1S48Vsegs;R8S47R6A1A3S63R6R5A2S30S60S25G0S17R6PdA2A2A2S64U0M1S2aRcRbRaR9R7S52S55R5AaS7bG1RdRcRbRaR8S53R6A8S18S45Vsegs;ReS46Vsegs;S66G1S2aS6RdRcRaA6S56R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HBIG.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  apply (f0_s2 0 UStopLe true S1c_NT C2_NT EfD_NT ED_NT run2_NT D2_NT W2_NT NX2_NT EQ2_NT RUN2_NT L2_NT AXD_NT
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
  exact (f0_s3n 0 UStopLe TD_NT TDr_NT CD_NT Eps_NT Ebg_NT Erc_NT run3_NT AXDr_NT ENTD_NT RUN3_NT L3_NT NX3_NT SMF_NT CertR_NT
           ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
           (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Theorem free_spine_NT : ltac2:(tb__ "0|5|
S4OF_;S42OF_;S34S2bS18S18S7S26Q40M0A1M1A1S43S2cR5A1S48Vsegs;R8S47R6A1A3S63R6R5A2S30S60S25G0S17R6PdA2A2A2S80R7S25G0S17R7PaA2A2S1cS14S57A1A1A3S0G1S17R8P99A2S27G0S36S35RbA1A1A2A3S1S2fZ1S36S35RcA1M2A1M3A2S2fG3S76S38G2A1A1A2A2S64U0M4S2aRfReRdRcRaS52S55R8AaS7bG4R10RfReRdRbS53R9A8S18S45Vsegs;R11S46Vsegs;S7fR10RfRdA3S57R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitp_NT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_NT LH0_NT LT_NT EX_NT S1c_NT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_NT l2_NT l3_NT l4_NT HNX HLEN
           (runT_some _ _ _ _ RUN1p_NT NE1) L1okp_NT (runT_some _ _ _ _ RUN2p_NT NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_NT NE3) H3 (runT_some _ _ _ _ RUN4p_NT NE4) H4
           (hside_of A Kc rho1 P0_NT LT_NT tp SIDEp_NT OBNDp_NT HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_NT keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HBIG rhoE).
Qed.
Theorem free_spine_m_NT : ltac2:(tb__ "0|5|
S4OF_;S42OF_;S34S2bS18S18S7S26Q40M0A1M1A1S43S2cR5A1S48Vsegs;R8S47R6A1A3S63R6R5A2S30S60S25G0S17R6PdA2A2A2S80R7S25G0S17R7PaA2A2S1cS14S54A1A1A3S0G1S17R8P99A2S27G0S36S35RbA1A1A2A3S1S2fZ1S36S35RcA1M2A1M3A2S2fG3S76S38G2A1A1A2A2S64U0M4S2aRfReRdRcRaS52S55R8AaS7bG4R10RfReRdRbS53R9A8S18S45Vsegs;R11S46Vsegs;S7fR10RfRdA3S54R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitm_NT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_NT MH0_NT MT_NT MX_NT S1c_NT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_NT m2_NT m3_NT m4_NT HNX HLEN
           (runT_some _ _ _ _ RUN1m_NT NE1) L1okm_NT (runT_some _ _ _ _ RUN2m_NT NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_NT NE3) H3 (runT_some _ _ _ _ RUN4m_NT NE4) H4
           (hside_of A Kc rho1 PMID_NT MT_NT tp SIDEm_NT OBNDm_NT HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_NT keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HBIG rhoE).
Qed.
Lemma espine_tail_NT : ltac2:(tb__ "0|2|
S4OF_;S34S2bS18S18S7S26Q40M0A1A1S42OF_;S2cR5A1S63R5R4A2S30S60S25G0S17R5PdA2A2A2S65U0M1S2aRaR9R8R6S52S55R4A9S7cG1RbRaR9R7S53R5A7S18S44Vsegs;S46Vsegs;S66G1S2aS6RcRbR9A6S56R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HBIG.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  apply (ef0_s2 0 UStopLe true S1c_NT C2_NT EfD_NT ED_NT run2_NT D2_NT W2_NT NX2_NT EQ2_NT RUN2_NT L2_NT AXD_NT
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
  exact (ef0_s3n 0 UStopLe TD_NT TDr_NT CD_NT Eps_NT Ebg_NT Erc_NT run3_NT AXDr_NT ENTD_NT RUN3_NT L3_NT NX3_NT SMF_NT NXB_NT ECertR_NT
           A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
           (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Theorem efree_spine_NT : ltac2:(tb__ "0|5|
S4OF_;S34S2bS18S18S7S26Q40M0A1M1A1S42OF_;S2cR5A1S63R5R4A2S30S60S25G0S17R5PdA2A2A2S80R6S25G0S17R6PaA2A2S1cS14S57A1A1A3S0G1S17R7P99A2S27G0S36S35RaA1A1A2A3S1S2fZ1S36S35RbA1M2A1M3A2S2fG3S76S38G2A1A1A2A2S65U0M4S2aRdRcRbR9S52S55R7A9S7cG4ReRdRcRaS53R8A7S18S44Vsegs;S46Vsegs;S7fRfReRcA3S57R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitp_NT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_NT LH0_NT LT_NT EX_NT S1c_NT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_NT l2_NT l3_NT l4_NT HNX HLEN
           (runT_some _ _ _ _ RUN1p_NT NE1) L1okp_NT (runT_some _ _ _ _ RUN2p_NT NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_NT NE3) H3 (runT_some _ _ _ _ RUN4p_NT NE4) H4
           (hside_of A Kc rho1 P0_NT LT_NT tp SIDEp_NT OBNDp_NT HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_NT keep A Kc rho rho1 tp Q HKc HR Hn HD1 HBIG rhoE).
Qed.
Theorem efree_spine_m_NT : ltac2:(tb__ "0|5|
S4OF_;S34S2bS18S18S7S26Q40M0A1M1A1S42OF_;S2cR5A1S63R5R4A2S30S60S25G0S17R5PdA2A2A2S80R6S25G0S17R6PaA2A2S1cS14S54A1A1A3S0G1S17R7P99A2S27G0S36S35RaA1A1A2A3S1S2fZ1S36S35RbA1M2A1M3A2S2fG3S76S38G2A1A1A2A2S65U0M4S2aRdRcRbR9S52S55R7A9S7cG4ReRdRcRaS53R8A7S18S44Vsegs;S46Vsegs;S7fRfReRcA3S54R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitm_NT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_NT MH0_NT MT_NT MX_NT S1c_NT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_NT m2_NT m3_NT m4_NT HNX HLEN
           (runT_some _ _ _ _ RUN1m_NT NE1) L1okm_NT (runT_some _ _ _ _ RUN2m_NT NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_NT NE3) H3 (runT_some _ _ _ _ RUN4m_NT NE4) H4
           (hside_of A Kc rho1 PMID_NT MT_NT tp SIDEm_NT OBNDm_NT HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_NT keep A Kc rho rho1 tp Q HKc HR Hn HD1 HBIG rhoE).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S4S9cVCST;R1A2S2Sa2R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S4S9cVCST;R1A2S1S2S1S2fS79R2A2S30R2S7aA2A2A1S2S1S2fZ17db48R2A2S30R2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.
Lemma HTD_NT : ltac2:(tb__ "0|0|
S0S16S55S9fSa0S6fS52A1S6eS6dS52S5fA5S23S14S52A1A1A2A3").
Proof. unfold TD_NT, TDv_of, RD_NT; reflexivity. Qed.
Theorem hdf_NT : ltac2:(tb__ "0|1|
S34S2bS18S7S26Q40M0A1A1S93S4S4S4S3dS2cR8A1S2fS32S3aRaA1S39RaA1A2S98A2S78S28RbR9R8R7A5S68SdS4S4A2SfS4S4R7R6A4S3bRcA1A3S99R8R7A2S0S4S25G0S17RcPcA2A2R9A3S73RfRdRaR9R8R7A6S42OF_;S43S48S28R2S47R11A1A3S85S28R3S47R12A1A3S64U0S2aS72VCST;VXGL;R14A3R4R14R13S3cR14R12RfReRdRcA6S52S55R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFT 0 (rd_okG NVN 0) HSEG CST XGL HCST HXGL HCSTD ED_NT TD_NT (sDv_of ED_NT) RD_NT HeD_NT HchkD_NT HTD_NT DCHK_NT
           A Kc (rhoF_of A rho p n t jv) HKc HKM (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_NT : ltac2:(tb__ "0|1|
S34S2bS18S7S26Q40M0A1A1S93S4S4S4S3dS2cR8A1S2fS32S3aRaA1S39RaA1A2S98A2S78S28RbR9R8R7A5S68SdS4S4A2SfS4S4R7R6A4S3bRcA1A3S99R8R7A2S0S4S25G0S17RcPcA2A2R9A3S73RfRdRaR9R8R7A6S42OF_;S65U0S2aS72VCST;VXGL;R11A3R11R10S3cR11RfRcRbRaR9A6S52S55R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFET 0 (rd_okG NVN 0) HSEGE CST XGL HCST HXGL HCSTD ED_NT TD_NT (sDv_of ED_NT) RD_NT HeD_NT HchkD_NT HTD_NT DCHK_NT
           A Kc (rhoF_of A rho p n t jv) HKc HKM (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.
Lemma entry_pure_NT : ltac2:(tb__ "0|2|
S34S2bS18S7S26Q40M0A1A1S42S9aS6S25G0S17R3PcA2A2S25G0S17R3PdM1A2A2A3S0S5S37R6A1S6A3S30S60S25G0S17R5G1A2A2A2S46S28S7eR8R7A2S75S2eA1R6R5R4A6S7dS6S2dU0A1S2aR9R7A5F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w HK Hii HBG [_ [HJ _]]. destruct HJ as (HA & _ & HL & _).
  split; [exact HL|]. split; [exists tp, (cfg_model (w_cfg w)); exact HA|].
  pose proof (cls_hyp_blk true _ _ HK) as HCL.
  destruct (blkF_mem A rho tp _ _ _ HA HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp _ HA) as (jv & JM & Hjv).
  exists t, jv. split; [exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv)|]. split; [exact JM|].
  exact (instG_here_N A rho tp _ _ _ HA HL HCL Hii eq_refl eq_refl t (conj T1 (conj T2 (conj T3 T4))) jv Hjv true (Wcan 0) UStopLe HK HBG).
Qed.

Theorem free_hi_N_T : ltac2:(tb__ "0|1|
S42OF_;S34S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S74VCST;VXGL;R6R5R4R3A6S43S2cR6A1S48S28R9S47R7A1A3S85S28RaS47R8A1A3S2fS61S31R6Z10A2A2S0S5S37RbA1S6A3S30S60R7A2S4S3dS73RfRdRbRaR2R1A6S0S4S3eR2A1S62A3S63RfS3cR11RfRdRcR4R3A6A2S7bU0S72VCST;VXGL;R12A3R13R12R11S3cR12R10ReRdR5R4A6S53RcA8F_;F_;F_;Fjv;Ft;S45S28RfS46S28S7eReRdA2S75S2eA1RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN true (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_NT A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (t_instantiate true NVN VFN Wa_NT Da_NT Wb_NT Wc_NT Wd_NT Fb_NT XI_NT A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree A rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_NT (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1 HO eq_refl HST
           (hdf_NT A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem free_hi_ia0_N_T : ltac2:(tb__ "0|2|
S42OF_;S34S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S74VCST;VXGL;R6R5R4R3A6S43S2cR6A1S48S28R9S47R7A1A3S85S28RaS47R8A1A3S2fS61S31R6Z10A2A2S0S5S37RbA1S9A3S30S60R7A2S18S4S3dS9bR10S3cR10ReRcRbR2R1A6R3A3S73S77R11A1R4RdRcR3R2A6S0S4S3eR3A1S62A3S63R6S3cS77R13A1R6RfReR5R4A6A2S7bU0S72VCST;VXGL;S77R14A1M1A3R15G1R13S3cG1R7R10RfR6R5A6S53S74VCST;VXGL;G1R13R7R11A6A8F_;F_;F_;F_;Fjv;Ft;Frho2;S45S28RfS46S28S7eReRdA2S75S2eA1RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix Wai_NT Dai_NT Wbi_NT Wci_NT Certi_NT ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (HBG2 : kQuarantineMax < bv_unsigned (rw rho2 13%positive)) by (rewrite E13; exact HBG).
  assert (IFF : instG_facts true (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true NVN VFN Wbm_NT Wcm_NT Wdm_NT Fb_NT XIm_NT A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite EID; exact HBG2).
  exact (free_spine_m_NT (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1 HO eq_refl HST
           (hdf_NT A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_N_T : ltac2:(tb__ "0|1|
S34S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S74VCST;VXGL;R6R5R4R3A6S43S2cR6A1S2fS61S31R4Z10A2A2S0S5S37R9A1S6A3S30S60R5A2S4S3dS73RdRbR9R8R2R1A6S0S4S3eR2A1S62A3S63RdS3cRfRdRbRaR4R3A6A2S7cU0S72VCST;VXGL;R10A3R10RfS3cR10ReRcRbR5R4A6S53RaA7F_;F_;F_;Fjv;Ft;S44S28S46S28S7eRcRbA2S75S2eA1RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureN true (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_NT A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (t_instantiate true NVN VFN Wa_NT Da_NT Wb_NT Wc_NT Wd_NT Fb_NT XI_NT A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree A rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_NT (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1 HO eq_refl HST
           (hdfe_NT A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.
Theorem efree_hi_ia0_N_T : ltac2:(tb__ "0|2|
S34S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S74VCST;VXGL;R6R5R4R3A6S43S2cR6A1S2fS61S31R4Z10A2A2S0S5S37R9A1S9A3S30S60R5A2S18S4S3dS9bReS3cReRcRaR9R2R1A6R3A3S73S77RfA1R4RbRaR3R2A6S0S4S3eR3A1S62A3S63R6S3cS77R11A1R6RdRcR5R4A6A2S7cU0S72VCST;VXGL;S77R12A1M1A3G1R11S3cG1R7ReRdR6R5A6S53S74VCST;VXGL;G1R11R7RfA6A7F_;F_;F_;F_;Fjv;Ft;Frho2;S44S28S46S28S7eRcRbA2S75S2eA1RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix Wai_NT Dai_NT Wbi_NT Wci_NT ECerti_NT A Kc rho tp Q p n t jv Hii HKc).
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
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (HBG2 : kQuarantineMax < bv_unsigned (rw rho2 13%positive)) by (rewrite E13; exact HBG).
  assert (IFF : instG_facts true (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid true NVN VFN Wbm_NT Wcm_NT Wdm_NT Fb_NT XIm_NT A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite EID; exact HBG2).
  exact (efree_spine_m_NT (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1 HO eq_refl HST
           (hdfe_NT A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ANT.
End F0T_aNT.

(* [comment removed for export] *)
Module F0T_aLNT.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "andb"; "false"; "cons"; "nil"; "negb"; "prod"; "orb"; "pair"; "length"; "option"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_lenient"; "ss_next"; "sv"; "ss_objs"; "swf"; "SVar"; "sv_below"; "SLit"; "sobj"; "sprop"; "ss_facts"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "Wcan"; "AE_A"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "aa_internal_inited"; "topG"; "aa_Kf"; "aa_Km"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kt.F0T_aLNT"; "MT_LNT"; "m1_LNT"; "MX_LNT"; "MH0_LNT"; "m2_LNT"; "m3_LNT"; "m4_LNT"; "okbm_LNT"; "okbp_LNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cLNT"; "ED_LNT"; "Erc_LNT"; "PMID_LNT"; "TD_LNT"; "S1c_LNT"; "P0_LNT"; "LT_LNT"; "l1_LNT"; "EX_LNT"; "LH0_LNT"; "l2_LNT"; "l3_LNT"; "l4_LNT"; "RD_LNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "PostDv"; "PreDv"; "sDv_of"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln"; "QFNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "contN"; "econtN"; "entry_pureN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "JT"; "objs_le"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state";
"carve_link_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cLNT.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma RUN1p_DUMMY_LNT : True. Proof. exact I. Qed.
Definition RUN1p_LNT := RUN1_LNT. Definition RUN2p_LNT := RUN2f_LNT. Definition RUN3p_LNT := RUN3f_LNT. Definition RUN4p_LNT := RUN4f_LNT.
Definition okbp_LNT := l1okb_LNT. Definition chkp_LNT := chk_LNT. Definition H0eqp_LNT := LH0eq_LNT. Definition SIDEp_LNT := SIDE_LNT. Definition OBNDp_LNT := OBND_LNT.
Lemma splitp_LNT : ltac2:(tb__ "0|9|
S1S1S2S0S7S13A1M0S58SbS13A1M1A3A1S1S2S0G0S5bG1A3A1S1S2S0G0S5cG1A3A1S2S0G0S5dG1A3A1A2A2A2S1S0S5S50S58A1S6A3S1S0S5S8fS10S13S6aS68S58A2A2U1A2S6A3S1S0S5S66S13S13SeS3eS15R1A1M2S57A2S3eG2S59A2A2LL;S5bA3S6A3S1S0S5S1dS14S8dS57S1eS69A1M3A2A1A1S6A3S1S0S5S1fS1aS14S57A1M4A1M5G3A2S6A3S1S0S5S66S13S8cS57S59S69A3S5cA3S6A3S1S0S5S66S13S13S3eG2S55A2LL;S5dA3S6A3S1S1S6fS29S1aS14S56A1M6A1A2S1S6fS29S1aS14S5aA1M7A1A2S1S6fS29G5A2S6fS29S1aS14S59A1M8A1A2A2A2A2S1S0S5S19G6A1S9A3S1S0S5S19G7A1S9A3S1S0S5S19G4A1S9A3S0S5S19G8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkp_LNT as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okp_LNT : ltac2:(tb__ "0|1|
S13S67S13R1S58A3S3S0S16S15R2A1M0S5aA3S0S5S3eG0S55A2S6A3A2F_;FL;").
Proof.
  destruct splitp_LNT as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_LNT)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqp_LNT. destruct (atpc LOOPH l1_LNT) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.
Lemma Wai_LNT : ltac2:(tb__ "0|0|
S0S5S1dS88S2dU0A1S2aA2A1S6A3"). Proof. vmr. Qed.
Lemma Dai_LNT : ltac2:(tb__ "0|4|
S0S11SdS7SdS1bS1bA2M0A1M1S7S22A1M2A2M3A1S9cS14S74S2eA1A1S88S2dU0A1S2aA2A2S12G3SfG1G2SaG0SfS1bS1bS1eP18A1S20Sa0A1A4SbG0A1A3SbS22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_LNT : ltac2:(tb__ "0|0|
S0S5S1dS8aS2dU0A1S2aA2A1S6A3"). Proof. vmr. Qed.
Lemma Wci_LNT : ltac2:(tb__ "0|0|
S0S5S1dS8bS2dU0A1S2aA2A1S6A3"). Proof. vmr. Qed.
Definition Certi_LNT__runs : ltac2:(tb__ "0|0|
S7S11S7S13A1A1A1") := ltac2:(tb__ "0|0|
S9dS28Ubb8S85S87U0S2aA2A4").
Lemma Certi_LNT : ltac2:(tb__ "0|1|
S0S5S94S28Ubb8S85S29S87U0M0S2aA2SaS16S86S2dG0A1S2aA2SbS16A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_LNT__runs); [unfold Certi_LNT__runs; reflexivity | vmr]. Qed.
Lemma ECerti_LNT : ltac2:(tb__ "0|2|
S0S5S95S28Ubb8S85S29S89U0M0S2aA2SaS93S96S86S2dG0A1S2aA2Z0M1S20G1A1A3SbS93A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_LNT__runs); [unfold Certi_LNT__runs; reflexivity | vmr]. Qed.
Definition m1_LNT : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_LNT.
Definition MH0_LNT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_LNT) DUMMY).
Definition m2_LNT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_LNT.
Definition MH1_LNT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_LNT) DUMMY).
Definition MT_LNT : axst := Eval vm_compute in LT_ofg MH1_LNT F0_LNT.
Definition MX_LNT : axst := Eval vm_compute in EX_ofg MH1_LNT F0_LNT.
Definition m3_LNT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_LNT (SVar pFR)).
Definition m4_LNT : list leafA := Eval vm_compute in runA FUELF [CASX] MX_LNT.
Lemma RUN1m_LNT : ltac2:(tb__ "0|0|
S0S7S13A1S82S3fSaS4S68SaS4S40SbS4A1A3A3S53A3S49A3"). Proof. Time vmr. Qed.
Lemma RUN2m_LNT : ltac2:(tb__ "0|0|
S0S7S13A1S82S3fSaS4S68SaS4S6bSbS4A1A3A3S4bA3S4cA3"). Proof. Time vmr. Qed.
Lemma RUN3m_LNT : ltac2:(tb__ "0|0|
S0S7S13A1S82S3fSaS4S68SaS4S6bSbS4A1A3A3S8eS48S1eS69A1A2A3S4dA3"). Proof. Time vmr. Qed.
Lemma RUN4m_LNT : ltac2:(tb__ "0|0|
S0S7S13A1S82S3fSaS4S40SbS4A1A3S4aA3S4eA3"). Proof. Time vmr. Qed.
Definition okbm_LNT (l : list leafA) : bool := ltac2:(tb__ "0|1|
S66S13S13SeS32S24S14S15R1A1M0A1A1S68A2S3eG0S55A2A2LL;Vl;A3").
Lemma chkm_LNT : ltac2:(tb__ "0|a|
S0S5S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8ScS7S13A1M0S5Lx;M1S49S6S13G0S9Ll0;Ll;M2X7x2A1ScG1S4cS6G2X7x2A1A2ScG1S4dS6G2X7x2A1A2ScG1S4eS6G2X7x2A1A2S4fS49A1A2S8fS10S13S6aS68S49A2A2U1A2A2S66S13S13SeS3eS15R1A1M3S48A2S3eG3S4aA2A2LL;S4cA3A2S1dS14S8dS48S1eS69A1M4A2A1A1A2S1fS1aS14S48A1M5A1M6G4A2A2S66S13S8cS48S4aS69A3S4dA3A2S66S13S13S3eG3S55A2LL;S4eA3A2S70S29S1aS14S53A1M7A1A2A2S70S29S1aS14S4bA1M8A1A2A2S70S29G6A2A2S70S29S1aS14S4aA1M9A1A2A2ScS19G7A1A1A2ScS19G8A1A1A2ScS19G5A1A1A2ScS19G9A1A1A2S6A3").
Proof. Time vmr. Qed.
Lemma H0eqm_LNT : ltac2:(tb__ "0|0|
S0S16S15S91S13U0S6aS68S49A2S83A4A1S4bA3"). Proof. vmr. Qed.
Lemma SIDEm_LNT : ltac2:(tb__ "0|0|
S0S5S81S53S48A2S6A3"). Proof. Time vmr. Qed.
Lemma OBNDm_LNT : ltac2:(tb__ "0|1|
S0S7SdSdS1bS1bA2S1bA2M0A1S90S21G0S80S1cS14S48A1A1A4S90S21G0S80S1cS14S53A1A1A4A3"). Proof. Time vmr. Qed.
Lemma splitm_LNT : ltac2:(tb__ "0|9|
S1S1S2S0S7S13A1M0S49SbS13A1M1A3A1S1S2S0G0S4cG1A3A1S1S2S0G0S4dG1A3A1S2S0G0S4eG1A3A1A2A2A2S1S0S5S4fS49A1S6A3S1S0S5S8fS10S13S6aS68S49A2A2U1A2S6A3S1S0S5S66S13S13SeS3eS15R1A1M2S48A2S3eG2S4aA2A2LL;S4cA3S6A3S1S0S5S1dS14S8dS48S1eS69A1M3A2A1A1S6A3S1S0S5S1fS1aS14S48A1M4A1M5G3A2S6A3S1S0S5S66S13S8cS48S4aS69A3S4dA3S6A3S1S0S5S66S13S13S3eG2S55A2LL;S4eA3S6A3S1S1S6fS29S1aS14S53A1M6A1A2S1S6fS29S1aS14S4bA1M7A1A2S1S6fS29G5A2S6fS29S1aS14S4aA1M8A1A2A2A2A2S1S0S5S19G6A1S9A3S1S0S5S19G7A1S9A3S1S0S5S19G4A1S9A3S0S5S19G8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_LNT as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okm_LNT : ltac2:(tb__ "0|1|
S13S67S13R1S49A3S3S0S16S15R2A1M0S4bA3S0S5S3eG0S55A2S6A3A2F_;FL;").
Proof.
  destruct splitm_LNT as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_LNT)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqm_LNT. destruct (atpc LOOPH m1_LNT) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ALNT.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Lemma spine_tail_LNT : ltac2:(tb__ "0|2|
S4OF_;S41OF_;S33S2bS18S18S7S26Q40M0A1A1S42S2cR5A1S47Vsegs;R8S46R6A1A3S62R6R5A2S30S5fS25G0S17R6PdA2A2A2S63U0M1S2aRcRbRaR9R7S51S54R5AaS7aG1RdRcRbRaR8S52R6A8S18S44Vsegs;ReS45Vsegs;S65G1S2aS6RdRcRaA6S55R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HBIG.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  apply (f0_s2 0 UStopLe true S1c_LNT C2_LNT EfD_LNT ED_LNT run2_LNT D2_LNT W2_LNT NX2_LNT EQ2_LNT RUN2_LNT L2_LNT AXD_LNT
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
  exact (f0_s3n 0 UStopLe TD_LNT TDr_LNT CD_LNT Eps_LNT Ebg_LNT Erc_LNT run3_LNT AXDr_LNT ENTD_LNT RUN3_LNT L3_LNT NX3_LNT SMF_LNT CertR_LNT
           ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
           (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Theorem free_spine_LNT : ltac2:(tb__ "0|5|
S4OF_;S41OF_;S33S2bS18S18S7S26Q40M0A1M1A1S42S2cR5A1S47Vsegs;R8S46R6A1A3S62R6R5A2S30S5fS25G0S17R6PdA2A2A2S7fR7S25G0S17R7PaA2A2S1cS14S56A1A1A3S0G1S17R8P99A2S27G0S35S34RbA1A1A2A3S1S2fZ1S35S34RcA1M2A1M3A2S2fG3S75S37G2A1A1A2A2S63U0M4S2aRfReRdRcRaS51S54R8AaS7aG4R10RfReRdRbS52R9A8S18S44Vsegs;R11S45Vsegs;S7eR10RfRdA3S56R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitp_LNT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LNT LH0_LNT LT_LNT EX_LNT S1c_LNT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LNT l2_LNT l3_LNT l4_LNT HNX HLEN
           (runT_some _ _ _ _ RUN1p_LNT NE1) L1okp_LNT (runT_some _ _ _ _ RUN2p_LNT NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_LNT NE3) H3 (runT_some _ _ _ _ RUN4p_LNT NE4) H4
           (hside_of A Kc rho1 P0_LNT LT_LNT tp SIDEp_LNT OBNDp_LNT HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_LNT keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HBIG rhoE).
Qed.
Theorem free_spine_m_LNT : ltac2:(tb__ "0|5|
S4OF_;S41OF_;S33S2bS18S18S7S26Q40M0A1M1A1S42S2cR5A1S47Vsegs;R8S46R6A1A3S62R6R5A2S30S5fS25G0S17R6PdA2A2A2S7fR7S25G0S17R7PaA2A2S1cS14S53A1A1A3S0G1S17R8P99A2S27G0S35S34RbA1A1A2A3S1S2fZ1S35S34RcA1M2A1M3A2S2fG3S75S37G2A1A1A2A2S63U0M4S2aRfReRdRcRaS51S54R8AaS7aG4R10RfReRdRbS52R9A8S18S44Vsegs;R11S45Vsegs;S7eR10RfRdA3S53R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitm_LNT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LNT MH0_LNT MT_LNT MX_LNT S1c_LNT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LNT m2_LNT m3_LNT m4_LNT HNX HLEN
           (runT_some _ _ _ _ RUN1m_LNT NE1) L1okm_LNT (runT_some _ _ _ _ RUN2m_LNT NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LNT NE3) H3 (runT_some _ _ _ _ RUN4m_LNT NE4) H4
           (hside_of A Kc rho1 PMID_LNT MT_LNT tp SIDEm_LNT OBNDm_LNT HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_LNT keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HBIG rhoE).
Qed.
Lemma espine_tail_LNT : ltac2:(tb__ "0|2|
S4OF_;S33S2bS18S18S7S26Q40M0A1A1S41OF_;S2cR5A1S62R5R4A2S30S5fS25G0S17R5PdA2A2A2S64U0M1S2aRaR9R8R6S51S54R4A9S7bG1RbRaR9R7S52R5A7S18S43Vsegs;S45Vsegs;S65G1S2aS6RcRbR9A6S55R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HBIG.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  apply (ef0_s2 0 UStopLe true S1c_LNT C2_LNT EfD_LNT ED_LNT run2_LNT D2_LNT W2_LNT NX2_LNT EQ2_LNT RUN2_LNT L2_LNT AXD_LNT
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
  exact (ef0_s3n 0 UStopLe TD_LNT TDr_LNT CD_LNT Eps_LNT Ebg_LNT Erc_LNT run3_LNT AXDr_LNT ENTD_LNT RUN3_LNT L3_LNT NX3_LNT SMF_LNT NXB_LNT ECertR_LNT
           A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
           (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Theorem efree_spine_LNT : ltac2:(tb__ "0|5|
S4OF_;S33S2bS18S18S7S26Q40M0A1M1A1S41OF_;S2cR5A1S62R5R4A2S30S5fS25G0S17R5PdA2A2A2S7fR6S25G0S17R6PaA2A2S1cS14S56A1A1A3S0G1S17R7P99A2S27G0S35S34RaA1A1A2A3S1S2fZ1S35S34RbA1M2A1M3A2S2fG3S75S37G2A1A1A2A2S64U0M4S2aRdRcRbR9S51S54R7A9S7bG4ReRdRcRaS52R8A7S18S43Vsegs;S45Vsegs;S7eRfReRcA3S56R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitp_LNT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LNT LH0_LNT LT_LNT EX_LNT S1c_LNT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LNT l2_LNT l3_LNT l4_LNT HNX HLEN
           (runT_some _ _ _ _ RUN1p_LNT NE1) L1okp_LNT (runT_some _ _ _ _ RUN2p_LNT NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_LNT NE3) H3 (runT_some _ _ _ _ RUN4p_LNT NE4) H4
           (hside_of A Kc rho1 P0_LNT LT_LNT tp SIDEp_LNT OBNDp_LNT HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_LNT keep A Kc rho rho1 tp Q HKc HR Hn HD1 HBIG rhoE).
Qed.
Theorem efree_spine_m_LNT : ltac2:(tb__ "0|5|
S4OF_;S33S2bS18S18S7S26Q40M0A1M1A1S41OF_;S2cR5A1S62R5R4A2S30S5fS25G0S17R5PdA2A2A2S7fR6S25G0S17R6PaA2A2S1cS14S53A1A1A3S0G1S17R7P99A2S27G0S35S34RaA1A1A2A3S1S2fZ1S35S34RbA1M2A1M3A2S2fG3S75S37G2A1A1A2A2S64U0M4S2aRdRcRbR9S51S54R7A9S7bG4ReRdRcRaS52R8A7S18S43Vsegs;S45Vsegs;S7eRfReRcA3S53R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HBIG rhoP.
  destruct splitm_LNT as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LNT MH0_LNT MT_LNT MX_LNT S1c_LNT pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LNT m2_LNT m3_LNT m4_LNT HNX HLEN
           (runT_some _ _ _ _ RUN1m_LNT NE1) L1okm_LNT (runT_some _ _ _ _ RUN2m_LNT NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LNT NE3) H3 (runT_some _ _ _ _ RUN4m_LNT NE4) H4
           (hside_of A Kc rho1 PMID_LNT MT_LNT tp SIDEm_LNT OBNDm_LNT HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_LNT keep A Kc rho rho1 tp Q HKc HR Hn HD1 HBIG rhoE).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S4S9bVCST;R1A2S2Sa1R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S4S9bVCST;R1A2S1S2S1S2fS78R2A2S30R2S79A2A2A1S2S1S2fZ17db48R2A2S30R2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.
Lemma HTD_LNT : ltac2:(tb__ "0|0|
S0S16S54S9eS9fS6eS51A1S6dS6cS51S5eA5S23S14S51A1A1A2A3").
Proof. unfold TD_LNT, TDv_of, RD_LNT; reflexivity. Qed.
Theorem hdf_LNT : ltac2:(tb__ "0|1|
S33S2bS18S7S26Q40M0A1A1S92S4S4S4S3cS2cR8A1S2fS31S39RaA1S38RaA1A2S97A2S77S28RbR9R8R7A5S67SdS4S4A2SfS4S4R7R6A4S3aRcA1A3S98R8R7A2S0S4S25G0S17RcPcA2A2R9A3S72RfRdRaR9R8R7A6S41OF_;S42S47S28R2S46R11A1A3S84S28R3S46R12A1A3S63U0S2aS71VCST;VXGL;R14A3R4R14R13S3bR14R12RfReRdRcA6S51S54R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFT 0 (rd_okG NVN 0) HSEG CST XGL HCST HXGL HCSTD ED_LNT TD_LNT (sDv_of ED_LNT) RD_LNT HeD_LNT HchkD_LNT HTD_LNT DCHK_LNT
           A Kc (rhoF_of A rho p n t jv) HKc HKM (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LNT : ltac2:(tb__ "0|1|
S33S2bS18S7S26Q40M0A1A1S92S4S4S4S3cS2cR8A1S2fS31S39RaA1S38RaA1A2S97A2S77S28RbR9R8R7A5S67SdS4S4A2SfS4S4R7R6A4S3aRcA1A3S98R8R7A2S0S4S25G0S17RcPcA2A2R9A3S72RfRdRaR9R8R7A6S41OF_;S64U0S2aS71VCST;VXGL;R11A3R11R10S3bR11RfRcRbRaR9A6S51S54R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFET 0 (rd_okG NVN 0) HSEGE CST XGL HCST HXGL HCSTD ED_LNT TD_LNT (sDv_of ED_LNT) RD_LNT HeD_LNT HchkD_LNT HTD_LNT DCHK_LNT
           A Kc (rhoF_of A rho p n t jv) HKc HKM (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.
Lemma entry_pure_NT : ltac2:(tb__ "0|2|
S33S2bS18S7S26Q40M0A1A1S41S99S9S25G0S17R3PcA2A2S25G0S17R3PdM1A2A2A3S0S5S36R6A1S6A3S30S5fS25G0S17R5G1A2A2A2S45S28S7dR8R7A2S74S2eA1R6R5R4A6S7cS9S2dU0A1S2aR9R7A5F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w HK Hii HBG [_ [HJ _]]. destruct HJ as (HA & _ & HL & _).
  split; [exact HL|]. split; [exists tp, (cfg_model (w_cfg w)); exact HA|].
  pose proof (cls_hyp_blk false _ _ HK) as HCL.
  destruct (blkF_mem A rho tp _ _ _ HA HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp _ HA) as (jv & JM & Hjv).
  exists t, jv. split; [exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv)|]. split; [exact JM|].
  exact (instG_here_N A rho tp _ _ _ HA HL HCL Hii eq_refl eq_refl t (conj T1 (conj T2 (conj T3 T4))) jv Hjv false (Wcan 0) UStopLe HK HBG).
Qed.

Theorem free_lo_N_T : ltac2:(tb__ "0|1|
S41OF_;S33S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S73VCST;VXGL;R6R5R4R3A6S42S2cR6A1S47S28R9S46R7A1A3S84S28RaS46R8A1A3S2fS31R6R5A2S60A2S0S5S36RbA1S6A3S30S5fR7A2S4S3cS72RfRdRbRaR2R1A6S0S4S3dR2A1S61A3S62RfS3bR11RfRdRcR4R3A6A2S7aU0S71VCST;VXGL;R12A3R13R12R11S3bR12R10ReRdR5R4A6S52RcA8F_;F_;F_;Fjv;Ft;S44S28RfS45S28S7dReRdA2S74S2eA1RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN false (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_NT A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (t_instantiate false NVN VFN Wa_LNT Da_LNT Wb_LNT Wc_LNT Wd_LNT Fb_LNT XI_LNT A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree A rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_LNT (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1 HO eq_refl HST
           (hdf_LNT A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem free_lo_ia0_N_T : ltac2:(tb__ "0|2|
S41OF_;S33S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S73VCST;VXGL;R6R5R4R3A6S42S2cR6A1S47S28R9S46R7A1A3S84S28RaS46R8A1A3S2fS31R6R5A2S60A2S0S5S36RbA1S9A3S30S5fR7A2S18S4S3cS9aR10S3bR10ReRcRbR2R1A6R3A3S72S76R11A1R4RdRcR3R2A6S0S4S3dR3A1S61A3S62R6S3bS76R13A1R6RfReR5R4A6A2S7aU0S71VCST;VXGL;S76R14A1M1A3R15G1R13S3bG1R7R10RfR6R5A6S52S73VCST;VXGL;G1R13R7R11A6A8F_;F_;F_;F_;Fjv;Ft;Frho2;S44S28RfS45S28S7dReRdA2S74S2eA1RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix Wai_LNT Dai_LNT Wbi_LNT Wci_LNT Certi_LNT ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (HBG2 : kQuarantineMax < bv_unsigned (rw rho2 13%positive)) by (rewrite E13; exact HBG).
  assert (IFF : instG_facts false (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false NVN VFN Wbm_LNT Wcm_LNT Wdm_LNT Fb_LNT XIm_LNT A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite EID; exact HBG2).
  exact (free_spine_m_LNT (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1 HO eq_refl HST
           (hdf_LNT A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_N_T : ltac2:(tb__ "0|1|
S33S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S73VCST;VXGL;R6R5R4R3A6S42S2cR6A1S2fS31R4R3A2S60A2S0S5S36R9A1S6A3S30S5fR5A2S4S3cS72RdRbR9R8R2R1A6S0S4S3dR2A1S61A3S62RdS3bRfRdRbRaR4R3A6A2S7bU0S71VCST;VXGL;R10A3R10RfS3bR10ReRcRbR5R4A6S52RaA7F_;F_;F_;Fjv;Ft;S43S28S45S28S7dRcRbA2S74S2eA1RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureN false (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_NT A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (t_instantiate false NVN VFN Wa_LNT Da_LNT Wb_LNT Wc_LNT Wd_LNT Fb_LNT XI_LNT A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree A rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_LNT (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1 HO eq_refl HST
           (hdfe_LNT A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.
Theorem efree_lo_ia0_N_T : ltac2:(tb__ "0|2|
S33S2bS18S7S26Q40M0A1A1S25G0S17R2PcA2A2S4S25G0S17R3PdA2A2S4S73VCST;VXGL;R6R5R4R3A6S42S2cR6A1S2fS31R4R3A2S60A2S0S5S36R9A1S9A3S30S5fR5A2S18S4S3cS9aReS3bReRcRaR9R2R1A6R3A3S72S76RfA1R4RbRaR3R2A6S0S4S3dR3A1S61A3S62R6S3bS76R11A1R6RdRcR5R4A6A2S7bU0S71VCST;VXGL;S76R12A1M1A3G1R11S3bG1R7ReRdR6R5A6S52S73VCST;VXGL;G1R11R7RfA6A7F_;F_;F_;F_;Fjv;Ft;Frho2;S43S28S45S28S7dRcRbA2S74S2eA1RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix Wai_LNT Dai_LNT Wbi_LNT Wci_LNT ECerti_LNT A Kc rho tp Q p n t jv Hii HKc).
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
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (HBG2 : kQuarantineMax < bv_unsigned (rw rho2 13%positive)) by (rewrite E13; exact HBG).
  assert (IFF : instG_facts false (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid false NVN VFN Wbm_LNT Wcm_LNT Wdm_LNT Fb_LNT XIm_LNT A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite EID; exact HBG2).
  exact (efree_spine_m_LNT (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1 HO eq_refl HST
           (hdfe_LNT A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALNT.
End F0T_aLNT.

(* [comment removed for export] *)
Module F0A_aLN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "bool"; "pair"; "prod"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN0"; "Erc_LN0"; "ED_LN0_1"; "ED_LN0_2"; "TD_LN0_1"; "TD_LN0_2"; "P0_LN0"; "PMID_LN0"; "exits1_LN0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "QFN"; "contN"; "econtN"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cLN0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
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
S0S44VCST;R1A2S1aS1bS1aS21S39R2A2S20R2S3aA2A2A1S1bS1aS21Z17db48R2A2S20R2Z17db4cA2A2A1A2F_;Fa;").
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
  apply (fi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Certi_0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  apply (efi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.ECerti_0A A Kc rho tp Q p n t jv Hii HKc).
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
Module F0A_aLN2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "true"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN2"; "Erc_LN2"; "ED_LN2_1"; "ED_LN2_2"; "ED_LN2_3"; "ED_LN2_4"; "TD_LN2_1"; "TD_LN2_2"; "TD_LN2_3"; "TD_LN2_4"; "P0_LN2"; "PMID_LN2"; "exits1_LN2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "QFN"; "contN"; "econtN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cLN2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALN2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_LN2 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S26Vsegs;R8S24R6A1A3S22R6R5A2S2dS3cSbG0S9R6PdA2A2A2S20U2M1S1RcRbRaR9R7S31S35R5AaS20G1S1RdRcRbRaR8S32S36R6AaS20G1S1ReRdRcRbR9S33S37R7AaS20G1S1RfReRdRcRaS34S38R8AaS44G1R10RfReRdRbS30R9A8S46S8S3fS46R2S3bA3S1fVsegs;R13S25Vsegs;S23G1S1S10R12R11RfA6R3R2ReA5RdA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2 UStopLe true S1c_LN2_1 C2_LN2_1 EfD_LN2_1 ED_LN2_1 run2_LN2_1 D2_LN2_1 W2_LN2_1 NX2_LN2_1 EQ2_LN2_1 RUN2_LN2_1 L2_LN2_1 AXD_LN2_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_LN2_1 TDr_LN2_1 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_1 ENTD_LN2_1 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 CertR_LN2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LN2_2 C2_LN2_2 EfD_LN2_2 ED_LN2_2 run2_LN2_2 D2_LN2_2 W2_LN2_2 NX2_LN2_2 EQ2_LN2_2 RUN2_LN2_2 L2_LN2_2 AXD_LN2_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_LN2_2 TDr_LN2_2 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_2 ENTD_LN2_2 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 CertR_LN2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LN2_3 C2_LN2_3 EfD_LN2_3 ED_LN2_3 run2_LN2_3 D2_LN2_3 W2_LN2_3 NX2_LN2_3 EQ2_LN2_3 RUN2_LN2_3 L2_LN2_3 AXD_LN2_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_LN2_3 TDr_LN2_3 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_3 ENTD_LN2_3 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 CertR_LN2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LN2_4 C2_LN2_4 EfD_LN2_4 ED_LN2_4 run2_LN2_4 D2_LN2_4 W2_LN2_4 NX2_LN2_4 EQ2_LN2_4 RUN2_LN2_4 L2_LN2_4 AXD_LN2_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_LN2_4 TDr_LN2_4 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_4 ENTD_LN2_4 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 CertR_LN2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_LN2 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S22R5R4A2S2dS3cSbG0S9R5PdA2A2A2S21U2M1S1RaR9R8R6S31S35R4A9S21G1S1RbRaR9R7S32S36R5A9S21G1S1RcRbRaR8S33S37R6A9S21G1S1RdRcRbR9S34S38R7A9S45G1ReRdRcRaS30R8A7S46S8S3fS46R2S3bA3S1eVsegs;S25Vsegs;S23G1S1S10R11R10ReA6R3R2RdA5RcA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2 UStopLe true S1c_LN2_1 C2_LN2_1 EfD_LN2_1 ED_LN2_1 run2_LN2_1 D2_LN2_1 W2_LN2_1 NX2_LN2_1 EQ2_LN2_1 RUN2_LN2_1 L2_LN2_1 AXD_LN2_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_LN2_1 TDr_LN2_1 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_1 ENTD_LN2_1 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 NXB_LN2 ECertR_LN2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LN2_2 C2_LN2_2 EfD_LN2_2 ED_LN2_2 run2_LN2_2 D2_LN2_2 W2_LN2_2 NX2_LN2_2 EQ2_LN2_2 RUN2_LN2_2 L2_LN2_2 AXD_LN2_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_LN2_2 TDr_LN2_2 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_2 ENTD_LN2_2 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 NXB_LN2 ECertR_LN2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LN2_3 C2_LN2_3 EfD_LN2_3 ED_LN2_3 run2_LN2_3 D2_LN2_3 W2_LN2_3 NX2_LN2_3 EQ2_LN2_3 RUN2_LN2_3 L2_LN2_3 AXD_LN2_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_LN2_3 TDr_LN2_3 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_3 ENTD_LN2_3 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 NXB_LN2 ECertR_LN2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LN2_4 C2_LN2_4 EfD_LN2_4 ED_LN2_4 run2_LN2_4 D2_LN2_4 W2_LN2_4 NX2_LN2_4 EQ2_LN2_4 RUN2_LN2_4 L2_LN2_4 AXD_LN2_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_LN2_4 TDr_LN2_4 CD_LN2 Eps_LN2 Ebg_LN2 Erc_LN2 run3_LN2 AXDr_LN2_4 ENTD_LN2_4 RUN3_LN2 L3_LN2 NX3_LN2 SMF_LN2 NXB_LN2 ECertR_LN2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_LN2 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S26Vsegs;R8S24R6A1A3S22R6R5A2S2dS3cSbG0S9R6PdA2A2A2S20U2M1S1RcRbRaR9R7S31S35R5AaS20G1S1RdRcRbRaR8S32S36R6AaS20G1S1ReRdRcRbR9S33S37R7AaS20G1S1RfReRdRcRaS34S38R8AaS44G1R10RfReRdRbS30R9A8S8S1fVsegs;R11S25Vsegs;S23G1S1S10R10RfRdA6S39R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (f0_s1c 2 UStopLe true P0_LN2 exits1_LN2 Cert1_LN2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.
Theorem efree_spine_LN2 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S22R5R4A2S2dS3cSbG0S9R5PdA2A2A2S21U2M1S1RaR9R8R6S31S35R4A9S21G1S1RbRaR9R7S32S36R5A9S21G1S1RcRbRaR8S33S37R6A9S21G1S1RdRcRbR9S34S38R7A9S45G1ReRdRcRaS30R8A7S8S1eVsegs;S25Vsegs;S23G1S1S10RfReRcA6S39R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (ef0_s1c 2 UStopLe true P0_LN2 exits1_LN2 NX0_LN2 ECert1_LN2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.

Theorem free_spine_m_LN2 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S26Vsegs;R8S24R6A1A3S22R6R5A2S2dS3cSbG0S9R6PdA2A2A2S20U2M1S1RcRbRaR9R7S31S35R5AaS20G1S1RdRcRbRaR8S32S36R6AaS20G1S1ReRdRcRbR9S33S37R7AaS20G1S1RfReRdRcRaS34S38R8AaS44G1R10RfReRdRbS30R9A8S8S1fVsegs;R11S25Vsegs;S23G1S1S10R10RfRdA6S3aR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (f0_s1c 2 UStopLe true PMID_LN2 exits1_LN2 Cert1m_LN2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.
Theorem efree_spine_m_LN2 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S22R5R4A2S2dS3cSbG0S9R5PdA2A2A2S21U2M1S1RaR9R8R6S31S35R4A9S21G1S1RbRaR9R7S32S36R5A9S21G1S1RcRbRaR8S33S37R6A9S21G1S1RdRcRbR9S34S38R7A9S45G1ReRdRcRaS30R8A7S8S1eVsegs;S25Vsegs;S23G1S1S10RfReRcA6S3aR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (ef0_s1c 2 UStopLe true PMID_LN2 exits1_LN2 NX0m_LN2 ECert1m_LN2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S48VCST;R1A2S1bS49R2A1A1F_;Fa;").

Theorem hdf_LN2_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S31S35R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_1 TD_LN2_1 (sD_of ED_LN2_1 1) RD_LN2_1 HeD_LN2_1 HchkD_LN2_1 HTD_LN2_1 DCHK_LN2_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN2_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S31S35R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_1 TD_LN2_1 (sD_of ED_LN2_1 1) RD_LN2_1 HeD_LN2_1 HchkD_LN2_1 HTD_LN2_1 DCHK_LN2_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.
Theorem hdf_LN2_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S32S36R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_2 TD_LN2_2 (sD_of ED_LN2_2 2) RD_LN2_2 HeD_LN2_2 HchkD_LN2_2 HTD_LN2_2 DCHK_LN2_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN2_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S32S36R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_2 TD_LN2_2 (sD_of ED_LN2_2 2) RD_LN2_2 HeD_LN2_2 HchkD_LN2_2 HTD_LN2_2 DCHK_LN2_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.
Theorem hdf_LN2_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S33S37R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_3 TD_LN2_3 (sD_of ED_LN2_3 3) RD_LN2_3 HeD_LN2_3 HchkD_LN2_3 HTD_LN2_3 DCHK_LN2_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN2_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S33S37R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_3 TD_LN2_3 (sD_of ED_LN2_3 3) RD_LN2_3 HeD_LN2_3 HchkD_LN2_3 HTD_LN2_3 DCHK_LN2_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.
Theorem hdf_LN2_4 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S34S38R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_4 TD_LN2_4 (sD_of ED_LN2_4 4) RD_LN2_4 HeD_LN2_4 HchkD_LN2_4 HTD_LN2_4 DCHK_LN2_4
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN2_4 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S34S38R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN2_4 TD_LN2_4 (sD_of ED_LN2_4 4) RD_LN2_4 HeD_LN2_4 HchkD_LN2_4 HTD_LN2_4 DCHK_LN2_4
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.

Theorem free_lo_N_2 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S26SaR9S24R7A1A3S42SaRaS24R8A1A3S2eS2fR6R5A2S3dA2S19S11S18RbA1S10A3S2dS3cR7A2S0S14S28RfRdRbRaR2R1A6S19S0S15R2A1S3eA3S22RfS13R11RfRdRcR4R3A6A2S44G1S27VCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S30RcA8F_;F_;F_;Fjv;Ft;S1fSaRfS25SaS5S29SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN false (Wcan 2) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate false 2 UStopLe NVN VFN Wa_LN2 Da_LN2 Wb_LN2 Wc_LN2 Wd_LN2 Fb_LN2 XI_LN2 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_LN2 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_LN2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_N_2 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S2eS2fR4R3A2S3dA2S19S11S18R9A1S10A3S2dS3cR5A2S0S14S28RdRbR9R8R2R1A6S19S0S15R2A1S3eA3S22RdS13RfRdRbRaR4R3A6A2S45G1S27VCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S30RaA7F_;F_;F_;Fjv;Ft;S1eSaS25SaS5S29SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN false (Wcan 2) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate false 2 UStopLe NVN VFN Wa_LN2 Da_LN2 Wb_LN2 Wc_LN2 Wd_LN2 Fb_LN2 XI_LN2 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_LN2 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_LN2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S48VCST;R1A2S1aS1bS1aS2eS2bR2A2S2dR2S2cA2A2A1S1bS1aS2eZ17db48R2A2S2dR2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_N_2 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S26SaR9S24R7A1A3S42SaRaS24R8A1A3S2eS2fR6R5A2S3dA2S19S11S18RbA1S12A3S2dS3cR7A2S8S0S14S47R10S13R10ReRcRbR2R1A6R3A3S28S2aR11A1R4RdRcR3R2A6S19S0S15R3A1S3eA3S22R6S13S2aR13A1R6RfReR5R4A6A2S44G1S27VCST;VXGL;S2aR14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S30S43VCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS25SaS5S29SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Certi_2A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 2) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 2 UStopLe NVN VFN Wbm_LN2 Wcm_LN2 Wdm_LN2 Fb_LN2 XIm_LN2 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_LN2 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_LN2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_N_2 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S2eS2fR4R3A2S3dA2S19S11S18R9A1S12A3S2dS3cR5A2S8S0S14S47ReS13ReRcRaR9R2R1A6R3A3S28S2aRfA1R4RbRaR3R2A6S19S0S15R3A1S3eA3S22R6S13S2aR11A1R6RdRcR5R4A6A2S45G1S27VCST;VXGL;S2aR12A1M2A3G2R11S13G2R7ReRdR6R5A6S30S43VCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS25SaS5S29SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.ECerti_2A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 2) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 2) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid false 2 UStopLe NVN VFN Wbm_LN2 Wcm_LN2 Wdm_LN2 Fb_LN2 XIm_LN2 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_LN2 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_LN2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALN2.
End F0A_aLN2.

