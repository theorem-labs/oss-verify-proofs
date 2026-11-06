(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke j6 kz kr l5 j7 l1.

(* [comment removed for export] *)
Module DepotCallIW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.DepotCallMW2"; "T4_i"; "nobj_i"; "s4_i"; "R4_i"; "sd_i"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "list"; "nat"; "prod"; "cons"; "Some"; "option"; "pair"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.DepotCallW"; "omrg"; "X4"; "isSome"; "oreb"; "X4r"; "permW"; "T4d"; "T40"; "T4a"; "T4b"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "X4a"; "X4b"; "X4c"; "X4f"; "F_call"; "in_famb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SLit"; "sstate"; "ss_next"; "ss_objs"; "SVar"; "sobj"; "SPUle"; "sprop_below"; "SAlu"; "rw"; "valuation"; "SExt"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E4d"; "C5"; "F_gen"; "V_CNT"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.DepotCallIW2.INST"; "pm__29"; "pm__30"; "pm__31"; "pm__32"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__37"; "pm__38"; "pm__39"; "pm__40"; "pm__41"; "pm__42"; "pm__43"; "pm__44"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__0"; "pm__1"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__15"; "pm__16"; "pm__2"; "pm__3"; "pm__4"; "pm__49"; "pm__5"; "pm__50"; "pm__51"; "pm__52"; "pm__6"; "pm__7"; "pm__8"; "pm__9"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "coveredb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.DepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.DepotCallMW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLe. Let tmax : Z := 4.
Ltac memo_rw t M := lazymatch goal with |- context [t] => pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta | _ => fail "memo_rw: stage term not found" t end.
Ltac vmc := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NXE_i : ltac2:(tb__ "0|0|
S0S15S98S58S3aS4S45S9U2A1Vst;Vtmax;A3A1A1A2S16A3").
Proof.  memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.
Lemma FBE_i : ltac2:(tb__ "0|0|
S0S15S49S36S3fS3aS4S45S9U2A1Vst;Vtmax;A3A1A1A1S33A3S16A3").
Proof.  memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.
Lemma XE4_i : ltac2:(tb__ "0|1|
S0S18S1aS35S35A2M0A1S5S45S9U2A1Vst;Vtmax;A3A1S17G0A1A3").
Proof.  memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.
Lemma F192_i : ltac2:(tb__ "0|1|
S4aS36S1bS36S3eS38Z1A1S3cPc0A1M0A2S1bS36S3eG0S38Vtmax;A1A2S17S36A1A3A3S37S4S45S9U2A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.
Lemma FDEP_i : ltac2:(tb__ "0|0|
S4aS36SbSaA1S37S4S45S9U2A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.
Lemma FUNW_i : ltac2:(tb__ "0|1|
S4aS36ScS9U2A1M0Vst;A2S37S4S45G0Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.
Lemma FGEN4_i : ltac2:(tb__ "0|0|
S4aS36S47S37S4S45S9U2A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.
Lemma YP4_i : ltac2:(tb__ "0|0|
S4bS36S3eS38Z1A1S3cS48A1A2S37S4S45S9U2A1Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E4d (Wcan 2) st tmax) mE. vmc. Qed.

Ltac PM_sub0 t := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t.
Ltac PM_all0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X4f] in (X4f 2%nat UStopLe 4) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S3S32U2S8Z4A3S79A3"). Proof. cbv delta [X4f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X4f 2%nat UStopLe 4) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 2%nat UStopLe 4 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S3S25U2S8Z4Z1A4S7aA3"). Proof. cbv delta [X4r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X4r 2%nat UStopLe 4 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 2%nat UStopLe 4 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|0|
S0S3S25U2S8Z4Z2A4S82A3"). Proof. cbv delta [X4r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X4r 2%nat UStopLe 4 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 2%nat UStopLe 4 3) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S3S25U2S8Z4Z3A4S83A3"). Proof. cbv delta [X4r pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X4r 2%nat UStopLe 4 3) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 2%nat UStopLe 4 4) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|1|
S0S3S25U2S8Z4M0G0A4S84A3"). Proof. cbv delta [X4r pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X4r 2%nat UStopLe 4 4) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 2%nat UStopLe 4 1) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S3S2fU2S8Z4Z1A4S86A3"). Proof. cbv delta [X4a pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X4a 2%nat UStopLe 4 1) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 2%nat UStopLe 4 2) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|0|
S0S3S2fU2S8Z4Z2A4S8aA3"). Proof. cbv delta [X4a pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X4a 2%nat UStopLe 4 2) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 2%nat UStopLe 4 3) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S3S2fU2S8Z4Z3A4S8bA3"). Proof. cbv delta [X4a pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X4a 2%nat UStopLe 4 3) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 2%nat UStopLe 4 4) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|1|
S0S3S2fU2S8Z4M0G0A4S8cA3"). Proof. cbv delta [X4a pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X4a 2%nat UStopLe 4 4) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 2%nat UStopLe 4 1) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S3S30U2S8Z4Z1A4S8dA3"). Proof. cbv delta [X4b pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X4b 2%nat UStopLe 4 1) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 2%nat UStopLe 4 2) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|0|
S0S3S30U2S8Z4Z2A4S7bA3"). Proof. cbv delta [X4b pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X4b 2%nat UStopLe 4 2) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 2%nat UStopLe 4 3) in let t := eval cbv beta zeta in t in let t := PM_sub11 t in exact t).
Lemma pm__11_eq : ltac2:(tb__ "0|0|
S0S3S30U2S8Z4Z3A4S7cA3"). Proof. cbv delta [X4b pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (X4b 2%nat UStopLe 4 3) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 2%nat UStopLe 4 4) in let t := eval cbv beta zeta in t in let t := PM_sub12 t in exact t).
Lemma pm__12_eq : ltac2:(tb__ "0|1|
S0S3S30U2S8Z4M0G0A4S7dA3"). Proof. cbv delta [X4b pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (X4b 2%nat UStopLe 4 4) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 2%nat UStopLe 4 1) in let t := eval cbv beta zeta in t in let t := PM_sub13 t in exact t).
Lemma pm__13_eq : ltac2:(tb__ "0|0|
S0S3S31U2S8Z4Z1A4S7eA3"). Proof. cbv delta [X4c pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (X4c 2%nat UStopLe 4 1) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 2%nat UStopLe 4 2) in let t := eval cbv beta zeta in t in let t := PM_sub14 t in exact t).
Lemma pm__14_eq : ltac2:(tb__ "0|0|
S0S3S31U2S8Z4Z2A4S7fA3"). Proof. cbv delta [X4c pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (X4c 2%nat UStopLe 4 2) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 2%nat UStopLe 4 3) in let t := eval cbv beta zeta in t in let t := PM_sub15 t in exact t).
Lemma pm__15_eq : ltac2:(tb__ "0|0|
S0S3S31U2S8Z4Z3A4S80A3"). Proof. cbv delta [X4c pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (X4c 2%nat UStopLe 4 3) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 2%nat UStopLe 4 4) in let t := eval cbv beta zeta in t in let t := PM_sub16 t in exact t).
Lemma pm__16_eq : ltac2:(tb__ "0|1|
S0S3S31U2S8Z4M0G0A4S81A3"). Proof. cbv delta [X4c pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (X4c 2%nat UStopLe 4 4) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac:(let t := eval cbv delta [X4] in (X4 2%nat UStopLe 4 1) in let t := eval cbv beta zeta in t in let t := PM_sub17 t in exact t).
Lemma pm__17_eq : ltac2:(tb__ "0|0|
S0S3S22U2S8Z4Z1A4S5dA3"). Proof. cbv delta [X4 pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (X4 2%nat UStopLe 4 1) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac:(let t := eval cbv delta [X4] in (X4 2%nat UStopLe 4 2) in let t := eval cbv beta zeta in t in let t := PM_sub18 t in exact t).
Lemma pm__18_eq : ltac2:(tb__ "0|0|
S0S3S22U2S8Z4Z2A4S5eA3"). Proof. cbv delta [X4 pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (X4 2%nat UStopLe 4 2) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac:(let t := eval cbv delta [X4] in (X4 2%nat UStopLe 4 3) in let t := eval cbv beta zeta in t in let t := PM_sub19 t in exact t).
Lemma pm__19_eq : ltac2:(tb__ "0|0|
S0S3S22U2S8Z4Z3A4S5fA3"). Proof. cbv delta [X4 pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (X4 2%nat UStopLe 4 3) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac:(let t := eval cbv delta [X4] in (X4 2%nat UStopLe 4 4) in let t := eval cbv beta zeta in t in let t := PM_sub20 t in exact t).
Lemma pm__20_eq : ltac2:(tb__ "0|1|
S0S3S22U2S8Z4M0G0A4S60A3"). Proof. cbv delta [X4 pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (X4 2%nat UStopLe 4 4) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
S53SeZ1A1S37S4S5dA1A1A2").
Lemma pm__21_eq : ltac2:(tb__ "0|0|
S0S3S28U2S8Z4SeZ1A5S61A3"). Proof. cbv delta [T40 pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T40 2%nat UStopLe 4 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
S53SeZ2A1S37S4S5eA1A1A2").
Lemma pm__22_eq : ltac2:(tb__ "0|0|
S0S3S28U2S8Z4SeZ2A5S62A3"). Proof. cbv delta [T40 pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T40 2%nat UStopLe 4 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
S53SeZ3A1S37S4S5fA1A1A2").
Lemma pm__23_eq : ltac2:(tb__ "0|0|
S0S3S28U2S8Z4SeZ3A5S63A3"). Proof. cbv delta [T40 pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T40 2%nat UStopLe 4 T4_i 3) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
S53SeZ4A1S37S4S60A1A1A2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S3S28U2S8Z4M0SeG0A5S64A3"). Proof. cbv delta [T40 pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T40 2%nat UStopLe 4 T4_i 4) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|0|
S24S61U0A2").
Lemma pm__25_eq : ltac2:(tb__ "0|0|
S0S3S29U2S8Z4SeZ1A5S65A3"). Proof. cbv delta [T4a pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T4a 2%nat UStopLe 4 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|0|
S24S62U0A2").
Lemma pm__26_eq : ltac2:(tb__ "0|0|
S0S3S29U2S8Z4SeZ2A5S66A3"). Proof. cbv delta [T4a pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T4a 2%nat UStopLe 4 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Definition pm__27 : axst := ltac2:(tb__ "0|0|
S24S63U0A2").
Lemma pm__27_eq : ltac2:(tb__ "0|0|
S0S3S29U2S8Z4SeZ3A5S67A3"). Proof. cbv delta [T4a pm__27]; cbv beta zeta. PM_all27. reflexivity. Qed.
Ltac PM_sub28 t := let t := lazymatch (eval pattern (T4a 2%nat UStopLe 4 T4_i 3) in t) with ?P _ => eval cbv beta in (P pm__27) end in PM_sub27 t.
Ltac PM_all28 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__27_eq; PM_all27.
Definition pm__28 : axst := ltac2:(tb__ "0|0|
S24S64U0A2").
Lemma pm__28_eq : ltac2:(tb__ "0|1|
S0S3S29U2S8Z4M0SeG0A5S68A3"). Proof. cbv delta [T4a pm__28]; cbv beta zeta. PM_all28. reflexivity. Qed.
Ltac PM_sub29 t := let t := lazymatch (eval pattern (T4a 2%nat UStopLe 4 T4_i 4) in t) with ?P _ => eval cbv beta in (P pm__28) end in PM_sub28 t.
Ltac PM_all29 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__28_eq; PM_all28.
Definition pm__29 : axst := ltac2:(tb__ "0|0|
S24S65U1A2").
Lemma pm__29_eq : ltac2:(tb__ "0|0|
S0S3S2aU2S8Z4SeZ1A5S59A3"). Proof. cbv delta [T4b pm__29]; cbv beta zeta. PM_all29. reflexivity. Qed.
Ltac PM_sub30 t := let t := lazymatch (eval pattern (T4b 2%nat UStopLe 4 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__29) end in PM_sub29 t.
Ltac PM_all30 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__29_eq; PM_all29.
Definition pm__30 : axst := ltac2:(tb__ "0|0|
S24S66U1A2").
Lemma pm__30_eq : ltac2:(tb__ "0|0|
S0S3S2aU2S8Z4SeZ2A5S5aA3"). Proof. cbv delta [T4b pm__30]; cbv beta zeta. PM_all30. reflexivity. Qed.
Ltac PM_sub31 t := let t := lazymatch (eval pattern (T4b 2%nat UStopLe 4 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__30) end in PM_sub30 t.
Ltac PM_all31 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__30_eq; PM_all30.
Definition pm__31 : axst := ltac2:(tb__ "0|0|
S24S67U1A2").
Lemma pm__31_eq : ltac2:(tb__ "0|0|
S0S3S2aU2S8Z4SeZ3A5S5bA3"). Proof. cbv delta [T4b pm__31]; cbv beta zeta. PM_all31. reflexivity. Qed.
Ltac PM_sub32 t := let t := lazymatch (eval pattern (T4b 2%nat UStopLe 4 T4_i 3) in t) with ?P _ => eval cbv beta in (P pm__31) end in PM_sub31 t.
Ltac PM_all32 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__31_eq; PM_all31.
Definition pm__32 : axst := ltac2:(tb__ "0|0|
S24S68U1A2").
Lemma pm__32_eq : ltac2:(tb__ "0|1|
S0S3S2aU2S8Z4M0SeG0A5S5cA3"). Proof. cbv delta [T4b pm__32]; cbv beta zeta. PM_all32. reflexivity. Qed.
Ltac PM_sub33 t := let t := lazymatch (eval pattern (T4b 2%nat UStopLe 4 T4_i 4) in t) with ?P _ => eval cbv beta in (P pm__32) end in PM_sub32 t.
Ltac PM_all33 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__32_eq; PM_all32.
Definition pm__33 : axst := ltac2:(tb__ "0|1|
S6S59S52S4S59A1M0S4dS3bG0A1S26SfA1A2A2A2").
Lemma pm__33_eq : ltac2:(tb__ "0|0|
S0S3S2bU2S8Z4SeSfZ1A6S69A3"). Proof. cbv delta [T4c pm__33]; cbv beta zeta. PM_all33. reflexivity. Qed.
Ltac PM_sub34 t := let t := lazymatch (eval pattern (T4c 2%nat UStopLe 4 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__33) end in PM_sub33 t.
Ltac PM_all34 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__33_eq; PM_all33.
Definition pm__34 : axst := ltac2:(tb__ "0|1|
S6S5aS52S4S5aA1M0S4dS3bG0A1S26SfA1A2A2A2").
Lemma pm__34_eq : ltac2:(tb__ "0|0|
S0S3S2bU2S8Z4SeSfZ2A6S6aA3"). Proof. cbv delta [T4c pm__34]; cbv beta zeta. PM_all34. reflexivity. Qed.
Ltac PM_sub35 t := let t := lazymatch (eval pattern (T4c 2%nat UStopLe 4 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__34) end in PM_sub34 t.
Ltac PM_all35 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__34_eq; PM_all34.
Definition pm__35 : axst := ltac2:(tb__ "0|1|
S6S5bS52S4S5bA1M0S4dS3bG0A1S26SfA1A2A2A2").
Lemma pm__35_eq : ltac2:(tb__ "0|0|
S0S3S2bU2S8Z4SeSfZ3A6S6bA3"). Proof. cbv delta [T4c pm__35]; cbv beta zeta. PM_all35. reflexivity. Qed.
Ltac PM_sub36 t := let t := lazymatch (eval pattern (T4c 2%nat UStopLe 4 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__35) end in PM_sub35 t.
Ltac PM_all36 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__35_eq; PM_all35.
Definition pm__36 : axst := ltac2:(tb__ "0|1|
S6S5cS52S4S5cA1M0S4dS3bG0A1S26SfA1A2A2A2").
Lemma pm__36_eq : ltac2:(tb__ "0|1|
S0S3S2bU2S8Z4M0SeSfG0A6S6cA3"). Proof. cbv delta [T4c pm__36]; cbv beta zeta. PM_all36. reflexivity. Qed.
Ltac PM_sub37 t := let t := lazymatch (eval pattern (T4c 2%nat UStopLe 4 T4_i nobj_i 4) in t) with ?P _ => eval cbv beta in (P pm__36) end in PM_sub36 t.
Ltac PM_all37 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__36_eq; PM_all36.
Definition pm__37 : axst := ltac2:(tb__ "0|0|
S21S69U0A2").
Lemma pm__37_eq : ltac2:(tb__ "0|0|
S0S3S2cU2S8Z4SeSfZ1A6S6dA3"). Proof. cbv delta [T4m1 pm__37]; cbv beta zeta. PM_all37. reflexivity. Qed.
Ltac PM_sub38 t := let t := lazymatch (eval pattern (T4m1 2%nat UStopLe 4 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__37) end in PM_sub37 t.
Ltac PM_all38 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__37_eq; PM_all37.
Definition pm__38 : axst := ltac2:(tb__ "0|0|
S21S6aU0A2").
Lemma pm__38_eq : ltac2:(tb__ "0|0|
S0S3S2cU2S8Z4SeSfZ2A6S6eA3"). Proof. cbv delta [T4m1 pm__38]; cbv beta zeta. PM_all38. reflexivity. Qed.
Ltac PM_sub39 t := let t := lazymatch (eval pattern (T4m1 2%nat UStopLe 4 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__38) end in PM_sub38 t.
Ltac PM_all39 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__38_eq; PM_all38.
Definition pm__39 : axst := ltac2:(tb__ "0|0|
S21S6bU0A2").
Lemma pm__39_eq : ltac2:(tb__ "0|0|
S0S3S2cU2S8Z4SeSfZ3A6S6fA3"). Proof. cbv delta [T4m1 pm__39]; cbv beta zeta. PM_all39. reflexivity. Qed.
Ltac PM_sub40 t := let t := lazymatch (eval pattern (T4m1 2%nat UStopLe 4 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__39) end in PM_sub39 t.
Ltac PM_all40 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__39_eq; PM_all39.
Definition pm__40 : axst := ltac2:(tb__ "0|0|
S21S6cU0A2").
Lemma pm__40_eq : ltac2:(tb__ "0|1|
S0S3S2cU2S8Z4M0SeSfG0A6S70A3"). Proof. cbv delta [T4m1 pm__40]; cbv beta zeta. PM_all40. reflexivity. Qed.
Ltac PM_sub41 t := let t := lazymatch (eval pattern (T4m1 2%nat UStopLe 4 T4_i nobj_i 4) in t) with ?P _ => eval cbv beta in (P pm__40) end in PM_sub40 t.
Ltac PM_all41 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__40_eq; PM_all40.
Definition pm__41 : axst := ltac2:(tb__ "0|0|
S21S6dU0A2").
Lemma pm__41_eq : ltac2:(tb__ "0|0|
S0S3S2dU2S8Z4SeSfZ1A6S71A3"). Proof. cbv delta [T4m2 pm__41]; cbv beta zeta. PM_all41. reflexivity. Qed.
Ltac PM_sub42 t := let t := lazymatch (eval pattern (T4m2 2%nat UStopLe 4 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__41) end in PM_sub41 t.
Ltac PM_all42 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__41_eq; PM_all41.
Definition pm__42 : axst := ltac2:(tb__ "0|0|
S21S6eU0A2").
Lemma pm__42_eq : ltac2:(tb__ "0|0|
S0S3S2dU2S8Z4SeSfZ2A6S72A3"). Proof. cbv delta [T4m2 pm__42]; cbv beta zeta. PM_all42. reflexivity. Qed.
Ltac PM_sub43 t := let t := lazymatch (eval pattern (T4m2 2%nat UStopLe 4 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__42) end in PM_sub42 t.
Ltac PM_all43 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__42_eq; PM_all42.
Definition pm__43 : axst := ltac2:(tb__ "0|0|
S21S6fU0A2").
Lemma pm__43_eq : ltac2:(tb__ "0|0|
S0S3S2dU2S8Z4SeSfZ3A6S73A3"). Proof. cbv delta [T4m2 pm__43]; cbv beta zeta. PM_all43. reflexivity. Qed.
Ltac PM_sub44 t := let t := lazymatch (eval pattern (T4m2 2%nat UStopLe 4 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__43) end in PM_sub43 t.
Ltac PM_all44 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__43_eq; PM_all43.
Definition pm__44 : axst := ltac2:(tb__ "0|0|
S21S70U0A2").
Lemma pm__44_eq : ltac2:(tb__ "0|1|
S0S3S2dU2S8Z4M0SeSfG0A6S74A3"). Proof. cbv delta [T4m2 pm__44]; cbv beta zeta. PM_all44. reflexivity. Qed.
Ltac PM_sub45 t := let t := lazymatch (eval pattern (T4m2 2%nat UStopLe 4 T4_i nobj_i 4) in t) with ?P _ => eval cbv beta in (P pm__44) end in PM_sub44 t.
Ltac PM_all45 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__44_eq; PM_all44.
Definition pm__45 : axst := ltac2:(tb__ "0|0|
S21S71U0A2").
Lemma pm__45_eq : ltac2:(tb__ "0|0|
S0S3S2eU2S8Z4SeSfZ1A6S75A3"). Proof. cbv delta [T4m3 pm__45]; cbv beta zeta. PM_all45. reflexivity. Qed.
Ltac PM_sub46 t := let t := lazymatch (eval pattern (T4m3 2%nat UStopLe 4 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__45) end in PM_sub45 t.
Ltac PM_all46 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__45_eq; PM_all45.
Definition pm__46 : axst := ltac2:(tb__ "0|0|
S21S72U0A2").
Lemma pm__46_eq : ltac2:(tb__ "0|0|
S0S3S2eU2S8Z4SeSfZ2A6S76A3"). Proof. cbv delta [T4m3 pm__46]; cbv beta zeta. PM_all46. reflexivity. Qed.
Ltac PM_sub47 t := let t := lazymatch (eval pattern (T4m3 2%nat UStopLe 4 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__46) end in PM_sub46 t.
Ltac PM_all47 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__46_eq; PM_all46.
Definition pm__47 : axst := ltac2:(tb__ "0|0|
S21S73U0A2").
Lemma pm__47_eq : ltac2:(tb__ "0|0|
S0S3S2eU2S8Z4SeSfZ3A6S77A3"). Proof. cbv delta [T4m3 pm__47]; cbv beta zeta. PM_all47. reflexivity. Qed.
Ltac PM_sub48 t := let t := lazymatch (eval pattern (T4m3 2%nat UStopLe 4 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__47) end in PM_sub47 t.
Ltac PM_all48 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__47_eq; PM_all47.
Definition pm__48 : axst := ltac2:(tb__ "0|0|
S21S74U0A2").
Lemma pm__48_eq : ltac2:(tb__ "0|1|
S0S3S2eU2S8Z4M0SeSfG0A6S78A3"). Proof. cbv delta [T4m3 pm__48]; cbv beta zeta. PM_all48. reflexivity. Qed.
Ltac PM_sub49 t := let t := lazymatch (eval pattern (T4m3 2%nat UStopLe 4 T4_i nobj_i 4) in t) with ?P _ => eval cbv beta in (P pm__48) end in PM_sub48 t.
Ltac PM_all49 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__48_eq; PM_all48.
Definition pm__49 : axst := ltac2:(tb__ "0|0|
S21S75U0A2").
Lemma pm__49_eq : ltac2:(tb__ "0|0|
S0S3S27U2S8Z4SeSfZ1A6S85A3"). Proof. cbv delta [T4d pm__49]; cbv beta zeta. PM_all49. reflexivity. Qed.
Ltac PM_sub50 t := let t := lazymatch (eval pattern (T4d 2%nat UStopLe 4 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__49) end in PM_sub49 t.
Ltac PM_all50 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__49_eq; PM_all49.
Definition pm__50 : axst := ltac2:(tb__ "0|0|
S21S76U0A2").
Lemma pm__50_eq : ltac2:(tb__ "0|0|
S0S3S27U2S8Z4SeSfZ2A6S87A3"). Proof. cbv delta [T4d pm__50]; cbv beta zeta. PM_all50. reflexivity. Qed.
Ltac PM_sub51 t := let t := lazymatch (eval pattern (T4d 2%nat UStopLe 4 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__50) end in PM_sub50 t.
Ltac PM_all51 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__50_eq; PM_all50.
Definition pm__51 : axst := ltac2:(tb__ "0|0|
S21S77U0A2").
Lemma pm__51_eq : ltac2:(tb__ "0|0|
S0S3S27U2S8Z4SeSfZ3A6S88A3"). Proof. cbv delta [T4d pm__51]; cbv beta zeta. PM_all51. reflexivity. Qed.
Ltac PM_sub52 t := let t := lazymatch (eval pattern (T4d 2%nat UStopLe 4 T4_i nobj_i 3) in t) with ?P _ => eval cbv beta in (P pm__51) end in PM_sub51 t.
Ltac PM_all52 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__51_eq; PM_all51.
Definition pm__52 : axst := ltac2:(tb__ "0|0|
S21S78U0A2").
Lemma pm__52_eq : ltac2:(tb__ "0|1|
S0S3S27U2S8Z4M0SeSfG0A6S89A3"). Proof. cbv delta [T4d pm__52]; cbv beta zeta. PM_all52. reflexivity. Qed.
Ltac PM_sub53 t := let t := lazymatch (eval pattern (T4d 2%nat UStopLe 4 T4_i nobj_i 4) in t) with ?P _ => eval cbv beta in (P pm__52) end in PM_sub52 t.
Ltac PM_all53 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__52_eq; PM_all52.
Lemma WX4r_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S44S4S25U2Vst;Vtmax;R2A4A1A1S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX4r_i : ltac2:(tb__ "0|5|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S1dS1aS18S1aS35S35A2M0A1M1S18S36A1M2A2M3A1S90S4S32U2M4Vst;Vtmax;A3A1S4S25G4Vst;Vtmax;R2A4A1A2S1cG3S1eG1G2S1bG0S1eS35S35S43S1fQ20S3cPc0A1A3S38R2A1A4S17G0A1A3S17S36A1A4A2A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S50S4S25U2Vst;Vtmax;R2A4A1U0S38Nee0A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S50S4S2fU2Vst;Vtmax;R2A4A1U1S38N8e0A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S50S4S30U2M0Vst;Vtmax;R2A4A1G0S38N840A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S50S4S31U2Vst;Vtmax;R2A4A1U3S38N48A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HER_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S1dS18S3dA1M0A1S93S22U2Vst;Vtmax;R2A4S55R2A1S10R2A1A3S1cG0S11R2A1A2A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S3S94S10R2A1S55R2A1S54R2A1S22U2Vst;Vtmax;R2A4S11R2A1A5SeR2A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S1aS35S35A2M0A1S5S22U2Vst;Vtmax;R2A4A1S17G0A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S36S3fS3aS4S22U2Vst;Vtmax;R2A4A1M0A1A1S37G0A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S92S22U2Vst;Vtmax;R2A4S55R2A1S10R2A1S11R2A1S1bS3S54R2A1S17S3A1A3A5S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S14S3aS4S22U2M0Vst;Vtmax;R2A4A1A1S3aS4S45S9G0A1Vst;Vtmax;A3A1A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S35S56S10R2A1PaM0A2S40S8eS3cG0A1S38N8e0A1A3A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc | vmc ]. Qed.
Lemma WG15_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S35S56S10R2A1PfA2S38N600A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc | vmc ]. Qed.
Lemma WG12_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S35S56S10R2A1PcA2S40S8eS3cPaA1S38N840A1A3A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc | vmc ]. Qed.
Lemma FAM4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S3dS34U2A1S11R2A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc | vmc ]. Qed.
Lemma NEWO_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S3dA1S91S4S55R2A1A1S4S54R2A1A1A2S17S3dA1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc | vmc ]. Qed.
Lemma XPost_i : ltac2:(tb__ "0|1|
S13S0S18S1aS35S35A2M0A1S5S54R1A1A1S17G0A1A3Fsz;").
Proof. intros sz. reflexivity. Qed.
Lemma FBT4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S36S3fS3aS4SeR2A1A1A1A1S37S4S22U2Vst;Vtmax;R2A4A1A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S1aS35S35A2M0A1S5SeR2A1A1S17G0A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc | vmc ]. Qed.
Lemma RB1_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S51S4S28U2Vst;Vtmax;SeR2A5A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S51S4S29U2Vst;Vtmax;SeR2A5A1U1A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nd_i : ltac2:(tb__ "0|0|
S0S15S4eS26SfA1A1S16A3").
Proof.   vmc. Qed.
Lemma PERM_lt_i : ltac2:(tb__ "0|0|
S0S15S49S19S19S97R1SfA2Li;S26SfA1A3S16A3").
Proof.   vmc. Qed.
Lemma PERM_cov_i : ltac2:(tb__ "0|0|
S0S15S49S19S19S4cS19S96R1A1S26SfA1A3Li;S8fU0SfA2A3S16A3").
Proof.   vmc. Qed.
Lemma PERM_len_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S19S20S3dS3bS4S2aU2Vst;Vtmax;SeR2A5A1A1A2SfA3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S4fS4S2bU2Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S4fS4S2cU2Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S4fS4S2dU2Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S23S39S4fS4S2eU2Vst;Vtmax;SeSfR2A6A1U0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S7S27U2M0Vst;Vtmax;SeSfR2A6S46S9G0A1Vst;Vtmax;A3S12R2A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5_i : ltac2:(tb__ "0|0|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S57S12R2A1S58A2S16A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc | vmc | vmc ]. Qed.
Lemma R4cov_i : ltac2:(tb__ "0|1|
S13S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S95S37S4S27U2Vst;Vtmax;SeSfR2A6A1M0A1S11R2A1S3bG0A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all53; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Htmax_i : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.
Lemma HUS_i : stopJ_stable (Wcan 2) st.
Proof. apply stopJ_stable_le. Qed.
Lemma HUSr_i : ltac2:(tb__ "0|1|
S42S42S14S99R1S58A2S0S9aQ40A1S41R3R2A2S41R4R2A2A3F_;Fi;SdS9U2A1Vst;R3A3M0G0F_;F_;Fr';Fr;").
Proof. intros r r' _ H. exact H. Qed.

End INST.
End DepotCallIW2.

(* [comment removed for export] *)
Module DepotCallHW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@Corelib.Init.Logic"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "HD_stmt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.DepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.DepotCallMW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.DepotCallIW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLe. Let tmax : Z := 4.

Theorem depot_call_HD_2 : ltac2:(tb__ "0|1|
S1S2S0S0A2A1M0G0SeR2A1S10R2A1S0SfR5R1A2S3S11R2A1A1F_;Fa;S4OF_;SdSbS6S5ScR3A1S8S9R6S7R4A1A3S12S9R7S7R5A1A3S14U2Vst;Vtmax;SaRdRcR7A3R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HD 2%nat st tmax HUS_i HUSr_i CST XGL HCST HXGL HCSTD Htmax_i NXE_i FBE_i XE4_i F192_i FDEP_i FUNW_i FGEN4_i YP4_i WX4r_i DX4r_i SPL1_i SPL2_i SPL3_i SPL4_i
           s4_i R4_i T4_i HER_i HT4_i XX4_i FBX4_i Hchk4_i NX4_i WG10_i WG15_i WG12_i FAM4_i NEWO_i XPost_i FBT4_i XT4_i RB1_i RB2_i
           nobj_i PERM_nd_i PERM_lt_i PERM_cov_i PERM_len_i MRG1_i MRG2_i MRG3_i MRG4_i sd_i ENT5_i SID5_i R4cov_i).
Qed.

Theorem depot_call_HDE_2 : ltac2:(tb__ "0|1|
S1S2S0S0A2A1M0G0SeR2A1S10R2A1S0SfR5R1A2S3S11R2A1A1F_;Fa;SdSbS6S4OF_;ScR3A1S13U2Vst;Vtmax;SaRaR9R5A3R5R4R3R2A8F_;FQ;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HDE 2%nat st tmax HUS_i HUSr_i CST XGL HCST HXGL HCSTD Htmax_i NXE_i FBE_i XE4_i F192_i FDEP_i FUNW_i FGEN4_i YP4_i WX4r_i DX4r_i SPL1_i SPL2_i SPL3_i SPL4_i
           s4_i R4_i T4_i HER_i HT4_i XX4_i FBX4_i Hchk4_i NX4_i WG10_i WG15_i WG12_i FAM4_i NEWO_i XPost_i FBT4_i XT4_i RB1_i RB2_i
           nobj_i PERM_nd_i PERM_lt_i PERM_cov_i PERM_len_i MRG1_i MRG2_i MRG3_i MRG4_i sd_i ENT5_i SID5_i R4cov_i).
Qed.
End INST.
End DepotCallHW2.

(* [comment removed for export] *)
Module F0T_aLTA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA"; "q_LTA"; "Ebg_LTA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "pair"; "prod"; "cons"; "false"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "VFACT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTA"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tg"; "P0T_c"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_LTA : ltac2:(tb__ "0|0|
S0S9S1dS3eS16U0A1A1A1SaA3"). Proof. vmr. Qed.
Lemma Da_LTA : ltac2:(tb__ "0|4|
S0S12SeSbSeS1cS1cA2M0A1M1SbS1eA1M2A2M3A1S4bS15S2dS17A1A1S3eS16U0A1A1A2S11G3SdG1G2SfG0SdS1cS1cS21P18A1S20S50A1A4ScG0A1A3ScS1eA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LTA : ltac2:(tb__ "0|0|
S0S9S1dS3fS16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Wc_LTA : ltac2:(tb__ "0|0|
S0S9S1dS40S16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Wd_LTA : ltac2:(tb__ "0|0|
S0S9S1dS41S16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Fb_LTA : ltac2:(tb__ "0|0|
S0S9S5bS1eS22S4fA1S59S10S3dS7A1A2A3SaA3"). Proof. vmr. Qed.
Lemma XI_LTA : ltac2:(tb__ "0|2|
S0S12S14A1S4dS42S10S16U0M0A1S25S7A1M1S3dS7A1A4S51G0S13S4eG1A2A2A2S11S14S5aS10S7A2A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S4S2aS52R2A2S3S2fS46R2A2S31R2S47A2A2A2S2F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S1S58R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S1S57R2A1A1F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_lo_LTA : ltac2:(tb__ "0|2|
S35OF_;S48S19S1fSbS2cQ40M0A1A1S2bG0S1bR2PcA2A2S5S2bG0S1bR3PdA2A2S5S24S6S36R4R3SfSeS14S23A2M1SdS14S23S2eS17A1S18S45S6A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S32S1aR6A1S39S6R9S38R7A1A3S4cS6RaS38R8A1A3S2fS30R6R5A2S43A2S0S9S49RbA1SaA3S29S7RcA2S5S28S3bRfRdRbRaR2R1A6S0S5S27R2A1S44A3S3cRfS26R11RfRdRcR4R3A6A2S55S3aVCST;VXGL;R12A3R13R12R11S26R12R10ReRdR5R4A6S8RcA7F_;F_;F_;Fjv;Ft;S53RfRdA2S34S6R10S37S6S4aRfReA2S2dS17A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF false (Wcan 0) UStopLe q_LTA A rho)); [intros w Hw; exact (entry_pure_T false _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (tq_instantiate false q_LTA Wa_LTA Da_LTA Wb_LTA Wc_LTA Wd_LTA Fb_LTA XI_LTA A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (free_spine_LTA (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR (conj HO (conj E153 HST))
           (hdf_LTA HSEG CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_LTA CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_LTA CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_LTA : ltac2:(tb__ "0|2|
S48S19S1fSbS2cQ40M0A1A1S2bG0S1bR2PcA2A2S5S2bG0S1bR3PdA2A2S5S24S6S36R4R3SfSeS14S23A2M1SdS14S23S2eS17A1S18S45S6A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S32S1aR6A1S2fS30R4R3A2S43A2S0S9S49R9A1SaA3S29S7RaA2S5S28S3bRdRbR9R8R2R1A6S0S5S27R2A1S44A3S3cRdS26RfRdRbRaR4R3A6A2S56S3aVCST;VXGL;R10A3R10RfS26R10ReRcRbR5R4A6S8RaA6F_;F_;F_;Fjv;Ft;S54RbA1S33S6S37S6S4aRdRcA2S2dS17A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureF false (Wcan 0) UStopLe q_LTA A rho)); [intros w Hw; exact (entry_pure_T false _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (tq_instantiate false q_LTA Wa_LTA Da_LTA Wb_LTA Wc_LTA Wd_LTA Fb_LTA XI_LTA A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (efree_spine_LTA (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR (conj HO (conj E153 HST))
           (hdfe_LTA HSEGE CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_LTA CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_LTA CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.
End F0T_aLTA.

(* [comment removed for export] *)
Module F0T_aLTBe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe"; "q_LTBe"; "Ebg_LTBe"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "pair"; "prod"; "cons"; "false"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "VFACT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTBe"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tg"; "P0T_c"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBe.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_LTBe : ltac2:(tb__ "0|0|
S0S9S1dS3eS16U0A1A1A1SaA3"). Proof. vmr. Qed.
Lemma Da_LTBe : ltac2:(tb__ "0|4|
S0S12SeSbSeS1cS1cA2M0A1M1SbS1eA1M2A2M3A1S4bS15S2dS17A1A1S3eS16U0A1A1A2S11G3SdG1G2SfG0SdS1cS1cS21P18A1S20S50A1A4ScG0A1A3ScS1eA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LTBe : ltac2:(tb__ "0|0|
S0S9S1dS3fS16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Wc_LTBe : ltac2:(tb__ "0|0|
S0S9S1dS40S16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Wd_LTBe : ltac2:(tb__ "0|0|
S0S9S1dS41S16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Fb_LTBe : ltac2:(tb__ "0|0|
S0S9S5bS1eS22S4fA1S59S10S3dS7A1A2A3SaA3"). Proof. vmr. Qed.
Lemma XI_LTBe : ltac2:(tb__ "0|2|
S0S12S14A1S4dS42S10S16U0M0A1S25S7A1M1S3dS7A1A4S51G0S13S4eG1A2A2A2S11S14S5aS10S7A2A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S4S2aS52R2A2S3S2fS46R2A2S31R2S47A2A2A2S2F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S1S58R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S1S57R2A1A1F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_lo_LTBe : ltac2:(tb__ "0|2|
S35OF_;S48S19S1fSbS2cQ40M0A1A1S2bG0S1bR2PcA2A2S5S2bG0S1bR3PdA2A2S5S24S6S36R4R3SfSeS14S23A2M1SdS14S23S2eS17A1S18S45S6A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S32S1aR6A1S39S6R9S38R7A1A3S4cS6RaS38R8A1A3S2fS30R6R5A2S43A2S0S9S49RbA1SaA3S29S7RcA2S5S28S3bRfRdRbRaR2R1A6S0S5S27R2A1S44A3S3cRfS26R11RfRdRcR4R3A6A2S55S3aVCST;VXGL;R12A3R13R12R11S26R12R10ReRdR5R4A6S8RcA7F_;F_;F_;Fjv;Ft;S53RfRdA2S34S6R10S37S6S4aRfReA2S2dS17A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF false (Wcan 0) UStopLe q_LTBe A rho)); [intros w Hw; exact (entry_pure_T false _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (tq_instantiate false q_LTBe Wa_LTBe Da_LTBe Wb_LTBe Wc_LTBe Wd_LTBe Fb_LTBe XI_LTBe A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (free_spine_LTBe (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR (conj HO (conj E153 HST))
           (hdf_LTBe HSEG CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_LTBe CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_LTBe CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_LTBe : ltac2:(tb__ "0|2|
S48S19S1fSbS2cQ40M0A1A1S2bG0S1bR2PcA2A2S5S2bG0S1bR3PdA2A2S5S24S6S36R4R3SfSeS14S23A2M1SdS14S23S2eS17A1S18S45S6A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S32S1aR6A1S2fS30R4R3A2S43A2S0S9S49R9A1SaA3S29S7RaA2S5S28S3bRdRbR9R8R2R1A6S0S5S27R2A1S44A3S3cRdS26RfRdRbRaR4R3A6A2S56S3aVCST;VXGL;R10A3R10RfS26R10ReRcRbR5R4A6S8RaA6F_;F_;F_;Fjv;Ft;S54RbA1S33S6S37S6S4aRdRcA2S2dS17A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureF false (Wcan 0) UStopLe q_LTBe A rho)); [intros w Hw; exact (entry_pure_T false _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (tq_instantiate false q_LTBe Wa_LTBe Da_LTBe Wb_LTBe Wc_LTBe Wd_LTBe Fb_LTBe XI_LTBe A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (efree_spine_LTBe (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR (conj HO (conj E153 HST))
           (hdfe_LTBe HSEGE CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_LTBe CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_LTBe CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.
End F0T_aLTBe.

(* [comment removed for export] *)
Module F0T_aLTBf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf"; "q_LTBf"; "Ebg_LTBf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "pair"; "prod"; "cons"; "false"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "VFACT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iLTBf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tg"; "P0T_c"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_LTBf : ltac2:(tb__ "0|0|
S0S9S1dS3eS16U0A1A1A1SaA3"). Proof. vmr. Qed.
Lemma Da_LTBf : ltac2:(tb__ "0|4|
S0S12SeSbSeS1cS1cA2M0A1M1SbS1eA1M2A2M3A1S4bS15S2dS17A1A1S3eS16U0A1A1A2S11G3SdG1G2SfG0SdS1cS1cS21P18A1S20S50A1A4ScG0A1A3ScS1eA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LTBf : ltac2:(tb__ "0|0|
S0S9S1dS3fS16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Wc_LTBf : ltac2:(tb__ "0|0|
S0S9S1dS40S16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Wd_LTBf : ltac2:(tb__ "0|0|
S0S9S1dS41S16U0A1S25S7A1A2A1SaA3"). Proof. vmr. Qed.
Lemma Fb_LTBf : ltac2:(tb__ "0|0|
S0S9S5bS1eS22S4fA1S59S10S3dS7A1A2A3SaA3"). Proof. vmr. Qed.
Lemma XI_LTBf : ltac2:(tb__ "0|2|
S0S12S14A1S4dS42S10S16U0M0A1S25S7A1M1S3dS7A1A4S51G0S13S4eG1A2A2A2S11S14S5aS10S7A2A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S4S2aS52R2A2S3S2fS46R2A2S31R2S47A2A2A2S2F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S1S58R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S2aVCST;R1A2S1S57R2A1A1F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_lo_LTBf : ltac2:(tb__ "0|2|
S35OF_;S48S19S1fSbS2cQ40M0A1A1S2bG0S1bR2PcA2A2S5S2bG0S1bR3PdA2A2S5S24S6S36R4R3SfSeS14S23A2M1SdS14S23S2eS17A1S18S45S6A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S32S1aR6A1S39S6R9S38R7A1A3S4cS6RaS38R8A1A3S2fS30R6R5A2S43A2S0S9S49RbA1SaA3S29S7RcA2S5S28S3bRfRdRbRaR2R1A6S0S5S27R2A1S44A3S3cRfS26R11RfRdRcR4R3A6A2S55S3aVCST;VXGL;R12A3R13R12R11S26R12R10ReRdR5R4A6S8RcA7F_;F_;F_;Fjv;Ft;S53RfRdA2S34S6R10S37S6S4aRfReA2S2dS17A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF false (Wcan 0) UStopLe q_LTBf A rho)); [intros w Hw; exact (entry_pure_T false _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (tq_instantiate false q_LTBf Wa_LTBf Da_LTBf Wb_LTBf Wc_LTBf Wd_LTBf Fb_LTBf XI_LTBf A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (free_spine_LTBf (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR (conj HO (conj E153 HST))
           (hdf_LTBf HSEG CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_LTBf CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_LTBf CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_LTBf : ltac2:(tb__ "0|2|
S48S19S1fSbS2cQ40M0A1A1S2bG0S1bR2PcA2A2S5S2bG0S1bR3PdA2A2S5S24S6S36R4R3SfSeS14S23A2M1SdS14S23S2eS17A1S18S45S6A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S32S1aR6A1S2fS30R4R3A2S43A2S0S9S49R9A1SaA3S29S7RaA2S5S28S3bRdRbR9R8R2R1A6S0S5S27R2A1S44A3S3cRdS26RfRdRbRaR4R3A6A2S56S3aVCST;VXGL;R10A3R10RfS26R10ReRcRbR5R4A6S8RaA6F_;F_;F_;Fjv;Ft;S54RbA1S33S6S37S6S4aRdRcA2S2dS17A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureF false (Wcan 0) UStopLe q_LTBf A rho)); [intros w Hw; exact (entry_pure_T false _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (tq_instantiate false q_LTBf Wa_LTBf Da_LTBf Wb_LTBf Wc_LTBf Wd_LTBf Fb_LTBf XI_LTBf A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (efree_spine_LTBf (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR (conj HO (conj E153 HST))
           (hdfe_LTBf HSEGE CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_LTBf CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_LTBf CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.
End F0T_aLTBf.

(* [comment removed for export] *)
Module F0T_aTA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA"; "q_TA"; "Ebg_TA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "VFACT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTA"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tg"; "P0T_c"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xiTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_TA : ltac2:(tb__ "0|0|
S0S7S1cS3dS15U0A1A1A1S6A3"). Proof. vmr. Qed.
Lemma Da_TA : ltac2:(tb__ "0|4|
S0SeSbS8SbS1bS1bA2M0A1M1S8S1dA1M2A2M3A1S4aS14S2cS16A1A1S3dS15U0A1A1A2SdG3SaG1G2ScG0SaS1bS1bS20P18A1S1fS4fA1A4S9G0A1A3S9S1dA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_TA : ltac2:(tb__ "0|0|
S0S7S1cS3eS15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Wc_TA : ltac2:(tb__ "0|0|
S0S7S1cS3fS15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Wd_TA : ltac2:(tb__ "0|0|
S0S7S1cS40S15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Fb_TA : ltac2:(tb__ "0|0|
S0S7S5aS1dS21S4eA1S58S6S3cS11A1A2A3S6A3"). Proof. vmr. Qed.
Lemma XI_TA : ltac2:(tb__ "0|2|
S0SeS13A1S4cS41S6S15U0M0A1S24S11A1M1S3cS11A1A4S50G0SfS4dG1A2A2A2SdS13S59S6S11A2A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S4S29S51R2A2S3S2eS45R2A2S30R2S46A2A2A2S2F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S1S57R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S1S56R2A1A1F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_hi_TA : ltac2:(tb__ "0|2|
S34OF_;S47S18S1eS8S2bQ40M0A1A1S2aG0S1aR2PcA2A2S5S2aG0S1aR3PdA2A2S5S23S10S35R4R3ScSbS13S22A2M1SaS13S22S2dS16A1S17S44S10A1VCST;VXGL;R6R5A5A4S9G1A1A3A5S31S19R6A1S38S10R9S37R7A1A3S4bS10RaS37R8A1A3S2eS42S2fR6Z10A2A2S0S7S48RbA1S6A3S28S11RcA2S5S27S3aRfRdRbRaR2R1A6S0S5S26R2A1S43A3S3bRfS25R11RfRdRcR4R3A6A2S54S39VCST;VXGL;R12A3R13R12R11S25R12R10ReRdR5R4A6S12RcA7F_;F_;F_;Fjv;Ft;S52RfRdA2S33S10R10S36S10S49RfReA2S2cS16A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 0) UStopLe q_TA A rho)); [intros w Hw; exact (entry_pure_T true _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (tq_instantiate true q_TA Wa_TA Da_TA Wb_TA Wc_TA Wd_TA Fb_TA XI_TA A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (free_spine_TA (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR (conj HO (conj E153 HST))
           (hdf_TA HSEG CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_TA CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_TA CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_TA : ltac2:(tb__ "0|2|
S47S18S1eS8S2bQ40M0A1A1S2aG0S1aR2PcA2A2S5S2aG0S1aR3PdA2A2S5S23S10S35R4R3ScSbS13S22A2M1SaS13S22S2dS16A1S17S44S10A1VCST;VXGL;R6R5A5A4S9G1A1A3A5S31S19R6A1S2eS42S2fR4Z10A2A2S0S7S48R9A1S6A3S28S11RaA2S5S27S3aRdRbR9R8R2R1A6S0S5S26R2A1S43A3S3bRdS25RfRdRbRaR4R3A6A2S55S39VCST;VXGL;R10A3R10RfS25R10ReRcRbR5R4A6S12RaA6F_;F_;F_;Fjv;Ft;S53RbA1S32S10S36S10S49RdRcA2S2cS16A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 0) UStopLe q_TA A rho)); [intros w Hw; exact (entry_pure_T true _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (tq_instantiate true q_TA Wa_TA Da_TA Wb_TA Wc_TA Wd_TA Fb_TA XI_TA A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (efree_spine_TA (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR (conj HO (conj E153 HST))
           (hdfe_TA HSEGE CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_TA CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_TA CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.
End F0T_aTA.

