(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_059.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc cg.

(* [comment removed for export] *)
Module SpineCallocSec5I.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "leafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "X5s"; "WI"; "T5d"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "C5S"; "coveredbL"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I.INST"; "X5ac"; "X5bc"; "T4a_i"; "T4b_i"; "nobja"; "nobjb"; "U4ac"; "U4bc"; "s4a_i"; "s4b_i"; "R4a_i"; "R4b_i"; "pm__15"; "pm__16"; "pm__43"; "pm__44"; "C5ac"; "C5bc"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__37"; "pm__38"; "pm__39"; "pm__40"; "pm__41"; "pm__42"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__49"; "pm__50"; "pm__51"; "pm__52"; "pm__9"; "sda_i"; "sdb_i"; "CPa1"; "CPa2"; "CPb1"; "CPb2"; "EXoa"; "EXob"; "pm__0"; "pm__1"; "pm__2"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__29"; "pm__3"; "pm__30"; "pm__31"; "pm__32"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__4"; "pm__5"; "pm__53"; "pm__54"; "pm__55"; "pm__6"; "pm__7"; "pm__8"; "run5a"; "run5b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "S"; "nat"; "option"; "pair"; "Some"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_facts"; "ss_next"; "SVar"; "ss_objs"; "sprop_below"; "SAlu"; "SPUle"; "swf"; "SExt"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "isSome"; "O_1"; "O_2"; "O_blk"; "O_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "omrg"; "oreb"; "F_call"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4I"; "T4ac"; "T4bc"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

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
Module SpineCallocSec5IW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "entailsA"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "X5s"; "WI"; "T5d"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "C5S"; "coveredbL"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1.INST"; "X5ac"; "X5bc"; "T4a_i"; "T4b_i"; "nobja"; "nobjb"; "U4ac"; "U4bc"; "s4a_i"; "s4b_i"; "R4a_i"; "R4b_i"; "pm__22"; "pm__23"; "pm__24"; "pm__63"; "pm__64"; "pm__65"; "C5ac"; "C5bc"; "pm__13"; "pm__14"; "pm__15"; "pm__16"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__29"; "pm__30"; "pm__31"; "pm__32"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__54"; "pm__55"; "pm__56"; "pm__57"; "pm__58"; "pm__59"; "pm__60"; "pm__61"; "pm__62"; "pm__66"; "pm__67"; "pm__68"; "pm__69"; "pm__70"; "pm__71"; "pm__72"; "pm__73"; "pm__74"; "pm__75"; "pm__76"; "pm__77"; "sda_i"; "sdb_i"; "CPa1"; "CPa2"; "CPb1"; "CPb2"; "EXoa"; "EXob"; "pm__0"; "pm__1"; "pm__10"; "pm__11"; "pm__12"; "pm__2"; "pm__3"; "pm__37"; "pm__38"; "pm__39"; "pm__4"; "pm__40"; "pm__41"; "pm__42"; "pm__43"; "pm__44"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__49"; "pm__5"; "pm__50"; "pm__51"; "pm__52"; "pm__53"; "pm__6"; "pm__7"; "pm__78"; "pm__79"; "pm__8"; "pm__80"; "pm__81"; "pm__9"; "run5a"; "run5b"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "S"; "nat"; "option"; "pair"; "Some"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "ss_facts"; "sstate"; "ss_next"; "SVar"; "ss_objs"; "sprop_below"; "SAlu"; "SPUle"; "swf"; "SExt"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "omrg"; "oreb"; "F_call"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "isSome"; "O_1"; "O_2"; "O_blk"; "O_w"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IW1"; "T4ac"; "T4bc"; "@Corelib.Lists.ListDef";
"seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Lemma by_cases12 : ltac2:(tb__ "0|2|
S87OF_;R1Z1M0A1R2Z2A1R3Z3M1A1S87S1S2G0R1A2S2R1G1A2A2R6R2A1F_;Fsz;F_;F_;F_;FP;").
Proof. intros P H1 H2 H3 sz Hsz. assert (E : sz = 1 \/ sz = 2 \/ sz = 3) by lia. destruct E as [-> | [-> | ->]]; assumption. Qed.
Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
S91S8eS8eSbbS8dS98A1M0A2S4A2M1A1G1Lo;Vo;G1R1Lx;S92S8eS8dS8eS88S96A2M2A1M3G0A2S4S92G3G0S8bG2A1S8bS98A1A4Sb2Z0A1A4X91x2").
Lemma Htmax_0 : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.

Definition U4ac : axst := Eval vm_compute in (U4p nx0 T4ac).
Lemma WU4a_0 : ltac2:(tb__ "0|0|
S0S89Sa2S5S23A1A1S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4a_0 : ltac2:(tb__ "0|4|
S0S91S8eS8dS8eS96S96A2M0A1M1S8dS97A1M2A2M3A1Sc1S5Sc5A1S5S23A1A2S93G3S92G1G2S8bG0A1Sc3Sb7A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4a_0 : ltac2:(tb__ "0|0|
S0S88S9cS5S23A1A1S9cS5Sc5A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4a_0 : ltac2:(tb__ "0|0|
S0S4S6Sc5S5S23A1A2S23A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5a : option (list leafA) := Eval vm_compute in (runT5 U4ac).
Lemma run5a__runeq : ltac2:(tb__ "0|1|
S0S8dS91S8dS9A1A1M0A1ScbSc4Ufa0S8cS87Sc2S8bS87A1A3S8cS4S23S8bS4A1A3A4S8cG0S85S8bG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5a]). Qed.
Definition X5ac : axst := Eval vm_compute in (leafS 0 run5a).
Lemma Cert5a_0 : ltac2:(tb__ "0|1|
S0S89ScaSc4Ufa0S8cS87Sc2S8bS87A1A3VGS0;S8cS4S23S8bS4A1M0A3S8cS4S1dG0A3A6S8aA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4ac] [X5ac] [run5a]); [exact run5a__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5ac : axst := Eval vm_compute in (C5S X5ac).

Definition CPa1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 1) 1)).
Definition CPa2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 2) 2)).
Definition CPa (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
S89S8eS8eSbbS8dS98A1A2S4A2L_;S3Vsz;Z1A2S5dS5eX89x2").
Definition s4a_i (sz : Z) : wsub := fst (fst (CPa sz)).
Definition R4a_i (sz : Z) : list sobj := snd (fst (CPa sz)).
Definition T4a_i (sz : Z) : axst := snd (CPa sz).
Definition nobja : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4a_i 1) (X5s X5ac 1))))).
Definition sda_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
Sc8VGS0;S5ScS21S1fVsz;A1SaS1dVsz;A2A3A1S5S2fA1A3").
Definition EXoa : list sobj := ltac2:(tb__ "0|0|
S8cS98SabSb7A1S8cS98SaaSb7A1S8cS98SacS8bS98A1A3A3A3").

Lemma NXEa_0 : ltac2:(tb__ "0|0|
S0S89Sd6VGS0;S9cS5S1dA1A1A2S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEa_0 : ltac2:(tb__ "0|0|
S0S89SaeS97S9fS9cS5S1dA1A1A1Sa8A3S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5a_0 : ax_X X5ac = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192a_0 : ltac2:(tb__ "0|1|
SafS97S8cS97Sa1S99Z1A1S9dPc0A1M0A2S8cS97Sa1G0S99Vtmax;A1A2S8bS97A1A3A3S9aS5S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPa_0 : ltac2:(tb__ "0|0|
SafS97Sd2Sd1A1S9aS5S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWa_0 : ltac2:(tb__ "0|0|
SafS97Sd3VW;Vst;A2S9aS5S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBa_0 : ltac2:(tb__ "0|0|
Sb0S97Sa4Sc0S9dScfA1S9dSd0A1A3S9aS5S1dA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Ltac PM_sub0 t := t.
Ltac PM_all0 := idtac.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S4S19S1dA1S63A3"). Proof. cbv delta [X5f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X5f X5ac) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S4SdS1dZ1A2S64A3"). Proof. cbv delta [X5r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X5r X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|0|
S0S4SdS1dZ2A2S68A3"). Proof. cbv delta [X5r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X5r X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S4SdS1dZ3A2S69A3"). Proof. cbv delta [X5r pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X5r X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|0|
S0S4S16S1dZ1A2S6dA3"). Proof. cbv delta [X5a pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X5a X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S4S16S1dZ2A2S78A3"). Proof. cbv delta [X5a pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X5a X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|0|
S0S4S16S1dZ3A2S7dA3"). Proof. cbv delta [X5a pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X5a X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S4S17S1dZ1A2S7eA3"). Proof. cbv delta [X5b pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X5b X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|0|
S0S4S17S1dZ2A2S81A3"). Proof. cbv delta [X5b pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X5b X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S4S17S1dZ3A2S84A3"). Proof. cbv delta [X5b pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X5b X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|0|
S0S4S18S1dZ1A2S65A3"). Proof. cbv delta [X5c pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X5c X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub11 t in exact t).
Lemma pm__11_eq : ltac2:(tb__ "0|0|
S0S4S18S1dZ2A2S66A3"). Proof. cbv delta [X5c pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (X5c X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub12 t in exact t).
Lemma pm__12_eq : ltac2:(tb__ "0|0|
S0S4S18S1dZ3A2S67A3"). Proof. cbv delta [X5c pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (X5c X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub13 t in exact t).
Lemma pm__13_eq : ltac2:(tb__ "0|0|
S0S4SaS1dZ1A2S31A3"). Proof. cbv delta [X5s pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (X5s X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub14 t in exact t).
Lemma pm__14_eq : ltac2:(tb__ "0|0|
S0S4SaS1dZ2A2S32A3"). Proof. cbv delta [X5s pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (X5s X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub15 t in exact t).
Lemma pm__15_eq : ltac2:(tb__ "0|0|
S0S4SaS1dZ3A2S33A3"). Proof. cbv delta [X5s pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (X5s X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac2:(tb__ "0|0|
SbeS1fZ1A1S9aS5S31A1A1A2").
Lemma pm__16_eq : ltac2:(tb__ "0|1|
S0S4SfS1fZ1M0A1SaS1dG0A2A2S34A3"). Proof. cbv delta [T50 pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (T50 (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac2:(tb__ "0|0|
SbeS1fZ2A1S9aS5S32A1A1A2").
Lemma pm__17_eq : ltac2:(tb__ "0|1|
S0S4SfS1fZ2M0A1SaS1dG0A2A2S35A3"). Proof. cbv delta [T50 pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (T50 (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac2:(tb__ "0|0|
SbeS1fZ3A1S9aS5S33A1A1A2").
Lemma pm__18_eq : ltac2:(tb__ "0|1|
S0S4SfS1fZ3M0A1SaS1dG0A2A2S36A3"). Proof. cbv delta [T50 pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (T50 (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac2:(tb__ "0|0|
Sa7S34U0A2").
Lemma pm__19_eq : ltac2:(tb__ "0|1|
S0S4S10S1fZ1M0A1SaS1dG0A2A2S37A3"). Proof. cbv delta [T5a pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (T5a (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac2:(tb__ "0|0|
Sa7S35U0A2").
Lemma pm__20_eq : ltac2:(tb__ "0|1|
S0S4S10S1fZ2M0A1SaS1dG0A2A2S38A3"). Proof. cbv delta [T5a pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (T5a (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
Sa7S36U0A2").
Lemma pm__21_eq : ltac2:(tb__ "0|1|
S0S4S10S1fZ3M0A1SaS1dG0A2A2S39A3"). Proof. cbv delta [T5a pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T5a (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
Sa7S37U1A2").
Lemma pm__22_eq : ltac2:(tb__ "0|1|
S0S4S11S1fZ1M0A1SaS1dG0A2A2S29A3"). Proof. cbv delta [T5b pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T5b (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
Sa7S38U1A2").
Lemma pm__23_eq : ltac2:(tb__ "0|1|
S0S4S11S1fZ2M0A1SaS1dG0A2A2S2aA3"). Proof. cbv delta [T5b pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T5b (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
Sa7S39U1A2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S4S11S1fZ3M0A1SaS1dG0A2A2S2bA3"). Proof. cbv delta [T5b pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T5b (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|1|
S6S29SbdS5S29A1M0Sb8S9eG0A1SeS21A1A2A2A2").
Lemma pm__25_eq : ltac2:(tb__ "0|1|
S0S4S12S21S1fZ1M0A1SaS1dG0A2A3S3aA3"). Proof. cbv delta [T5c pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|1|
S6S2aSbdS5S2aA1M0Sb8S9eG0A1SeS21A1A2A2A2").
Lemma pm__26_eq : ltac2:(tb__ "0|1|
S0S4S12S21S1fZ2M0A1SaS1dG0A2A3S3bA3"). Proof. cbv delta [T5c pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Definition pm__27 : axst := ltac2:(tb__ "0|1|
S6S2bSbdS5S2bA1M0Sb8S9eG0A1SeS21A1A2A2A2").
Lemma pm__27_eq : ltac2:(tb__ "0|1|
S0S4S12S21S1fZ3M0A1SaS1dG0A2A3S3cA3"). Proof. cbv delta [T5c pm__27]; cbv beta zeta. PM_all27. reflexivity. Qed.
Ltac PM_sub28 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__27) end in PM_sub27 t.
Ltac PM_all28 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__27_eq; PM_all27.
Definition pm__28 : axst := ltac2:(tb__ "0|0|
Sa6S3aSbA2").
Lemma pm__28_eq : ltac2:(tb__ "0|1|
S0S4S13S21S1fZ1M0A1SaS1dG0A2A3S3dA3"). Proof. cbv delta [T5m1 pm__28]; cbv beta zeta. PM_all28. reflexivity. Qed.
Ltac PM_sub29 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__28) end in PM_sub28 t.
Ltac PM_all29 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__28_eq; PM_all28.
Definition pm__29 : axst := ltac2:(tb__ "0|0|
Sa6S3bSbA2").
Lemma pm__29_eq : ltac2:(tb__ "0|1|
S0S4S13S21S1fZ2M0A1SaS1dG0A2A3S3eA3"). Proof. cbv delta [T5m1 pm__29]; cbv beta zeta. PM_all29. reflexivity. Qed.
Ltac PM_sub30 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__29) end in PM_sub29 t.
Ltac PM_all30 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__29_eq; PM_all29.
Definition pm__30 : axst := ltac2:(tb__ "0|0|
Sa6S3cSbA2").
Lemma pm__30_eq : ltac2:(tb__ "0|1|
S0S4S13S21S1fZ3M0A1SaS1dG0A2A3S3fA3"). Proof. cbv delta [T5m1 pm__30]; cbv beta zeta. PM_all30. reflexivity. Qed.
Ltac PM_sub31 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__30) end in PM_sub30 t.
Ltac PM_all31 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__30_eq; PM_all30.
Definition pm__31 : axst := ltac2:(tb__ "0|0|
Sa6S3dSbA2").
Lemma pm__31_eq : ltac2:(tb__ "0|1|
S0S4S14S21S1fZ1M0A1SaS1dG0A2A3S40A3"). Proof. cbv delta [T5m2 pm__31]; cbv beta zeta. PM_all31. reflexivity. Qed.
Ltac PM_sub32 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__31) end in PM_sub31 t.
Ltac PM_all32 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__31_eq; PM_all31.
Definition pm__32 : axst := ltac2:(tb__ "0|0|
Sa6S3eSbA2").
Lemma pm__32_eq : ltac2:(tb__ "0|1|
S0S4S14S21S1fZ2M0A1SaS1dG0A2A3S41A3"). Proof. cbv delta [T5m2 pm__32]; cbv beta zeta. PM_all32. reflexivity. Qed.
Ltac PM_sub33 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__32) end in PM_sub32 t.
Ltac PM_all33 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__32_eq; PM_all32.
Definition pm__33 : axst := ltac2:(tb__ "0|0|
Sa6S3fSbA2").
Lemma pm__33_eq : ltac2:(tb__ "0|1|
S0S4S14S21S1fZ3M0A1SaS1dG0A2A3S42A3"). Proof. cbv delta [T5m2 pm__33]; cbv beta zeta. PM_all33. reflexivity. Qed.
Ltac PM_sub34 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__33) end in PM_sub33 t.
Ltac PM_all34 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__33_eq; PM_all33.
Definition pm__34 : axst := ltac2:(tb__ "0|0|
Sa6S40SbA2").
Lemma pm__34_eq : ltac2:(tb__ "0|1|
S0S4S15S21S1fZ1M0A1SaS1dG0A2A3S43A3"). Proof. cbv delta [T5m3 pm__34]; cbv beta zeta. PM_all34. reflexivity. Qed.
Ltac PM_sub35 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__34) end in PM_sub34 t.
Ltac PM_all35 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__34_eq; PM_all34.
Definition pm__35 : axst := ltac2:(tb__ "0|0|
Sa6S41SbA2").
Lemma pm__35_eq : ltac2:(tb__ "0|1|
S0S4S15S21S1fZ2M0A1SaS1dG0A2A3S44A3"). Proof. cbv delta [T5m3 pm__35]; cbv beta zeta. PM_all35. reflexivity. Qed.
Ltac PM_sub36 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__35) end in PM_sub35 t.
Ltac PM_all36 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__35_eq; PM_all35.
Definition pm__36 : axst := ltac2:(tb__ "0|0|
Sa6S42SbA2").
Lemma pm__36_eq : ltac2:(tb__ "0|1|
S0S4S15S21S1fZ3M0A1SaS1dG0A2A3S45A3"). Proof. cbv delta [T5m3 pm__36]; cbv beta zeta. PM_all36. reflexivity. Qed.
Ltac PM_sub37 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__36) end in PM_sub36 t.
Ltac PM_all37 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__36_eq; PM_all36.
Definition pm__37 : axst := ltac2:(tb__ "0|0|
Sa6S43SbA2").
Lemma pm__37_eq : ltac2:(tb__ "0|1|
S0S4ScS21S1fZ1M0A1SaS1dG0A2A3S6aA3"). Proof. cbv delta [T5d pm__37]; cbv beta zeta. PM_all37. reflexivity. Qed.
Ltac PM_sub38 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__37) end in PM_sub37 t.
Ltac PM_all38 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__37_eq; PM_all37.
Definition pm__38 : axst := ltac2:(tb__ "0|0|
Sa6S44SbA2").
Lemma pm__38_eq : ltac2:(tb__ "0|1|
S0S4ScS21S1fZ2M0A1SaS1dG0A2A3S6bA3"). Proof. cbv delta [T5d pm__38]; cbv beta zeta. PM_all38. reflexivity. Qed.
Ltac PM_sub39 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__38) end in PM_sub38 t.
Ltac PM_all39 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__38_eq; PM_all38.
Definition pm__39 : axst := ltac2:(tb__ "0|0|
Sa6S45SbA2").
Lemma pm__39_eq : ltac2:(tb__ "0|1|
S0S4ScS21S1fZ3M0A1SaS1dG0A2A3S6cA3"). Proof. cbv delta [T5d pm__39]; cbv beta zeta. PM_all39. reflexivity. Qed.
Ltac PM_sub40 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__39) end in PM_sub39 t.
Ltac PM_all40 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__39_eq; PM_all39.
Definition pm__40 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub40 t in exact t).
Lemma pm__40_eq : ltac2:(tb__ "0|0|
S0S4S1aS1dA1S6eA3"). Proof. cbv delta [C5S pm__40]; cbv beta zeta. PM_all40. reflexivity. Qed.
Ltac PM_sub41 t := let t := lazymatch (eval pattern (C5S X5ac) in t) with ?P _ => eval cbv beta in (P pm__40) end in PM_sub40 t.
Ltac PM_all41 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__40_eq; PM_all40.
Lemma WX5ra_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa2S5SdS1dR2A2A1A1S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5ra_0 : ltac2:(tb__ "0|4|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S91S8eS8dS8eS96S96A2M0A1M1S8dS97A1M2A2M3A1Sc1S5S19S1dA1A1S5SdS1dR2A2A1A2S93G3S92G1G2S8cG0S92S96S96Sa3S94Q20S9dPc0A1A3S99R2A1A4S8bG0A1A3S8bS97A1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5SdS1dR2A2A1SbS99Nf10A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5S16S1dR2A2A1S8fSbA1S99N910A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5S17S1dR2A2A1S8fS8fSbA1A1S99N848A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5S18S1dR2A2A1S8fS8fS8fSbA1A1A1S99N50A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERa_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S91S8dS98A1M0A1ScdSaS1dR2A2Sb2R2A1S25R2A1A3S93G0S27R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S4SceS25R2A1Sb2R2A1Sb3R2A1SaS1dR2A2S27R2A1A5S1fR2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4a_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S8dS8eS96S96A2M0A1S7SaS1dR2A2A1S8bG0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4a_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SaeS97S9fS9cS5SaS1dR2A2A1M0A1A1S9aG0A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SccSaS1dR2A2Sb2R2A1S25R2A1S27R2A1S8cS4Sb3R2A1S8bS4A1A3A5S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S88S9cS5SaS1dR2A2A1A1S9cS5S1dA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10a_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S96SbaS25R2A1PaM0A2Sa0SbfS9dG0A1S99N910A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S96SbaS25R2A1PfA2S99N600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S96SbaS25R2A1PcA2Sa0SbfS9dPaA1S99N848A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SaeS98S1cU1Sb7S61A3S27R2A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOa_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S8dS98A1Sc9S5Sb2R2A1A1S5Sb3R2A1A1A2S8bS98A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPosta_0 : ltac2:(tb__ "0|1|
S87S0S8dS8eS96S96A2M0A1S7Sb3R1A1A1S8bG0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SaeS97S9fS9cS5S1fR2A1A1A1A1S9aS5SaS1dR2A2A1A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4a_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S8dS8eS96S96A2M0A1S7S1fR2A1A1S8bG0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb6S5SfS1fR2A1SaS1dR2A2A2A1U0A2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb6S5S10S1fR2A1SaS1dR2A2A2A1U1A2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nda_0 : ltac2:(tb__ "0|0|
S0S89Sb9SeS21A1A1S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lta_0 : ltac2:(tb__ "0|0|
S0S89SaeS90S90Sd5R1S21A2Li;SeS21A1A3S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_cova_0 : ltac2:(tb__ "0|0|
S0S89SaeS90S90Sb1S90Sd4R1A1SeS21A1A3Li;Sc7U0S21A2A3S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lena_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S90S95S98S9eS5S11S1fR2A1SaS1dR2A2A2A1A1A2S21A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S12S21S1fR2A1SaS1dR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S13S21S1fR2A1SaS1dR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S14S21S1fR2A1SaS1dR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S15S21S1fR2A1SaS1dR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89S8ScS21S1fR2A1SaS1dR2A2A3S2fS5bR2A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5a_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SbcS5bR2A1VGS0;A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4cova_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89S1bS9aS5ScS21S1fR2A1SaS1dR2A2A3A1M0A1S27R2A1S9eG0A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all41; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

Definition U4bc : axst := Eval vm_compute in (U4p nx0 T4bc).
Lemma WU4b_0 : ltac2:(tb__ "0|0|
S0S89Sa2S5S24A1A1S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4b_0 : ltac2:(tb__ "0|4|
S0S91S8eS8dS8eS96S96A2M0A1M1S8dS97A1M2A2M3A1Sc1S5Sc6A1S5S24A1A2S93G3S92G1G2S8bG0A1Sc3Sb7A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4b_0 : ltac2:(tb__ "0|0|
S0S88S9cS5S24A1A1S9cS5Sc6A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4b_0 : ltac2:(tb__ "0|0|
S0S4S6Sc6S5S24A1A2S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5b : option (list leafA) := Eval vm_compute in (runT5 U4bc).
Lemma run5b__runeq : ltac2:(tb__ "0|1|
S0S8dS91S8dS9A1A1M0A1ScbSc4Ufa0S8cS87Sc2S8bS87A1A3S8cS4S24S8bS4A1A3A4S8cG0S86S8bG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5b]). Qed.
Definition X5bc : axst := Eval vm_compute in (leafS 0 run5b).
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S0S89ScaSc4Ufa0S8cS87Sc2S8bS87A1A3VGS0;S8cS4S24S8bS4A1M0A3S8cS4S1eG0A3A6S8aA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4bc] [X5bc] [run5b]); [exact run5b__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5bc : axst := Eval vm_compute in (C5S X5bc).

Definition CPb1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 1) 1)).
Definition CPb2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 2) 2)).
Definition CPb (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
S89S8eS8eSbbS8dS98A1A2S4A2L_;S3Vsz;Z1A2S5fS60X89x2").
Definition s4b_i (sz : Z) : wsub := fst (fst (CPb sz)).
Definition R4b_i (sz : Z) : list sobj := snd (fst (CPb sz)).
Definition T4b_i (sz : Z) : axst := snd (CPb sz).
Definition nobjb : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4b_i 1) (X5s X5bc 1))))).
Definition sdb_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
Sc8VGS0;S5ScS22S20Vsz;A1SaS1eVsz;A2A3A1S5S30A1A3").
Definition EXob : list sobj := ltac2:(tb__ "0|0|
S8cS98SabSb7A1S8cS98SaaSb7A1S8cS98SadS8bS98A1A3A3A3").

Lemma NXEb_0 : ltac2:(tb__ "0|0|
S0S89Sd6VGS0;S9cS5S1eA1A1A2S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEb_0 : ltac2:(tb__ "0|0|
S0S89SaeS97S9fS9cS5S1eA1A1A1Sa8A3S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5b_0 : ax_X X5bc = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192b_0 : ltac2:(tb__ "0|1|
SafS97S8cS97Sa1S99Z1A1S9dPc0A1M0A2S8cS97Sa1G0S99Vtmax;A1A2S8bS97A1A3A3S9aS5S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPb_0 : ltac2:(tb__ "0|0|
SafS97Sd2Sd1A1S9aS5S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWb_0 : ltac2:(tb__ "0|0|
SafS97Sd3VW;Vst;A2S9aS5S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBb_0 : ltac2:(tb__ "0|0|
Sb0S97Sa5Sa4Sc0S9dScfA1S9dSd0A1A3A1S9aS5S1eA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pm__41 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub41 t in exact t).
Lemma pm__41_eq : ltac2:(tb__ "0|0|
S0S4S19S1eA1S6fA3"). Proof. cbv delta [X5f pm__41]; cbv beta zeta. PM_all41. reflexivity. Qed.
Ltac PM_sub42 t := let t := lazymatch (eval pattern (X5f X5bc) in t) with ?P _ => eval cbv beta in (P pm__41) end in PM_sub41 t.
Ltac PM_all42 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__41_eq; PM_all41.
Definition pm__42 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub42 t in exact t).
Lemma pm__42_eq : ltac2:(tb__ "0|0|
S0S4SdS1eZ1A2S70A3"). Proof. cbv delta [X5r pm__42]; cbv beta zeta. PM_all42. reflexivity. Qed.
Ltac PM_sub43 t := let t := lazymatch (eval pattern (X5r X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__42) end in PM_sub42 t.
Ltac PM_all43 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__42_eq; PM_all42.
Definition pm__43 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub43 t in exact t).
Lemma pm__43_eq : ltac2:(tb__ "0|0|
S0S4SdS1eZ2A2S71A3"). Proof. cbv delta [X5r pm__43]; cbv beta zeta. PM_all43. reflexivity. Qed.
Ltac PM_sub44 t := let t := lazymatch (eval pattern (X5r X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__43) end in PM_sub43 t.
Ltac PM_all44 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__43_eq; PM_all43.
Definition pm__44 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub44 t in exact t).
Lemma pm__44_eq : ltac2:(tb__ "0|0|
S0S4SdS1eZ3A2S72A3"). Proof. cbv delta [X5r pm__44]; cbv beta zeta. PM_all44. reflexivity. Qed.
Ltac PM_sub45 t := let t := lazymatch (eval pattern (X5r X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__44) end in PM_sub44 t.
Ltac PM_all45 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__44_eq; PM_all44.
Definition pm__45 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub45 t in exact t).
Lemma pm__45_eq : ltac2:(tb__ "0|0|
S0S4S16S1eZ1A2S73A3"). Proof. cbv delta [X5a pm__45]; cbv beta zeta. PM_all45. reflexivity. Qed.
Ltac PM_sub46 t := let t := lazymatch (eval pattern (X5a X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__45) end in PM_sub45 t.
Ltac PM_all46 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__45_eq; PM_all45.
Definition pm__46 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub46 t in exact t).
Lemma pm__46_eq : ltac2:(tb__ "0|0|
S0S4S16S1eZ2A2S74A3"). Proof. cbv delta [X5a pm__46]; cbv beta zeta. PM_all46. reflexivity. Qed.
Ltac PM_sub47 t := let t := lazymatch (eval pattern (X5a X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__46) end in PM_sub46 t.
Ltac PM_all47 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__46_eq; PM_all46.
Definition pm__47 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub47 t in exact t).
Lemma pm__47_eq : ltac2:(tb__ "0|0|
S0S4S16S1eZ3A2S75A3"). Proof. cbv delta [X5a pm__47]; cbv beta zeta. PM_all47. reflexivity. Qed.
Ltac PM_sub48 t := let t := lazymatch (eval pattern (X5a X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__47) end in PM_sub47 t.
Ltac PM_all48 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__47_eq; PM_all47.
Definition pm__48 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub48 t in exact t).
Lemma pm__48_eq : ltac2:(tb__ "0|0|
S0S4S17S1eZ1A2S76A3"). Proof. cbv delta [X5b pm__48]; cbv beta zeta. PM_all48. reflexivity. Qed.
Ltac PM_sub49 t := let t := lazymatch (eval pattern (X5b X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__48) end in PM_sub48 t.
Ltac PM_all49 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__48_eq; PM_all48.
Definition pm__49 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub49 t in exact t).
Lemma pm__49_eq : ltac2:(tb__ "0|0|
S0S4S17S1eZ2A2S77A3"). Proof. cbv delta [X5b pm__49]; cbv beta zeta. PM_all49. reflexivity. Qed.
Ltac PM_sub50 t := let t := lazymatch (eval pattern (X5b X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__49) end in PM_sub49 t.
Ltac PM_all50 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__49_eq; PM_all49.
Definition pm__50 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub50 t in exact t).
Lemma pm__50_eq : ltac2:(tb__ "0|0|
S0S4S17S1eZ3A2S79A3"). Proof. cbv delta [X5b pm__50]; cbv beta zeta. PM_all50. reflexivity. Qed.
Ltac PM_sub51 t := let t := lazymatch (eval pattern (X5b X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__50) end in PM_sub50 t.
Ltac PM_all51 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__50_eq; PM_all50.
Definition pm__51 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub51 t in exact t).
Lemma pm__51_eq : ltac2:(tb__ "0|0|
S0S4S18S1eZ1A2S7aA3"). Proof. cbv delta [X5c pm__51]; cbv beta zeta. PM_all51. reflexivity. Qed.
Ltac PM_sub52 t := let t := lazymatch (eval pattern (X5c X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__51) end in PM_sub51 t.
Ltac PM_all52 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__51_eq; PM_all51.
Definition pm__52 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub52 t in exact t).
Lemma pm__52_eq : ltac2:(tb__ "0|0|
S0S4S18S1eZ2A2S7bA3"). Proof. cbv delta [X5c pm__52]; cbv beta zeta. PM_all52. reflexivity. Qed.
Ltac PM_sub53 t := let t := lazymatch (eval pattern (X5c X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__52) end in PM_sub52 t.
Ltac PM_all53 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__52_eq; PM_all52.
Definition pm__53 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub53 t in exact t).
Lemma pm__53_eq : ltac2:(tb__ "0|0|
S0S4S18S1eZ3A2S7cA3"). Proof. cbv delta [X5c pm__53]; cbv beta zeta. PM_all53. reflexivity. Qed.
Ltac PM_sub54 t := let t := lazymatch (eval pattern (X5c X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__53) end in PM_sub53 t.
Ltac PM_all54 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__53_eq; PM_all53.
Definition pm__54 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub54 t in exact t).
Lemma pm__54_eq : ltac2:(tb__ "0|0|
S0S4SaS1eZ1A2S46A3"). Proof. cbv delta [X5s pm__54]; cbv beta zeta. PM_all54. reflexivity. Qed.
Ltac PM_sub55 t := let t := lazymatch (eval pattern (X5s X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__54) end in PM_sub54 t.
Ltac PM_all55 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__54_eq; PM_all54.
Definition pm__55 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub55 t in exact t).
Lemma pm__55_eq : ltac2:(tb__ "0|0|
S0S4SaS1eZ2A2S47A3"). Proof. cbv delta [X5s pm__55]; cbv beta zeta. PM_all55. reflexivity. Qed.
Ltac PM_sub56 t := let t := lazymatch (eval pattern (X5s X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__55) end in PM_sub55 t.
Ltac PM_all56 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__55_eq; PM_all55.
Definition pm__56 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub56 t in exact t).
Lemma pm__56_eq : ltac2:(tb__ "0|0|
S0S4SaS1eZ3A2S48A3"). Proof. cbv delta [X5s pm__56]; cbv beta zeta. PM_all56. reflexivity. Qed.
Ltac PM_sub57 t := let t := lazymatch (eval pattern (X5s X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__56) end in PM_sub56 t.
Ltac PM_all57 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__56_eq; PM_all56.
Definition pm__57 : axst := ltac2:(tb__ "0|0|
SbeS20Z1A1S9aS5S46A1A1A2").
Lemma pm__57_eq : ltac2:(tb__ "0|1|
S0S4SfS20Z1M0A1SaS1eG0A2A2S49A3"). Proof. cbv delta [T50 pm__57]; cbv beta zeta. PM_all57. reflexivity. Qed.
Ltac PM_sub58 t := let t := lazymatch (eval pattern (T50 (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__57) end in PM_sub57 t.
Ltac PM_all58 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__57_eq; PM_all57.
Definition pm__58 : axst := ltac2:(tb__ "0|0|
SbeS20Z2A1S9aS5S47A1A1A2").
Lemma pm__58_eq : ltac2:(tb__ "0|1|
S0S4SfS20Z2M0A1SaS1eG0A2A2S4aA3"). Proof. cbv delta [T50 pm__58]; cbv beta zeta. PM_all58. reflexivity. Qed.
Ltac PM_sub59 t := let t := lazymatch (eval pattern (T50 (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__58) end in PM_sub58 t.
Ltac PM_all59 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__58_eq; PM_all58.
Definition pm__59 : axst := ltac2:(tb__ "0|0|
SbeS20Z3A1S9aS5S48A1A1A2").
Lemma pm__59_eq : ltac2:(tb__ "0|1|
S0S4SfS20Z3M0A1SaS1eG0A2A2S4bA3"). Proof. cbv delta [T50 pm__59]; cbv beta zeta. PM_all59. reflexivity. Qed.
Ltac PM_sub60 t := let t := lazymatch (eval pattern (T50 (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__59) end in PM_sub59 t.
Ltac PM_all60 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__59_eq; PM_all59.
Definition pm__60 : axst := ltac2:(tb__ "0|0|
Sa7S49U0A2").
Lemma pm__60_eq : ltac2:(tb__ "0|1|
S0S4S10S20Z1M0A1SaS1eG0A2A2S4cA3"). Proof. cbv delta [T5a pm__60]; cbv beta zeta. PM_all60. reflexivity. Qed.
Ltac PM_sub61 t := let t := lazymatch (eval pattern (T5a (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__60) end in PM_sub60 t.
Ltac PM_all61 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__60_eq; PM_all60.
Definition pm__61 : axst := ltac2:(tb__ "0|0|
Sa7S4aU0A2").
Lemma pm__61_eq : ltac2:(tb__ "0|1|
S0S4S10S20Z2M0A1SaS1eG0A2A2S4dA3"). Proof. cbv delta [T5a pm__61]; cbv beta zeta. PM_all61. reflexivity. Qed.
Ltac PM_sub62 t := let t := lazymatch (eval pattern (T5a (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__61) end in PM_sub61 t.
Ltac PM_all62 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__61_eq; PM_all61.
Definition pm__62 : axst := ltac2:(tb__ "0|0|
Sa7S4bU0A2").
Lemma pm__62_eq : ltac2:(tb__ "0|1|
S0S4S10S20Z3M0A1SaS1eG0A2A2S4eA3"). Proof. cbv delta [T5a pm__62]; cbv beta zeta. PM_all62. reflexivity. Qed.
Ltac PM_sub63 t := let t := lazymatch (eval pattern (T5a (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__62) end in PM_sub62 t.
Ltac PM_all63 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__62_eq; PM_all62.
Definition pm__63 : axst := ltac2:(tb__ "0|0|
Sa7S4cU1A2").
Lemma pm__63_eq : ltac2:(tb__ "0|1|
S0S4S11S20Z1M0A1SaS1eG0A2A2S2cA3"). Proof. cbv delta [T5b pm__63]; cbv beta zeta. PM_all63. reflexivity. Qed.
Ltac PM_sub64 t := let t := lazymatch (eval pattern (T5b (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__63) end in PM_sub63 t.
Ltac PM_all64 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__63_eq; PM_all63.
Definition pm__64 : axst := ltac2:(tb__ "0|0|
Sa7S4dU1A2").
Lemma pm__64_eq : ltac2:(tb__ "0|1|
S0S4S11S20Z2M0A1SaS1eG0A2A2S2dA3"). Proof. cbv delta [T5b pm__64]; cbv beta zeta. PM_all64. reflexivity. Qed.
Ltac PM_sub65 t := let t := lazymatch (eval pattern (T5b (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__64) end in PM_sub64 t.
Ltac PM_all65 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__64_eq; PM_all64.
Definition pm__65 : axst := ltac2:(tb__ "0|0|
Sa7S4eU1A2").
Lemma pm__65_eq : ltac2:(tb__ "0|1|
S0S4S11S20Z3M0A1SaS1eG0A2A2S2eA3"). Proof. cbv delta [T5b pm__65]; cbv beta zeta. PM_all65. reflexivity. Qed.
Ltac PM_sub66 t := let t := lazymatch (eval pattern (T5b (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__65) end in PM_sub65 t.
Ltac PM_all66 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__65_eq; PM_all65.
Definition pm__66 : axst := ltac2:(tb__ "0|1|
S6S2cSbdS5S2cA1M0Sb8S9eG0A1SeS22A1A2A2A2").
Lemma pm__66_eq : ltac2:(tb__ "0|1|
S0S4S12S22S20Z1M0A1SaS1eG0A2A3S4fA3"). Proof. cbv delta [T5c pm__66]; cbv beta zeta. PM_all66. reflexivity. Qed.
Ltac PM_sub67 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__66) end in PM_sub66 t.
Ltac PM_all67 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__66_eq; PM_all66.
Definition pm__67 : axst := ltac2:(tb__ "0|1|
S6S2dSbdS5S2dA1M0Sb8S9eG0A1SeS22A1A2A2A2").
Lemma pm__67_eq : ltac2:(tb__ "0|1|
S0S4S12S22S20Z2M0A1SaS1eG0A2A3S50A3"). Proof. cbv delta [T5c pm__67]; cbv beta zeta. PM_all67. reflexivity. Qed.
Ltac PM_sub68 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__67) end in PM_sub67 t.
Ltac PM_all68 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__67_eq; PM_all67.
Definition pm__68 : axst := ltac2:(tb__ "0|1|
S6S2eSbdS5S2eA1M0Sb8S9eG0A1SeS22A1A2A2A2").
Lemma pm__68_eq : ltac2:(tb__ "0|1|
S0S4S12S22S20Z3M0A1SaS1eG0A2A3S51A3"). Proof. cbv delta [T5c pm__68]; cbv beta zeta. PM_all68. reflexivity. Qed.
Ltac PM_sub69 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__68) end in PM_sub68 t.
Ltac PM_all69 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__68_eq; PM_all68.
Definition pm__69 : axst := ltac2:(tb__ "0|0|
Sa6S4fSbA2").
Lemma pm__69_eq : ltac2:(tb__ "0|1|
S0S4S13S22S20Z1M0A1SaS1eG0A2A3S52A3"). Proof. cbv delta [T5m1 pm__69]; cbv beta zeta. PM_all69. reflexivity. Qed.
Ltac PM_sub70 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__69) end in PM_sub69 t.
Ltac PM_all70 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__69_eq; PM_all69.
Definition pm__70 : axst := ltac2:(tb__ "0|0|
Sa6S50SbA2").
Lemma pm__70_eq : ltac2:(tb__ "0|1|
S0S4S13S22S20Z2M0A1SaS1eG0A2A3S53A3"). Proof. cbv delta [T5m1 pm__70]; cbv beta zeta. PM_all70. reflexivity. Qed.
Ltac PM_sub71 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__70) end in PM_sub70 t.
Ltac PM_all71 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__70_eq; PM_all70.
Definition pm__71 : axst := ltac2:(tb__ "0|0|
Sa6S51SbA2").
Lemma pm__71_eq : ltac2:(tb__ "0|1|
S0S4S13S22S20Z3M0A1SaS1eG0A2A3S54A3"). Proof. cbv delta [T5m1 pm__71]; cbv beta zeta. PM_all71. reflexivity. Qed.
Ltac PM_sub72 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__71) end in PM_sub71 t.
Ltac PM_all72 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__71_eq; PM_all71.
Definition pm__72 : axst := ltac2:(tb__ "0|0|
Sa6S52SbA2").
Lemma pm__72_eq : ltac2:(tb__ "0|1|
S0S4S14S22S20Z1M0A1SaS1eG0A2A3S55A3"). Proof. cbv delta [T5m2 pm__72]; cbv beta zeta. PM_all72. reflexivity. Qed.
Ltac PM_sub73 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__72) end in PM_sub72 t.
Ltac PM_all73 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__72_eq; PM_all72.
Definition pm__73 : axst := ltac2:(tb__ "0|0|
Sa6S53SbA2").
Lemma pm__73_eq : ltac2:(tb__ "0|1|
S0S4S14S22S20Z2M0A1SaS1eG0A2A3S56A3"). Proof. cbv delta [T5m2 pm__73]; cbv beta zeta. PM_all73. reflexivity. Qed.
Ltac PM_sub74 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__73) end in PM_sub73 t.
Ltac PM_all74 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__73_eq; PM_all73.
Definition pm__74 : axst := ltac2:(tb__ "0|0|
Sa6S54SbA2").
Lemma pm__74_eq : ltac2:(tb__ "0|1|
S0S4S14S22S20Z3M0A1SaS1eG0A2A3S57A3"). Proof. cbv delta [T5m2 pm__74]; cbv beta zeta. PM_all74. reflexivity. Qed.
Ltac PM_sub75 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__74) end in PM_sub74 t.
Ltac PM_all75 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__74_eq; PM_all74.
Definition pm__75 : axst := ltac2:(tb__ "0|0|
Sa6S55SbA2").
Lemma pm__75_eq : ltac2:(tb__ "0|1|
S0S4S15S22S20Z1M0A1SaS1eG0A2A3S58A3"). Proof. cbv delta [T5m3 pm__75]; cbv beta zeta. PM_all75. reflexivity. Qed.
Ltac PM_sub76 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__75) end in PM_sub75 t.
Ltac PM_all76 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__75_eq; PM_all75.
Definition pm__76 : axst := ltac2:(tb__ "0|0|
Sa6S56SbA2").
Lemma pm__76_eq : ltac2:(tb__ "0|1|
S0S4S15S22S20Z2M0A1SaS1eG0A2A3S59A3"). Proof. cbv delta [T5m3 pm__76]; cbv beta zeta. PM_all76. reflexivity. Qed.
Ltac PM_sub77 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__76) end in PM_sub76 t.
Ltac PM_all77 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__76_eq; PM_all76.
Definition pm__77 : axst := ltac2:(tb__ "0|0|
Sa6S57SbA2").
Lemma pm__77_eq : ltac2:(tb__ "0|1|
S0S4S15S22S20Z3M0A1SaS1eG0A2A3S5aA3"). Proof. cbv delta [T5m3 pm__77]; cbv beta zeta. PM_all77. reflexivity. Qed.
Ltac PM_sub78 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__77) end in PM_sub77 t.
Ltac PM_all78 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__77_eq; PM_all77.
Definition pm__78 : axst := ltac2:(tb__ "0|0|
Sa6S58SbA2").
Lemma pm__78_eq : ltac2:(tb__ "0|1|
S0S4ScS22S20Z1M0A1SaS1eG0A2A3S7fA3"). Proof. cbv delta [T5d pm__78]; cbv beta zeta. PM_all78. reflexivity. Qed.
Ltac PM_sub79 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__78) end in PM_sub78 t.
Ltac PM_all79 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__78_eq; PM_all78.
Definition pm__79 : axst := ltac2:(tb__ "0|0|
Sa6S59SbA2").
Lemma pm__79_eq : ltac2:(tb__ "0|1|
S0S4ScS22S20Z2M0A1SaS1eG0A2A3S80A3"). Proof. cbv delta [T5d pm__79]; cbv beta zeta. PM_all79. reflexivity. Qed.
Ltac PM_sub80 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__79) end in PM_sub79 t.
Ltac PM_all80 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__79_eq; PM_all79.
Definition pm__80 : axst := ltac2:(tb__ "0|0|
Sa6S5aSbA2").
Lemma pm__80_eq : ltac2:(tb__ "0|1|
S0S4ScS22S20Z3M0A1SaS1eG0A2A3S82A3"). Proof. cbv delta [T5d pm__80]; cbv beta zeta. PM_all80. reflexivity. Qed.
Ltac PM_sub81 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__80) end in PM_sub80 t.
Ltac PM_all81 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__80_eq; PM_all80.
Definition pm__81 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub81 t in exact t).
Lemma pm__81_eq : ltac2:(tb__ "0|0|
S0S4S1aS1eA1S83A3"). Proof. cbv delta [C5S pm__81]; cbv beta zeta. PM_all81. reflexivity. Qed.
Ltac PM_sub82 t := let t := lazymatch (eval pattern (C5S X5bc) in t) with ?P _ => eval cbv beta in (P pm__81) end in PM_sub81 t.
Ltac PM_all82 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__81_eq; PM_all81.
Lemma WX5rb_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa2S5SdS1eR2A2A1A1S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5rb_0 : ltac2:(tb__ "0|4|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S91S8eS8dS8eS96S96A2M0A1M1S8dS97A1M2A2M3A1Sc1S5S19S1eA1A1S5SdS1eR2A2A1A2S93G3S92G1G2S8cG0S92S96S96Sa3S94Q20S9dPc0A1A3S99R2A1A4S8bG0A1A3S8bS97A1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5SdS1eR2A2A1SbS99Nf10A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5S16S1eR2A2A1S8fSbA1S99N910A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5S17S1eR2A2A1S8fS8fSbA1A1S99N848A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb5S5S18S1eR2A2A1S8fS8fS8fSbA1A1A1S99N50A1A3A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERb_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S91S8dS98A1M0A1ScdSaS1eR2A2Sb2R2A1S26R2A1A3S93G0S28R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S4SceS26R2A1Sb2R2A1Sb3R2A1SaS1eR2A2S28R2A1A5S20R2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4b_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S8dS8eS96S96A2M0A1S7SaS1eR2A2A1S8bG0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4b_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SaeS97S9fS9cS5SaS1eR2A2A1M0A1A1S9aG0A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SccSaS1eR2A2Sb2R2A1S26R2A1S28R2A1S8cS4Sb3R2A1S8bS4A1A3A5S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S88S9cS5SaS1eR2A2A1A1S9cS5S1eA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10b_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S96SbaS26R2A1PaM0A2Sa0SbfS9dG0A1S99N910A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S96SbaS26R2A1PfA2S99N600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S96SbaS26R2A1PcA2Sa0SbfS9dPaA1S99N848A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SaeS98S1cU1Sb7S62A3S28R2A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOb_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S8dS98A1Sc9S5Sb2R2A1A1S5Sb3R2A1A1A2S8bS98A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPostb_0 : ltac2:(tb__ "0|1|
S87S0S8dS8eS96S96A2M0A1S7Sb3R1A1A1S8bG0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SaeS97S9fS9cS5S20R2A1A1A1A1S9aS5SaS1eR2A2A1A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4b_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S8dS8eS96S96A2M0A1S7S20R2A1A1S8bG0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb6S5SfS20R2A1SaS1eR2A2A2A1U0A2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb6S5S10S20R2A1SaS1eR2A2A2A1U1A2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_ndb_0 : ltac2:(tb__ "0|0|
S0S89Sb9SeS22A1A1S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_ltb_0 : ltac2:(tb__ "0|0|
S0S89SaeS90S90Sd5R1S22A2Li;SeS22A1A3S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_covb_0 : ltac2:(tb__ "0|0|
S0S89SaeS90S90Sb1S90Sd4R1A1SeS22A1A3Li;Sc7U0S22A2A3S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lenb_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S90S95S98S9eS5S11S20R2A1SaS1eR2A2A2A1A1A2S22A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S12S22S20R2A1SaS1eR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S13S22S20R2A1SaS1eR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S14S22S20R2A1SaS1eR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89Sa9S9bSb4S5S15S22S20R2A1SaS1eR2A2A3A1SbA2A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89S8ScS22S20R2A1SaS1eR2A2A3S30S5cR2A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5b_0 : ltac2:(tb__ "0|0|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89SbcS5cR2A1VGS0;A2S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4covb_0 : ltac2:(tb__ "0|1|
S87S1S2Z1R1A2S2R1Vtmax;A2A2S0S89S1bS9aS5ScS22S20R2A1SaS1eR2A2A3A1M0A1S28R2A1S9eG0A1A3S8aA3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all82; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

End INST.
End SpineCallocSec5IW1.

(* [comment removed for export] *)
Module SpineCallocSec5IL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "leafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "X5s"; "WI"; "T5d"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "C5S"; "coveredbL"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL.INST"; "X5ac"; "X5bc"; "T4a_i"; "T4b_i"; "nobja"; "nobjb"; "U4ac"; "U4bc"; "s4a_i"; "s4b_i"; "R4a_i"; "R4b_i"; "pm__15"; "pm__16"; "pm__43"; "pm__44"; "C5ac"; "C5bc"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__37"; "pm__38"; "pm__39"; "pm__40"; "pm__41"; "pm__42"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__49"; "pm__50"; "pm__51"; "pm__52"; "pm__9"; "sda_i"; "sdb_i"; "CPa1"; "CPa2"; "CPb1"; "CPb2"; "EXoa"; "EXob"; "pm__0"; "pm__1"; "pm__2"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__29"; "pm__3"; "pm__30"; "pm__31"; "pm__32"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__4"; "pm__5"; "pm__53"; "pm__54"; "pm__55"; "pm__6"; "pm__7"; "pm__8"; "run5a"; "run5b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "S"; "nat"; "option"; "pair"; "Some"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_facts"; "ss_next"; "SVar"; "ss_objs"; "sprop_below"; "SAlu"; "SPUle"; "swf"; "SExt"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "isSome"; "O_1"; "O_2"; "O_blk"; "O_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "omrg"; "oreb"; "F_call"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IL"; "T4ac"; "T4bc"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

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
Module SpineMallocSec6J.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sobj"; "rl"; "sv"; "holds"; "sprop"; "SVar"; "eval"; "obj_range"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_ptr_committed"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "AE_A"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I"; "FXPa"; "FXPb"; "PXa"; "PXb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7"; "bx_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S46VCST;R1A2S46S55R2A2S1fF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S6S46VCST;R1A2S46S56R2A2S1fF_;F_;Fa;").

Lemma PXnba_0 : ltac2:(tb__ "0|2|
S17S16S2aS8S27Q40A1M0S8S0G0A1S0S39A1S38S31U0Vst;S33S26S16S37R1A1LX;R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S4fA3S0SbA1S1cS0S1S1SdSdA2SdA2M1A1S35SbG1S4aR1A4S35SbG1S4aS51A4A3S34SbSbS32S12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxa_noband 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXoka_0 : ltac2:(tb__ "0|0|
S17S53S26S16S37R1A1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHa_0 : ltac2:(tb__ "0|6|
S17S16S2aS8S27Q40M0A1M1S8S0G1A1S0S39A1S38S31U0Vst;S33S26S16S37R1A1LX;M2R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S4fA3S26G2RbS4cRaS28G0S9R8PcA2A2A2A3S16S1dS1dS20Z8M3Z20000M4A2S20G4G4A2A2S1dS20S21S25G3S23S2S19S18RbA1A2A1A2G4A2S1bR1A1M5A2S1cG1S11R7S13S54S10S4bA1S14Z4000A1A3A2S29G0S22G5G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_a 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0ha_P : ltac2:(tb__ "0|9|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S0S1S40S42A2M3A1S36G3S3S40S42S2fS2bVW;Vst;A3S2eS44S15A1VCST;VXGL;R8R7A5A4R1A3S49VW;Vst;A2S2cR9A1S3fS15RcS3eRaA1A3S7S1cG1S9RaR1A2S9RbR1A2A3Fi;S7S1cS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2dVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S19S18RfA1A2A1S1aRfA1A2S1S6S6A2M5S36G5R1S47RbA1A3S45R2S3S6S6S28G0ReA2M6S48S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1dS20S43G6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1eS1cS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S3aS15R15S3dS15S31U0Vst;S33S26S16S37R1A1LX;ReA2R14R13R11R10A8S4dR2R1A5S41S15S3cR12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) C5ac C5Aa C5Ba Y6Aa Y6Ba E6a CT6a CO6a T6a s6Aa s6Ba s6a R6a
           HC5Aa_0 HC5Ba_0 FBAa_0 FBBa_0 Cert6Aa_0 Cert6Ba_0 E6Aa_0 I6Aa_0 E6Ba_0 I6Ba_0
           WC6a_0 DF6a_0 NX6a_0 HC6a_0 SK6a_0 FC6a_0 FX6a_0 XC6a_0 HCO6a_0 WCO6a_0 He6a_0 Hchk6a_0 HT6a_0 FBC6a_0 FBT6a_0 NXC6a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6a_0.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D6a U7a ET7a CT7a CO7a CR7a CS7a CM7a T7a s7a R7a n7a
           WU7a_0 DU7a_0 NXU7a_0 HU7a_0 Cert7a_0 WC7a_0 DF7a_0 NX7a_0 HC7a_0 SK7a_0 FC7a_0 FX7a_0 XC7a_0 HCO7a_0 WCO7a_0
           RB7a_0 HCR7a_0 LEN7a_0 PERM_nd7a_0 PERM_lt7a_0 PERM_cov7a_0 HCS7a_0 MRG7a_0 HCM7a_0 He7a_0 Hchk7a_0 HT7a_0 FBC7a_0 FBT7a_0 NXC7a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7a_0.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D7a U8a ET8a CT8a CO8a T8a s8a R8a
           WU8a_0 DU8a_0 NXU8a_0 HU8a_0 Cert8a_0 WC8a_0 DF8a_0 NX8a_0 HC8a_0 SK8a_0 FC8a_0 FX8a_0 XC8a_0 HCO8a_0 WCO8a_0
           He8a_0 Hchk8a_0 HT8a_0 FBC8a_0 FBT8a_0 NXC8a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8a_0.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D8a U9a E9fa E9pa CO9pa E9qa
           WU9a_0 DU9a_0 NXU9a_0 HU9a_0 Cert9a_0 SK9a_0 FC9a_0 FX9a_0 FP9a_0 XC9a_0 HCO9a_0 WCO9a_0 Cert9qa_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9fa S9afa S9bfa T9fa iMfa s9fa R9fa HS9afa_0 HS9bfa_0 He9fa_0 Hchk9fa_0 HT9fa_0 FBC9fa_0 FBT9fa_0 NXC9fa_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9fa_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfa swcfa c1fa c2fa c4fa c5fa mcfa xcfa tybfa SELFfa_0 NDFfa_0 BNDFfa_0 COVFfa_0 XFnfa_0 BFbfa_0 FPFfa_0 FXFfa_0 FPARfa_0
             Hc1fa_0 Hmcfa_0 Htybfa_0 Hxcfa_0 WCUfa_0 SELUfa_0 NDUfa_0 BNDUfa_0 COVUfa_0 W9fa_0 D9fa_0 XB9fa_0 sFfa ENT9fa_0 SID9fa_0 G110fa_0 D9fa CertFfa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9qa S9aqa S9bqa T9qa iMqa s9qa R9qa HS9aqa_0 HS9bqa_0 He9qa_0 Hchk9qa_0 HT9qa_0 FBC9qa_0 FBT9qa_0 NXC9qa_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9qa_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqa swcqa c1qa c2qa c4qa c5qa mcqa xcqa tybqa SELFqa_0 NDFqa_0 BNDFqa_0 COVFqa_0 XFnqa_0 BFbqa_0 FPFqa_0 FXFqa_0 FPARqa_0
             Hc1qa_0 Hmcqa_0 Htybqa_0 Hxcqa_0 WCUqa_0 SELUqa_0 NDUqa_0 BNDUqa_0 COVUqa_0 W9qa_0 D9qa_0 XB9qa_0 sFqa ENT9qa_0 SID9qa_0 G110qa_0 D9qa CertFqa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0ha : ltac2:(tb__ "0|8|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S49VW;Vst;A2S2cR7A1S3fS15RaS3eR8A1A3S7S1cG1S9R8R1A2S9R9R1A2A3Fi;S7S1cS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2dVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S19S18RdA1A2A1S1aRdA1A2S1S6S6A2M4S36G4R1S47R9A1A3S45R2S3S6S6S28G0RcA2M5S48S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1dS20S43G5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1eS1cS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S3aS15R13S3dS15S31U0Vst;S33S26S16S37R1A1LX;RcA2R12R11RfReA8S4dR2R1A5S41S15S3cR10RdS30S2bS44S15A1VCST;VXGL;VW;Vst;R12R11A8A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0ha_P ok A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Lemma PXnbb_0 : ltac2:(tb__ "0|2|
S17S16S2aS8S27Q40A1M0S8S0G0A1S0S39A1S38S31U0Vst;S33S26S16R1LX;R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S50A3S0SbA1S1cS0S1S1SdSdA2SdA2M1A1S35SbG1S4aR1A4S35SbG1S4aS52A4A3S34SbSbS32S12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxb_noband 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXokb_0 : ltac2:(tb__ "0|0|
S17S53S26S16R1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHb_0 : ltac2:(tb__ "0|5|
S17S16S2aS8S27Q40M0A1M1S8S0G1A1S0S39A1S38S31U0Vst;S33S26S16R1LX;M2R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S50A3S26G2RbS4cRaS28G0S9R8PcA2A2A2A3S16S1dS1dS20Z8M3G3A2S20G3Z20000A2A2S1dS20S21S25G3S23S2S19S18RbA1A2A1A2G3A2S1bR1A1M4A2S1cG1S11R7S10S4bA1A2S29G0S22G4G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_b 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0hb_P : ltac2:(tb__ "0|9|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S0S1S40S42A2M3A1S36G3S3S40S42S2fS2bVW;Vst;A3S2eS44S15A1VCST;VXGL;R8R7A5A4R1A3S49VW;Vst;A2S2cR9A1S3fS15RcS3eRaA1A3S7S1cG1S9RaR1A2S9RbR1A2A3Fi;S7S1cS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2dVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S19S18RfA1A2A1S1aRfA1A2S1S6S6A2M5S36G5R1S47RbA1A3S45R2S3S6S6S28G0ReA2M6S48S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1dS20S43G6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1eS1cS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S3aS15R15S3dS15S31U0Vst;S33S26S16R1LX;ReA2R14R13R11R10A8S4eR2R1A5S41S15S3cR12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) C5bc C5Ab C5Bb Y6Ab Y6Bb E6b CT6b CO6b T6b s6Ab s6Bb s6b R6b
           HC5Ab_0 HC5Bb_0 FBAb_0 FBBb_0 Cert6Ab_0 Cert6Bb_0 E6Ab_0 I6Ab_0 E6Bb_0 I6Bb_0
           WC6b_0 DF6b_0 NX6b_0 HC6b_0 SK6b_0 FC6b_0 FX6b_0 XC6b_0 HCO6b_0 WCO6b_0 He6b_0 Hchk6b_0 HT6b_0 FBC6b_0 FBT6b_0 NXC6b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6b_0.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D6b U7b ET7b CT7b CO7b CR7b CS7b CM7b T7b s7b R7b n7b
           WU7b_0 DU7b_0 NXU7b_0 HU7b_0 Cert7b_0 WC7b_0 DF7b_0 NX7b_0 HC7b_0 SK7b_0 FC7b_0 FX7b_0 XC7b_0 HCO7b_0 WCO7b_0
           RB7b_0 HCR7b_0 LEN7b_0 PERM_nd7b_0 PERM_lt7b_0 PERM_cov7b_0 HCS7b_0 MRG7b_0 HCM7b_0 He7b_0 Hchk7b_0 HT7b_0 FBC7b_0 FBT7b_0 NXC7b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7b_0.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D7b U8b ET8b CT8b CO8b T8b s8b R8b
           WU8b_0 DU8b_0 NXU8b_0 HU8b_0 Cert8b_0 WC8b_0 DF8b_0 NX8b_0 HC8b_0 SK8b_0 FC8b_0 FX8b_0 XC8b_0 HCO8b_0 WCO8b_0
           He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8b_0.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D8b U9b E9fb E9pb CO9pb E9qb
           WU9b_0 DU9b_0 NXU9b_0 HU9b_0 Cert9b_0 SK9b_0 FC9b_0 FX9b_0 FP9b_0 XC9b_0 HCO9b_0 WCO9b_0 Cert9qb_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9fb S9afb S9bfb T9fb iMfb s9fb R9fb HS9afb_0 HS9bfb_0 He9fb_0 Hchk9fb_0 HT9fb_0 FBC9fb_0 FBT9fb_0 NXC9fb_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9fb_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfb swcfb c1fb c2fb c4fb c5fb mcfb xcfb tybfb SELFfb_0 NDFfb_0 BNDFfb_0 COVFfb_0 XFnfb_0 BFbfb_0 FPFfb_0 FXFfb_0 FPARfb_0
             Hc1fb_0 Hmcfb_0 Htybfb_0 Hxcfb_0 WCUfb_0 SELUfb_0 NDUfb_0 BNDUfb_0 COVUfb_0 W9fb_0 D9fb_0 XB9fb_0 sFfb ENT9fb_0 SID9fb_0 G110fb_0 D9fb CertFfb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9qb S9aqb S9bqb T9qb iMqb s9qb R9qb HS9aqb_0 HS9bqb_0 He9qb_0 Hchk9qb_0 HT9qb_0 FBC9qb_0 FBT9qb_0 NXC9qb_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9qb_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqb swcqb c1qb c2qb c4qb c5qb mcqb xcqb tybqb SELFqb_0 NDFqb_0 BNDFqb_0 COVFqb_0 XFnqb_0 BFbqb_0 FPFqb_0 FXFqb_0 FPARqb_0
             Hc1qb_0 Hmcqb_0 Htybqb_0 Hxcqb_0 WCUqb_0 SELUqb_0 NDUqb_0 BNDUqb_0 COVUqb_0 W9qb_0 D9qb_0 XB9qb_0 sFqb ENT9qb_0 SID9qb_0 G110qb_0 D9qb CertFqb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0hb : ltac2:(tb__ "0|8|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S49VW;Vst;A2S2cR7A1S3fS15RaS3eR8A1A3S7S1cG1S9R8R1A2S9R9R1A2A3Fi;S7S1cS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2dVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S19S18RdA1A2A1S1aRdA1A2S1S6S6A2M4S36G4R1S47R9A1A3S45R2S3S6S6S28G0RcA2M5S48S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1dS20S43G5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1eS1cS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S3aS15R13S3dS15S31U0Vst;S33S26S16R1LX;RcA2R12R11RfReA8S4eR2R1A5S41S15S3cR10RdS30S2bS44S15A1VCST;VXGL;VW;Vst;R12R11A8A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0hb_P ok A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6J.

(* [comment removed for export] *)
Module SpineMallocSec6JL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sobj"; "rl"; "sv"; "holds"; "sprop"; "SVar"; "eval"; "obj_range"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_ptr_committed"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "AE_A"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL"; "FXPa"; "FXPb"; "PXa"; "PXb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7"; "bx_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S46VCST;R1A2S46S55R2A2S1fF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S6S46VCST;R1A2S46S56R2A2S1fF_;F_;Fa;").

Lemma PXnba_0 : ltac2:(tb__ "0|2|
S17S16S2aS8S27Q40A1M0S8S0G0A1S0S39A1S38S31U0Vst;S33S26S16S37R1A1LX;R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S4fA3S0SbA1S1cS0S1S1SdSdA2SdA2M1A1S35SbG1S4aR1A4S35SbG1S4aS51A4A3S34SbSbS32S12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxa_noband 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXoka_0 : ltac2:(tb__ "0|0|
S17S53S26S16S37R1A1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHa_0 : ltac2:(tb__ "0|6|
S17S16S2aS8S27Q40M0A1M1S8S0G1A1S0S39A1S38S31U0Vst;S33S26S16S37R1A1LX;M2R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S4fA3S26G2RbS4cRaS28G0S9R8PcA2A2A2A3S16S1dS1dS20Z8M3Z20000M4A2S20G4G4A2A2S1dS20S21S25G3S23S2S19S18RbA1A2A1A2G4A2S1bR1A1M5A2S1cG1S11R7S13S54S10S4bA1S14Z4000A1A3A2S29G0S22G5G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_a 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0la_P : ltac2:(tb__ "0|9|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S0S1S40S42A2M3A1S36G3S3S40S42S2fS2bVW;Vst;A3S2eS44S15A1VCST;VXGL;R8R7A5A4R1A3S49VW;Vst;A2S2cR9A1S3fS15RcS3eRaA1A3S7S1cG1S9RaR1A2S9RbR1A2A3Fi;S7S1cS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2dVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S19S18RfA1A2A1S1aRfA1A2S1S6S6A2M5S36G5R1S47RbA1A3S45R2S3S6S6S28G0ReA2M6S48S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1dS20S43G6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1eS1cS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S3aS15R15S3dS15S31U0Vst;S33S26S16S37R1A1LX;ReA2R14R13R11R10A8S4dR2R1A5S41S15S3cR12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) C5ac C5Aa Y6Aa E6a CT6a CO6a T6a s6Aa s6a R6a
           FLOWa_0 HC5Aa_0 FBAa_0 Cert6Aa_0 E6Aa_0 I6Aa_0
           WC6a_0 DF6a_0 NX6a_0 HC6a_0 SK6a_0 FC6a_0 FX6a_0 XC6a_0 HCO6a_0 WCO6a_0 He6a_0 Hchk6a_0 HT6a_0 FBC6a_0 FBT6a_0 NXC6a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_triple 0%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D6La U7a ET7a CT7a CO7a CR7a CS7a CM7a T7a s7a R7a n7a
           WU7a_0 DU7a_0 NXU7a_0 HU7a_0 Cert7a_0 WC7a_0 DF7a_0 NX7a_0 HC7a_0 SK7a_0 FC7a_0 FX7a_0 XC7a_0 HCO7a_0 WCO7a_0
           RB7a_0 HCR7a_0 LEN7a_0 PERM_nd7a_0 PERM_lt7a_0 PERM_cov7a_0 HCS7a_0 MRG7a_0 HCM7a_0 He7a_0 Hchk7a_0 HT7a_0 FBC7a_0 FBT7a_0 NXC7a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_triple 0%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D7La U8a ET8a CT8a CO8a T8a s8a R8a
           WU8a_0 DU8a_0 NXU8a_0 HU8a_0 Cert8a_0 WC8a_0 DF8a_0 NX8a_0 HC8a_0 SK8a_0 FC8a_0 FX8a_0 XC8a_0 HCO8a_0 WCO8a_0
           He8a_0 Hchk8a_0 HT8a_0 FBC8a_0 FBT8a_0 NXC8a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_triple 0%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D8La U9a E9fa E9pa CO9pa E9qa
           WU9a_0 DU9a_0 NXU9a_0 HU9a_0 Cert9a_0 SK9a_0 FC9a_0 FX9a_0 FP9a_0 XC9a_0 HCO9a_0 WCO9a_0 Cert9qa_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9fa S9afa S9bfa T9fa iMfa s9fa R9fa HS9afa_0 HS9bfa_0 He9fa_0 Hchk9fa_0 HT9fa_0 FBC9fa_0 FBT9fa_0 NXC9fa_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9fa_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfa swcfa c1fa c2fa c4fa c5fa mcfa xcfa tybfa SELFfa_0 NDFfa_0 BNDFfa_0 COVFfa_0 XFnfa_0 BFbfa_0 FPFfa_0 FXFfa_0 FPARfa_0
             Hc1fa_0 Hmcfa_0 Htybfa_0 Hxcfa_0 WCUfa_0 SELUfa_0 NDUfa_0 BNDUfa_0 COVUfa_0 W9fa_0 D9fa_0 XB9fa_0 sFfa ENT9fa_0 SID9fa_0 G110fa_0 D9fa CertFfa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9qa S9aqa S9bqa T9qa iMqa s9qa R9qa HS9aqa_0 HS9bqa_0 He9qa_0 Hchk9qa_0 HT9qa_0 FBC9qa_0 FBT9qa_0 NXC9qa_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9qa_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqa swcqa c1qa c2qa c4qa c5qa mcqa xcqa tybqa SELFqa_0 NDFqa_0 BNDFqa_0 COVFqa_0 XFnqa_0 BFbqa_0 FPFqa_0 FXFqa_0 FPARqa_0
             Hc1qa_0 Hmcqa_0 Htybqa_0 Hxcqa_0 WCUqa_0 SELUqa_0 NDUqa_0 BNDUqa_0 COVUqa_0 W9qa_0 D9qa_0 XB9qa_0 sFqa ENT9qa_0 SID9qa_0 G110qa_0 D9qa CertFqa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0la : ltac2:(tb__ "0|8|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S49VW;Vst;A2S2cR7A1S3fS15RaS3eR8A1A3S7S1cG1S9R8R1A2S9R9R1A2A3Fi;S7S1cS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2dVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S19S18RdA1A2A1S1aRdA1A2S1S6S6A2M4S36G4R1S47R9A1A3S45R2S3S6S6S28G0RcA2M5S48S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1dS20S43G5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1eS1cS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S3aS15R13S3dS15S31U0Vst;S33S26S16S37R1A1LX;RcA2R12R11RfReA8S4dR2R1A5S41S15S3cR10RdS30S2bS44S15A1VCST;VXGL;VW;Vst;R12R11A8A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0la_P ok A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Lemma PXnbb_0 : ltac2:(tb__ "0|2|
S17S16S2aS8S27Q40A1M0S8S0G0A1S0S39A1S38S31U0Vst;S33S26S16R1LX;R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S50A3S0SbA1S1cS0S1S1SdSdA2SdA2M1A1S35SbG1S4aR1A4S35SbG1S4aS52A4A3S34SbSbS32S12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxb_noband 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXokb_0 : ltac2:(tb__ "0|0|
S17S53S26S16R1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHb_0 : ltac2:(tb__ "0|5|
S17S16S2aS8S27Q40M0A1M1S8S0G1A1S0S39A1S38S31U0Vst;S33S26S16R1LX;M2R9A2R8R7R6R5R4R3R2R1AcS34SfSeR5A1S50A3S26G2RbS4cRaS28G0S9R8PcA2A2A2A3S16S1dS1dS20Z8M3G3A2S20G3Z20000A2A2S1dS20S21S25G3S23S2S19S18RbA1A2A1A2G3A2S1bR1A1M4A2S1cG1S11R7S10S4bA1A2S29G0S22G4G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_b 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0lb_P : ltac2:(tb__ "0|9|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S0S1S40S42A2M3A1S36G3S3S40S42S2fS2bVW;Vst;A3S2eS44S15A1VCST;VXGL;R8R7A5A4R1A3S49VW;Vst;A2S2cR9A1S3fS15RcS3eRaA1A3S7S1cG1S9RaR1A2S9RbR1A2A3Fi;S7S1cS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2dVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S19S18RfA1A2A1S1aRfA1A2S1S6S6A2M5S36G5R1S47RbA1A3S45R2S3S6S6S28G0ReA2M6S48S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1dS20S43G6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1eS1cS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S3aS15R15S3dS15S31U0Vst;S33S26S16R1LX;ReA2R14R13R11R10A8S4eR2R1A5S41S15S3cR12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) C5bc C5Ab Y6Ab E6b CT6b CO6b T6b s6Ab s6b R6b
           FLOWb_0 HC5Ab_0 FBAb_0 Cert6Ab_0 E6Ab_0 I6Ab_0
           WC6b_0 DF6b_0 NX6b_0 HC6b_0 SK6b_0 FC6b_0 FX6b_0 XC6b_0 HCO6b_0 WCO6b_0 He6b_0 Hchk6b_0 HT6b_0 FBC6b_0 FBT6b_0 NXC6b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_triple 0%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D6Lb U7b ET7b CT7b CO7b CR7b CS7b CM7b T7b s7b R7b n7b
           WU7b_0 DU7b_0 NXU7b_0 HU7b_0 Cert7b_0 WC7b_0 DF7b_0 NX7b_0 HC7b_0 SK7b_0 FC7b_0 FX7b_0 XC7b_0 HCO7b_0 WCO7b_0
           RB7b_0 HCR7b_0 LEN7b_0 PERM_nd7b_0 PERM_lt7b_0 PERM_cov7b_0 HCS7b_0 MRG7b_0 HCM7b_0 He7b_0 Hchk7b_0 HT7b_0 FBC7b_0 FBT7b_0 NXC7b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_triple 0%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D7Lb U8b ET8b CT8b CO8b T8b s8b R8b
           WU8b_0 DU8b_0 NXU8b_0 HU8b_0 Cert8b_0 WC8b_0 DF8b_0 NX8b_0 HC8b_0 SK8b_0 FC8b_0 FX8b_0 XC8b_0 HCO8b_0 WCO8b_0
           He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_triple 0%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D8Lb U9b E9fb E9pb CO9pb E9qb
           WU9b_0 DU9b_0 NXU9b_0 HU9b_0 Cert9b_0 SK9b_0 FC9b_0 FX9b_0 FP9b_0 XC9b_0 HCO9b_0 WCO9b_0 Cert9qb_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9fb S9afb S9bfb T9fb iMfb s9fb R9fb HS9afb_0 HS9bfb_0 He9fb_0 Hchk9fb_0 HT9fb_0 FBC9fb_0 FBT9fb_0 NXC9fb_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9fb_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfb swcfb c1fb c2fb c4fb c5fb mcfb xcfb tybfb SELFfb_0 NDFfb_0 BNDFfb_0 COVFfb_0 XFnfb_0 BFbfb_0 FPFfb_0 FXFfb_0 FPARfb_0
             Hc1fb_0 Hmcfb_0 Htybfb_0 Hxcfb_0 WCUfb_0 SELUfb_0 NDUfb_0 BNDUfb_0 COVUfb_0 W9fb_0 D9fb_0 XB9fb_0 sFfb ENT9fb_0 SID9fb_0 G110fb_0 D9fb CertFfb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st tmax nx0 Hnx_0 NXG_0 BX E9qb S9aqb S9bqb T9qb iMqb s9qb R9qb HS9aqb_0 HS9bqb_0 He9qb_0 Hchk9qb_0 HT9qb_0 FBC9qb_0 FBT9qb_0 NXC9qb_0
             ok A Kc rho a Q HUS HKc Hokl).
    intros rZ tZ. rewrite HD9qb_0.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqb swcqb c1qb c2qb c4qb c5qb mcqb xcqb tybqb SELFqb_0 NDFqb_0 BNDFqb_0 COVFqb_0 XFnqb_0 BFbqb_0 FPFqb_0 FXFqb_0 FPARqb_0
             Hc1qb_0 Hmcqb_0 Htybqb_0 Hxcqb_0 WCUqb_0 SELUqb_0 NDUqb_0 BNDUqb_0 COVUqb_0 W9qb_0 D9qb_0 XB9qb_0 sFqb ENT9qb_0 SID9qb_0 G110qb_0 D9qb CertFqb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0lb : ltac2:(tb__ "0|8|
S3bOF_;S16S2aS8S8S27Q40M0A1M1S0G1A1M2S17S49VW;Vst;A2S2cR7A1S3fS15RaS3eR8A1A3S7S1cG1S9R8R1A2S9R9R1A2A3Fi;S7S1cS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2dVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S19S18RdA1A2A1S1aRdA1A2S1S6S6A2M4S36G4R1S47R9A1A3S45R2S3S6S6S28G0RcA2M5S48S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1dS20S43G5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1eS1cS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S3aS15R13S3dS15S31U0Vst;S33S26S16R1LX;RcA2R12R11RfReA8S4eR2R1A5S41S15S3cR10RdS30S2bS44S15A1VCST;VXGL;VW;Vst;R12R11A8A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0lb_P ok A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JL.

(* [comment removed for export] *)
Module SpineMallocSec5JEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_next"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "list"; "true"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU"; "DPENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL"; "U4ac"; "U4bc"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec5JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSecE3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.
Lemma NXE5a_0 : ltac2:(tb__ "0|0|
S2S9S2eVGS0;S6S1fS27A1A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert5a_0 : ltac2:(tb__ "0|3|
S2S9S10S1Ufa0S7S0S20S8S0A1A3VGS0;S7SeSfS27Z1S4Z0M0A1M1A3S8SeA1M2A3S7SeSfS2bG0G1A3G2A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [DPENT] GS0 [mkVNA U4ac 1 (SLit 0)] [mkVNA X5ac 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.run5a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.run5a__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g41_0la : ltac2:(tb__ "0|6|
S19S15S3S1eQ40M0A1M1S12OF_;S2S18Vst;S17A3S2SaS14A1VW;S8S14A1A3F_;S26VW;Vst;A2S16R6A1S1aS3S3SaG1A1M2SdS0S0A2M3S2dG3R1S24R5A1A3S23R2ScS0S0S1dG0RbA2S25S1dG0S5RcPcA2A2A1A4A2F_;Fbn;S22R5RbR4A3S11S1S13S1S1bU0M4Vst;S1cS21S19S2fR1A1LX;M5R6A2ReRdR5RbA8S29R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S3G2S11S1S13S1S1bG4Vst;S1cG5RbRaR9R8A8S30R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCONT.
  eapply esec_g41 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := (fun X : AA => bumpP X)) (T4 := T4ac) (U4 := U4ac) (X5 := X5ac) (C5 := C5ac)
    (WU4 := WU4a_0) (DU4 := DU4a_0) (NXU4 := NXU4a_0) (HU4 := HU4a_0) (Cert5 := Cert5a_0)
    (NXE5 := NXE5a_0) (ECert5 := ECert5a_0) (HDSE := depot_call_SE_0la);
    [exact HW | exact HUS | exact HKc | exact HCONT].
Qed.
Lemma NXE5b_0 : ltac2:(tb__ "0|0|
S2S9S2eVGS0;S6S1fS28A1A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert5b_0 : ltac2:(tb__ "0|3|
S2S9S10S1Ufa0S7S0S20S8S0A1A3VGS0;S7SeSfS28Z1S4Z0M0A1M1A3S8SeA1M2A3S7SeSfS2cG0G1A3G2A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [DPENT] GS0 [mkVNA U4bc 1 (SLit 0)] [mkVNA X5bc 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.run5b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.run5b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g41_0lb : ltac2:(tb__ "0|6|
S19S15S3S1eQ40M0A1M1S12OF_;S2S18Vst;S17A3S2SaS14A1VW;S8S14A1A3F_;S26VW;Vst;A2S16R6A1S1aS3S3SaG1A1M2SdS0S0A2M3S2dG3R1S24R5A1A3S23R2ScS0S0S1dG0RbA2S25S1dG0S5RcPcA2A2A1A4A2F_;Fbn;S22R5RbR4A3S11S1S13S1S1bU0M4Vst;S1cS21S19R1LX;M5R6A2ReRdR5RbA8S2aR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S3G2S11S1S13S1S1bG4Vst;S1cG5RbRaR9R8A8S31R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCONT.
  eapply esec_g41 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := (fun X : AA => X)) (T4 := T4bc) (U4 := U4bc) (X5 := X5bc) (C5 := C5bc)
    (WU4 := WU4b_0) (DU4 := DU4b_0) (NXU4 := NXU4b_0) (HU4 := HU4b_0) (Cert5 := Cert5b_0)
    (NXE5 := NXE5b_0) (ECert5 := ECert5b_0) (HDSE := depot_call_SE_0lb);
    [exact HW | exact HUS | exact HKc | exact HCONT].
Qed.
End INST.
End SpineMallocSec5JEL.

