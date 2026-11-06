(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc6mstatehc6region01N37Corelib4Init5Logicmf3and46Stdlib6ZArith6BinInt1Zo93addo92leo92lt25stdpp9countabler1bN_countable35stdpp7numbers1Nt06eq_dec37Corelib4Init9Datatypesua4Someua6optionmf2eqmf3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~hhd5lr_lohc6r_basehc5r_lenhcbround_up_pghc9s_regions25stdpp4basehp36lookup25stdpp4gmaphq94gmaphq9bgmap_lookupua4boolua4true79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7F_am_K2~~~~~~htabclear_rangehcblive_rangeshcbranges_freeo96modulo" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.

(* [comment removed for export] *)
Definition clear_range : ltac2:(zQ "20!h9!la>2st$1>2lo$0>1n$0P") := ltac2:(zQ "h60!m3!mc!h9!o3!q1!q7!qc!s2!u1!hg2!hg9!hh2!hh7!hlf!la!hm8!hn1!hn9!ho7!hpf!hr5!hrd\2st$e\2lo$2\1n$2>3rid$1>1r$0>1x$2>0@3$b@1$a$0@6$h3$1$0@4$h4$1$8$7$0@4$h5$1$8$7$0^3@1$h2^6@2$9$0^2>0@2$3@2$5@1$d^3^2@2$6^2@2$4@1$f^3@1$h1@1$h0^3@1$c@2$3@2$5^7^3@2$6^3@2$4^7^6").

Lemma clear_range_of_ranges_free : ltac2:(zQ "80!h9!hsc!ht3!hh2!iha!ii9!la!ij7>2st$6>2lo$0>1n$0>0@3$3$1@3$7@1$5^3^2^1$2@3$4^4^3^2").
Proof. intros st lo n.
  intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma round_up_pg_aligned : ltac2:(zQ "40!h9!hh2!hn9!ik5>1x$0>0@3$1$0@2$3^1+hgg0Z@3$1$0@1$2^2^2").
Proof. intros x. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : mrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.
End GROW.
