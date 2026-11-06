(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3 ASlot_W1 ASlot_W10.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "46Stdlib6ZArith6BinInt1Z02le37Corelib4Init5Logichc3and37Corelib7Numbers7BinNumsj61Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~l39small_cnt02ltl37med_cnthc2eq06modulol3ahalve_even37Corelib4Init9Datatypess53natl39halve_big04land" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma small_cnt_range : ltac2:(zQ "50!h8!j0!kf!p1!pd>2sc$2>1i$2>0@2$1@2$0Z^2@2$4^2+9>0@2$1@2$0Z^2@2$4^2+3@2$1@2$0+4@2$3^4^3@2$0@2$3^4^3+hf").
Proof. intros sc i.
  intros Hsc Hi.
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). ndestruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). ndestruct Hi' as (k & -> & Hk).
  unfold small_cnt. rewrite !Nat2Z.id.
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [cbn [nth small_cnt_tab]; lia|]); lia |]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
End HALVE.

Lemma med_cnt_range : ltac2:(zQ "70!j0!q1!h8!kf!qb!pd!r0>1i$3>0@2$0@2$2Z^1@2$5^1+4@2$0@2$0@2$2+h4@1$1^2@2$2@1$1^2+i0@3$4$3@2$6@1$1^2+4Z").
Proof. intros i.
  intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; [change (med_cnt 0) with 28| change (med_cnt 1) with 24| change (med_cnt 2) with 20| change (med_cnt 3) with 32]; (split; [lia| reflexivity]).
Qed.

Lemma halve_even_range : ltac2:(zQ "50!h8!kf!r8!td!j0>1F$3>3cnt$1>1u$1>0@2$0+1^2@2$4@2$0+1@3$2^4^3^2@2$0@3$2^4^3^2^3").
Proof. intros F.
  induction F as [|F IH]; intros cnt u Hc; cbn [halve_even]; [lia|].
  destruct (Z.even cnt && (u <? 4 * cnt)) eqn:E; [|lia].
  apply andb_prop in E. destruct E as [E _]. rewrite even_of_land1 in E. apply Z.eqb_eq in E. rewrite land1_mod2 in E.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) u ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

Lemma halve_big_range : ltac2:(zQ "50!h8!kf!u3!td!j0>1F$3>3cnt$1>2sz$1>0@2$0Z^2@2$4@2$0Z@3$2^4^3^2@2$0@3$2^4^3^2^3").
Proof. intros F.
  induction F as [|F IH]; intros cnt sz Hc; cbn [halve_big]; [lia|].
  destruct (_ <=? _); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) sz ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

Lemma land3_range : ltac2:(zQ "40!uf!h8!j0!kf>1x$3@2$2@2$1Z@2$0^1+3@2$1@2$0^1+3+3").
Proof. intros x.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 3 n); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : mrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.
End COUNT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : ltac2:(zQ "20!h8!j0@2$1@2$0Z?4cnt0@2$0?4cnt0+i0").
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

Lemma cnt1_range : 0 <= cnt1 <= 32.
Proof. unfold cnt1. destruct (_ && _); lia. Qed.
End CNT2.
(* [comment removed for export] *)
