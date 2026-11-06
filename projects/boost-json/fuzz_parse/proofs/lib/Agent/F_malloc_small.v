(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface F_malloc_join.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc6mstate37Corelib4Init9Datatypesm34boolm34andbm36option01Nhc4aptr46Stdlib6ZArith6BinInt1Zpc3eqbpc3lorm34prodhc6activehc5usagepc3addpc3lebm32idm34negbm34pair02N0hccget_meta_rechc7m_availhc7m_freedhc4metapc4evenpc3ltb25stdpp6optionhj2bfrom_option37Corelib4Init5Logichkf2eqpc4landpc6modulopc3powm34truehkf3iffhcasize_classm33orb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~hq04zseq36Stdlib5Lists4Listhv27forallb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteF_malloc_small3HCW~~~~~~ih0alor1_checkpc2lehkf3andpc2ltih0h0lor1_range_checkih09coarse_schkf2or" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition coarse_sc : ltac2:(zQ "20!h9!la>2st$1>2sc$0$0") := ltac2:(zQ "h90!h9!nb!o2!o9!p2!p5!r4!ra!s0!s7!t0!t8!te!u4!u9!v0!v7!vb!hga!hh4!hhe!la!hi5!hic!hk0\2st$h5\2sc$0M3\1x@1$3$5$0@2$9^2^1\1a$5^2M1\0$1$0@2$2@2$2@2$2@2$2@2$c+4^1@2$h7^1+i0@1$e@2$6^1+6@1$h6^1@2$6@2$a^2^1Z=6usage1$0@2$a^2@2$7^1+1=6usage1$0M3\1x@1$3$5$0@2$9^3@2$7^2+1\1a$5=2ar$h4@2$h1^4@5$h8@2$8$4$0@2$8$4$0@1$d@2$8$4$0@4$f$4$0$h0-1@2$9^4@2$7^3+1M1\0$1$0@2$2@2$6@1$h2^1Z@2$6@1$h3^1Z@2$b^3+3^3@2$b^1+3M1\0$1$0@2$c^1+c@2$7^3+1^3^1").

Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  malloc_small_ctrl lay st n k bail =
  let sc := coarse_sc st (size_to_class n) in
  let g := active st sc in
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.
Proof. reflexivity. Qed.


Lemma land_ones64 : ltac2:(zQ "50!h9!hm3!hm9!hn0!hn9>1y$0@3$1$0@2$2^1+vvvvvvvvvvvvvvvf@2$3^1@2$4+2+k0").
Proof. intros y. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma land_1_even : ltac2:(zQ "70!hm3!h9!nb!hnf!ho6!hi5!hm9>1x$1@2$4@3$0$1@2$6^1+1Z@3$0$2@1$5^1$3").
Proof. intros x.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.even_spec. split.
  - intros H. exists (x / 2). lia.
  - intros [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : MFACTS st LB.
Hypothesis MR : mrep st1 m1.
Hypothesis MI : mem_inv asegs m1.

End COARSE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lor1_check : ltac2:(zQ "10!nb$0") := ltac2:(zQ "b0!o2!h9!hod!te!u9!hpa!hua!ig5!hi5!ra!hic@3$7$1\2sc$1@2$5@1$4@2$0@2$0@2$3+4^1@2$a^1+i0@1$8^1@2$3@1$2^1@1$2@2$9^1+1@2$6Z+j0").
Lemma lor1_check_true : ltac2:(zQ "40!nb!hnf!hm3!ilb@3$2$0$3$1").
Proof. vm_compute. reflexivity. Qed.

Lemma size_class_lor1 : ltac2:(zQ "a0!hod!im9!nb!hnf!ime!hm3!h9!hi5!ra!in5>2sc$6>0@2$4@2$1+4^1@2$9^1+i0>0@3$5$2@1$7^2$3@2$1@1$0^3@1$0@2$8^3+1").
Proof. intros sc.
  intros H E. pose proof (forallb_zseq _ 0 48 sc lor1_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  replace (4 <=? sc) with true in X by (symmetry; apply Z.leb_le; lia).
  replace (sc <? 32) with true in X by (symmetry; apply Z.ltb_lt; lia). rewrite E in X. cbn [andb negb orb] in X.
  apply Z.leb_le. exact X.
Qed.

Definition lor1_range_check : ltac2:(zQ "10!nb$0") := ltac2:(zQ "70!h9!ra!o2!hua!ig5!te!hic@3$4$0\2sc$0@2$2@2$5Z@2$1^1+1@2$6@2$1^1+1+j0@2$3Z+j0").
Lemma lor1_range_check_true : ltac2:(zQ "40!nb!hnf!hm3!ina@3$2$0$3$1").
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_range : ltac2:(zQ "50!ime!im9!ra!in5!h9>2sc$4>0@2$0@2$1Z^1@2$3^1+j0@2$0@2$1Z@2$2^2+1@2$3@2$2^2+1+j0").
Proof. intros sc.
  intros H. pose proof (forallb_zseq _ 0 48 sc lor1_range_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

Lemma coarse_sc_cases : ltac2:(zQ "c0!ime!hm3!h9!iof!im9!in5!nb!hnf!ipc!la!hi5!ra>2st$9>2sc$2>0@2$0@2$4Z^1@2$5^1+j0@2$8@3$1$2@2$3^3^2^2@2$0@3$1$2@2$3^3^2@2$b^2+1@2$0@2$0@2$4+4^2@2$5^2+i0@3$1$6@1$a^2$7").
Proof. intros st sc.
  intros H. unfold coarse_sc. destruct (active st sc); [left; reflexivity|].
  destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [|left; reflexivity].
  apply andb_prop in E. destruct E as [E E5]. apply andb_prop in E. destruct E as [E E4].
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  cbv zeta. destruct (_ <=? 12); [right|left]; auto.
Qed.

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis MED0 : rw_cells asegs m0 MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End SMALL.

End HCW.

(* [comment removed for export] *)
