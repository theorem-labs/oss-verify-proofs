(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_W13 ASlot_W14 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P ASlot_M4 ASlot_M5P.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~hc7slot_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m84aptr37Corelib4Init5Logicqd2eqm8cget_meta_recm8aget_stridem86mstatem86region46Stdlib6ZArith6BinInt1Zv43addv42le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hh73ivlhh77outside37Corelib4Init9Datatypeshm54listhm53appqd3andqd3iffv43mulqd2exqd3notqd2orv42lt01Nm84area35stdpp7numbers1Nhrd6eq_dec35stdpp7numbers1Zht86eq_dec25stdpp9countablehv3bN_countablehv3bZ_countablehv3eprod_countable25stdpp9decidableij4bprod_eq_dec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~il49meta_slotm87s_areas25stdpp4baseiqd7is_Someiqd6lookup25stdpp4gmapise4gmapisebgmap_lookupm84UNITm82IBm8asize_classv43sub89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_M5D3HCW~~~~~~jh04nreqm8dsize_to_classjh04nclsv43pow" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma slot_ok_N : ltac2:(zQ "a0!h9!le!q6!s1!s6!t5!u2!ub!hgc!hh2>2st$6>1g$2>1b$2>1r$7>3idx$0>1n$0>1N$0>0@6$1^7^6^5^4^3^2>0@3$3$0@1$5@2$4^8^7@2$8^2+4>0@2$9Z^3@6$1^a^9^8^7^6^4").
Proof. intros st g b r idx n N.
  intros SO STR N0. destruct SO. constructor; try assumption; try lia.
  intros off O0 OF. apply so_q16; lia.
Qed.

Lemma outside_app' : ltac2:(zQ "70!hl3!hla!hnd!ho5!hoc!hp2!h9>2W1@1$2$0>2W2@1$2$0>1a$6@2$5@2$1@3$3$0^3^2^1@2$4@2$1^3^1@2$1^2^1").
Proof. intros W1 W2 a. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma arith_prog_dec : ltac2:(zQ "a0!h9!hh2!hoc!s1!hgc!hp8!hpe!hq3!hq9!hqe>1a$0>1c$0>1s$0>1n$0>0@2$9Z^2@2$8@2$6$0\1j$0@2$2@2$2@2$1Z^1@2$1^1^3@3$3$0^6@2$4^5@2$5^4^1>1j$0>0@2$2@2$1Z^1@2$1^1^3@1$7@3$3$0^7@2$4^6@2$5^5^2").
Proof. intros a c s n.
  intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
  - pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
    destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
    + left. exists ((a - c) / s). split; [lia|]. lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
  - right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.

Lemma meta_slot_mono : ltac2:(zQ "h12!hr3!h9!q6!hr6!hse!hu9!ig4!ih3!ii2!ik5!ip6!u2!iq3!ir9!is4!ita!iu2&@4$f$2@4$9$0$4$1$5@6$8$0$4$6$1$5$7$3&@4$h0$2@4$9$0$4$1$5@6$8$0$4$6$1$5$7$3>3stA$b>3stB$b>1g$2>0>1a$2>0@2$d$3@6$e$2$3~0~1^1@1$c^4@2$d$3@6$e$2$3~0~1^2@1$c^4>0@2$a^4^2@2$a^4^3").
Proof. intros stA stB g.
  (intros HA nd_i1; ndestruct nd_i1 as (ar & arr & kk & Ha & Hk & E)). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
  nexists ar, arr', kk. auto.
Qed.

(* [comment removed for export] *)
Definition nreq : ltac2:(zQ "10!h9>2sc$0>4cnt1$0$0") := ltac2:(zQ "70!h9!iv1!hp8!iv8!ivd!hgc!jga\2sc$0\4cnt1$0@2$6@2$5$1@2$2^1@2$2$1@1$4^2$3").
Definition ncls : ltac2:(zQ "10!h9>2sc$0>4cnt1$0$0") := ltac2:(zQ "30!h9!jl6!jle\2sc$0\4cnt1$0@1$2@2$1^2^1").

Lemma nest_class : ltac2:(zQ "c0!hoc!hh2!hp8!jme!ivd!jl6!hgc!h9!iv1!hqe!s1!jn6>2sc$7>2SC@2$0@2$1Z^1@2$9^1+j0>4cnt1$7>0@2$0@2$1+1^1@2$1^1+i0>0@2$1@2$6@2$2@2$2@1$4^4$8^2$8+og0@2$0@3$a$7@2$5^5^3@2$6@2$2@2$2@1$4^5+h0^3+c@2$0@2$0@2$1Z@2$3^5^3@2$1@2$3^5^3+ha@2$0@2$1@2$6@2$2@2$2+h0@1$4^5^3+h0@2$2$8@1$4@2$3^5^3@2$0@2$9^5@2$3^5^3@2$0@2$0@2$1Z@2$5^5^3@2$9@2$5^5^3@2$b+2+i0@2$1@2$6@2$5^5^3+4@2$2+h0@1$4@2$3^5^3").
Proof. intros sc SC cnt1.
  intros C1 SM. pose proof (size_class_range sc SC) as SZR.
  assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
  assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
  pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
  assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
  destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
  split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
  split.
  { destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
    destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
    pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
  split; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Hypothesis IHf : alloc_slot_stmt2 f.




(* [comment removed for export] *)


End LEVEL.

End HCW.

(* [comment removed for export] *)
