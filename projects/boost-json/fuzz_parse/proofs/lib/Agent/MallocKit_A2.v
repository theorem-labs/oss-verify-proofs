(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require KStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hc3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~m52wa37Corelib4Init9Datatypesq46option37Corelib4Init5Logics53ands52eq04Npos46Stdlib6ZArith6BinInt1Zua3addua2leua2lt35stdpp9bitvectorbdefinitionshh22bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocKit_A2~~~~~~hj58agree_on79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~ho68mmap_len79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hsfbround_up_pghsf5Knownhsf9cell_readhsf7cellvalhsf7shadow0hsf4mctxhsf4optrhc7ptrs_inhsf8c_activehsfcc_avail_metahsfh2c_avail_meta_areashsf5c_brkhsfh0c_free_meta_headhsfh0c_meta_area_headhsfh0c_meta_area_tail01Nhsf4aptrhsf8brkstatehsf6mstatehsf7upd_ctx25stdpp9countablejg9bZ_countable25stdpp4gmapji94gmap35stdpp7numbers1Zjjd6eq_dechsf8step_seqhc7optr_inhsf5m_memhsf6m_nexthsf6m_prevhsf4metahsf8put_meta" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.
End PEXT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on : ltac2:(zQ "20!h9!lf>1m$1>2m'$1>1A$0>1n$0P") := ltac2:(zQ "b0!h9!lf!pf!rc!t9!tf!u4!hg2!hg8!hgd!hif\1m$1\2m'$1\1A$0\1n$0>1a$0>0@2$4@2$8^3^1@2$9^1@2$7^3^2@3$5@1$3@1$a@1$6#8@1^5@1$2^2@1^6@1$2^2").

Lemma agree_on_sub : ltac2:(zQ "50!h9!hna!lf!hg2!hg8>1m$2>2m'$2>1A$0>1n$0>2A'$0>2n'$0>0@4$1^6^5^4^3>0@2$4^5^3>0@2$4@2$3^4^3@2$3^6^5@4$1^9^8^5^4").
Proof. intros m m' A n A' n'. intros AG H1 H2 a Ha. apply AG. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_round_up : ltac2:(zQ "40!h9!tf!hs3!igd>1l$0@3$1$0@1$2^1@1$3^1").
Proof. intros l. unfold mmap_len. symmetry. apply KStep.round_up_pg_eq. Qed.

Lemma cell_read_shadow0 : ltac2:(zQ "60!tf!h9!ihc!ii5!ij2!ijd>1o$1@3$0$4@2$3$5^1@1$2Z").
Proof. intros o. unfold cell_read, shadow0. cbn. rewrite !lookup_empty. reflexivity. Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : mrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma nr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
Lemma nr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite nr_regions. apply lookup_insert_eq. Qed.
Lemma nr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma nr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.

Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : mrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (MLOCK <= a < MLOCK + 4 \/ LIBC <= a < LIBC + 0x408 \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).
End DROPREGION.
Lemma ptrs_in_upd_ctx_scalar : ltac2:(zQ "h40!ik8!tf!il0!il8!im2!ime!ine!ip5!ipe!ir3!is8!itd!h9!iu0!iu8!iv4!ive!jha!jj5!jke>1P>0$bP>2st$f>1f>1x$0$0>0>1c$0@3$1$2@1$8@1^2^1@1$8^1>0>1c$0@3$1$2@1$5@1^3^1@1$5^1>0>1c$0@3$1$2@1$9@1^4^1@1$9^1>0>1c$0@3$1$2@1$a@1^5^1@1$a^1>0>1c$0@3$1$2@1$6@1^6^1@1$6^1>0>1c$0@3$1@4$h2$c$h3$h1$d@1$4@1^7^1@1$4^1>0>1c$0@3$1$e@1$7@1^8^1@1$7^1>0@2$3^a^9@2$3^b@2$h0^9^a").
Proof. intros P st f.
  (intros E1 E2 E3 E4 E5 E6 E7 nd_i1; ndestruct nd_i1 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
  rewrite E1, E2, E3, E4, E5, E6, E7.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [|split; [exact H9| exact H10]].
  intros g. exact (H8 g).
Qed.
Lemma ptrs_in_step_seq : ltac2:(zQ "40!il8!itd!iv4!jl8>1P>0$1P>2st$2>0@2$0^2^1@2$0^3@1$3^2").
Proof. intros P st. intros H. unfold step_seq. destruct (c_seq (ctx st) =? 255); (apply ptrs_in_upd_ctx_scalar; [..|exact H]; reflexivity). Qed.
Lemma ptrs_in_put_meta : ltac2:(zQ "a0!jm4!il8!itd!iu0!jme!jn7!jo1!job!iv4!jp3>1P>0$2P>2st$8>1g$3>2mr$7>0@2$0^4@1$6^1>0@2$0^5@1$5^2>0@2$0^6@1$4^3>0@2$1^7^6@2$1^8@3$9^6^5^7").
Proof. intros P st g mr.
  (intros Q1 Q2 Q3 nd_i2; ndestruct nd_i2 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx put_meta set_metas s_metas s_areas s_groups] in *.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [|auto]. intros g'. unfold get_meta_rec. cbn [s_metas put_meta set_metas].
  destruct (decide (g' = g)) as [->|NE].
  - rewrite lookup_insert_eq. cbn. auto.
  - rewrite lookup_insert_ne by congruence. apply H8.
Qed.
(* [comment removed for export] *)
