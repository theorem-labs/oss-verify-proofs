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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option01Z89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree3HCW~~~~~~m53mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~r24aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_syscalls~~~~~~v75asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hk23mrdhk22wahfbbv_unsignedr22evm58pans_mem37Corelib4Init5Logichq73and46Stdlib6ZArith6BinInt1Zhs22lehs22lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~hu68mmap_ans79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~iif9neg_errnoiif9fixed_anshu69range_ansk14bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~ip94LIBChs23addk14listk14consk13nil37Corelib5Lists7ListDefive3mapip92wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~ji23memhs23powhq72ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jn94cellhk28bytes_atip95zeros89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree4HCW2~~~~~~jt29AUXV_CELLjt29auxv_list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~kj44u64sjn92C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~knc8rw_cellsr2dalloc_ceilingk14prodk14pairhq72orive6Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kv1ddisjoint_fromhq72eqhq73notk14None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsll25wviewr26mstater25rkindr26region01Nip93CTXhf7Z_to_bv25stdpp9countablels0bN_countable35stdpp7numbers1Nlu06eq_deck14Someip95lr_lor26r_baser26r_kindr25r_lenr2bround_up_pgr29s_regions25stdpp4basemjf6lookup25stdpp4gmapml54gmapml5bgmap_lookupiif6PStatehq74Truer28brkstater25c_brkr24concr23ctxiif6ps_brkr24optrk13fstjt27optr_in35stdpp7numbers1Zmsc6eq_decr24arear24ghdrls0bZ_countablels0eprod_countable25stdpp9decidablenh6bprod_eq_decr2cget_meta_recr26a_nextr26activer2cc_avail_metar2h2c_avail_meta_areasr2h0c_free_meta_headr2h0c_meta_area_headr2h0c_meta_area_tailr26g_metar25m_memr26m_nextr26m_prevr24mctxr27s_areasr28s_groupsjt27ptrs_ink14truer2blive_rangesr2branges_free36Stdlib5Lists4Listoi52Inr2h1region_live_rangejt2afresh_addrr2as_reservedll2dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeonf5bvmapiif5ps_faiif4ps_miif5ps_sok14unitip94mrepip92pwip98ticks_okjt28alloc_fpjt26am_reljt27auxv_okjt2bpres_exceptjn92C4kv13mkRkv13stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~pid2MSpid6ret_pchk27mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~po57seg_romr27RKGroupjt2bbrk_link_psji25implTr21Mip9h0alloc_meta_entryjt28AM_STACKjt27am_postr2aalloc_metahs23sub" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition mem : ltac2:(zQ "00S") := ltac2:(zQ "30!h9!jc!l9>0@1$1@1$0#k0@1$2@1$1@1$0#8").

Definition pans_mem : ltac2:(zQ "30!m2!qc!v0>1o$1>1q$2>5caddr$0>4hint$0$0") := ltac2:(zQ "a0!h9!m2!l9!jc!hja!qc!hnc!ho3!v0!ho9\1o$5\1q$8\5caddr$1\4hint$1M2\1x@1$2@1$3@1$0#8$1@3$6$4^4@1$7^2\1b@1$3@1$0#8@2$9@1$0#8^1Z").
Definition pupd_mem : ltac2:(zQ "30!qc!m2!hp7>1o$0>1e$2>1z$1$0") := ltac2:(zQ "30!m2!qc!hp7\1o$1\1e$2\1z$0^3").

Lemma pans_mem_range : ltac2:(zQ "70!m2!hpc!hrb!qc!v0!hta!hu0>1o$3>1q$4>1c$0>1h$0@2$2@2$5Z@4$1^4^3^2^1@2$6@4$1^4^3^2^1+hg0").
Proof.
  intros. unfold pans_mem. destruct (mrd asegs o (wa c)) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.

Lemma mrun_ret {R} o (r : R) : mrun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
Lemma mrun_peek {R} o p c h (k : Z -> Malloc.M R) : mrun o (SVis (EPeek p c h) k) = mrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.
Lemma mrun_vis {R} o e (k : Z -> Malloc.M R) :
  match e with EPeek _ _ _ => False | _ => True end ->
  mrun o (SVis e k) = SVis e (fun z => mrun o (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Definition implT {R} (o : mem) (t : Malloc.M R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM asegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.

(* [comment removed for export] *)

End HCW.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition mmap_val : ltac2:(zQ "20!m2!ii3>1a$1$0") := ltac2:(zQ "30!m2!ii3!imb\1a$1M1\1a$1$0^1\1e$0@1$2^1\1x$0^1").
Definition fixed_val : ltac2:(zQ "20!m2!in8>4addr$0>1a$1$0") := ltac2:(zQ "30!m2!in8!imb\4addr$0\1a$1M1\1a$1$0^1\1e$0@1$2^1^2\1e$0@1$2^1").
Definition range_val : ltac2:(zQ "20!m2!io5>1a$1$0") := ltac2:(zQ "40!io5!m2!ip2!imb\1a$0M0\1a$0$1^1\1e$1@1$3^1\7changed$2Z").

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
  exists ans o', follow (mrun o t) ans = Some (o', r).

Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. exists [], o. reflexivity. Qed.

Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
  (intros He nd_i1; ndestruct nd_i1 as (ans & o' & H)). exists (z :: ans), o'. unfold mrun, prun. cbn [eruns].
  destruct e; cbn [psel]; try exact H; destruct He.
Qed.

Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) r :
  leaf_of o (k (pans_mem o p c h)) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. (intros nd_i2; ndestruct nd_i2 as (ans & o' & H)). exists ans, o'. rewrite mrun_peek. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AUXV_CELL : ltac2:(zQ "10!m2$0") := ltac2:(zQ "20!itb!iu3@2$1$0+8").

Definition auxv_list : ltac2:(zQ "40!m2!iua!h9!jc>2x3$0>2x4$0>2x5$0>2x6$0>3x11$0>3x12$0>3x23$0>3rnd$0@1$1@1$3@1$2#k0") := ltac2:(zQ "70!m2!iv1!iv8!jh5!h9!jhc!jc\2x3$0\2x4$0\2x5$0\2x6$0\3x11$0\3x12$0\3x23$0\3rnd$0@4$3$0@1$6@1$4#k0$5@3$1$0+3@3$1$0^8@3$1$0+4@3$1$0^7@3$1$0+5@3$1$0^6@3$1$0+6@3$1$0^5@3$1$0+b@3$1$0^4@3$1$0+c@3$1$0^3@3$1$0+h7@3$1$0^2@3$1$0+h9@3$1$0^1@3$1$0Z@3$1$0Z@1$2$0").

Definition auxv_ok : ltac2:(zQ "20!m2!jm5>1m$1>1B$0P") := ltac2:(zQ "h50!hrb!m2!hta!jmc!jn3!hu0!iu3!hja!jr5!jrd!iv1!iv8!jhc!js9!kha!ki7!jm5!kme!kn6!kr7!ks3\1m$h0\1B$1@2$4$1\2av$1@2$4$1\2x3$1@2$4$1\2x4$1@2$4$1\2x5$1@2$4$1\2x6$1@2$4$1\3x11$1@2$4$1\3x12$1@2$4$1\3x23$1@2$4$1\3rnd$1@2$0@4$h3$7^b$e@3$a$8@1$h2@1$c^9@1$b$8@2$0@4$9$7^b^9@1$h1@8$f^8^7^6^5^4^3^2^1@2$0@4$9$7^b@2$6^1+8@1$dN8@2$0@2$2$h4^a@2$0@2$2^a^9@2$0@2$2@2$6^9+p0@2$3+2+k0@2$0@2$2^a@2$6^1+8@2$0@2$2@2$6^1+h0@2$3+2+k0@2$0@2$0@2$2Z^8@2$5^8@2$3+2+k0@2$0@2$0@2$2Z^7@2$5^7@2$3+2+k0@2$0@2$0@2$2Z^6@2$5^6@2$3+2+k0@2$0@2$0@2$2Z^5@2$5^5@2$3+2+k0@2$0@2$0@2$2Z^4@2$5^4@2$3+2+k0@2$0@2$0@2$2Z^3@2$5^3@2$3+2+k0@2$0@2$0@2$2Z^2@2$5^2@2$3+2+k0@2$0@2$2Z^1@2$5^1@2$3+2+k0").

Lemma Forall_disjoint_from : ltac2:(zQ "90!m2!kt3!hta!iua!kta!ku1!ku7!lid!iu3>1P>0@2$1$0$0P>1W@1$3@2$1$0$0>1a$0>1n$0>0@3$6@2$1$0$0^4^3>0>2lo$0>2hi$0>0@1^7@4$4$0$0^2^1@2$5@2$2@2$8^6^5^3@2$2^2^6@3$7^5^4^3").
Proof.
  intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pres_except : ltac2:(zQ "20!jm5!m2>1C>0$1P>1m$0>2m'$0P") := ltac2:(zQ "f0!h9!jc!ho3!l9!lje!lk4!lkb!hrb!m2!lo9!hja!jm5!hta!hu0!jmc\1C>0$8P\1m$b\2m'$b>1a$8>0@2$7@2$cZ^1@2$d^1@2$e+2+k0>0@1$5@1^5^2@2$7@3$4@1$3@1$1@1$0#8@1^4@1$2^3@1^5@1$2^3>0@1$5@3$4@1$3@1$1@1$0#8@3$9$a^5@1$2^3@1$6@1$1@1$0#8@1$5@3$4@1$3@1$1@1$0#8@3$9$a^5@1$2^4@1$6@1$1@1$0#8").

(* [comment removed for export] *)
Definition alloc_fp : ltac2:(zQ "30!m2!lp2!lpb>1K>0$2P>3st1$1>2lo$0>2sp$0>1a$0P") := ltac2:(zQ "hd2!lq3!hrb!lqc!iu3!h9!hta!hu0!ku1!m2!jn3!lqf!lr6!ho9!lt1!lv1!lvb!l9!lje!mg2!lp2!mgb!mh4!mhd!lpb!mi5!mj3!mkb!mm1!mm9&@2$c@1$4#k0@2$b@1$4#k0+hqmi0&@2$3~0-q4\1K>0$h7P\3st1$h3\2lo$8\2sp$8\1a$8@2$7@2$1@2$5^3^1@2$6^1^2@2$7@2$1@2$5~1^1@2$6^1@2$3~1+4@2$7@2$1@2$5$a^1@2$6^1@2$3$a+jq0@2$9$2\3rid$2@2$9$0\1r$0@2$1@3$h1@1$h0$0@6$ha$2$0@4$hb$2$e$d$0@4$hc$2$e$d$0^2@1$h9^6@2$f$0^1@2$1@1^7@1$h5^1@2$1@2$5@1$h2^1^3@2$6^3@2$3@1$h4^1@1$h8@1$h6^1").
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_link_ps : ltac2:(zQ "20!lp2!mn8>2st$0>1s$1P") := ltac2:(zQ "c0!m2!mo2!lqc!moa!kta!lje!mp5!mpd!mq4!lp2!mn8!mqa\2st$9\1s$aM3\1x$3P@1$6@1$8^2$1$1\3rid$2\3off$0@3$5$0@1$b^3@2$7^4@4$4$2$0^2^1").

(* [comment removed for export] *)
Definition optr_in : ltac2:(zQ "20!lqc!mr4>1P>0$0P>1p$1P") := ltac2:(zQ "70!l9!lqc!v0!mrb!mo2!m2!mr4\1P>0$1P\1p$6M0\1p@1$0$2P^1\1q$2@1^3@3$3$1$5^1$4").

Definition ptrs_in : ltac2:(zQ "20!lqc!lp2>1P>0$0P>2st$1P") := ltac2:(zQ "i90!lqc!m2!hrb!ms1!lv1!mtd!mu7!mue!v0!kt3!lt1!mv5!ng4!ni7!nj6!lvb!mrb!l9!mo2!lje!moa!mkb!mm1!mm9!nk5!nke!nl7!nm6!mp5!nnc!np0!nq4!mq4!nr8!ns1!ns9!nt2!ntb!lp2!nu2!nuc\1P>0$0P\2st$i6=1c$i5@1$i0^1@2$2@2$3^3@1$hd^1@2$2@2$3^3@1$ha^1@2$2@2$3^3@1$he^1@2$2@2$3^3@1$hf^1@2$2@2$3^3@1$hb^1@2$2>2sc$1@2$3^4@2$h9^3^1@2$2Mh4\1x$h4P@1$hc^1$h2$h2\3rid$0\3off$1@1^5^2@2$2>1g$8@2$2@2$3^4@1$i4@2$e^3^1@2$2@2$3^4@1$i3@2$e^3^1@2$3^4@1$i2@2$e^3^1@2$2>1a@2$9$0$1>2ar$6>0@3$h3@1$h1$6@6$h5@2$9$0$1$6@4$h6$8@4$d$0$4$1$5@6$c$0$4$a$1$5$b$6@4$h7$8@4$d$0$4$1$5@6$c$0$4$a$1$5$b$6^2@1$i7^4@2$f$6^1@2$2@1^6@3$h0$0$1^3@2$3^6@1$h8^2>1b@2$9$0$1>2gh$7>0@3$h3@1$h1$7@6$h5@2$9$0$1$7@4$h6$8@4$d$0$4$1$5@6$c$0$4$a$1$5$b$7@4$h7$8@4$d$0$4$1$5@6$c$0$4$a$1$5$b$7^2@1$i8^4@2$f$7^1@2$2@1^6@3$h0$0$1^3@2$3^6@1$i1^2").

Lemma ptrs_in_mono : ltac2:(zQ "30!lqc!nv7!lp2>1P>0$0P>2P'>0$0P>2st$2>0>1r$0>0@1^4^1@1^4^2>0@2$1^4^2@2$1^4^3").
Proof. intros P P' st.
  (intros HP nd_i3; ndestruct nd_i3 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
  split; [intros g; ndestruct (H8 g) as (X1 & X2 & X3); auto|].
  split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
  intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.

(* [comment removed for export] *)
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
  amr_active : forall sc, active st1 sc = active st sc;
  amr_usage : forall sc, usage st1 sc = usage st sc;
  amr_bounces : forall i, bounces st1 i = bounces st i;
  amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
  amr_seq : c_seq (ctx st1) = c_seq (ctx st);
  amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
  amr_groups : s_groups st1 = s_groups st;
  amr_slots : s_slots st1 = s_slots st;
  amr_shadow : s_shadow st1 = s_shadow st;
  amr_tick : s_tick st1 = s_tick st;
  amr_reserved : s_reserved st1 = s_reserved st;
  (* [comment removed for export] *)
  amr_metas : forall g, Some g <> mo ->
      (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
      get_meta_rec st1 g = get_meta_rec st g;
  (* [comment removed for export] *)
  amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
  (* [comment removed for export] *)
  amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  (* [comment removed for export] *)
  amr_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
      ptrs_in P st -> ptrs_in P st1;
  (* [comment removed for export] *)
  amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.

Definition AM_STACK : Z := 128.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_addr : ltac2:(zQ "20!m2!lp2>2st$1>1a$0P") := ltac2:(zQ "a0!ip2!og2!hrb!lje!m2!ks3!og9!lp2!oh7!hu0\2st$7\1a$4@2$2@2$9^1$5@3$3$0@3$8@1$6^2^1+1$1").

Lemma ranges_free_In : ltac2:(zQ "c0!m2!kt3!iu3!hta!ip2!iua!kta!og2!lje!ku1!oh7!oj8>1l@1$5@2$1$0$0>1a$0>1n$0>1b$0>1k$0>0@3$8$4@3$a^5^4^3$7>0@3$b@2$1$0$0@4$6$0$0^3^2^6@2$9@2$3@2$2^6^5^4@2$3@2$2^4^3^6").
Proof. intros l a n b k.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma ranges_free_intro : ltac2:(zQ "c0!m2!kt3!iu3!hta!ip2!iua!kta!og2!lje!ku1!oh7!oj8>1l@1$5@2$1$0$0>1a$0>1n$0>0>1b$0>1k$0>0@3$b@2$1$0$0@4$6$0$0^2^1^5@2$9@2$3@2$2^5^4^3@2$3@2$2^3^2^5@3$8$4@3$a^4^3^2$7").
Proof. intros l a n.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.

Lemma ranges_free_sub : ltac2:(zQ "90!m2!hta!ip2!og2!lje!oh7!iu3!iua!kt3>1l@1$7@2$8$0$0>1a$0>1n$0>2a'$0>2n'$0>0@3$4$2@3$5^5^4^3$3>0@2$1^5^3>0@2$1@2$6^4^3@2$6^6^5>0@2$1Z^4@3$4$2@3$5^9^6^5$3").
Proof. intros l a n a' n'.
  intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.

Lemma In_live_ranges : ltac2:(zQ "h10!lq3!lqc!m2!lt1!lv1!lvb!l9!kt3!lje!og9!lp2!oje!mj3!oj8!mkb!mm1!mm9>2st$a>3rid$1>1r$0>0@3$8@1$6$0@6$e$1$0@4$f$1$4$3$0@4$h0$1$4$3$0^2@1$c^3@2$5$0^1@3$d@2$7$2$2@1$b^2@1$9^4").
Proof. intros st rid r.
  intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma fresh_live_region : ltac2:(zQ "h50!lq3!lqc!iu3!hta!lt1!lv1!lvb!l9!lje!ku1!m2!mg2!ol3!lp2!mgb!mhd!mi5!mj3!mkb!mm1!mm9>2st$d>1a$a>3rid$1>1r$0>0@2$c^4^3>0@3$8@1$7$0@6$h2$1$0@4$h3$1$5$4$0@4$h4$1$5$4$0^3@1$h1^5@2$6$0^2@2$9@2$3@2$2^5+1@1$b^3@2$3@2$2@1$e^3@1$h0@1$f^3^5").
Proof. intros st a rid r.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.

(* [comment removed for export] *)
Lemma fresh_addr_anti : ltac2:(zQ "h80!lq3!lqc!lje!m2!lt1!lv1!hrb!lvb!l9!ol3!lp2!mgb!mh4!mhd!mj3!om1!mkb!mm1!mm9!iua!kt3!jn3!lpb!hta>2st$a>3st'$a>1a$3>0@3$2@1$h3@2$h4$3$3@1$f^2@1$f^3>0>3rid$1>1r$0>0@3$2@1$8$0@6$h0$1$0@4$h1$1$5$4$0@4$h2$1$5$4$0^2@1$e^6@2$7$0^1@2$h5$0\2r'$0@2$6@3$2@1$8$0@6$h0$1$0@4$h1$1$5$4$0@4$h2$1$5$4$0^4@1$e^7@2$7$0^1@2$6@3$2$h6@1$c^1@1$c^3@2$6@3$2$3@1$b^1@1$b^3@2$h7@1$d^3@1$d^1>0@2$9^4^3@2$9^6^4").
Proof. intros st st' a.
  intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. ndestruct HI as ([rid r] & E & HI). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    ndestruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.

Definition am_post : ltac2:(zQ "90!h9!jc!lp2!mn8!m2!ome!oq5!jm5!mr4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2st$2>1s$3>2lo$4>1m$7>3st1$2>2mo$8>2s'$3>0$5P") := ltac2:(zQ "id1!h9!jc!jn3!hrb!lje!m2!hja!ho9!lp2!l9!ome!jr5!lpb!mn8!oqe!or7!orf!lkb!iv1!iv8!kt3!os8!lk4!ku1!oq5!osf!ot7!otd!ou9!ov5!ovf!ol3!pga!jm5!ph9!phf!pi6!pma!pn0!pna!ps4!kr7!psf!mr4!iu3&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2st$8\1s$d\2lo$5\1m$i1\3st1$8\2mo$ib\2s'$d\3ms'$a@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$3@3$4$a^h1@7$i5@hf$i3^ia^i9^i8^i7^h0^f^e^i6^i5@2$ha^h4^h3^d^c^b^a^9^8^7^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^6^5^4^3^ha@1$i6^ia^h9@1$h1@1$1@1$0#k0^2@1$i8$6@2$3@2$i7$6^2@2$3@4$i4$6^2^h6@2$7@1$0#k0^i9@2$3@4$i9$6^2@2$ic@2$7@1$0#k0^i7-q4@3$h2$b@1$i2^1@1$h3$b@2$3@2$he^2@2$7@1$0#k0^i9@2$3@3$i0\1a$5@2$h7@5$hc\1k$c@1$h6@3$4$c^1$ia^h5^h7@2$7@1$0#k0^ia^1@2$hf^h9^1^h5^2@2$3@2$h9^h4^2@2$3@1$hb^h4@2$3@3$4$8@1$f^h2@1$f^h7@2$3@3$4@2$h4$5$5@1$e^h2@1$e^h7@2$3@3$4$h5@1$h0^h2@1$h0^h7@3$hd^h8^h4^h3").

(* [comment removed for export] *)
Definition alloc_meta_stmt : ltac2:(zQ "10!lp2>6am_pre>0$0PP") := ltac2:(zQ "i60!h9!jc!hja!lp2!ho9!mn8!lr6!lje!ome!pt9!pu8!jm5!jr5!pv1!mr4!hta!lkb!iv1!iv8!m2!oq5!pv5!osf!otd!qga!qh6!ovf!ph9!phf!pi6!pma!pna!ps4!kr7!ks3!qi1!iu3!qie\6am_pre>0$3P>1RT>1k>0$3>0$e@1$d^3>4bail@1$d^2>1o$b>1s$5>1Q>0^5>0$5>0$8P>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$b>2st$3>2lo$h3>4errv@1$1@1$0#k0>0@1^ic^3>0@2$h6^4^5>0@1$h7^5>0@2$9^6^ia>0@2$ha^8@2$4@1$0#k0^i8>0@4$hd$2^9^7@2$4@1$0#k0^i9>0@2$f$i2^8>0@2$f^9@2$i5@2$4@1$0#k0^ib$h8>0@4$i1$2^c@2$i4@2$4@1$0#k0^ia-q4@3$h1$c@1$hb^9@1$h2$c>0@2$hf$2^d>0@3$7@1$1@1$0#k0^id@2$6@1$0#k0+hqog0>0@3$7@1$1@1$0#k0^id@2$6@1$0#k0+hqmi0>0>3st1$3>2mo$e>2s'$5>3ms'$8>0@ha$h9^j5^j4^j3^j2^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^h6^h5^h3^j7^h2^h4^4^3^2^1>0@2$9^5^3@7$a?5HCEIL^jd^ja@2^jc^6^5^4^j8^3@7$a?5HCEIL^j8^j5@4$i3^j8^h0^j7^j6^j4^j3@7$he@hf$hc^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3@2$6@1$0#k0$h5^h2@1$h0@1$1@1$0#k0^h1@1$i0$2").

End HCW2.

(* [comment removed for export] *)
