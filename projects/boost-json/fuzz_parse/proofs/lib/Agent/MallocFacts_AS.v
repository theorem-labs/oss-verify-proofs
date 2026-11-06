(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep MallocTree MallocFacts_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34prodm36optionm34Somem34pair37Corelib4Init5Logicp92eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~r22bSr22kS01M02ev09try_avail79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree~~~~~~hh04SRet46Stdlib6ZArith6BinInt1Zhl52lep93and02IB04UNIT0asize_classhl53addhl53mulp92exm33nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hq83mem89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS3HCW~~~~~~hv23ISThv26req_okhq87leaf_of0aalloc_slot08full_layhl52lt04aptrm34Nonep93not0cget_meta_rec04optr05m_mem06m_next06m_prev0bm_sizeclasshv24lmem06active79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~it09meta_slot0h0c_free_meta_head03ctx04meta0am_freeable0am_last_idx08m_maplenhl53pow07m_avail07m_freedhv25mw_ok0aget_stride04ghdrk61N35stdpp7numbers1Njp76eq_dec35stdpp7numbers1Zjr26eq_dec25stdpp9countablejsdbN_countablejsdbZ_countablejsdeprod_countable25stdpp9decidablekgebprod_eq_dec0cg_active_idx08s_groups25stdpp4basekk66lookup25stdpp4gmapklc4gmapklcbgmap_lookupm33fstm33snd07Unknown09cell_read07cellval0aget_shadowhl57testbitm34boolm33orbm34true05meta0m34list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~ku1bAREACH_fromku15block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~lje3ISTlje7ta_fail" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition ta_fail : ltac2:(zQ "20!je!lf>2sc$1>2st$0>3st1$0P") := ltac2:(zQ "d0!lf!je!nb!o2!ob!p2!qd!v4!v9!ve!hg1!hg5!hkd\2sc$0\2st$1\3st1$1@3$6@1$9@1$3@2$2$1$0@5$b@1$3@2$2$1$0^3^2@2$8$1$0@1$7@2$2$1$0@4$c$a$0@1$3@2$2$1$0@2$4@2$2$1$0@4$5$1$0^1Z").

(* [comment removed for export] *)
Definition req_ok : ltac2:(zQ "10!lf>2sc$0>3req$0P") := ltac2:(zQ "80!lf!hmd!hn3!hn9!hnd!ho3!hof!hp6\2sc$0\3req$0@2$2@2$1Z^1@2$1@2$6^1$3@2$7$4@1$5^2").

(* [comment removed for export] *)
Inductive IST (st0 : mstate) : mstate -> Prop :=
| ist_top : forall t, (s_tick st0 < t)%N -> IST st0 (set_tick t st0)
| ist_am : forall o st sc st1 st2 m,
    IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
    leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
    IST st0 st2.

(* [comment removed for export] *)
Definition ISTR : ltac2:(zQ "10!je>3st0$0>3st3$0P") := ltac2:(zQ "h30!lf!je!hpd!nb!hn3!hq2!o2!hub!ob!p2!ijd!ik4!v4!v9!ike!il9!im5!hmd!imf\3st0$1\3st3$1@2$2$7\1o$7@2$2$1\2st$1@2$2$5\1f$5@2$2$0\2sc$0@2$2$0\3req$0@2$2$0\3idx$0@2$4@2$a^8^5@2$4@2$4@2$h1Z^3@2$h2^3+j0@2$4@2$b^3^2@4$e@1$6@2$3$1$0^6@8$f@1$6@2$3$1$0$h0^4^5^3^2@2$d$1$0@1$c@2$3$1$0@2$8@2$3$1$0@4$9$1$0^7^1").

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lmem : ltac2:(zQ "20!in5!je>2cs$1>1g$0P") := ltac2:(zQ "b0!in5!inb!qd!io2!io8!ip6!hn3!ipc!iq3!iqb!je\2cs$a\1g$0@2$6@1$3@3$2$5@1$7@2$4^2^1@1$1$0@2$6@1$3@3$2$5@1$8@2$4^2^1@1$1$0@1$3@3$2$5@1$9@2$4^2^1@1$1$0").

Definition fact_lists : ltac2:(zQ "10!je>2cs$0P") := ltac2:(zQ "h04!in5!io8!qd!ip6!hn3!ir3!ob!lf!is0!inb!io2!ipc!is8!iq3!iqb!je&@3$2$3@1$b@2$1^3^2@1$9$0&@1$a~0&@3$2$7@1$5@2$1^5^3@1$5@2$1^5^4&@2$4@2$8^5^3~2\2cs$f@2$4>2sc$7>1g$0>0@3$2$3@2$c^3^2@2$6$0^1@2$8^4^2@2$4>1g$0>1n$0>0~1>0@3$2$3@1$d@2$1^4^3@2$6$0^2~3>1g$0>1p$0>0~1>0@3$2$3@1$e@2$1^4^3@2$6$0^2~3").

Definition fact_freelist : ltac2:(zQ "10!je>2cs$0P") := ltac2:(zQ "h00!in5!hn3!qd!ip6!io8!inb!ob!io2!jh2!ipc!iq3!hpd!jhf!jj2!iqb!je\2cs$f>1h$0>0@3$2$3@1$c@1$d^2@2$6$0^1@2$1@2$8^3^2@2$1@3$2$3@1$9@2$4^3^2@1$5$0@2$1@1$7@3$2$3@1$a@2$4^3^2@1$5$0@2$b$0\1p$0@2$1@3$2$3@1$e@2$4^4^3@2$6$0^1@2$1@2$8^4^1@2$1@3$2$3@1$9@2$4^4^1@1$5$0@1$7@3$2$3@1$a@2$4^4^1@1$5$0").

Definition mw_ok : ltac2:(zQ "10!jj7>2mr$0P") := ltac2:(zQ "90!hn3!hmd!jjd!jk9!jl5!ir3!jj7!imf!jlf\2mr$6@2$0@2$0@2$1Z@1$3^1@2$1@1$3^1+hf@2$0@2$0@2$1Z@1$2^1@2$1@1$2^1+1@2$0@2$0@2$1Z@1$5^1@2$1@1$5^1+jf@2$0@2$1Z@1$4^1@2$7@1$4^1@2$8+2+j4").

Definition fact_mw : ltac2:(zQ "10!je>2cs$0P") := ltac2:(zQ "a0!io8!hn3!jm6!jmf!hmd!imf!jlf!jn8!in5!je\2cs$9>1g$8@2$1@1$7@2$0^2^1@2$1@2$1@2$4Z@1$2@2$0^2^1@2$5@1$2@2$0^2^1@2$6+2+i0@2$1@2$4Z@1$3@2$0^2^1@2$5@1$3@2$0^2^1@2$6+2+i0").

Definition fact_host_stride : ltac2:(zQ "10!je>2cs$0P") := ltac2:(zQ "f0!io8!in5!ir3!qd!hmd!ob!hn3!lf!hnd!jo1!ipc!je!ip6!ho3!hp6\2cs$b>1g$1>1b$1>0@3$3$c@1$a@2$0^3^2@2$5$1^1>0@2$6@2$4Z@1$2@2$0^4^3@2$4@1$2@2$0^4^3+hb@3$3$7@1$9@2$0^5^4@2$e$8@1$d@1$2@2$0^5^4").

(* [comment removed for export] *)
Definition fact_links : ltac2:(zQ "10!je>2cs$0P") := ltac2:(zQ "a0!in5!ob!qd!io8!ip6!iq3!iqb!hn3!is0!je\2cs$9>1g$0>0@2$8^2^1@2$7>1n$0>0@3$2$4@1$5@2$3^4^3@2$1$0^1@3$2$4@1$6@2$3^5^2@2$1$0^4>1p$0>0@3$2$4@1$6@2$3^4^3@2$1$0^1@3$2$4@1$5@2$3^5^2@2$1$0^4").

Definition fact_sc0_full : ltac2:(zQ "10!je>2cs$0P") := ltac2:(zQ "h80!lf!in5!jod!qd!jp3!jq8!js3!io8!ob!jte!jud!jvc!khf!o2!kie!jk9!ipc!ir3!je!ip6!kjc!kl2!km8!kn0\2cs$h2>1g$1>1b$1>2gh$2>0@3$3$h3@1$h0@2$7^4^3@2$8$1^2>0@3$3@1$d$2@6$h5$1$2@4$h6$1@4$c$4$5$0$6@6$b$4$5$9$0$6$a$2@4$h7$1@4$c$4$5$0$6@6$b$4$5$9$0$6$a$2^3@1$h4^5@2$8$2^2>0@3$3$0@1$h1@2$7^6^5Z@3$3$0@1$e^4@1$f@2$7^7^6").

Definition fact_ghdr_unk : ltac2:(zQ "10!je>2st$0P") := ltac2:(zQ "he0!lf!jp3!jod!jq8!js3!nb!qd!in5!jte!jud!jvc!khf!ob!knf!o2!ko5!hn3!hpd!kob!kp4!kpf!kq8!je!kjc!hof!hmd!imf!kl2!km8!kn0\2st$h6>1b@2$5$1$0>2gh$2>1o$0>0@3$6@1$e$2@6$hb@2$5$1$0$2@4$hc$7@4$b$1$3$0$4@6$a$1$3$8$0$4$9$2@4$hd$7@4$b$1$3$0$4@6$a$1$3$8$0$4$9$2^3@1$h7^4@2$c$2^2>0@2$h0@2$h9Z^2@2$ha^2+9@2$h1$0\1h$0@3$6$h4@2$h3@2$h5^7@3$d$1$0^6@2$h8@3$f$1$0^6^4@1$h2^1").

(* [comment removed for export] *)
Definition fact_bit_stride : ltac2:(zQ "10!je>2cs$0P") := ltac2:(zQ "h50!io8!in5!qd!ir3!hmd!kr4!ob!krf!ks6!ksc!lf!hnd!jo1!jm6!jmf!ipc!je!ip6!ho3!imf!hp6\2cs$h0>1g$1>1b$1>1i$a>0@3$2$h1@1$f@2$0^4^3@2$6$1^2>0@2$4Z^2>0@3$2$7@2$8@2$5@1$d@2$0^6^5^3@2$5@1$e@2$0^6^5^3$9>0@2$h3@1$3@2$0^7^6+j0@2$4@2$h4$b@1$h2@1$3@2$0^8^7@1$c@2$0^8^7").

Record LFACTS (cs : mstate) : Prop := mkLF {
  lf_lists : fact_lists cs;
  lf_freelist : fact_freelist cs;
  lf_mw : fact_mw cs;
  lf_host_stride : fact_host_stride cs;
  lf_links : fact_links cs;
  lf_sc0_full : fact_sc0_full cs;
  lf_bit_stride : fact_bit_stride cs
}.

(* [comment removed for export] *)
Record ISTF_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkISTF {
  isf_mf : @MFACTS_g resv st LB;
  isf_lf : LFACTS (strip st);
  isf_ghdr : fact_ghdr_unk st
}.

End HCW.


(* [comment removed for export] *)
Notation ISTF := (@ISTF_g agent_reserved).


(* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition nest_ok : ltac2:(zQ "20!in5!je>1m$0>3st3$1P") := ltac2:(zQ "d0!in5!qd!ob!hn3!io2!io8!ip6!jhf!jj2!iqb!jj7!kt3!je\1m$0\3st3$c@2$3@3$1$a@2$5^1^2$b>1h$0>0@3$1$6@1$7@1$8^2@2$2$0^1@2$3@1$4@3$1$0^2^4@1$4@3$1$6@1$9@2$5^3^2@2$2$0^4").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMP_AS_g : ltac2:(zQ "40!lf!kta!nb!je>4resv@1$1@2$2$0$0>6am_pre>0$3PP") := ltac2:(zQ "b0!je!lf!kta!nb!hn3!li6!lj5!lo5!loc!hmd!imf\4resv@1$2@2$3$1$1\6am_pre>0$0P>3st0$0>2LB@1$2$6>2st$0>2sc$1>3st1$0>0@4$5?4HSEC^7^5^4>0@2$7^6^4>0@2$4@2$9Z^4@2$a^4+j0>0@3$8^5^6^4@1^a^5").

End HCW2.

Notation AMP_AS := (AMP_AS_g agent_reserved).
