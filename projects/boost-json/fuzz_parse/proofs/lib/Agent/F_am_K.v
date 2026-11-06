(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat06length37Corelib4Init5Logici52eq37Corelib7Numbers7BinNumsje4Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~le5zeros35stdpp9bitvectorbdefinitionsq82bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~sa4cell04consle2wzsa2C8sa2C404list03nilleameta_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hja5meta0hja6mstatehja4aptrhja4areaje1Nje1Z35stdpp7numbers1Nhq36eq_dec35stdpp7numbers1Zhre6eq_dec25stdpp9countableht9bN_countableht9bZ_countableht9eprod_countable25stdpp9decidableihabprod_eq_dec25stdpp4gmapija4gmap04Some06optionhja6mkAreahja7s_areashja7upd_ctxhja3ctxhja9set_areas25stdpp4baseip06insertip06lookup25stdpp8fin_mapsir0amap_insertijabgmap_lookupijah2gmap_partial_alter04None02idhja6NSLOTShja7a_checkhja6a_nexthja8a_nslotshja4aaddhjah7c_avail_meta_area_counthjah0c_meta_area_tailhja8c_secrethja4mctxhjah9set_avail_meta_area_counthjah4set_avail_meta_areashjah2set_meta_area_headhjah2set_meta_area_tail46Stdlib6ZArith6BinInt1Zjtb3sub25stdpp6optionjvabfrom_option" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zeros_length : ltac2:(zQ "60!h8!hd!j9!l7!q0!s5>1n$0@3$2$0@2$1@1$5@1$3#8@1$4^1^1"). Proof. intros n. unfold zeros. apply repeat_length. Qed.

Lemma meta_cells_meta0 : ltac2:(zQ "b0!hg6!hgd!hh3!hh8!hhd!hi2!hi8!j9!hid!hn8!ho1>2st$a@3$7@1$5$0@2$8^1$9@3$1$0@1$3@1$2Z@3$1$0@1$3@1$2Z@3$1$0@1$3@1$2Z@3$1$0@1$4@1$2Z@3$1$0@1$4@1$2Z@3$1$0@1$3@1$2Z@1$6$0").
Proof. intros st. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition carve_st : ltac2:(zQ "20!ho1!hob>2st$0>1p$1$0") := ltac2:(zQ "i94!hob!hp3!hpb!hpf!hr4!hsf!hua!hv9!ig8!iib!ik6!ike!ho1!il4!ilc!im6!in1!inc!io3!ipc!iq6!is0!ise!itd!iv4!iva!ive!jg8!jh3!jhd!ji9!jj1!jkd!jm2!jme!jn6!jp4!jqd!js4!jv3!kg8&@4$a$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1&@4$h7$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1&@4$h5$0$1~0~1&@4$h6$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1\2st$c\1p$0=3st1$c@2$h0\1c$i2@2$i4@2$b$0@2$he^2+hgg0@2$i3@2$i7@1$hf^1+1^1^2=3st2$cMd\1x@1$d$0$c@1$i0@1$h1^1\2tl$0@2$h2@7$h3$0$1~0~2^1Md\1x@1$d$1$1@6$h4$0$1~0~3^1@1$f^2\1a$1@3$e@1$hb^1@2$b$0^4@1$hd^1@3$eZ@2$b$0^3Z@1$f^2^2@2$h0@1$i5@2$b$0^2^1=3st3$c@2$h0@1$i6@2$b$0^3^1=3old$1@5$i8$1$1@1$h9$1@3$eZ@1$h8$0Z@6$h4$0$1~0~3^4@1$f^1@2$h2@7$h3$0$1~0~2^5@3$e@1$i1@1$h1^2@1$hc^1$ha@1$f^2^2").

Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
  am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
