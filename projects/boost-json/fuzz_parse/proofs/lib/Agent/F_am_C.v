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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_am_A F_am_K.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq46Stdlib6ZArith6BinInt1Zj56modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~l64aptrl64area01N35stdpp7numbers1Nq56eq_dec35stdpp7numbers1Zrf6eq_dec25stdpp9countablet9bN_countablet9bZ_countablet9eprod_countable25stdpp9decidablehh7bprod_eq_dec25stdpp4gmaphj74gmap37Corelib4Init9Datatypeshkb4Somel66mstatel67s_areashkb4Nonehkb6optionl63ctxl66mkAreal69set_areasl67upd_ctx25stdpp4basehr56inserthr56lookup25stdpp8fin_mapsht5amap_inserthj7bgmap_lookuphj7h2gmap_partial_alter79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_K~~~~~~ih98carve_stl66NSLOTSl67a_checkl68a_nslotsl64aaddl6h7c_avail_meta_area_countl6h0c_meta_area_taill68c_secretl64mctxl64optrl6h9set_avail_meta_area_countl6h4set_avail_meta_areasl6h2set_meta_area_tailj53subl6h2set_meta_area_head" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition pgal : ltac2:(zQ "10!h9>1z$0P") := ltac2:(zQ "30!h9!j0!kd\1z$0@3$1$0@2$2^1+hgg0Z").

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma carve_st_some : ltac2:(zQ "i84!p4!pb!q2!h9!r6!t0!ua!v8!hg6!hi8!hk3!hm3!hmb!j0!hn4!hne!ho6!hp0!hp6!hpf!hqb!hs1!hsb!hu5!hv3!ig2!il8!im4!imd!in7!io2!io9!iq4!ir8!is3!isa!it1!iue!jg6!jhc&@4$a$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1&@4$h8$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1&@4$h9$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1&@4$h7$0$1~0~2>2st$c>1p$0>2tl$0>2ar$1>0@3$d$i3@1$i0@1$h1^4@2$b$0^2>0@3$d@1$h0$1@6$h6$0$1~0~1^3@1$e^5@2$b$1^2>0@3$d@1$h0$1@6$h6$0$1~0~1^5@1$e^6@1$f$1@3$d$c@2$ha^7^6=3st1$c@2$h4\1c$i2@2$i5@2$b$0@2$he^7+hgg0@2$i4@2$i7@1$hf^1+1^1^7=3st2$c@2$h3@7$h5$0$1~0~3^6@3$h2@1$hc^5@2$b$0^7@1$hd^5@1$e^1^1=3stC$c@2$h4@1$i6@2$b$0^8^1@2$h3@7$h5$0$1~0~3^9@3$h2@1$i1@1$h1^2@1$f$0$hb@1$e^1^1").
Proof. intros st p tl ar.
  intros HT Har Hp. assert (NE : tl <> p) by (intros ->; rewrite Hp in Har; discriminate).
  unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Har. rewrite lookup_insert_ne by exact NE. rewrite Hp. reflexivity.
Qed.

Lemma carve_st_none : ltac2:(zQ "i71!p4!q2!h9!pb!r6!t0!hmb!ua!v8!hg6!hi8!hne!hm3!j0!hqb!hk3!hp0!hn4!ho6!il8!im4!io2!io9!iq4!ir8!is3!hp6!isa!hpf!it1!iue!ji2!jg6!jhc!hs1!hsb!hu5!hv3!ig2&@4$f$0@4$a$1$4$2$5@6$9$1$4$7$2$5$8$3>2st$6>1p$0>0@3$d$hb@1$h7@1$h0^2@1$b$0>0@3$d@1$h2$3@6$i3$0$3~0@4$i5$0@4$a$1$4$2$5@6$9$1$4$7$2$5$8$3^2@1$h1^3@1$b$3@3$d$6@2$h3^4^3=3st1$6@2$e\1c$h9@2$he@2$c$0@2$h5^4+hgg0@2$hd@2$i1@1$h6^1+1^1^4=3st2$6@2$e@1$hf@2$c$0^4^1=3stC$6@2$e@1$i0@2$c$0^5^1@2$hc@7$i2$0$3~0@4$i4$0$3~0@4$i6$0@4$a$1$4$2$5@6$9$1$4$7$2$5$8$3^6@3$ha@1$h8@1$h0^2@1$b$0$h4@1$h1^1^1").
Proof. intros st p.
  intros HT Hp. unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Hp. reflexivity.
Qed.
