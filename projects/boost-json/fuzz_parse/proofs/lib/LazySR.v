(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Scfg PropExec CatSim ShapeAlg SReach LazyRestrict LazyRestrictRun LazyRestrictAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Exec MState Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~k66msteps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~o86msteps37Corelib4Init5Logicsc3andsc2exsc3iffo83evt37Corelib7Numbers7BinNumsv74Npos35stdpp9bitvectorbdefinitionshh72bv37Corelib4Init9Datatypeshja6optionhja4listhja4prod3h5LinuxProcessSemantics5Riscv7Preludehmc5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hpb2MSsc2eq69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~hu38restricthu3crestrict_mem0ems_svc_pendinghja4boolhja4truehja4Some06ms_memhu37hiddenbhu3ain_rangesbhh77Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR8WithSegs~~~~~~ip24rsubhja4consip28hid_samehu3dunrestrict_toip2ehidden_zero_on3h5LinuxProcessSemanticsfLinuxProcessSem3Runjh35mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statejk85Modelip24lzokhu38lazy_invhu3h5same_but_materializedjh36config69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~jr76sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3libfLazyRestrictRun~~~~~~jva6dstepsjh36cfg_msjh39cfg_modelhu3azin_rangebhh7bbv_unsignedhja4andbjk88m_vmmapsjk89page_sizejk88vm_limithu3aeager_usedhu3bpages_totalhu38with_mem46Stdlib6ZArith6BinInt1Zkt03addkt02lekt03muljk84m_vmhja4Nonejk87VmStatejk88m_haltedjk8fvm_backing_used3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelj67Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hlc!lmb@1$0$1").
Context {SC : StepCfg}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msteps_of_cj : ltac2:(zQ "30!j7!nf!s3>2ms$0>3ms'$0>0@3$2?4segs^2^1@3$1?4segs^3^2").
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] _ IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

Lemma msteps_to_cj : ltac2:(zQ "30!j7!nf!s3>2ms$0>3ms'$0>0@3$1?4segs^2^1@3$2?4segs^3^2").
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep _ IH].
  - apply Exec.msteps_refl.
  - eapply Exec.msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

(* [comment removed for export] *)
Lemma evt_cj_iff : ltac2:(zQ "60!j7!u0!u6!ub!nf!v1>1P>0$0P>2ms$0@2$3@3$5?4segs^2^1@2$2$0\3ms'$0@2$1@3$4?4segs^2^1@1^3^1").
Proof.
  intros P ms. split; (intros nd_i1; ndestruct nd_i1 as (ms' & H & HP)); exists ms'; split; auto using msteps_of_cj, msteps_to_cj.
Qed.

(* [comment removed for export] *)
Lemma restrict_MS : ltac2:(zQ "b3!hh0!hj4!hl2!hlc!hm4!hp2!ht8!hte!j7!ii2!iie&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$3~0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1L~1>1S~1>1R@2$5@1$0#5@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~2>2ro~2@3$7$8@3$9^9^8@7$6^7^6^5^4^3^2^1@7$6^7^6^5^4^3@3$a^9^8^2^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma restrict_svc : ltac2:(zQ "92!hh0!hj4!hlc!hm4!ije!hl2!hte!j7!ii2&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>2ms$7@3$6@1$5@1$1@1$0#k0@1$4@3$8^3^2^1@1$4^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hidden_zero_on : ltac2:(zQ "52!hh0!hj4!hlc!hm4!j7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>2Zr~1>3msF$4P") := ltac2:(zQ "e2!hh0!hj4!hlc!hm4!hte!ike!il6!ile!hl2!j7!im6!ime!in9!io7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0\1L~1\1S~1\2Zr~1\3msF$9>1a@1$1@1$0#k0>0@3$4$5@3$b^5^4^1$6>0@3$4$5@2$c^2^4$6@3$4@1$8@1$1@1$0#8@2$a^4^3@2$7@1$1@1$0#8@2$d@1$0#8Z").

(* [comment removed for export] *)
Definition rsub : ltac2:(zQ "42!hh0!hj4!hlc!hm4&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1A~1>1B~1P") := ltac2:(zQ "82!hh0!hj4!ike!hlc!hm4!il6!hte!in9&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$3~0\1A~1\1B~1>1x@1$1@1$0#k0>0@3$6$2@2$7^1^3$5@3$6$2@2$7^2^3$5").

Lemma rsub_cons_r : ltac2:(zQ "62!hh0!hj4!hm4!hlc!it4!itc&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>1A~1>1r~0>1B~1>0@2$4^3^1@2$4^4@3$5~0^3^2").
Proof. intros A r B H x Hx. rewrite in_rangesb_cons, (H x Hx). apply orb_true_r. Qed.
Lemma rsub_cons_2 : ltac2:(zQ "62!hh0!hj4!hm4!itc!hlc!it4&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>1r~0>1A~1>1B~1>0@2$5^2^1@2$5@3$3~0^4^3@3$3~0^4^2").
Proof.
  intros r A B H x Hx. rewrite in_rangesb_cons in *.
  destruct (zin_rangeb (bv_unsigned x) r); [reflexivity|]. cbn in *. apply H, Hx.
Qed.

(* [comment removed for export] *)
Record lzok (L S Zr : list (word * word)) (c : config) : Prop := {
  lzok_ranges : lazy_ranges_okb segs L = true;
  lzok_inv    : lazy_inv L S (cfg_model c);
  lzok_halted : m_halted (cfg_model c) = None;
  lzok_zero   : hidden_zero_on L S Zr (cfg_ms c);
  lzok_SZr    : rsub S Zr;
  lzok_ZrL    : rsub Zr L;
  lzok_LM     : rsub L (vm_maps (m_vmmaps (cfg_model c)))
}.


(* [comment removed for export] *)
Definition hid_same : ltac2:(zQ "52!hh0!hj4!hlc!hm4!j7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>3msF$4>4msF'$4P") := ltac2:(zQ "b2!hh0!hj4!hlc!hm4!hte!j7!im6!ike!hl2!il6!ime&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0\1L~1\1S~1\3msF$5\4msF'$5>1a@1$1@1$0#k0>0@3$4$7@3$a^5^4^1$9@3$4@1$8@1$1@1$0#8@2$6^3^2@2$6^4^2").

Lemma hid_same_refl : ltac2:(zQ "62!hh0!hj4!hlc!hm4!j7!iu4&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>3msF$4@4$5^3^2^1^1").
Proof. intros L S msF a _. reflexivity. Qed.

Lemma hid_same_trans : ltac2:(zQ "62!hh0!hj4!j7!iu4!hlc!hm4&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>1L~1>1S~1>2m1$2>2m2$2>2m3$2>0@4$3^5^4^3^2>0@4$3^6^5^3^2@4$3^7^6^5^3").
Proof. intros L S m1 m2 m3 H12 H23 a Ha. rewrite (H23 a Ha). apply H12. exact Ha. Qed.

Lemma hid_same_unrestrict : ltac2:(zQ "72!hh0!hj4!hlc!hm4!j7!iv0!iu4&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>3msF$4>3ms1$4@4$6^4^3^2@4$5^4^3^2^1").
Proof.
  intros L S msF ms1 a Ha. unfold unrestrict_to.
  exact (unrestrict_by_hidden (hiddenb L S) msF ms1 a Ha).
Qed.

Lemma hidden_zero_on_frame : ltac2:(zQ "72!hh0!hj4!hlc!hm4!j7!jg1!iu4&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>2Zr~1>3msF$4>4msF'$4>0@4$5^5^4^3^2>0@4$6^6^5^3^2@4$5^7^6^5^3").
Proof. intros L S Zr msF msF' HZ Hs a Ha Hz. rewrite (Hs a Ha). exact (HZ a Ha Hz). Qed.

(* [comment removed for export] *)
Lemma lzok_lifted : ltac2:(zQ "b2!hh0!hj4!hlc!hm4!j7!jjf!jn6!jnf!jo7!jp3!iu4&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>2Zr~1>3msF$4>2mo$6>4msF'$4>3mo'$6>0@4$7^7^6^5@2$5^4^3>0@3$8^8^7^2>0@2$9^5^3>0@4$a^a^9^7^5@4$7^b^a^9@2$5^6^5").
Proof.
  intros L S Zr msF mo msF' mo' [HL Hinv Hh HZ HSZ HZL HLM] Hinv' Hsame Hs. split; cbn in *.
  - exact HL.
  - exact Hinv'.
  - rewrite (same_but_materialized_halted _ _ Hsame). exact Hh.
  - eapply hidden_zero_on_frame; eassumption.
  - exact HSZ.
  - exact HZL.
  - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact HLM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_dsteps : ltac2:(zQ "30!jqd!jv0!kjc>1c$0>2c'$0>1Q>0$0P>0@3$2?4segs^3^2>0@4$1?4segs?2SC^2^3@4$1?4segs?2SC^3^5").
Proof.
  intros c c' Q H; induction H as [c | ms model ms' model' c3 Hh Hsvc Hacc H IH]; intros HQ; [exact HQ|].
  eapply sreach_silent1; [apply node_account; [exact Hh | exact Hsvc | exact Hacc] | apply IH; exact HQ].
Qed.

Section WithLazy.
Variables L S Zr : list (word * word).

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sreach_msteps_lazy : ltac2:(zQ "b0!j7!jjf!jn6!ii2!jnf!jv0!hte!jqd!nf!jp3!iu4>3msF$0>3ms1$0>2mo$2>1Q>0$7P>0@4$4?1L?1S?2Zr@2$1^4^2>0@3$8?4segs@3$3?1L?1S^5^4>0>4msF'$0>3mo'$2>0@4$4?1L?1S?2Zr@2$1^2^1>0@2$9^7^2>0@3$6$0@3$3?1L?1S^4^9>0@4$a?1L?1S^b^5@4$5?4segs?2SC^9@2$1^6^5@4$5?4segs?2SC^4@2$1^7^5").
Proof.
  intros msF ms1 mo Q Hok Hms Hk.
  destruct (msteps_restrict segs L S (lzok_ranges _ _ _ _ Hok) msF ms1 mo (lzok_inv _ _ _ _ Hok) (lzok_halted _ _ _ _ Hok) Hms)
    as (mo' & Hd & Hinv' & Hsame & Hh' & Hr).
  eapply sreach_dsteps; [exact Hd|].
  apply Hk; [| exact Hsame | exact Hr | apply hid_same_unrestrict].
  eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* [comment removed for export] *)
Theorem evt_sreach_lazy : ltac2:(zQ "d0!u0!j7!kk6!jjf!ii2!jnf!kl0!jqd!jn6!jp3!iu4!v1!jv0>1P>0$1P>3msF$1>2mo$8>0@4$5?1L?1S?2Zr@2$3^2^1>0@3$b?4segs^4@3$4?1L?1S^3@4$c?4segs?2SC\1c$7@2$0@1^6@3$4?1L?1S@1$2^1@2$0@4$5?1L?1S?2Zr^1@2$0@2$9^4@1$6^1@4$a?1L?1S^5@1$2^1@2$3^4^3").
Proof.
  intros P msF mo Hok Hevt. apply evt_cj_iff in Hevt. ndestruct Hevt as (ms1 & Hms & HP).
  eapply sreach_msteps_lazy; [exact Hok | exact Hms |].
  intros msF' mo' Hok' Hsame Hr Hs. apply sr_done. cbn. rewrite Hr. auto.
Qed.

(* [comment removed for export] *)
Theorem evt_sreach_lazy_k : ltac2:(zQ "a0!jjf!j7!jn6!ii2!jnf!jv0!jqd!jp3!iu4!v1>1P>0$1P>3msF$1>2mo$2>1Q>0$6P>0@4$4?1L?1S?2Zr@2$0^3^2>0@3$9?4segs^5@3$3?1L?1S^4>0>4msF'$1>3mo'$2>0@4$4?1L?1S?2Zr@2$0^2^1>0@2$7^7^2>0@4$8?1L?1S^9^4>0@1^b@3$3?1L?1S^5@4$5?4segs?2SC^9@2$0^6^5@4$5?4segs?2SC^4@2$0^6^5").
Proof.
  intros P msF mo Q Hok Hevt Hk.
  eapply sreach_seq; [exact (evt_sreach_lazy P msF mo Hok Hevt)|].
  (intros [msF' mo'] nd_i2; ndestruct nd_i2 as (HP & Hok' & Hsame & Hs)). cbn in HP, Hok', Hsame, Hs.
  apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Corollary evt_sreach_lazy_at : ltac2:(zQ "b0!j7!jjf!jn6!ii2!jnf!jv0!hte!jqd!jp3!iu4!v1>1P>0$0P>3msF$0>2ms$0>2mo$2>1Q>0$7P>0@4$4?1L?1S?2Zr@2$1^4^2>0@3$6$0@3$3?1L?1S^5^4>0@3$a?4segs^7^5>0>4msF'$0>3mo'$2>0@4$4?1L?1S?2Zr@2$1^2^1>0@2$8^8^2>0@4$9?1L?1S^b^4>0@1^d@3$3?1L?1S^5@4$5?4segs?2SC^a@2$1^6^5@4$5?4segs?2SC^5@2$1^8^6").
Proof. intros P msF ms mo Q Hok <- Hevt Hk. eapply evt_sreach_lazy_k; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem lzok_open_window : ltac2:(zQ "hf2!hh0!hj4!ike!hm4!itc!hte!ii2!il6!j7!jjf!kld!jnf!kmb!ile!kna!hl2!u0!im6!jn6!ko2!koe!kpb!kq7!ime!in9!kr5!ks4!ku8!kuf!kv5!io7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@3$4~0^6?1S>1W~0>3msF$8>2mo$h2>0@4$b?1L?1S?2Zr@2$9^2^1>0>1a@1$1@1$0#k0>0@3$5$2@2$a@2$c@1$0#k0^1^5$7@3$5$2@2$h8^2?2Zr$7>0@2$hc@2$hb@1$h6^3@2$hd@1$h9@3$4~0^5?1S$h4@1$h5@1$h3^3@2$h0@4$b?1L~1?2Zr@2$9^5^4@3$5$8@3$6?1L~1^5@2$ha@3$6?1L?1S^5\1a@1$1@1$0#k0M2\0$2@1$f@1$1@1$0#8@2$e@2$a@2$c@1$0#k0^1^7@3$h7?1L?1S^1@2$d@1$1@1$0#8@2$he@1$0#8Z@2$h1@3$6?1L?1S^6^1").
Proof.
  intros W msF mo [HL Hinv Hh HZ HSZ HZL HLM] HW Hb. cbn in *. split.
  - split; cbn; [exact HL | apply lazy_inv_open_window; assumption | exact Hh | | | exact HZL | exact HLM].
    + intros a Ha Hz. apply HZ; [| exact Hz]. eapply hiddenb_mono_cons. exact Ha.
    + intros x Hx. rewrite in_rangesb_cons in Hx. apply orb_true_iff in Hx.
      destruct Hx as [Hx | Hx]; [apply HW; exact Hx | apply HSZ; exact Hx].
  - rewrite (restrict_open_window_eq L W S msF).
    match goal with |- with_mem ?x ?f = with_mem ?y ?g => replace g with f; [reflexivity|] end.
    apply functional_extensionality. intros a.
    destruct (zin_rangeb (bv_unsigned a) W) eqn:EW; cbn [andb]; [|reflexivity].
    destruct (hiddenb L S a) eqn:Eh.
    + apply HZ; [exact Eh | apply HW; exact EW].
    + unfold restrict_mem_by. rewrite Eh. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithLazy.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lzok_vm_frame : ltac2:(zQ "f2!hh0!hj4!hlc!hm4!hte!j7!jjf!jn6!kvc!jnf!lg4!hl2!lgc!lh7!iu4&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>2Zr~1>3msF$5>2mo$7>4msF'$5>3mo'$7>0@4$9^7^6^5@2$6^4^3>0@3$4$c@1$8^2@1$8^4>0@3$4@1$b@1$1@1$0#k0@1$d^3@1$a@1$1@1$0#k0>0@4$e^a^9^7^5@4$9^b^a^9@2$6^6^5").
Proof.
  intros L S Zr msF mo msF' mo' [HL Hinv Hh HZ HSZ HZL HLM] Evm Hh' Hs. split; cbn in *.
  - exact HL.
  - eapply lazy_inv_vm_frame; [exact Evm | exact Hinv].
  - exact Hh'.
  - eapply hidden_zero_on_frame; eassumption.
  - exact HSZ.
  - exact HZL.
  - unfold m_vmmaps in *. rewrite Evm. exact HLM.
Qed.

(* [comment removed for export] *)
Lemma lzok_backing_used_le : ltac2:(zQ "e2!hh0!hj4!hlc!hm4!kl0!jqd!koe!li3!kq7!kr5!jnf!ku8!kuf!kv5&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>2Zr~1>1c$5>0@4$a^4^3^2^1@2$c@1$7@1$4^2@2$b@1$8@1$4^2@2$d@1$9^4$6").
Proof.
  intros L S Zr c [_ [Hl Hnd Hincl Hb] _ _ _ _ _]. rewrite vm_backing_used_split.
  rewrite <- all_pages_length.
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen. unfold page_size. nia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

Arguments lzok segs L S Zr c : clear implicits.
Arguments lzok_ranges {segs L S Zr c}.
Arguments lzok_inv {segs L S Zr c}.
Arguments lzok_halted {segs L S Zr c}.
Arguments lzok_zero {segs L S Zr c}.
Arguments lzok_SZr {segs L S Zr c}.
Arguments lzok_ZrL {segs L S Zr c}.
Arguments lzok_LM {segs L S Zr c}.
Arguments hidden_zero_on L S Zr msF : clear implicits.
Arguments hid_same L S msF msF' : clear implicits.
(* [comment removed for export] *)
