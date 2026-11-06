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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocFacts_A MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp AllocSlot_iface F_malloc_join F_malloc_core MallocHINV.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib7Numbers7BinNumsk61Nk61Z04aptr37Corelib4Init9Datatypesmd4pair46Stdlib6ZArith6BinInt1Zoc3addmd4Somemd4prod02IB04UNIT09add_slots0ec_mmap_counter08full_lay0cget_meta_rec0aget_stride0h0group_active_idx06lh_hdr0bm_set_avail0em_set_freeable0bm_set_freed0em_set_last_idx0cm_set_maplen09m_set_mem0fm_set_sizeclass04mctx04meta09put_group0h0set_mmap_counter03u3207upd_ctx08upd_metaoc3div06region37Corelib4Init5Logicht02eqht03andmd6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~hvabgrp_hdr_cov0aget_shadow25stdpp9countableil7bN_countable35stdpp7numbers1Nin76eq_deck64Npos35stdpp9bitvectorbdefinitionsip92bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~irc3memhva9unk_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jh32wa07Unknown09cell_read07cellval06r_base05r_len0bround_up_pg09s_regionsoc2leoc2lt25stdpp4basejq16lookup25stdpp4gmapjr74gmapjr7bgmap_lookupht03notht02or07RKGroup06r_kind05rkind06shadow08s_groups35stdpp7numbers1Zkh16eq_dec04ghdril7bZ_countableil7eprod_countable25stdpp9decidablekl3bprod_eq_dec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~kn39range_ansmd4boolmd4trueht04Trueirc9range_val0h0munmap_answer_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~kv39neg_errnomd4list06is_err0emmap_answer_okmd5falsemd3nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lm95hceilkn3cmmap_addr_ok0branges_freeoc6modulo05c_brk03ctxircbbrk_link_ps08brkstate04conc07BrkLivekv36PStateoc3powmd4cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mhe5munchmd4None05Known09hdr_havoc08s_shadowoc3ltboc3mul08set_tickmd3fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~mq2bAREACH_frommq25block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~mvfeagent_reserved0eMMAP_THRESHOLD0blive_ranges0anew_region08step_seq" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition big_final : ltac2:(zQ "40!je!lf!m3!m7>3st3$0>1g$3>3rid$1>1n$2$0") := ltac2:(zQ "i00!m3!lf!o5!je!q4!qa!m7!r1!r8!rc!s2!sd!td!u7!v5!hg1!hh4!hhc!hi9!hj9!hk6!hl6!hm4!hmf!ho0!ho6!hoc!hp7!hqa!hqf!hr8!hs2\3st3$3\1g$6\3rid$1\1n$0=6needed$0@2$4@2$4^1$8$9=3st4$3@3$he^4\2mr$h9@2$h3Z@2$h1Z@2$h5@2$hf@2$4^2+vvf+hgg0@2$h7+jf@2$h2+1@2$h4Z@2$h6@2$5@2$7$1$0@4$2$1$0^4Z^1^5=3st5$3@4$ha@4$2$1$0^4Z@2$5$6^5@2$f^1@4$2$1$0^4Z@3$h0$c^1@4$2$1$0^4Z=3st6$3@5$a^6@4$2$1$0^5Z@1$e@2$d^1^6+1^1@2$hd\1c$h8@2$hb@1$hc@2$4@1$b^1+1^1^1").

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).
End FINAL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
  malloc_core full_lay st1 n =
    SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
      if is_err r then ret (st1, None) else
      let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
      alloc_meta (step_seq st2) (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
        | Some g => ret (big_final st3 g rid n, Some (g, 0))
        end) (ret (st1, None))).
Proof.
  intros Hn. unfold malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma unk_agree_transfer : ltac2:(zQ "i41!hs8!hu4!lf!hua!m3!hv1!ijc!ikb!im8!io8!ip2!ir6!qa!ivf!jg6!jkd!jl3!jlc!jm7!je!jn0!jn8!jnf!joc!q4!jp7!jpc!jqd!js3!jsb!jta!ju1!ju7!jv0!jv8!jvf&@2$3@2$h9Z^2@2$ha^2@1$h6@1$h5^5>2st$h3>3st'$h3>1o$d>1m$d>2m'>1x@1$b@1$a#k0@1$5@1$b@1$a#8>0@3$e^5^3^2>0>3rid$2>1r$0>0@3$1@1$5$0@6$hb$2$0@4$hc$2$9$8$0@4$hd$2$9$8$0^2@1$h7^7@2$c$0^1>0@3$1$i2@1$i1^2$i0@2$hf@2$3@3$1@1$5$0@6$hb$2$0@4$hc$2$9$8$0@4$hd$2$9$8$0^4@1$h7^a@2$c$0^3@2$3@3$1$i3@2$7^9^4@2$7^a^4@2$3>3off$4>0@3$6^b^5^1@3$6^b^6^2>3off$4>1h$4>0~0>0@3$1$h2@2$h1@2$7^d^7^3@1$h0^2>0@1$he@3$6^d^8^4@3$1@1$5@1$b@1$a#8@1^b@1$f@2$h8@1$h4^8^5@1^c@1$f@2$h8@1$h4^8^5>3off$4>1h$4>0~0>0@3$1$h2@2$h1@2$7^c^7^3@1$h0^2@3$6^d^8^4@3$e^6^5^3").
Proof. intros st st' o m m'.
  intros UA H rid r off h Hr Hk Ho Hc NG.
  destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
  - rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
  - exfalso. apply NG. eapply NEW; eauto.
Qed.

Lemma grp_hdr_cov_same : ltac2:(zQ "f0!lf!m3!ijc!je!kg7!io8!ki2!hu4!m7!kic!im8!kj2!kk1!km4!js3>2st$3>3st'$3>3rid$0>3off$1>0@3$7@4$e$8@4$d$0$5$1$6@6$c$0$5$a$1$6$b$9@1$4^3@1$4^4>0@3$2^5^3^2@3$2^5^4^3").
Proof. intros st st' rid off. (intros EG nd_i1; ndestruct nd_i1 as (b & gh & Hb & E & R)). exists b, gh. rewrite EG. auto. Qed.

(* [comment removed for export] *)
Lemma munmap_answer_ok_range : ltac2:(zQ "a0!kr0!krd!jp7!ks4!ksb!hua!hu4!m3!kt3!ku0>1a$0>0M0\1a$0P^1\1e$7@2$5@2$2+1^1@2$2^1+vvf\7changed$1$4@3$6$1@1$9@1$8^2$3").
Proof. intros a.
  destruct a as [e|b]; cbn [range_val]; intros He.
  - unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
    replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (2 ^ 64 - e =? 0); reflexivity.
  - reflexivity.
Qed.

Lemma mmap_answer_ok_err : ltac2:(zQ "b0!m3!krd!ks4!hua!hu4!lif!jp7!ljc!r1!lk3!lkb>4live@1$7@2$8$0$0>3len$0>1e$0>0@2$3@2$6+1^1@2$6^1+vvf@2$3@3$4$1@3$a^4^3@1$5^2$2@3$4$1@1$9@1$5^2$2").
Proof. intros live len e.
  intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
  - replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_answer_ok_addr : ltac2:(zQ "h30!m3!hu4!krd!hua!ks4!r1!jnf!jp7!llb!ljc!lm3!lq4!lqd!lk3!lkb!lrd!q4!jpc!lsa>4live@1$9@2$5$0$0>3len$0>2xa$0>0@2$7Z^2>0@3$1$2@4$c?5HCEIL^3@1$a@2$5$0$0^2$4>0@3$1$2@3$e^5^4^3$4@2$3@2$h1Z^4@2$3@3$1$0@2$h2^4+hgg0Z@2$3@2$7@2$h0^4@1$6^5@1$b?5HCEIL@2$3@3$1$2@3$f^6^4@1$6^5$4@3$1$2@1$d^4$8").
Proof. intros live len xa.
  intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
  apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
  hcb. change page_size with 4096 in A1.
  unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
  assert (NE : is_errno_form xa = false).
  { unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  destruct B as [B|B]; [rewrite NE in B; discriminate|].
  rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
  repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Lemma brk_link_ps_ext : ltac2:(zQ "c0!m3!hu4!lf!lt3!lta!o5!ltf!lue!lv8!je!lve!mg7>2st$9>3st'$9>1s$b>0@3$1$7@1$3@1$4^2@1$3@1$4^3>0>3rid$2>3off$0>0@3$1$7@1$3@1$4^6@2$a^2^1@3$1$0@2$8^6@4$5$2$0^3^2@2$8^7@4$5$2$0^3^2>0@2$6^5^3@2$6^5^4").
Proof. intros st st' s.
  intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
  rewrite (EC rid off eq_refl). exact BL.
Qed.

Lemma munch_of_pointwise : ltac2:(zQ "h10!m3!jp7!r1!ivf!jkd!jpc!mh1!mh7!lm3!hv1!o5!hua!hu4!ju1!ip2!mla!ir6>2lo$0>2hi$0>1m$3>2m'$3>0@2$1Z^4>0@2$1^4@2$6+2+k0>0>1a$0>0@2$b@2$1Z^1@2$5^1@2$6+2+k0>0@2$d@2$5^2^8@2$1^7^2@3$c@1$9@1$h0@1$e#8@1^6@1$4^3@1^7@1$4^3@3$f@3$7@2$2$0$0@4$a$0$0^7^6@1$8@2$2$0$0^5^4").
Proof. intros lo hi m m'.
  intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.

(* [comment removed for export] *)
Lemma cell_read_hh0 : ltac2:(zQ "h70!lf!jvf!krd!hu4!m3!jm7!im8!io8!mm3!hv1!o5!mma!jl3!jlc!ikb!mn1!je!mnc!jp7!mo6!jqd!js3!jsb>2st$h0>3rid$0>3off$4>0@3$3@1$9$1@6$h4$0$1@4$h5$0$7$6$1@4$h6$0$7$6$1^2@1$h1^3@1$8$1>0@2$h2Z^2@3$3$5@2$d@2$e@2$f@4$a$0$4^4Z^5^4^3M2\0$2$5@2$h3^3+c@1$cZ@1$bZ").
Proof. intros st rid off.
  intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
  destruct (Z.eq_dec (off / 16) 0) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
    replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
    replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma round_up_pg_4115 : ltac2:(zQ "90!q4!m3!hu4!r8!rc!jnf!hs2!jp7!moc>1n$1>0@2$7Z^1@3$2$1@1$5@2$0@2$0^2$3$4@2$8@2$6@2$0^2+hgh3+hgg0+hgg0").
Proof. intros n. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMP_BIG : ltac2:(zQ "10!je>6am_pre>0$0PP") := ltac2:(zQ "hb0!q4!je!krd!hu4!lf!m3!r8!rc!mp2!llb!mpc!ljc!ks4!hua!mu7!mv6!nk1!nl3!ju7!lk3!nm3!lkb!nn0!nnc!jp7!jpc!mh1\6am_pre>0$1P>2st$1>2LB@1$b$f>1t$4>2xa$5>1n$5>0@4$e?4HSEC$h0^5^4>0@2$d@2$h8$h1^2@2$h9^2@2$ha+2+i0>0@3$3$2@3$h5@1$h4@2$8^5^7@2$0@2$0^3$6$7^4$c>0@3$3$2@1$h3^5$9@1^a@1$h7@3$a$1$4@4$h6$h2^6@2$0@2$0^5$6$7@2$8^7^9").

Section BIG.
Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_BIG am_pre.
End BIG.

End HCW.

