(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K F_am_K2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A2 RF_am_K.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01N35stdpp7numbers1Nhc6eq_dec01Z35stdpp7numbers1Zj96eq_dec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~l34aptr25stdpp9countablep8bN_countable37Corelib4Init5Logicr72eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref8RF_am_K22A2~~~~~~t08agree_on25stdpp4gmaphhd4gmapl34areal34ghdrl36regionp8bZ_countablep8eprod_countable25stdpp9decidablehm7bprod_eq_dec37Corelib4Init9Datatypesho76optionho74Somel37s_areasl38s_groupsl39s_regions25stdpp4baseht26lookuphhdbgmap_lookup04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~hvd5rmrepl34concl36mstatel37s_metasl3as_reservedl38s_shadow35stdpp9bitvectorbdefinitionsin92bvho74listho74prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~iqc3memhvd8RGOT_SSPhvd5RLIBChvd6RMLOCKhvdaRSSP_GUARDhvd9rmrep_ctxl37RKGroupl34metal36r_basel36r_kindl35r_lenl35rkindl3bround_up_pgl36shadowr73andhvd4RCTX46Stdlib6ZArith6BinInt1Zjo83add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~jq75rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~juc6u64arrjuc5u8arrl36activel37bouncesl33ctxl39unmap_seql35usager72or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~kmb7activeskmb8bouncesskmbaunmap_seqskmb6usagesl34mctxl34optrjo82lejo82ltho73fstkmb5lr_lohvdbrregions_wfho74boolho74truer73nothvdcref_reservedl3blive_rangesl3branges_freejo86modulo69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lm15hceill35RKBrk" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rmrep_agree_but_ctx : ltac2:(zQ "ie2!h9!id!j6!ka!p1!q9!sb!hh2!hi9!hj1!hj8!hjf!hk8!hl6!hn8!hpf!hq9!hr1!hrb!hs6!hte!hu8!hv7!ije!ik7!ike!il7!im1!ime!ip6!ipc!iq4!iuf!iv6!jg2!jgb!jh5!ji3!jj0!jja!jk1!jka!jl3!jlb!jm3!jn1&@4$8$4@4$e$0$1$2$3@6$d$0$1$5$2$3$c$9&@4$8$4@4$e$0$1$2$3@6$d$0$1$5$2$3$c$a>2st$h9>3st'$h9>1m>0@1$hd@1$h6#k0@1$f@1$hd@1$h6#8>2m'$i0>0@4$h7?5HCEIL?4HSEC^4^2>0@3$6@4$8$0$1$5$b@1$h3^4@1$h3^5>0@3$6@4$8$4@4$e$0$1$2$3@6$d$0$1$5$2$3$c$i7@1$ha^5@1$ha^6>0@3$6~0@1$h1^6@1$h1^7>0@3$6~1@1$h2^7@1$h2^8>0@3$6@4$8$0$1$5$id@1$hc^8@1$hc^9>0@3$6@1$he@2$hf$2$2@1$hb^9@1$hb^a>0@4$7^9^8$i3+4>0@4$7^a^9$i2+m8>0@4$7^b^a$i1+8>0@4$7^c^b$i4+8>0@4$7^d^c+hisqv0+4>0>1a$4>2ar$9>0@3$6@1$f$9@6$h4$4$9~0@4$h5$4@4$e$0$1$2$3@6$d$0$1$5$2$3$c$9^2@1$h1^h2@2$h0$9^1@4$7^h1^h0@2$h8^h3^3+hgg0>0>1b$4>2gh$a>0@3$6@1$f$a@6$h4$4$a~1@4$h5$4@4$e$0$1$2$3@6$d$0$1$5$2$3$c$a^2@1$h2^h3@2$h0$a^1@4$7^h2^h1@2$h8^h4^3+9>0>3rid$0>1r$b>0@3$6@1$f$b@6$h4$0$b@4$8$0$1$5$b@4$h5$0$1$5$b^2@1$h3^h4@2$h0$b^1>0@3$6$ib@1$i9^2$i6@4$7^h4^h3@1$i8^3@1$ic@1$ia^3>0@2$i5^h2^h0@4$h7?5HCEIL?4HSEC^h3^h1").
Proof. try hcb. try hsb.
  (intros st st' m m' nd_i1 ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGV AGA AGG AGR CX'; ndestruct nd_i1 as (WF & CX & GL & AR & GR & SH)).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - ndestruct WF as (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG, ERs. split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA| exact WG].
  - ndestruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G6|]. eapply A2.agree_on_sub; [exact AGV| lia| cbn; lia].
  - intros a ar Ha. rewrite EA in Ha. ndestruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
    unfold rarea_rep. rewrite !Hconc.
    assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
    assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
    rewrite PW. split; [|split].
    + eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
    + eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. ndestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
    unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
    + eapply RA2.rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctx_mid_agree : ltac2:(zQ "i10!j6!jna!sb!jo0!jq0!ju3!hv7!ki6!kj0!kj9!kk2!kkc!ike!hs6!kl2!kle!ip6!hpf!km6!h9!kqd!kr8!ks4!kt2!iuf!hh2!ije!ktc!ku3!hjf!q9!hi9!id>2st$c>3st'$c>1m>0@1$h0@1$6#k0@1$h1@1$h0@1$6#8>2m'$h8>0@4$ha?5HCEIL?4HSEC^4^2>0@2$h2@3$2$hb@1$b^4@1$b^5@2$1>2sc$0@3$2$hc@2$9^5^1@2$9^6^1@2$1>2sc$0@3$2$0@2$f^5^1@2$f^6^1@2$1>1i$0@3$2$0@2$e^5^1@2$e^6^1>1i$0@3$2$0@2$a^5^1@2$a^6^1>0@3$2@4$hf$h3$i0$he$hd@1$d^5@1$d^6>0@4$h9^5^4@2$4$3+l0+jk0@2$1@4$7$5^5@2$4$3+l0@1$h4^7@2$1@4$7$5^5@2$4$3+ht0@1$h7^7@2$1@4$8$5^5@2$4$3+jl0@1$h6^7@4$8$5^5@2$4$3+jn0@1$h5^7").
Proof. try hcb. try hsb.
  (intros st st' m m' nd_i2 HX ER AG; ndestruct nd_i2 as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _)).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
  assert (E3 : usages st' = usages st).
  { unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st).
  { unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
  assert (E5 : bouncess st' = bouncess st).
  { unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
  rewrite E2, E3, E4, E5.
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold RCTX in *.
  split; [|split; [|split]].
  - eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rarea_in_live : ltac2:(zQ "i00!h9!j6!hj1!hjf!id!q9!ka!hq9!hpf!iq4!jna!sb!p1!ik7!jq0!kua!kv0!hte!hk8!hl6!hn8!hi9!hu8!kv6!kvd!lg6!ike!jk1!jl3!jm3!hr1!hs6>2st$ha>1a@2$9$0$1>2ar$2>1r$3>1x$1>0@2$h9?5HCEIL^5>0@3$b@1$8$2@6$h1@2$9$0$1$2@4$h5$c@4$h4$0$4$1$6@6$h3$0$4$5$1$6$h2$2@4$h6$c@4$h4$0$4$1$6@6$h3$0$4$5$1$6$h2$2^5@1$he^6@2$7$2^4>0@3$b@1$8$3@6$h1$0$3@4$h5$0$4$5$3@4$h6$0$4$5$3@3$h7$0$1^6@1$hf^7@2$7$3^4>0@2$a@2$f@2$d^8^7^4@2$h0^4@2$e@2$d^8^7+hgg0@2$a@2$f@1$h8^6^5@2$h0^5@2$e@1$hb^6@1$hd@1$hc^6").
Proof. try hcb. try hsb.
  intros st a ar r x WF Ha Hr Hx. ndestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
  rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
  pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.

Lemma rgroup_in_live : ltac2:(zQ "i00!h9!j6!hj8!hjf!id!q9!ka!hq9!hpf!iq4!jna!sb!p1!ik7!jq0!kua!kv0!hte!hk8!hl6!hn8!hi9!hu8!kv6!kvd!lg6!ike!jk1!jl3!jm3!hrb!hs6>2st$ha>1b@2$9$0$1>2gh$2>1r$3>1x$1>0@2$h9?5HCEIL^5>0@3$b@1$8$2@6$h1@2$9$0$1$2@4$h5$c@4$h4$0$4$1$6@6$h3$0$4$5$1$6$h2$2@4$h6$c@4$h4$0$4$1$6@6$h3$0$4$5$1$6$h2$2^5@1$he^6@2$7$2^4>0@3$b@1$8$3@6$h1$0$3@4$h5$0$4$5$3@4$h6$0$4$5$3@3$h7$0$1^6@1$hf^7@2$7$3^4>0@2$a@2$f@2$d^8^7^4@2$h0^4@2$e@2$d^8^7+9@2$a@2$f@1$h8^6^5@2$h0^5@2$e@1$hb^6@1$hd@1$hc^6").
Proof. try hcb. try hsb.
  intros st b gh r x WF Hb Hr Hx. ndestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
  rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

(* [comment removed for export] *)
Lemma rimage_clear_of_ranges_free : ltac2:(zQ "h00!j6!jna!sb!kua!kv0!lh5!ipc!iq4!lhd!li5!lib!ljb!ike!lk9!im1!jq0>2st$c>2lo$0>1n$0>1x$0>0@3$2@1$6@2$7$0$0@1$e^4@1$a?5HCEIL>0@3$2$5@3$d@1$b^5^4^3$8>0@2$1@2$3+hggg0^3@2$4^3+hitgg0@1$9@2$1@2$3^6^4@2$4^4@2$f^6^5").
Proof. intros st lo n x. try hcb. try hsb.
  intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : ltac2:(zQ "10!ije@4$0?5HCEIL?4HSEC?2st?1m").
Hypothesis Hr : ltac2:(zQ "b0!hjf!h9!q9!id!hq9!hpf!sb!hs6!hte!hi9!hu8@3$6@1$5$0@6$8$1$0@4$9$1$3$2$0@4$a$1$3$2$0?3rid@1$7?2st@2$4$0?1r").
Hypothesis NK : ltac2:(zQ "50!sb!li5!jj0!jka!jlb@1$1@3$0$4@1$3?1r$2").
Hypothesis LEN : ltac2:(zQ "30!sb!j6!jl3@3$0$1@1$2?1r?3off").
Hypothesis OFF : ltac2:(zQ "10!kua@2$0Z?3off").
Hypothesis OAL : ltac2:(zQ "30!sb!j6!ll7@3$0$1@2$2?3off+hgg0Z").
Hypothesis RF : ltac2:(zQ "70!lh5!lhd!sb!ljb!jk1!lk9!jq0@3$2$0@3$5@1$3?2st@2$6@1$4?1r?3off+hgg0$1").
Hypothesis CEIL : ltac2:(zQ "40!jq0!lpc!jk1!kua@2$3@2$0@2$0@1$2?1r?3off+hgg0@1$1?5HCEIL").
Hypothesis RPOS : ltac2:(zQ "d0!hjf!h9!q9!id!hq9!hpf!sb!jl3!hs6!kv0!hte!hi9!hu8>1q$1>2rq$0>0@3$6@1$5$0@6$a$1$0@4$b$1$3$2$0@4$c$1$3$2$0^2@1$8?2st@2$4$0^1@2$9Z@1$7^2").
Hypothesis UNIQ : ltac2:(zQ "f0!hjf!h9!sb!li5!q9!id!hq9!hpf!lq5!jka!jlb!hs6!hte!hi9!hu8>1q$1>2rq$0>0@3$2@1$7$0@6$c$1$0@4$d$1$5$4$0@4$e$1$5$4$0^2@1$b?2st@2$6$0^1>0@1$3@3$2$1^3?3rid@1$3@3$2$a@1$9^3$8").

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. try hcb. try hsb. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. try hcb. try hsb. reflexivity. Qed.
Lemma rgr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof. try hcb. try hsb.
  rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
  - rewrite lookup_insert_eq in H. left. split; congruence.
  - rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. try hcb. try hsb. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. try hcb. try hsb. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma rgr_conc q : conc st' q = conc st q.
Proof. try hcb. try hsb.
  unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
  - rewrite E, rgr_lookup_new, Hr. reflexivity.
  - rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
Lemma rgr_ru : ltac2:(zQ "40!jm3!jq0!sb!j6@3$2$3@1$0@2$1?3off+hgg0@2$1@1$0?3off+hgg0").
Proof. try hcb. try hsb. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

Lemma rgr_regions_wf : rregions_wf st'.
Proof. try hcb. try hsb.
  pose proof MR as (WF & _). npose WF as (RS & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
    cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
    apply ranges_free_intro. intros b n HI.
    pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
    assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; exact HI)).
    destruct HI as [E|[E|[E|[E|[E|[]]]]]]; [unfold Prog.rband in E| | | |]; inversion E; subst; cbv delta [Decode.CEIL_BAND] in *; lia.
  - intros q1 r1 q2 r2 H1 H2 NE.
    assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
              r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
    { intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
      replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
      - left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
        pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
        destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
      - right. exact D. }
    destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + exact (OLD q2 r2 H2' NE2).
    + destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. ndestruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
    destruct (decide (fst a = rid)) as [E|NE].
    + exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
      cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      rewrite LEN in A1. repeat split; try assumption; lia.
    + exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
  - intros b gh Hb. ndestruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
    assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
    exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.

Lemma rmrep_grow_region : rmrep st' m.
Proof. try hcb. try hsb.
  npose MR as (WF & CX & GL & AR & GR & SH).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
  assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
  split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
  - ndestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    replace (ctx_head_cells st') with (ctx_head_cells st) by (unfold ctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
    replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
    replace (ctx_tail_cells st') with (ctx_tail_cells st).
    2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
  - intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. ndestruct (AR a ar Ha) as (A1 & A3 & A4).
    unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
    split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
  - intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. ndestruct (GR b gh Hb) as (w8 & R & Hw8).
    exists w8. rewrite rgr_conc, PW. split; assumption.
  - intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
    destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + exfalso. apply NK. exact Hk.
    + exact (SH q rq H Hk).
Qed.

End GROW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
  (forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
  impl rsegs (at_node rsegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof. try hcb. try hsb.
  intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec' rsp) as [a|] eqn:E.
  - destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
  - cbn. apply evt_done. exact I.
Qed.

End HCW.


(* [comment removed for export] *)
