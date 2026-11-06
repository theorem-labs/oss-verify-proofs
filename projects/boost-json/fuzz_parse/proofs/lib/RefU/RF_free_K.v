(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free MallocBlocks MallocFacts_B MallocKit_B MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export F_free_K.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z01N46Stdlib6ZArith6BinInt1Zhf2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcRMallocKit_B~~~~~~jc8rfree_fp37Corelib4Init9Datatypesob3fstob4prodob3snd37Corelib4Init5Logicr63andr62eqr62ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8F_free_K~~~~~~ta6hdr_st79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~hi48ticks_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hn25Knownhn29cell_readhn27cellvalhn2aget_shadowhn26mstatehf3subhn24ghdrhn26region35stdpp7numbers1Nig16eq_dec25stdpp9countableihcbN_countable35stdpp7numbers1Zijc6eq_decob6optionhn24aptrob4Somer63not04Npos25stdpp4baseinb6lookup35stdpp9bitvectorbdefinitionsip12bvihcbZ_countableihceprod_countable25stdpp9decidableit5bprod_eq_dec25stdpp4gmapiv54gmapiv5bgmap_lookupob4listob3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~ji55block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_B~~~~~~jn38ci_mptrs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth1MallocFacts_Bpres~~~~~~js54KINVjs54ZINV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~ki07ptrs_in79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~kme5rmrephn27RKGrouphn26r_kindhn25rkindhn28s_groupshn29s_regions" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rfree_fp_hdr_st : ltac2:(zQ "h20!h9!hc!j7!o0!q3!q9!r0!sa!t0!t5!hhb!hm6!hr0!hr9!hs6!ht1!htf!hu9>2st$h0>2pf@2$5$1$0>2lo$0>2sp$0>3sp'$0>1a$0>0@1$b^6>0>1k$0>0@2$7@2$2+1^1@2$2^1+3@2$9$0\1w$0@3$8$e@2$d@2$f^a@3$4$1$0^9@2$h1@3$6$1$0^9^3@1$c^1>0@2$2^4^5>0@4$3@2$a^9^8^7^5^4@4$3^a^8^7^5").
Proof. intros st pf lo sp sp' a. try hcb. try hsb.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. ndestruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    nexists rid, r, w. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ltac2:(zQ "40!hc!t0!imf!km3@2$3\1x$0@1$2@3$1$0^1?3rid?2st").

Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. try hcb. try hsb. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. try hcb. try hsb. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. try hcb. try hsb. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. try hcb. try hsb. reflexivity. Qed.

Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof. try hcb. try hsb.
  ndestruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). ndestruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof. try hcb. try hsb.
  ndestruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
Lemma ractives_drop : actives st' = actives st.
Proof. try hcb. try hsb.
  ndestruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof. try hcb. try hsb.
  ndestruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof. try hcb. try hsb.
  intros MR. npose MR as (WF & CX & GL & AR & GR & SH). npose WF as (Hres & WR & DJ & WA & WG).
  ndestruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. ndestruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. ndestruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. ndestruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. ndestruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid : ltac2:(zQ "i40!hc!h9!huf!hv7!ih2!t0!iid!ikd!il7!im0!im8!q9!imf!in5!io7!iqe!ir4!is3!iu6!jg1!jg9!q3!jh8!jhf!jma!jr9!kh0!kh8!km3!kr0!kr9!htf!ks4!kse!kt7!ku3>3st2$hf>2LB@1$h6$h8>1c$1>3rid$0>1r$3>1m>0@1$f@1$d#k0@1$8@1$f@1$d#8>0@3$ha^6^5^4>0@2$hb^7@1$h7$9>0@4$hd?5HCEIL?4HSEC^8^3>0@3$5@1$8$3@6$e$0$3@4$h3$0$4$6$3@4$h4$0$4$6$3^6@1$i3^9@2$a$3^5>0@3$5$i1@1$i0^6$he>0>1b@2$b$0$1>2gh$2>0@3$5@1$8$2@6$e@2$b$0$1$2@4$h3$9@4$h2$0$4$1$7@6$h1$0$4$6$1$7$h0$2@4$h4$9@4$h2$0$4$1$7@6$h1$0$4$6$1$7$h0$2^2@1$i2^d@2$a$2^1@1$c@3$5$0@3$h5$0$1^3^b>0@1$h9^c@2$hc\1x$0@1$c@3$5$0^1^b^d").
Proof. intros st2 LB c rid r m. try hcb. try hsb.
  (intros K ZI MR Hr Kr NOG nd_i1; ndestruct nd_i1 as (M1 & M2 & M3 & M4 & M5)).
  pose proof MR as (WF & _). npose WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { (intros q nd_i2 E; ndestruct nd_i2 as (a & ar & k & Ha & Hk & ->)). cbn in E. ndestruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. (intros nd_i3 E; ndestruct nd_i3 as (r' & Hr' & NK)). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. ndestruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End HCW.


(* [comment removed for export] *)
