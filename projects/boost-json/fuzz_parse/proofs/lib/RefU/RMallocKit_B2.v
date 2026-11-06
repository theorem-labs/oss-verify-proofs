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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_enframe.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export MallocKit_B2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01N01Z04Npos35stdpp9bitvectorbdefinitionsi52bv37Corelib4Init9Datatypesk73snd79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m56region37Corelib4Init5Logicqc2eqk76optionm56r_base46Stdlib6ZArith6BinInt1Zt73addk73fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~vb2wa25stdpp9countablehjabN_countable35stdpp7numbers1Nhla6eq_deck74Somek74consk73nilk74prodqc3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~hp63rdv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hu73memhu78pans_memvb8bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~ik85rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ip35rsegsm57RKGroupm57Unknownm59cell_readm57cellvalm5aget_shadowm56mstatem56r_kindm55r_lenm55rkindm5bround_up_pgm59s_regionst72let72lt25stdpp4basejl66lookupi5bbv_unsigned25stdpp4gmapjna4gmapjnabgmap_lookup3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjpd5wviewvb5wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentbMallocKit_B~~~~~~ju58agree_on79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kj58rw_cellsk74list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ko34cellko3acells_sizet76of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~kte6u64arrk76lengtht73mulkte5u8arrqc2exk74Noneqc3nott73pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcRMallocKit_B~~~~~~ll28rrepfoot89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUdRMallocKit_B23HCW~~~~~~lq2h0rgrp_region_addrqc2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mg53ivlmg55munchmg57outside79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~mlccrpres_except" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. try hcb. try hsb. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof. try hcb. try hsb.
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  apply rimplT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. try hcb. try hsb. intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. exact H. Qed.

Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  rimplT o (rd32 st q k) s Q ms.
Proof. try hcb. try hsb. intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. exact H. Qed.

(* [comment removed for export] *)
Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. try hcb. try hsb. intros H1 H2. destruct c; auto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rrdv_cur : ltac2:(zQ "ia1!h9!hc!hf!k2!lf!q3!s0!s5!se!uf!v5!hj5!hkb!hmb!hn5!hnc!ho3!ho9!hp0!hu0!iia!ij1!ijd!ioa!it0!it9!iu3!iud!iv9!jg3!jh0!jh9!ji2!jia!jj2!jk0!jkc!jl1!jm2!jmc!jo6!joe&@1$b@2$9@1$8^8@3$4$0$1^9>1o>1x@1$3@1$2#k0@1$7@1$3@1$2#8>2st$he>2mX>0@1$3@1$2#k0@1$7@1$3@1$2#8>1q@2$h1$0$1>1r$5>1x@1$3@1$2#8>0@4$h7?5HCEIL?4HSEC^5^4>0@3$6@1$7$5@6$i6$0$5@4$i8$0$d$c$5@4$i9$0$d$c$5@3$a$0$1^4@1$i3^6@2$e$5^3>0@3$6$i1@1$hf^4$h9>0@2$h2@2$i4Z@3$4$0$1^6@2$i5@3$4$0$1^6@1$i2@1$i0^5>0>1h$1>0@3$6$hc@2$hb@2$hd^a@3$a$0$1^8@3$4$0$1^8@1$ha^1@3$6@1$7@1$3@1$2#8@1^c~0@1^a~0>0@4$h6$h8^9@2$9@1$8^7@3$4$0$1^8@3$f@1$3@1$2#8^6@1$h0@1$3@1$2#8@3$6$1@5$h3$h4$h5^c^b^9@2$i7@1$2#8^7").
Proof. try hcb. try hsb.
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read rsegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    ndestruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RBC.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rwview_ext : ltac2:(zQ "61!hf!k2!s5!s0!jt4!it0&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1a@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#8@1^2^1@1^3^1@3$3@1$2@1$1@1$0#8@3$4$5^3^2@3$4$5^4^2").
Proof. try hcb. try hsb. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rwr_at_agree : ltac2:(zQ "71!hf!k2!s5!hc!jtd!it0!ki9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1A$3>1n$3>0@4$4$5^4^2^1>0@4$6^5^4^3^2@4$4$5^5^4^3").
Proof. try hcb. try hsb.
  (intros m m' A n nd_i1 AG; ndestruct nd_i1 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree' : ltac2:(zQ "b1!hf!k2!s5!kn0!it0!knc!hc!ki9!krf!ks7!kt5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1A$6>2cs@1$5$8>0@4$3$4^4^2^1>0@4$7^5^4^3@1$a@1$9^2@4$3$4^5^4^3").
Proof. try hcb. try hsb.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree' : ltac2:(zQ "b1!hf!k2!s5!lh8!it0!li2!knc!hc!ki9!lib!kt5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1A$7>2ws@1$6@1$1@1$0#k0>0@4$3$4^4^2^1>0@4$8^5^4^3@2$9+8@1$a@2$5@1$1@1$0#k0^2@4$3$4^5^4^3").
Proof. try hcb. try hsb.
  intros m m' A ws [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree' : ltac2:(zQ "a1!hf!k2!s5!lj1!it0!li2!knc!hc!ki9!kt5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1A$7>2bs@1$6@1$1@1$0#8>0@4$3$4^4^2^1>0@4$8^5^4^3@1$9@2$5@1$1@1$0#8^2@4$3$4^5^4^3").
Proof. try hcb. try hsb. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.



(* [comment removed for export] *)
Definition rgrp_region_addr : ltac2:(zQ "20!hc!jh0>2st$1>1a$0P") := ltac2:(zQ "h80!q3!h9!hp0!s0!lja!se!hkb!hmb!hn5!s5!hc!it9!jh0!jh9!ji2!jia!jj2!jk0!uf!jkc!jl1!jm2!jo6!joe\2st$c\1a$a@2$4$1\3rid$1@2$4$0\1r$0@2$2@3$3@1$9$0@6$h5$1$0@4$h6$1$7$6$0@4$h7$1$7$6$0^2@1$h1^4@2$8$0^1@2$2@3$3$f@1$d^1$b@2$2@2$h3@1$5^1^3@2$h4^3@2$h2@1$5^1@1$h0@1$e^1").

Lemma rmrep_transport_agree : ltac2:(zQ "h21!hf!k2!s5!hj5!s0!ljf!hp0!lk6!hc!jt4!ioa!it0!jkc!jl1!lkc!lp6!lub!jh0&@2$6@2$cZ^1@2$d^1@2$e+2+k0>2st$h1>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@4$a?5HCEIL?4HSEC^3^2>0>1a$8>0~0>0@2$f^6^2@3$4@1$2@1$1@1$0#8@1^5@1$3^3@1^6@1$3^3>0>1a$8>0~0>0@2$h0^7^2>0@1$7@3$4@1$2@1$1@1$0#8@3$9$b^7@1$3^3@1$5@1$1@1$0#8@1$7@3$4@1$2@1$1@1$0#8@3$9$b^7@1$3^4@1$5@1$1@1$0#8@4$a?5HCEIL?4HSEC^6^4").
Proof. try hcb. try hsb.
  (intros st m m' nd_i3 AG WG; ndestruct nd_i3 as (WF & CX & GL & AR & GR & SH)).
  npose WF as (Hres & WR & DJ & WA & WGr).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - ndestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - ndestruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
    + apply TC; [exact G6 |]. intros a Ha. apply rrepfoot_vmlock. cbn in Ha. lia.
  - intros ak ar Ha. ndestruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. ndestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    ndestruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RBC.
    split.
    + ndestruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rmrep_transport_agree' : ltac2:(zQ "f0!hf!k2!s5!hj5!ioa!hp0!s0!mg0!hc!lp6!lub!jh0!jkc!jl1!lkc>2st$b>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@4$4?5HCEIL?4HSEC^3^2>0>1a$8>0@2$5@2$cZ^1@2$d^1@2$e+2+k0>0@2$7@2$9^6^2@2$a^6^2@3$6@1$2@1$1@1$0#8@1^5@1$3^3@1^6@1$3^3@4$4?5HCEIL?4HSEC^5^3").
Proof. try hcb. try hsb.
  intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_of_munch_nw : ltac2:(zQ "e1!hf!k2!s5!hc!knc!hp0!lk6!mk1!mk8!ml1!mpf!jkc!jl1!lkc&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1C>1x$3P>1W@1$4$7>1m~0>2m'~0>0@3$8^3^2^1>0>1a$3>0@2$5@2$bZ^1@2$c^1@2$d+2+k0>0@1$6@1^7^2@2$9^7^3@3$a^6^4^3").
Proof. try hcb. try hsb.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.

End HCW.


(* [comment removed for export] *)
