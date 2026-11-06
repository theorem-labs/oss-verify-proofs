(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W18 ASlot_I ASlot_M0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list37Corelib4Init5Logicjb3andjb2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W9~~~~~~la3gmf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~q15block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~ue6ISTF_gue4lmem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~hk5cref_reserved79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hp64aptrhp6cget_meta_rechp6bm_sizeclasshp66mstate46Stdlib6ZArith6BinInt1Zig52leig52ltla3tafhp66r_basehp66regionhp65r_lenhp6bround_up_pgig53addjb2or01N25stdpp9countableimabN_countable35stdpp7numbers1Nioa6eq_dechc4Somehc6option69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ir55hceilhp69s_regions25stdpp4basejg66lookup25stdpp4gmapjhc4gmapjhcbgmap_lookup04Npos35stdpp9bitvectorbdefinitionsjk52bvhk55rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMalloc_fp~~~~~~jn1armalloc_fphk54RCTX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~js83mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~kh28rauxv_okkh2crpres_except79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kn08rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~kr75rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kvc4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~lk09ENTRY_REL" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rgmf_of_facts : ltac2:(zQ "f0!h9!j4!kf!l5!pb!u6!hj5!hje!ho6!ht4!htc!huc!hvb!ihd!ii3>2st$c>2LB@1$1$5>2sc$0>1g$9>0@3$6@1$8?5HCEIL^4^3>0@2$7^5^2>0@3$3$0@1$b@2$a^6^3^4>0@2$2@2$dZ^5@2$e^5+j0@3$4^8^6^5").
Proof. intros st LB sc g. try hcb. try hsb.
  (intros F nd_i1 GSC SCR; ndestruct nd_i1 as (MEM & NX & PV)). assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
  pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  ndestruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
  pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  constructor.
  - exact MSL.
  - exact AVr.
  - exact FRr.
  - exact MW.
  - exact SC48.
  - exact GSC.
  - exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
    + intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
      change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
      exact (X Hmem Hgh S0).
    + intros o Ho. exact (GU b _ o Hgh Ho).
  - intros i Hi Hb. ndestruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
  - intros i Hi Hb. ndestruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
  - destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
    exists n, p. split; reflexivity.
Qed.

Lemma rtaf_of_facts : ltac2:(zQ "a0!j4!kf!h9!ii9!u6!hj5!ho6!hvb!ihd!ii3>2st$7>2LB@1$0$4>2sc$2>0@3$5@1$6?5HCEIL^3^2>0@2$1@2$8Z^2@2$9^2+j0@2$3^5^3").
Proof. intros st LB sc. try hcb. try hsb.
  intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
  pose proof (lf_lists _ LF) as (L1 & L2 & L3).
  change (fact_active (strip st)) with (fact_active st).
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  pose proof (lf_links _ LF) as LK.
  constructor.
  - intros g Hg. ndestruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
    change (lmem (strip st) g) with (lmem st g) in LM.
    split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
  - intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
    change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
    split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
    split; [exact SCn|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
    exact (LKn n Hn).
  - intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
    change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
    split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
    exact (LKp p Hp).
  - pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : ltac2:(zQ "10!jm8@4$0?5HCEIL?4HSEC?2st?1m").
Hypothesis ER : ltac2:(zQ "10!lo0@2$0?3st0?2st").

Lemma rst0_region : ltac2:(zQ "h30!iif!ihd!ij9!kf!ik3!ikc!ilb!im2!im7!inb!ipb!iq5!iqc!l5!iv0!iv9!jh2!ji8!jj0>3rid$8>1r$2>0@3$d@1$c$2@6$h0$8$2@4$h1$8$a$9$2@4$h2$8$a$9$2^2@1$f?3st0@2$b$2^1@2$3@2$1Z@1$0^2@2$3@2$1@2$6@1$0^2@1$5@1$4^2@1$e?5HCEIL@2$3@2$7@2$1@2$6@1$0^2@1$5@1$4^2+hggg0@2$1+kngg0@1$0^2@2$3@2$7@2$1@2$6@1$0^2@1$5@1$4^2+kngg0@2$1+vhgg0@1$0^2@2$3@2$7@2$1@2$6@1$0^2@1$5@1$4^2+vhgg0@2$1+vpgg0@1$0^2@2$7@2$1@2$6@1$0^2@1$5@1$4^2+vpgg0@2$1+hitgg0@1$0^2").
Proof. intros rid r. try hcb. try hsb.
  intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
  pose proof MR as (WF & _). npose WF as (_ & WR & _).
  ndestruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *. lia.
Qed.

Lemma rmalloc_fp_cases_ER : ltac2:(zQ "c0!h9!jjf!ii3!jm2!iqc!kf!im2!iv0!jm8!jr2!hvb!ihd>3stE$a>2mE>0@1$3@1$1#k0@1$4@1$3@1$1#8>2lo$0>2sp$0>1a$0>0@4$8?5HCEIL?4HSEC^5^4>0@5$9?3st0^6^4^3^2@2$6@2$5@2$b^5^3@2$2^3^4@2$2^3@1$7?5HCEIL").
Proof. intros stE mE lo sp a. try hcb. try hsb.
  intros (WF2 & _) H. npose WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  all: try pose proof (rfresh_below st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)) as FC'.
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. ndestruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. ndestruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. ndestruct (rst0_region (fst b) r Hr) as (_ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. ndestruct (rst0_region (fst b) r Hr) as (_ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in FC. lia.
Qed.

Lemma rmalloc_fp_image_ER : ltac2:(zQ "e0!ihd!kf!h9!ii3!jjf!js0!jm2!iqc!im2!iv0!jm8!jr2!hvb!ilb>3stE$c>2mE>0@1$6@1$4#k0@1$7@1$6@1$4#8>2lo$2>2sp$2>1a$2>0@4$a?5HCEIL?4HSEC^5^4>0@5$b?3st0^6^4^3^2>0@2$0@1$9?5HCEIL^5>0@2$1@2$0+hggg0^4@2$3^4+hitgg0@2$8@2$1@2$0$5^5@2$3^5@2$d$5+jq0@2$1@2$0+hgrmh4^5@2$3^5+hgrmh8").
Proof. intros stE mE lo sp a. try hcb. try hsb.
  intros (WF2 & _) H CLO HA. npose WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - exfalso. ndestruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. ndestruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. ndestruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. ndestruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

Lemma rauxv_ok_malloc_fp_ER : ltac2:(zQ "c0!h9!jjf!kgb!kl4!ihd!jm2!iqc!iv0!jm8!km0!jr2!hvb>3stE$b>2mE>0@1$5@1$1#k0@1$6@1$5@1$1#8>2lo$0>2sp$0>2m1$2>2m'$2>1B$0>0@4$8?5HCEIL?4HSEC^7^6>0@4$3?5HCEIL?4HSEC^4^2>0@3$9@4$a?3st0^9^7^6^5^4>0@2$4@1$7?5HCEIL^8>0@2$4^8^5@4$3?5HCEIL?4HSEC^7^6").
Proof. intros stE mE lo sp m1 m' B. try hcb. try hsb.
  intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
    ndestruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL in Ha.
    destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

Lemma rframe_keep_ER : ltac2:(zQ "f0!h9!jjf!kgb!kqb!kv3!ihd!jm2!j4!iqc!iv0!lj8!jm8!km0!jr2!hvb>3stE$e>2mE>0@1$6@1$1#k0@1$8@1$6@1$1#8>2lo$0>2sp$0>2m1$2>2m'$2>1A$0>2cs@1$7$a>0@4$b?5HCEIL?4HSEC^8^7>0@3$c@4$d?3st0^9^7^6^5^4>0@4$3$4^6^4^3>0@2$5^8^5>0@2$5@1$9?5HCEIL^6@4$3$4^8^7^6").
Proof. intros stE mE lo sp m1 m' A cs. try hcb. try hsb.
  intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

End HCW.

