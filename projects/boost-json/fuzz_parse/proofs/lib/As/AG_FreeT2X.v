(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AsanAllocCons AsanAllocConsC SReach LazyRestrict LazyLedger LazySR LazyNodes.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepX AsDepotInv AsDepotHash AsUnwind AW_DepotFrame
     AW_MallocBase AW_Put1 AW_Enqueue2 AG_MallocModel AG_Malloc2 AG_Frame AG_FreeModel AG_FreeModel2 AG_Free2 AG_RepQ AG_FreeMid AG_FreeTail SecLazy
     AG_WriteSet AG_RecycleDefs AG_RecycleModel3 AG_ComplFrame AG_FreeT2 AG_FreeT2W AG_RecycleChunk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hc5chunk36Stdlib5Lists4Listm52In37Corelib4Init9Datatypesnd4pairnd4prod37Corelib4Init5Logicq32eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~rc4a_strc3albrc3asthcaCAllocatedhc8ch_statehc7ch_usedhcbch_user_beghcachunk_listhc6cstatehc8qc_bytes3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshledmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhq65mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehtb5Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ih25asegshc5as_tq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~ile6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~iq1dhunspell_scfg46Stdlib6ZArith6BinInt1Ziu92ltnd4boolnd4true79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_FreeTail~~~~~~jh5bfree_gpostXjh59free_mids69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocConsC~~~~~~jn24NUMchcfas_cache_initedhc5as_gqhcdkMaxCacheSizehch2kQuarantineMaxSizeiu93addrc6ARHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~kgbcdepot_placedrc8AFS_SIZErc5a_fsbrc4disjiu93mulq33and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~ko24d_nbko24d_sb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~kt25aceiliu92le04Npos35stdpp9bitvectorbdefinitionsli5bbv_unsignediu93powiu96modulorc3ATP" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma alb_intro : ltac2:(zQ "f0!h9!ld!n8!p5!pc!r7!va!hg1!hg7!hgd!hha!hi5!hif!hjd!hka>1s$8>2ch$1>0@3$2$1^1@1$d@1$6^2>0@3$5$e@1$a^2$9@3$2@2$4$0$0@4$3$0$0@1$c^3@1$b^3@1$7^4").
Proof.
  intros s ch IN AL. unfold alb. apply in_map_iff. exists ch. split; [reflexivity|]. apply filter_In. split; [exact IN|].
  unfold is_alloc. rewrite AL. reflexivity.
Qed.

Section FreeTail2X.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk).

  Let st := a_st s.
  Let TH := a_thr s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x90ca0 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let LB' := lb_remove U LB.

  Hypothesis HR : ltac2:(zQ "10!kg2@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis DPL : ltac2:(zQ "10!kkb@3$0?5HCEIL?1s?1d").
  Hypothesis DFS : ltac2:(zQ "70!klb!km6!kme!kn5!knc!ks2!ksa@2$4@4$2@1$1?1s$0@1$5?1d@2$3+h0+hggg0@4$2@1$1?1s$0@1$6?1d@2$3+8+ogg0").
  Hypothesis LO : ltac2:(zQ "20!lh0!lh9@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!lhf!jvb!lh9!lk2@2$2@2$1?2lo+so0@2$3@1$0#k0?2sp").
  Hypothesis SPT : ltac2:(zQ "50!lhf!jvb!lh9!ll1!lk2@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SPA : ltac2:(zQ "50!r7!lhf!h9!ll8!lk2@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis TPv : ltac2:(zQ "50!r7!lhf!h9!lm2!lk2@3$0$2@2$4@1$1#k0?2tp$3").

  Theorem free_tail2 : ltac2:(zQ "h60!va!hl3!hp5!ht2!ig9!ikd!il6!ip7!it8!jg1!jg7!jge!r7!jl6!jm5!hg7!jr3!jrb!jsd!jt5!ju5!jvb>2sm$f>4msF2$2>3mo2$4>0@he$e?5HCEIL?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1m?2mo?1s?2LB?1d?2lo?2CH?2ch^3^2^1>0@2$9$h3@1$1@1$6@1$0^4>0@2$9$h4@2$h5@1$1@1$h2@1$0^5@1$1@1$6@1$0^5>0@3$c$a@1$h1@1$0^6$b>0@1$h0@1$0^7>0>4msF'$2>3mo'$4>0@hd$d?5HCEIL?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1m?2mo?1s?2LB?1d?2lo?2CH?2ch^2^1@4$7$5$8?1Q@2$3^3^2@4$7$5$8?1Q@2$3^8^7").
  Proof.
    intros sm msF2 mo2 MID GT GT2 INIT NM K.
    ndestruct MID as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jk & rest & m2 & Ethr & Ectx & Efsb & Ezr & Etop & Ebot & Esb & Epa & Esec & Egq & HAL & TNE & TQB & GQB & OK2 & VIS2 & HQ & AWV & FX & AMX & NVS & DEP & DPL2 & DCOV & MI2 & ST2 & PFR & ESO & TRB & LR & NR & TFB & F4 & AMF & WM & ACM & AVX & (stX & ev0 & ev2 & EM & SBS & SC0)).
    npose HQ as (RQ & ND & LBs).
    pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ2. pose proof (WFQ_consts _ _ _ WQ2) as (CQmax & CQmin & CQc). pose proof (WFQ_lens _ _ _ WQ2) as [L32 _].
    assert (DLO : d_nb d' + 16 * 65536 <= lo /\ d_sb d' + 8 * 32768 <= lo).
    { npose DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & G12 & G13). unfold d'. rewrite d_nb_put, d_sb_put. clear - G11 G13 LO. lia. }
    eapply (free_tail2_w ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q s LB d lo CH ch LO HI SPT SPA TPv DLO (step_chunk_real gp tp F fc Q d' lo) sm msF2 mo2
              t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jk rest m2 Ethr Etop Ebot TNE TQB GQB OK2 VIS2 HQ AWV FX AMX DEP DPL2 DCOV MI2 ST2 PFR ESO TRB LR NR TFB F4 GT GT2 INIT NM).
    intros msF' mo' PO. apply K.
    ndestruct PO as (sF & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5
                    & Et5 & Ec5 & Ef5 & Ez5 & Etp5 & Ebt5 & Eal5 & Esb5 & Epa5 & SUB5 & INIT5 & AU5 & OK5 & VIS5 & RQ5 & AWV5 & FX5 & AMX5
                    & NVS5 & AVM5 & DCOV5 & DEP5 & DPL5 & MI5 & ST5 & ACM5 & AVS5 & _ & ALK5 & AGA5 & MOD5).
    (* [comment removed for export] *)
    pose proof SBS as SBS0. unfold same_but_shadow in SBS0.
    ndestruct SBS0 as (_ & _ & Erg & _ & _ & _ & _ & Ech & Etq & Egq' & _ & _ & _ & Eqm & Eqmin & Eqc).
    ndestruct (MOD5 stX SBS) as (stR & evR & QR & SR).
    assert (L32X : length (as_regions (transfer_m stX)) = 32%nat) by (unfold transfer_m; cbn [as_regions set_gq set_tq]; rewrite Erg; exact L32).
    ndestruct (quarantine_recycle_final (transfer_m stX) (as_qmin stX) stR evR L32X QR) as (CS & TQR & GQR).
    pose proof SR as SR0. unfold same_but_shadow in SR0.
    ndestruct SR0 as (_ & _ & _ & _ & _ & _ & _ & EchF & EtqF & EgqF & _).
    pose proof (WFQ_consts _ _ _ (AREPQ_WFQ _ _ _ _ RQ5)) as (FQmax & FQmin & FQc).
    assert (QB : qbounds (a_st sF)).
    { unfold qbounds. rewrite <- EtqF, <- EgqF, TQR, FQc, FQmax. unfold transfer_m. cbn [as_tq set_gq set_tq qcache0 qc_bytes].
      split; [unfold kMaxCacheSize; clear; lia|]. rewrite Eqmin, CQmin in GQR. clear - GQR. unfold kQuarantineMinSize, kQuarantineMaxSize in *. lia. }
    (* [comment removed for export] *)
    assert (CSF : forall x, In x (chunk_list (a_st sF)) -> In x (chunk_list (a_st sm))).
    { intros x Hx. rewrite <- (chunk_list_ext stX (a_st sm) Ech). rewrite <- (chunk_list_ext stR (a_st sF) EchF) in Hx.
      apply CS in Hx. rewrite (chunk_list_ext (transfer_m stX) stX eq_refl) in Hx. exact Hx. }
    assert (LBF : forall b, In b LB' <-> In b (alb sF)).
    { intros [A n]. split.
      - intros Hb. apply (proj1 (LBs (A, n))) in Hb. ndestruct (alb_In sm A n Hb) as (x & IN & AL & <- & <-).
        exact (alb_intro sF x (ALK5 x IN AL) AL).
      - intros Hb. apply (proj2 (LBs (A, n))). ndestruct (alb_In sF A n Hb) as (x & IN & AL & <- & <-).
        exact (alb_intro sm x (CSF x IN) AL). }
    (* [comment removed for export] *)
    assert (OKs : ast_ok s) by exact (proj1 (proj1 HR)).
    assert (HLB1 : forall b, In b LB' -> In b (alb sm)) by (intros b Hb; exact (proj1 (LBs b) Hb)).
    assert (SUB1 : forall sc, In sc (as_sec (a_st sm)) -> In sc (as_sec (a_st s))) by (intros sc Hsc; rewrite <- Esec; exact Hsc).
    assert (ACM5d : acompl sm sF d lo (bv_unsigned sp) m2 m5) by (exact (proj1 (acompl_dput sm sF d (depot_hash T) nT lo (bv_unsigned sp) m2 m5) ACM5)).
    unfold free_gpostX.
    nexists sF, u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m5.
    split; [rewrite Et5; exact Ethr|]. split; [rewrite Ec5; exact Ectx|]. split; [rewrite Ef5; exact Efsb|].
    split; [rewrite Ez5; exact Ezr|]. split; [rewrite Etp5; exact Etop|]. split; [rewrite Ebt5; exact Ebot|].
    split; [intros sc Hsc; exact (SUB1 sc (SUB5 sc Hsc))|].
    split; [rewrite Eal5; exact HAL|].
    split; [exact OK5|]. split; [exact VIS5|].
    split; [split; [exact (AREP_of_AREPQ sF m5 RQ5 QB)| split; [exact ND| exact LBF]]|].
    split; [exact AWV5|]. split; [exact FX5|]. split; [exact AMX5|].
    split; [exact (nonvm_same_trans _ _ _ NVS NVS5)|].
    split; [exact DEP5|]. split; [exact DPL5|]. split; [exact DCOV5|]. split; [exact MI5|]. split; [exact ST5|].
    split.
    { apply (amframe_trans s LB' (bv_unsigned sp) m m2 m5 AMF).
      apply (amframe_of_compl s sm sF LB' d lo (bv_unsigned sp) m2 m5 OKs HLB1 (conj Ethr (conj Esb Epa)) Esec SUB5 DPL DFS LO ltac:(clear - HI; lia) ACM5d AGA5). }
    split; [exact (avis_trans s sm sF m m2 m5 SUB1 SUB5 (avis_of_wmono s sm m m2 WM) AVS5)|].
    split; [exact (acompl_trans s sm sF d lo (bv_unsigned sp) m m2 m5 (conj Ethr (conj Esb Epa)) SUB1 ACM ACM5d)|].
    split; [exact (avmx_trans s sm sF mo mo2 mo' SUB1 SUB5 AVX AVM5)|].
    rewrite EM, (free_tail_recycle U size stX ev0 ev2) by (rewrite ?Etq, ?Egq', ?Eqc, ?Eqm, ?CQc, ?CQmax; first [exact GT| exact GT2]).
    rewrite QR. eexists stR, _. split; [reflexivity| exact SR].
  Qed.
End FreeTail2X.
End HCW.
