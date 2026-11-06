(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free F_free_spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RF_ntf RF_free_K RF_free.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv3.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~j63mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~nfaRAUXV_CELL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~se8rauxv_ok46Stdlib6ZArith6BinInt1Zhhc2lehc3andsecrpres_excepthhc3addhhc2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~hlc5block36Stdlib5Lists4Listhqa2In37Corelib4Init9Datatypeshs34list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_free~~~~~~hu34lbrm79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUdRMalloc_iface~~~~~~iiaarheap_presiiaarfree_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_B~~~~~~iob4CINVnf5rmrep69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~iu15hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ji56region01N25stdpp9countablejn0bN_countable35stdpp7numbers1Njp06eq_dechs34Somehs33fsths36optionhc2eqhc2exhlc8blk_slotji59s_regions25stdpp4baseju76lookup25stdpp4gmapjvd4gmapjvdbgmap_lookuphc2orhu37DROPPED79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcRMallocKit_B~~~~~~kj08rfree_fp" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rauxv_ok_pres_B : ltac2:(zQ "a0!h9!j0!n9!s1!hh1!hj4!hja!hk0!hkf!hl6>1C>0$0P>1m$2>2m'$2>1B$0>0@4$4?5HCEIL?4HSEC^3^1>0@3$7^5^4^3>0>1a$0>0@2$5^4^1@1$1@1^8^2>0>1a$0>0@2$6@2$5$3^1@2$9^1@2$8$3+8@1$1@1^9^2@4$4?5HCEIL?4HSEC^6^5").
Proof. try hcb. try hsb.
  (intros C m m' B nd_i1 HP HB HC; ndestruct nd_i1 as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H)).
  nexists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : ltac2:(zQ "10!it1@2$0?2st?3LB0").
Hypothesis MR : ltac2:(zQ "10!it9@4$0?5HCEIL?4HSEC?2st?1m").
Hypothesis LO : ltac2:(zQ "20!jhc!hj4@2$1@1$0?5HCEIL?2lo").
Hypothesis LS : ltac2:(zQ "10!hj4@2$0?2lo?2sp").
Hypothesis BLKR : ltac2:(zQ "h20!jm3!jmd!hq1!jo1!jq1!jqb!jr3!jra!js4!js9!h9!ii2!jse!jta!hrd!jv3!kg9!kh1>4blk'$2>0@3$e$2^1@2$b?3LB0?3blk@2$9$0\2r'$0@3$8@1$7$0@6$f$1$0@4$h0$1$4$3$0@4$h1$1$4$3$0@3$6$1$a@1$c^3@1$d?3st'@2$5$0^1").
Hypothesis SHR : ltac2:(zQ "b0!jm3!jmd!jo1!jq1!jqb!jra!js4!jta!jv3!kg9!kh1>3rid$1>2r'$0>0@3$6@1$5$0@6$8$1$0@4$9$1$3$2$0@4$a$1$3$2$0^2@1$7?3st'@2$4$0^1@3$6@1$5$0@6$8$1$0@4$9$1$3$2$0@4$a$1$3$2$0^3@1$7?2st@2$4$0^2").
Hypothesis PE : ltac2:(zQ "80!ki0!hja!h9!ki5!kn4!hk0!hj4!hl6@3$5\1a$2@2$0@4$4?2st?2lo?2sp^1@2$0@3$3?2st?3st'^1@2$1@2$6+hgurl4^1@2$7^1+hgurl8?1m?2m'").

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 1108820 <= a < 1108824.

(* [comment removed for export] *)
Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof. try hcb. try hsb.
  intros Ha. pose proof MR as (WF & _). npose WF as (Hres & WR & DJ & WA & WG). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in LO.
  intros [FP|[DR|ER]].
  - pose proof (rfree_fp_lt st m lo sp a MR ltac:(hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia) LS FP). lia.
  - ndestruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - lia.
Qed.

Lemma rfp_not_img a : 0xf4000 <= a < 0x131000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (1108820 <= a < 1108824) -> ~ FPT a.
Proof. try hcb. try hsb.
  intros Ha N1 N2. pose proof MR as (WF & _). npose WF as (Hres & WR & DJ & WA & WG). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in LO.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + ndestruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + ndestruct X as (b & gh & Hb & Hin). ndestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + ndestruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - ndestruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - exact (N2 ER).
Qed.

Lemma rfp_not_image a : 0xf4000 <= a < 0x131000 -> ~ ralloc_static a -> ~ FPT a.
Proof. try hcb. try hsb.
  intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof. try hcb. try hsb.
  intros Hb' Hab. pose proof MR as (WF & _). npose WF as (Hres & WR & DJ & WA & WG). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in LO.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RGC.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + ndestruct X as (rid & r & Hr & NK & Hin).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + ndestruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * ndestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + ndestruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - ndestruct DR as (rid & r & Hr & Hr' & Kr & Hin).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed.

Lemma rheap_pres_free : ltac2:(zQ "50!hq1!hrd!htb!ii2!imf>3LB'@1$2$0>0>1b$0>0@3$1$0^1^2@3$1$0^2@2$3?3LB0?3blk@4$4^2?2sp?1m?2m'").
Proof. intros LB'. try hcb. try hsb.
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

Lemma rauxv_ok_free : ltac2:(zQ "30!hh1!h9!hj4>1B$1>0@4$0?5HCEIL?4HSEC?1m^1>0@2$2?2sp^2@4$0?5HCEIL?4HSEC?2m'^3").
Proof. intros B. try hcb. try hsb.
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rfree_spec_proof : ltac2:(zQ "10!ind@2$0?5HCEIL?4HSEC").
Proof. try hcb. try hsb.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  ndestruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
  (* [comment removed for export] *)
  eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - exact HOK.
  - apply rimplT_reach.
    apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    ndestruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
    unfold rfree_post. neexists 16. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
    split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
             intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [reflexivity|]. split; [reflexivity|].
    exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
    split; [reflexivity|]. split; [exact MR'|]. split.
    + (* [comment removed for export] *) unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + ndestruct LEAF as (ans & o' & FO).
      eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
      cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
      cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.

End HCW.

