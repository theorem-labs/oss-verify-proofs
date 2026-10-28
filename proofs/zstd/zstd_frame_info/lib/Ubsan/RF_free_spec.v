(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free F_free_spec.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RF_ntf RF_free_K RF_free.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require MallocFacts_inv3.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rauxv_ok_pres_B : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof.
  intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. Local Ltac2 Set LiaHints.tbl := fun () => "0020>31848951228.256568648877.25 00000400:S2HaS1H2Ha".
lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : ATOP <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 188300 <= a < 188304) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 188300 <= a < 188304.

(* [comment removed for export] *)
#[using="rc m MR LO LS"] Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). atop_facts.
  intros [FP|[DR|ER]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0040>17993200296.2759308665329.2759309007462.3159314873579.2800000400G00X00^S2LOS2LO2LS2Ha5ATOPR2ERS2LO2LS2Ha3Hin2RCS2Ha1H".
pose proof (rfree_fp_lt st m lo sp a MR ltac:(atop_facts; lia) LS FP). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc m MR LO"] Lemma rfp_not_img a : 0x1c000 <= a < 0x4f000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (188300 <= a < 188304) -> ~ FPT a.
Proof.
  intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). atop_facts.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + Local Ltac2 Set LiaHints.tbl := fun () => "0050>59308579281.3759308579281.3859308579281.4259308579414.3859315137787.2900000A00R01101E01TS2Ha2N23Hin2H12H2S2Ha2N23Hin2H12H2S2Ha2N23Hin2Cb3Sb03Sb12H02H12H2S2Ha2N23Hin2H12H22H3S2LO2Ha5ATOPR1X".
lia.
    + exact (N1 X).
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - exact (N2 ER).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc m MR LO"] Lemma rfp_not_image a : 0x1c000 <= a < 0x4f000 -> ~ ralloc_static a -> ~ FPT a.
Proof.
  intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

#[using="rc m C MR LO BLKR SHR"] Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
  intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). atop_facts.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). atop_facts.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + Local Ltac2 Set LiaHints.tbl := fun () => "0070>59308579414.5359308579543.5659308579543.5759308579543.5959308665329.4759314955108.5159315137787.4700000I00e01A01h02?02d03AS3Hab3A163LRG3Hin2H34AENDS3Hab3A163LRG3Hin2H44AEND2H3S3Hab3A163LRG3Hin2H44AEND2H3S3Hab3A163LRG3Hin2Cb3Sb12H44AEND3Sb02H3S3Hab3A164AEND2AL2H22ERS3Hab3A164AEND2AL2HD1H2H02H12H23Hin1ES2LO3Hab4AEND3RGC1X3A162AL2H2".
lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & NK & Hin).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc st st' lo C MR LO LS BLKR SHR PE FPT"] Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof.
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

#[using="st st' lo MR LO LS PE FPT"] Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof.
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. Local Ltac2 Set LiaHints.tbl := fun () => "0040>16075364609.2317514996479.2346011996001.2359919736071.2300000400800<00CS2HaS2HaS2HaS2HB2Ha".
lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem rfree_spec_proof : rfree_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
  (* [comment removed for export] *)
  eapply (implM_evt usegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - rewrite <- Hst. exact (rregions_wf_atop _ (proj1 MR)).
  - exact HOK.
  - apply rimplT_reach.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020?28702212166.10842550707152.80 00000500:S3SLOS3SLO".
apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
    unfold rfree_post. do 16 eexists. split; [reflexivity|].
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
    + destruct LEAF as (ans & o' & FO).
      eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
      cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
      cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
