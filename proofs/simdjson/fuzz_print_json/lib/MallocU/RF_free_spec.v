(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free F_free_spec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RF_ntf RF_free_K RF_free.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require MallocFacts_inv3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rauxv_ok_pres_B : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 977220 <= a < 977224) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 977220 <= a < 977224.

Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in LO; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  intros [FP|[DR|ER]].
  - pose proof (rfree_fp_lt st m lo sp a MR ltac:(unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia) LS FP). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - lia.
Qed.

Lemma rfp_not_img a : 0xd5000 <= a < 0x110000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (977220 <= a < 977224) -> ~ FPT a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in LO; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - exact (N2 ER).
Qed.

Lemma rfp_not_image a : 0xd5000 <= a < 0x110000 -> ~ ralloc_static a -> ~ FPT a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in LO; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in RGC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
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
Qed.

Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

Theorem rfree_spec_proof : rfree_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.

  assert (INI : c_init_done (ctx st) <> 0).
  { destruct (MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL' & (IR & IA & _) & _).
    destruct (MI_Inv.ia_secret _ IA) as [_ [(_ & _ & E0)|(E1 & _)]]; [| unfold ctx; lia].
    exfalso. pose proof (go_slot _ _ _ (ci_gmetas _ _ C b g HBg)) as (a & ar & k & Ha & _).
    rewrite E0 in Ha. rewrite lookup_empty in Ha. discriminate. }

  eapply (implM_evt usegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - exact HOK.
  - apply rimplT_reach.
    apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0 | exact INI].
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
    +   unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + destruct LEAF as (ans & o' & FO).
      eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
      cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
      cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.
End WithCeiling0.
