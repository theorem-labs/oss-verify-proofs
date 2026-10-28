(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B MallocFacts_A Malloc_iface. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free F_free_spec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RMalloc_ifaceP RF_ntf RF_free_K RF_free RRealloc_iface RF_realloc_A RF_realloc_B RF_realloc_AS RF_realloc_BS RF_realloc RF_aligned_B RF_aligned_C RF_aligned RF_realloc_AI RF_realloc_BI.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import LibProg MI_Inv MAlign MI_WFree.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require MallocFacts_inv2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => let v := eval vm_compute in (bv_unsigned pc) in idtac "PC" v | _ => idtac "no evt goal" end.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem rrealloc_inplace_proof : rrealloc_inplace_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n0 n lo B errv old
         HEAP Hin AV HB ST LO SLO ERR OLD MI TP A0 A1 N.
  unfold RREALLOC_STACK in SLO.
  pose proof (RHEAP_block_range_proof s LB m (p, A, n0) HEAP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR.
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in BR.
  unfold raw_realloc_inplace. apply implM_get_bind'.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; destruct BR as (BR0 & _ & _ & BRC0 & _); lia).
  destruct (realloc_inplace (ps_m s) (fst p) n) eqn:INPL; [| apply implM_unr].
  (* [comment removed for export] *)
  pose proof HEAP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n0) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  destruct (MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLm & INV & _ & _ & _ & CR).
  destruct (MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin0) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] nn]. cbn [bslot boff bsize blk_slot blk_addr blk_size fst snd] in C1, C2, C3. subst c nn.
  destruct (MI_WFree.block_facts x0 st L BLm LS INV (fst p) bo n0 Hk) as (g' & bm & i' & ai & a & ar & ka & BF).
  pose proof (MI_WFree.bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as [OFF0 _].
  assert (INI : c_init_done (ctx st) <> 0).
  { destruct (MI_WFree.bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Har & _).
    pose proof INV as (IR & IA & _).
    destruct (MI_Inv.ia_secret _ IA) as [_ [(_ & _ & E0)|(E1 & _)]]; [| unfold ctx; lia].
    exfalso. rewrite E0 in Har. rewrite lookup_empty in Har. discriminate. }
  clear g' bm i' ai a ar ka BF.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF. pose proof (mf_ticks _ _ MF) as TK.
  (* [comment removed for export] *)
  apply LibProg.realloc_inplace_true in INPL. destruct INPL as (gq & iq & SLq & NMM & SCq1 & SCq2).
  rewrite <- Hst in SLq, SCq1, SCq2. change (s_slots (strip st)) with (s_slots st) in SLq.
  change (get_meta_rec (strip st) gq) with (get_meta_rec st gq) in SCq1, SCq2.
  assert (SCI : forall g i, (s_slots st) !! (blk_slot (p, A, n0)) = Some (g, i) ->
             m_sizeclass (get_meta_rec st g) <= size_to_class n + 1 /\ m_sizeclass (get_meta_rec st g) < 48).
  { intros g i SL. cbn [blk_slot fst] in SL. rewrite SLq in SL. inversion SL; subst. split; [exact SCq1| exact SCq2]. }
  destruct BR as (BR0 & BR16 & BRn & BRC & BRI).
  apply implM_ret.
  (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl ctusegs m) as WM.
  unfold RREALLOC_SYM, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *.
  subst a0 a1.
  assert (ETP : bv_unsigned tp + -164 = 3355012) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (ERR0 : rw_cells ctusegs m 3355012 [C4 errv]) by (rewrite <- ETP; exact ERR). clear ERR.
  (* [comment removed for export] *)
  st1. st1. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  carve_frame 64%nat ST.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; lia);
    assert (HEAP1 : RHEAP s LB mX) by (eapply RHEAP_frame_proof; [exact HEAP| exact MUs| exact WM|]; constructor; [left; cbn; lia| constructor]);
    assert (AV1 : rauxv_ok mX B) by (eapply rauxv_ok_frame; [exact AV| exact MUs| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]);
    assert (MI1 : mem_inv ctusegs mX) by assumption
  end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    first [ assert (ERR1 : rw_cells ctusegs mX 3355012 [C4 errv])
              by (eapply rw_cells_transport; [exact ERR0| exact MUs| exact WM|]; cbn [disjoint_from cells_size csize]; lia)
          | pose proof (ERR0 : rw_cells ctusegs mX 3355012 [C4 errv]) as ERR1 ];
    first [ assert (OLD1 : rw_cells ctusegs mX A [CB (Z.to_nat n0) old])
              by (eapply rw_cells_transport; [exact OLD| exact MUs| exact WM|]; cbn [disjoint_from cells_size csize]; lia)
          | pose proof (OLD : rw_cells ctusegs mX A [CB (Z.to_nat n0) old]) as OLD1 ];
    assert (HP01 : rheap_pres LB (bv_unsigned sp) m mX)
      by (eapply (rheap_pres_stack s LB m mX); [exact HEAP| exact MUs| exact WM|]; constructor; [cbn [fst snd]; lia| constructor])
  end.
  eapply evt_cut.
  { eapply rrealloc_hdr_spec_I with (st:=st) (LB:=LB0) (blk:=(p, A, n0)) (off:=bo) (n:=n) (L:=L) (BL:=BLm) (LS:=LS);
      [exact C| exact Hin0| exact OFF0| exact C3| exact INV| exact CR| exact MR1| exact TK| exact MI1| exact INI
      | apply unsigned_lit; lia| exact N| exact NMM| exact SCI
      | rewrite unsigned_lit by lia; exact FR| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia]. }
  cbv beta. intros msf TPOST.
  destruct TPOST as (g2 & i2 & r2 & mR & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & -> &
                     SL2 & Hr2 & Kr2 & Q20 & R32 & OFF258 & MRR & TKR & WF & RS16 & EHI & FITE & RBC2 & RIMG & NOBLK).
  cbn [blk_addr blk_slot blk_size blk_id fst snd] in SL2, Hr2, Kr2, R32, MRR, TKR, WF, RS16, EHI, FITE, NOBLK |- *.
  rewrite ?unsigned_lit in WF |- * by lia.
  destruct WF as (MUR & WMR & MIR & WRR).
  set (stride := get_stride (get_meta_rec st g2)) in *.
  set (S_ := A - UNIT * bo) in *. set (E_ := S_ + stride - IB) in *.
  set (st3 := fst (realign_at st g2 i2 n bo 0)) in *.
  unfold UNIT, IB in *.
  (* [comment removed for export] *)
  assert (ALE : E_ + 4 <= alloc_ceiling) by lia.
  assert (DJW : forall a, alloc_ceiling <= a \/ 0x10000 <= a < 0x355000 -> outside (raligned_W S_ A n E_) a).
  { intros a Ha. unfold raligned_W, outside. repeat split; first [exact I | lia]. }
  assert (FR3 : rw_cells ctusegs mR (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR| exact MUR| exact WMR|].
    cbn [cells_size csize]. unfold raligned_W, disjoint_from. repeat split; lia. }
  assert (ST3 : stk ctusegs mR lo (bv_unsigned sp + -64)).
  { eapply stk_transport_disjoint; [exact ST| exact MUR| exact WMR|].
    unfold raligned_W, disjoint_from. repeat split; lia. }
  release_frame FR3 ST3 (bv_unsigned sp).
  assert (ERR3 : rw_cells ctusegs mR 3355012 [C4 errv]).
  { eapply rw_cells_transport; [exact ERR1| exact MUR| exact WMR|].
    cbn [cells_size csize]. unfold raligned_W, disjoint_from. repeat split; lia. }
  assert (AUX3 : rauxv_ok mR B).
  { eapply rauxv_ok_frame; [exact AV1| exact MUR| exact WMR|].
    unfold raligned_W, RAUXV_CELL.
    constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; (split; [lia| destruct RIMG; [left; lia| right; lia]]). }
  (* [comment removed for export] *)
  assert (NDS : List.NoDup (map blk_slot LB)) by (exact (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C))).
  assert (ELB : lb_remove p LB = lbrm LB (p, A, n0)) by (apply lb_remove_lbrm; [exact NDS| exact Hin]).
  assert (NOB : forall b, In b (lb_remove p LB) -> blk_addr b + blk_size b <= S_ - 4 \/ E_ <= blk_addr b).
  { intros b Hb. rewrite ELB in Hb. unfold lbrm in Hb. apply In_filter_iff in Hb. destruct Hb as [HbL Hne].
    apply NOBLK; [eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HbL]|].
    intros Eb. cbn [blk_slot fst] in Hne, Eb. rewrite Eb, aptr_eqb_refl in Hne. exact Hne. }
  assert (HPR : rheap_pres (lb_remove p LB) (bv_unsigned sp) m mR).
  { intros a Ha CA. split.
    - rewrite (MUR (wa a)).
      2:{ rewrite wa_unsigned by lia.
          destruct CA as [CA|[[CA _]|(b & Hb & Hab)]].
          + apply DJW. left. lia.
          + apply DJW. right. lia.
          + destruct (NOB b Hb); unfold raligned_W, outside; repeat split; lia. }
      destruct (HP01 a Ha ltac:(destruct CA as [CA|[CA|(b & Hb & Hab)]]; [left; exact CA| right; left; exact CA| right; right; exists b; split; [exact (lb_remove_incl _ _ _ Hb)| exact Hab]])) as [E1 _].
      exact E1.
    - intros W0. apply WMR. apply WM. exact W0. }
  (* [comment removed for export] *)
  assert (PERM3 : Permutation ((p, A, n) :: lbrm LB0 (p, A, n0)) ((p, A, n) :: lb_remove p LB)).
  { apply perm_skip. rewrite ELB. apply lbrm_perm. exact PERM. }
  assert (AR3 : AREACH_from ref_reserved st3 ((p, A, n) :: lbrm LB0 (p, A, n0))).
  { pose proof (areach_realign st LB0 (p, A, n0) g2 i2 bo 0 n AR Hin0 SL2 Q20 R32 OFF0 C3 ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(cbn [blk_size snd]; lia) ltac:(replace (0 / UNIT) with 0 by reflexivity; lia)) as X.
    cbn [blk_id blk_addr blk_size fst snd] in X. rewrite Z.add_0_r in X. exact X. }
  assert (HEAP3 : RHEAP s ((p, A, n) :: lb_remove p LB) mR).
  { exists st3, ((p, A, n) :: lbrm LB0 (p, A, n0)). split; [exact PERM3|].
    split; [subst st3; rewrite strip_realign_at; exact Hst|]. split; [exact MRR|]. split; [| exact AR3].
    unfold brk_link in *. subst st3. rewrite ctx_realign_at. revert BL.
    destruct (Malloc.c_brk (ctx st)) as [| |brid boff]; intros BL; [exact I| exact I| rewrite conc_realign_at; exact BL]. }
  (* [comment removed for export] *)
  pose proof (rw_cells_split_CB ctusegs _ A [] (Z.to_nat n0) old [] [Z.to_nat n; Z.to_nat (n0 - n)] OLD1 ltac:(cbn; lia)) as OLDS.
  cbn [app mk_CB_cells] in OLDS.
  destruct (rw_cells_app_inv _ A [CB (Z.to_nat n) (firstn (Z.to_nat n) old)] _ OLDS) as [OLDa _].
  assert (KEEP : rw_cells ctusegs mR A [CB (Z.to_nat n) (firstn (Z.to_nat n) old)]).
  { eapply rw_cells_transport; [exact OLDa| exact MUR| exact WMR|].
    cbn [cells_size csize]. unfold raligned_W, disjoint_from. repeat split; lia. }
  (* [comment removed for export] *)
  apply evt_done. unfold rrealloc_inplace_post.
  do 15 eexists. exists mR, errv.
  split. { rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia.
           rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact MIR|]. split; [assumption|]. split; [rewrite ETP; exact ERR3|]. split; [exact AUX3|].
  split; [exact HPR|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HEAP3| exact KEEP].
Qed.
End WithCeiling0.
