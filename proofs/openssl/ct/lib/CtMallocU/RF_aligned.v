(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_enframe MallocBlocks MallocHINV MallocFacts_B MallocFacts_A Malloc_iface Malloc_fp F_free_spec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog LibProg MAlign.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_A MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMalloc_iface RMalloc_ifaceP RRealloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RF_malloc_top RF_realloc RF_aligned_A RF_aligned_B RF_aligned_H RF_aligned_C.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import MI_Kit MI_Inv MI_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma impl_post_evt {R} : forall (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl ctusegs (at_node ctusegs) t Q ms -> (forall r ms', Q r ms' -> evt ctusegs (Q' r) ms') -> impl ctusegs (at_node ctusegs) t Q' ms.
Proof.
  induction t as [r|nd k IH]; cbn; intros Q Q' ms H HQ.
  - eapply evt_cut; [exact H| exact (HQ r)].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.

Lemma implM_post_evt : forall {A} (c : Monad.M PState A) s (Q Q' : A -> PState -> machine_state -> Prop) ms,
  implM ctusegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt ctusegs (Q' a s') ms') -> implM ctusegs c s Q' ms.
Proof.
  intros A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms' Hx; cbn in Hx |- *; [apply evt_done; exact I| exact (HQ a s' ms' Hx)].
Qed.

Lemma list_filter_all {T} (P : T -> Prop) `{forall x, Decision (P x)} (l : list T) : (forall x, In x l -> P x) -> filter P l = l.
Proof.
  induction l as [|y l IH]; intros HP; cbn; [reflexivity|].
  rewrite decide_True by (apply HP; left; reflexivity). f_equal. apply IH. intros x Hx. apply HP. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma lbrm_fresh_perm (b : block) (LB LB2 : list block) :
  Permutation LB2 (b :: LB) -> List.NoDup (map blk_slot LB2) -> Permutation (lbrm LB2 b) LB.
Proof.
  intros P ND.
  eapply Permutation_trans; [apply lbrm_perm; exact P|]. unfold lbrm. cbn.
  rewrite aptr_eqb_refl. destruct (decide (negb true)) as [X|X]; [exfalso; exact X|].
  rewrite list_filter_all; [apply Permutation_refl|].
  intros x Hx. rewrite (aptr_eqb_neq (blk_slot x) (blk_slot b)); [exact I|]. intros E.
  pose proof (NoDup_map_perm blk_slot _ _ P ND) as ND'. cbn in ND'. apply List.NoDup_cons_iff in ND' as [NI _].
  apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma conc_strip' (st : mstate) (q : aptr) : conc (strip st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_realign_at st g i n off adj q : conc (fst (realign_at st g i n off adj)) q = conc st q.
Proof. rewrite <- (conc_strip' (fst (realign_at st g i n off adj))), strip_realign_at. reflexivity. Qed.
Lemma regions_realign_at st g i n off adj : s_regions (fst (realign_at st g i n off adj)) = s_regions st.
Proof. change (s_regions (strip (fst (realign_at st g i n off adj))) = s_regions (strip st)). rewrite strip_realign_at. reflexivity. Qed.
Lemma ctx_realign_at st g i n off adj : ctx (fst (realign_at st g i n off adj)) = ctx st.
Proof. change (s_ctx (strip (fst (realign_at st g i n off adj))) = s_ctx (strip st)). rewrite strip_realign_at. reflexivity. Qed.

Section ALIGNED.
Hypothesis HM : rmalloc_impl_stmt.

Theorem rposix_memalign_proof : rposix_memalign_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB al n mp lo B errv.
  intros HEAP AV SB ST CLO LO ERR MI TP A0 SPMP MPB WMP A1 HAL A2 N0 NR.
  unfold RALIGNED_STACK, RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *.
  pose proof HEAP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  pose proof WMP as (MP0 & MP8 & _).
  assert (ETP : bv_unsigned tp + -164 = 3355012) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (ERR0 : rw_cells ctusegs m 3355012 [C4 errv]) by (rewrite <- ETP; exact ERR). clear ERR.
  assert (NR0 : 0 <= aligned_req al n < 2^32) by (unfold aligned_req in *; lia).
  (* [comment removed for export] *)
  unfold raw_aligned_alloc.
  eapply (implM_evt ctusegs _ _ _ (raligned_entry_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m al n mp lo)).
  { eapply raligned_entry_walk; [exact A0| exact A1| exact A2| exact HAL| exact N0| lia| lia| exact (rmrep_replaced st m MR)| exact ST| exact CLO| lia| exact MI]. }
  intros ms1 (m1 & junk & -> & MU & WM & MI1 & ST1 & FR1).
  assert (HEAP1 : RHEAP s LB m1).
  { eapply RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
  assert (AV1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AV| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
  assert (ERR1 : rw_cells ctusegs m1 3355012 [C4 errv])
    by (eapply rw_cells_transport; [exact ERR0| exact MU| exact WM|]; cbn [disjoint_from cells_size csize]; lia).
  assert (WMP1 : wr_at ctusegs m1 mp 8) by (eapply wr_at_transport; [exact WMP| exact WM]).
  assert (HP01 : rheap_pres LB (bv_unsigned sp) m m1).
  { eapply (rheap_pres_stack s LB m m1); [exact HEAP| exact MU| exact WM|]. constructor; [cbn [fst snd]; lia| constructor]. }
  (* [comment removed for export] *)
  eapply implM_post_evt.
  { eapply HM with (B:=B) (lo:=lo) (LB:=LB) (errv:=errv) (n:=aligned_req al n);
      [exact HEAP1| exact AV1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact CLO
      | rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| rewrite ETP; exact ERR1| exact MI1| exact TP| reflexivity| exact NR0]. }
  cbv beta. intros r s' ms' PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & RES).
  rewrite !unsigned_lit in ST2, HPR by lia.
  replace (ret_pc (Z_to_bv 64 2837784)) with (Z_to_bv 64 2837784) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (ERR2' : rw_cells ctusegs m2 3355012 [C4 errv2]) by (rewrite <- ETP; exact ERR2).
  assert (FR2 : rw_cells ctusegs m2 (bv_unsigned sp + -48) [CB 8 junk; C8 s1; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0; C8 ra])
    by (eapply rheap_pres_rw_cells; [exact HPR| exact FR1| left; lia]).
  assert (WMP2 : wr_at ctusegs m2 mp 8) by (eapply rheap_pres_wr_at; [exact HPR| exact WMP1| left; lia]).
  assert (HP02 : rheap_pres LB (bv_unsigned sp) m m2).
  { eapply rheap_pres_trans; [exact HP01|]. eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]. }
  destruct r as [p|].
  2:{ (* [comment removed for export] *)
    destruct RES as [-> HEAP2].
    (* [comment removed for export] *)
    st1. try if_true.
    st1. st1. st1. st1. st1.
    (* [comment removed for export] *)
    st1. try if_true.
    st1. st1. st1. st1. rewrite ?ETP. st1.
    st1. st1. st1. st1.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold rposix_memalign_post.
    do 15 eexists. exists m2, errv2.
    split. { reflexivity. }
    split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
    split; [apply rheap_pres_but_of_pres; exact HP02|]. split; [exact EFA|]. split; [exact ESO|].
    split; [exact HEAP2|].
    intros a Ha. destruct (HP02 a ltac:(lia) ltac:(left; lia)) as [E _]. exact E. }
  (* [comment removed for export] *)
  destruct RES as (A & junkn & -> & BR & HEAP2 & NEW & _ & (off & gq & iq & OFFR & AOFF & SLq & S30q)).
  destruct BR as (BR0 & BR16 & BRn & BRC & BRI).
  pose proof HEAP2 as (st2 & LB2 & PERM2 & Hst2 & MR2 & [BL2 AR2]).
  cbn [ps_m] in AOFF, SLq, S30q. rewrite <- Hst2 in AOFF, SLq, S30q.
  change (conc (strip st2) (fst p)) with (conc st2 (fst p)) in AOFF.
  change (s_slots (strip st2)) with (s_slots st2) in SLq.
  change (get_meta_rec (strip st2) gq) with (get_meta_rec st2 gq) in S30q.
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR2) as C2.
  destruct (MallocFacts_inv.areach_inv _ _ _ AR2) as (L & LS & BLm & INV & _ & _ & _ & CR).
  assert (Hin2 : In (p, A, aligned_req al n) LB2) by (eapply Permutation_in; [apply Permutation_sym; exact PERM2| left; reflexivity]).
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR2) as MF2. pose proof (mf_ticks _ _ MF2) as TK2.
  assert (INI2 : c_init_done (ctx st2) <> 0).
  { destruct (MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin2) as (k & Hk & (C1 & _ & _)).
    destruct k as [[c bo] nn]. cbn [bslot fst snd blk_slot] in C1. subst c.
    destruct (MI_WFree.block_facts x0 st2 L BLm LS INV (fst p) bo nn Hk) as (g' & bm & i' & ai & aa & ar & ka & BF).
    destruct (MI_WFree.bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Har & _).
    pose proof INV as (IR & IA & _).
    destruct (MI_Inv.ia_secret _ IA) as [_ [(_ & _ & E0)|(E1 & _)]]; [| unfold ctx; lia].
    exfalso. rewrite E0 in Har. rewrite lookup_empty in Har. discriminate. }
  assert (SZ2 : blk_size (p, A, aligned_req al n) = n + al - 16) by reflexivity.
  assert (S30 : forall g i, s_slots st2 !! (blk_slot (p, A, aligned_req al n)) = Some (g, i) -> get_stride (get_meta_rec st2 g) - IB - blk_size (p, A, aligned_req al n) < 2^30).
  { intros g i SLg. cbn [blk_slot fst] in SLg. rewrite SLq in SLg. inversion SLg; subst. cbn [blk_size snd]. exact S30q. }
  eapply evt_cut.
  { eapply (raligned_tail_spec _ _ gp tp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 s1 F fc m2
              st2 LB2 (p, A, aligned_req al n) off n al mp L BLm LS junk C2 Hin2 OFFR AOFF INV CR MR2 TK2 MI2 INI2 SZ2 N0 HAL
              ltac:(unfold aligned_req in NR; lia) S30); rewrite ?unsigned_lit by lia; [exact FR2| exact WMP2| lia| lia| lia]. }
  cbv beta. intros msf TPOST.
  destruct TPOST as (g2 & i2 & adj & r2 & mR & w0 & w1 & w2 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & -> &
                     SL2 & Hr2 & Kr2 & Q20 & R32 & ADJ0 & ADJ16 & ADJN & OFF258 & PAL & MRR & TKR & WF & RS16 & EHI & FITE & RBC2 & RIMG & NOBLK).
  cbn [blk_addr blk_slot blk_size blk_id fst snd] in SL2, Hr2, Kr2, ADJN, PAL, MRR, TKR, WF, RS16, EHI, FITE, NOBLK |- *.
  rewrite ?unsigned_lit by lia.
  destruct WF as (MUR & WMR & MIR & WRR).
  set (stride := get_stride (get_meta_rec st2 g2)) in *.
  set (S_ := A - UNIT * off) in *. set (E_ := S_ + stride - IB) in *.
  set (A' := A + adj) in *.
  set (m3 := write_to_mem mR (wa mp) (le8 (Z_to_bv 64 A'))).
  set (st3 := fst (realign_at st2 g2 i2 n off adj)) in *.
  unfold UNIT, IB in *.
  (* [comment removed for export] *)
  assert (ALE : E_ + 4 <= alloc_ceiling) by lia.
  assert (DJW : forall a, alloc_ceiling <= a \/ 0x10000 <= a < 0x355000 -> outside (raligned_W S_ A' n E_) a).
  { intros a Ha. unfold raligned_W, outside. unfold aligned_req in *. repeat split; first [exact I | lia]. }
  assert (MUmp : munch [(mp, mp + 8)] mR m3).
  { subst m3. apply munch_write; [apply munch_refl| lia| rewrite length_le8; lia| rewrite length_le8; cbn; left; lia]. }
  assert (WMmp : wmono ctusegs mR m3) by (subst m3; apply wmono_write; apply wmono_refl).
  assert (WRmp : wr_at ctusegs mR mp 8) by (eapply wr_at_transport; [exact WMP2| exact WMR]).
  assert (MI3 : mem_inv ctusegs m3).
  { subst m3. apply mem_inv_store; [exact MIR|]. rewrite length_le8. replace (wa mp) with (wa (mp + 0)) by (f_equal; lia).
    apply (wr_at_store_ok ctusegs mR mp 8 0 8 WRmp); lia. }
  assert (FR3 : rw_cells ctusegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s1; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 2837568); C8 s0; C8 ra]).
  { eapply rw_cells_transport; [| exact MUmp| exact WMmp| cbn [disjoint_from cells_size csize]; lia].
    eapply rw_cells_transport; [exact FR2| exact MUR| exact WMR|].
    cbn [cells_size csize]. unfold raligned_W, disjoint_from. unfold aligned_req in *. repeat split; lia. }
  assert (ST3 : stk ctusegs m3 lo (bv_unsigned sp + -48)).
  { eapply stk_transport_disjoint; [| exact MUmp| exact WMmp| cbn [disjoint_from]; lia].
    eapply stk_transport_disjoint; [exact ST2| exact MUR| exact WMR|].
    unfold raligned_W, disjoint_from. unfold aligned_req in *. repeat split; lia. }
  release_frame FR3 ST3 (bv_unsigned sp).
  assert (ERR3 : rw_cells ctusegs m3 3355012 [C4 errv2]).
  { eapply rw_cells_transport; [| exact MUmp| exact WMmp| cbn [disjoint_from cells_size csize]; lia].
    eapply rw_cells_transport; [exact ERR2'| exact MUR| exact WMR|].
    cbn [cells_size csize]. unfold raligned_W, disjoint_from. unfold aligned_req in *. repeat split; lia. }
  assert (AUX3 : rauxv_ok m3 B).
  { eapply rauxv_ok_frame; [| exact MUmp| exact WMmp| constructor; [cbn [fst snd]; unfold RAUXV_CELL; lia| constructor]].
    eapply rauxv_ok_frame; [exact AUX2| exact MUR| exact WMR|].
    unfold raligned_W, RAUXV_CELL. unfold aligned_req in *.
    constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; (split; [lia| destruct RIMG; [left; lia| right; lia]]). }
  (* [comment removed for export] *)
  assert (NOB : forall b, In b LB -> blk_addr b + blk_size b <= S_ - 4 \/ E_ <= blk_addr b).
  { intros b Hb. apply NOBLK; [eapply Permutation_in; [apply Permutation_sym; exact PERM2| right; exact Hb]|].
    intros Eb. pose proof (NoDup_map_perm blk_slot _ _ PERM2 (ci_nodup _ _ C2)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [NI _].
    apply NI. cbn [blk_slot fst]. rewrite <- Eb. apply in_map. exact Hb. }
  assert (HP23 : rheap_pres_but LB (bv_unsigned sp) (mp, mp + 8) m2 m3).
  { intros a Ha CA NX. cbn [fst snd] in NX. split.
    - rewrite (MUmp (wa a)) by (rewrite wa_unsigned by lia; cbn [outside]; split; [lia| exact I]).
      apply MUR. rewrite wa_unsigned by lia.
      destruct CA as [CA|[[CA _]|(b & Hb & Hab)]].
      + apply DJW. left. lia.
      + apply DJW. right. lia.
      + destruct (NOB b Hb); unfold raligned_W, outside; unfold aligned_req in *; repeat split; lia.
    - intros W0. apply WMmp. apply WMR. exact W0. }
  assert (HP03 : rheap_pres_but LB (bv_unsigned sp) (mp, mp + 8) m m3).
  { eapply rheap_pres_but_trans; [apply rheap_pres_but_of_pres; exact HP02| exact HP23]. }
  (* [comment removed for export] *)
  assert (PERM3 : Permutation ((p, A', n) :: lbrm LB2 (p, A, aligned_req al n)) ((p, A', n) :: LB)).
  { apply perm_skip. apply (lbrm_fresh_perm (p, A, aligned_req al n) LB LB2 PERM2 (ci_nodup _ _ C2)). }
  assert (AR3 : AREACH_from ref_reserved st3 ((p, A', n) :: lbrm LB2 (p, A, aligned_req al n))).
  { pose proof (areach_realign st2 LB2 (p, A, aligned_req al n) g2 i2 off adj n AR2 Hin2 SL2 Q20 R32 (proj1 OFFR) AOFF ADJ0 ADJ16 N0 ADJN OFF258) as X.
    exact X. }
  assert (HEAP3R : RHEAP s' ((p, A', n) :: LB) mR).
  { exists st3, ((p, A', n) :: lbrm LB2 (p, A, aligned_req al n)). split; [exact PERM3|].
    split; [subst st3; rewrite strip_realign_at; exact Hst2|]. split; [exact MRR|]. split; [| exact AR3].
    unfold brk_link in *. subst st3. rewrite ctx_realign_at. revert BL2.
    destruct (Malloc.c_brk (ctx st2)) as [| |brid boff]; intros BL2; [exact I| exact I| rewrite conc_realign_at; exact BL2]. }
  assert (HEAP3 : RHEAP s' ((p, A', n) :: LB) m3).
  { eapply RHEAP_frame_proof; [exact HEAP3R| exact MUmp| exact WMmp|]. constructor; [left; cbn; lia| constructor]. }
  (* [comment removed for export] *)
  assert (UCH : exists uj, rw_cells ctusegs m3 A' [CB (Z.to_nat n) uj]).
  { destruct (ruser_chunk st3 mR (fst (fst p), A' - r_base r2) r2 n MRR ltac:(cbn [fst]; subst st3; rewrite regions_realign_at; exact Hr2) Kr2
                ltac:(cbn [snd]; lia) ltac:(cbn [snd]; lia) N0) as [uj U].
    rewrite conc_realign_at, (conc_region' st2 (fst (fst p), A' - r_base r2) r2 Hr2) in U. cbn [snd] in U.
    replace (r_base r2 + (A' - r_base r2)) with A' in U by lia.
    exists uj. eapply rw_cells_transport; [exact U| exact MUmp| exact WMmp| cbn [disjoint_from cells_size csize]; lia]. }
  destruct UCH as [uj UCH].
  assert (CELL : rw_cells ctusegs m3 mp [C8 (Z_to_bv 64 A')]).
  { apply rw_cells_of_bytes; [cbn; tauto| | cbn [cells_size csize]; eapply wr_at_transport; [exact WRmp| exact WMmp]].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. subst m3. apply bytes_at_write_same; [lia| rewrite length_le8; lia]. }
  (* [comment removed for export] *)
  apply evt_done. unfold rposix_memalign_post.
  do 15 eexists. exists m3, errv2.
  split. { try (replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned). reflexivity. }
  split; [exact MI3|]. split; [assumption|]. split; [rewrite ETP; exact ERR3|]. split; [exact AUX3|].
  split; [exact HP03|]. split; [exact EFA|]. split; [exact ESO|].
  exists A', uj.
  split; [reflexivity|]. split; [exact PAL|].
  split. { unfold rblock_range, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL. unfold aligned_req in *.
           split; [lia|]. split.
           { pose proof (Z.div_mod A 16 ltac:(lia)) as D1. rewrite BR16 in D1. pose proof (Z.div_mod adj 16 ltac:(lia)) as D2. rewrite ADJ16 in D2.
             replace A' with ((A / 16 + adj / 16) * 16) by lia. apply Z_mod_mult. }
           split; [lia|]. split; lia. }
  split; [exact HEAP3|]. split; [exact UCH| exact CELL].
Qed.
End ALIGNED.
End WithCeiling0.
