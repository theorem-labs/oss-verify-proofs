(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim Monad MSafe MSafeP MPaths STree Malloc MallocCtrl KInv KStep PState KLink KEv KEvP StepB
  MI_NN MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow MI_WFree MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WTry2 MI_WSlot MI_WSlot2 MI_WEnframe MI_WEnframe2 MI_WMalloc MI_Sim MI_Contracts PTotal
  FreshIface ProgC MF_Defs MF_Inv MF_WMalloc MF_Model MF_WFree RSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma map_bslot (X : list (bptr * Z)) : map bslot X = map fst (map fst X).
Proof. rewrite map_map. reflexivity. Qed.

Lemma FF_reoff c off off' n X k st : FF (((c, off), n) :: X) k st -> FF (((c, off'), n) :: X) k st.
Proof.
  intros [G B]. split; [| exact B]. intros b m ai Hb. destruct (G _ _ _ Hb) as [N30 K]. split; [exact N30|].
  intros HK. destruct (K HK) as [L (xb & Hin & E & R)]. split; [exact L|].
  destruct Hin as [<-|Hin]; [exists ((c, off'), n); cbn in *; auto| exists xb; auto using in_cons].
Qed.

Lemma KREQ_KC30 n : KREQ n -> n < MMAP_THRESHOLD /\ KC30 (size_to_class n).
Proof.
  unfold KREQ, KC30, KCLS. intros [->|[->|[->| ->]]];
    [replace (size_to_class 5968) with 30 by (vm_compute; reflexivity)| replace (size_to_class 65536) with 44 by (vm_compute; reflexivity)
    | replace (size_to_class 7176) with 31 by (vm_compute; reflexivity)| replace (size_to_class 32768) with 40 by (vm_compute; reflexivity)];
    (split; [unfold MMAP_THRESHOLD; lia| lia]).
Qed.


Lemma malloc_simF st L BL LS n (X : list blk) k (o : unit) ans o' st' r :
  INVL x0 st L BL LS -> 0 <= n -> FF X k st ->
  (forall xb, In xb X -> In (bslot xb) (map bslot BL)) -> List.NoDup (map bslot X) -> FPRE X k n ->
  follow (prun pans0 pupd0 o (malloc st n)) ans = Some (o', (st', r)) ->
  exists rc, follow (cmalloc (strip st) n) ans = Some (strip st', rc) /\
    match r, rc with
    | None, None => True
    | Some pf, Some c => (forall off, FF (((c, off), n) :: X) (k + 1) st')
                         /\ (n < MMAP_THRESHOLD -> KC30 (size_to_class n) -> s_regions st !! (fst c) = None /\ gonly0 st' (fst c))
    | _, _ => False
    end.
Proof.
  intros INV Hn HF HX HND HP Hf.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (HF0 : FF X k st0) by (apply (FF_ctrl X k st st0); [constructor; reflexivity| exact HF]).
  set (K := fun x : mstate * option (aptr * Z) => let '(st1, r) := x in
        match r with
        | None => ret (st1, @None aptr)
        | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
        end).
  assert (E1 : steq (prun pans0 pupd0 o (malloc st n)) (sbind (prun pans0 pupd0 o (malloc_core full_lay st0 n)) (fun x => prun pans0 pupd0 (fst x) (K (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (malloc_core_ftF st0 L BL LS n INV0 TF0' Hn)) as PTQ.
  pose proof (ptree_followk _ L _ ans PTQ FK) as CQ. unfold CORE_POSTF in CQ. cbn [snd fst] in CQ.
  set (L1 := lafter L (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & CP). destruct CQ as (_ & MFs & MFb & CQ).
  pose proof (malloc_core_ctrl pans0 pupd0 n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32 & _).
    destruct CQ as (LS1' & bg' & Hg' & Hidx' & INV1' & _ & _ & _ & KX).
    pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ _ Hg' Hg) as ->.
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    destruct (core_FF st0 L BL LS n X k INV0 Hn HF0 HX HND HP st1 L1 LS1 g bg idx 0 MFs MFb Hg Hidx INV1 KX) as [FF1 FR1].
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, snd res = Some (aadd c0 (UNIT * off)) /\ strip (fst res) = strip st1 /\ ctrl_eq st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [reflexivity|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9, C10; reflexivity| exact CE])).
    pose proof (ftree_prun pans0 pupd0 pans0_range _ L1 _ o1 EF) as PTE.
    cbn [K fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Er & SS2 & CE2)]. cbn [fst snd] in Er, SS2, CE2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    split.
    + intros off'. apply (FF_reoff c0 0). apply (FF_ctrl _ _ st1 st' CE2). exact FF1.
    + intros Hlt HK. destruct (FR1 Hlt HK) as (_ & R & _ & O). split; [exact R|]. apply (gonly0_same st1); [exact (ce_groups _ _ CE2)| exact O].
  - destruct CP as (LS1 & INV1). cbn [K fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity| exact I].
Qed.


Section RAW.
Local Notation bptrs := (fun X : list (bptr * Z) => map fst X).
Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Theorem raw_malloc_specF (X : list (bptr * Z)) G n k s0 : frame_ok G -> 0 <= n -> FPRE X k n ->
  mspec (fun s mo => s = s0 /\ OWN (bptrs X) G s mo /\ FF X k (ps_m s)) (raw_malloc n)
        (fun r s mo => match r with
                       | Some p => OWN (p :: bptrs X) G s mo /\ FF ((p, n) :: X) (k + 1) (ps_m s) /\ n < 2^63
                                   /\ (n < MMAP_THRESHOLD -> KC30 (size_to_class n) -> fresh_top s0 s p)
                       | None => OWN (bptrs X) G s mo
                       end).
Proof.
  intros HG Hn HP. unfold raw_malloc.
  eapply mspec_bind; [apply mspec_get|]. intros s0'.
  apply mspec_pointwise. intros s1 mo1 (-> & -> & [(L & Hc & HK & Hi) [Hnd HGs]] & HF).
  destruct (creach_sim _ _ Hc) as (st & BL & LS & Est & INV & LIVE).
  assert (HFst : FF X k st) by (rewrite <- FF_strip, Est; exact HF).
  assert (HX : forall xb, In xb X -> In (bslot xb) (map bslot BL)).
  { intros xb Hxb. rewrite <- LIVE. apply Hi. rewrite <- map_bslot. apply in_map. exact Hxb. }
  assert (HND : List.NoDup (map bslot X)) by (rewrite map_bslot; exact Hnd).
  eapply mspec_bind.
  { rewrite (MI_Contracts.creach_atop _ _ Hc).
    eapply mspec_pre; [apply (membed_spec (cmalloc (ps_m s0) n) _ G L s0 HG (MI_Contracts.cmalloc_contract_proof _ _ _ Hc Hn))|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso).
  pose proof (KEv.cpath_live _ _ _ _ Hp) as Hlive. cbn [snd] in HPost.
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  assert (Hcr : creach st' (match p with Some c => set_live (c :: ld_live L') L' | None => L' end)).
  { exact (creach_malloc _ _ _ _ _ _ Hc Hn Hp). }
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  destruct (cpath_follow _ _ _ _ Hp) as (ans & Hf & HL2). rewrite <- Est in Hf.
  pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [stf rf]]|] eqn:FF'; [| destruct SF].
  destruct (malloc_simF st L BL LS n X k tt ans o' stf rf INV Hn HFst HX HND HP FF') as (rc & Hf2 & RES).
  rewrite Hf in Hf2. assert (Est' : st' = strip stf) by congruence. assert (Erc : p = rc) by congruence. subst rc.
  destruct p as [c|].
  - destruct rf as [pf|]; [| exfalso; exact RES]. destruct RES as [FFs FR].
    split; [| split; [| split]].
    + split; [|split; [|exact HG2]].
      * exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
        cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
      * cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
    + cbn [ps_m set_m map fst]. rewrite Est', <- FF_strip. apply FFs.
    + destruct (size_overflows n) eqn:E.
      * exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
      * unfold size_overflows in E. apply Z.leb_gt in E. lia.
    + intros Hlt HKc. destruct (FR Hlt HKc) as [R [O1 O2]]. unfold fresh_top, brid. cbn [ps_m set_m fst].
      rewrite <- Est, Est'. change (s_regions (strip st)) with (s_regions st). change (s_groups (strip stf)) with (s_groups stf).
      split; [exact R|]. split; [exact O1|]. apply map_Forall_lookup. intros b h Hb E. exact (O2 b h Hb E).
  - split; [|split; [exact Hnd| exact HG2]].
    exists L'. split; [exact Hcr|]. split; [exact HK'|]. rewrite Hlive. exact Hi.
Qed.

Theorem raw_malloc_specFP (X : list (bptr * Z)) G n k s0 : frame_ok G -> 0 <= n <= 2^62 -> FPRE X k n ->
  mspecP (fun s mo => s = s0 /\ (OWN (bptrs X) G s mo /\ FF X k (ps_m s))) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => (OWN (p :: bptrs X) G s mo /\ FF ((p, n) :: X) (k + 1) (ps_m s)) /\ n < 2^63 /\ (KREQ n -> fresh_topb s0 s p = true)
                        | None => False
                        end).
Proof.
  intros HG Hn HP.
  assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; lia).
  eapply mspecP_post.
  - apply mspecP_conj.
    + eapply mspecP_pre; [apply (raw_malloc_specP (bptrs X) G n HG ltac:(lia) Hov)|]. intros s mo (_ & HO & _). exact HO.
    + apply mspec_mspecP. eapply mspec_pre; [apply (raw_malloc_specF X G n k s0 HG ltac:(lia) HP)|]. intros s mo (E & HO & HF). auto.
  - cbv beta. intros [p|] s mo [A B]; [| exact A]. destruct B as (HO & HF & Hn63 & FR).
    split; [split; [exact HO| exact HF]|]. split; [exact Hn63|].
    intros HK. apply fresh_topb_true. destruct (KREQ_KC30 n HK) as [Hlt HKc]. exact (FR Hlt HKc).
Qed.

Theorem raw_malloc_stotF (X : list (bptr * Z)) G n k s mo : frame_ok G -> OWN (bptrs X) G s mo -> FF X k (ps_m s) ->
  0 <= n -> size_overflows n = false -> FPRE X k n -> tglob nstep PhiP (raw_malloc n s) mo ->
  STOTP (raw_malloc n s) mo
        (fun r s' mo' => exists p, r = Some p /\ OWN (p :: bptrs X) G s' mo' /\ FF ((p, n) :: X) (k + 1) (ps_m s') /\ n < 2^63
                         /\ (KREQ n -> fresh_topb s s' p = true)
                         /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros HG HO HF Hn Hov HP HT.
  destruct (raw_malloc_STOT (bptrs X) G n s mo HG HO Hn Hov HT) as (S1 & S2 & S3).
  pose proof (raw_malloc_specF X G n k s HG Hn HP s mo (conj eq_refl (conj HO HF))) as W.
  split; [| split; [exact S2| exact S3]].
  intros tr r mo' Hp. destruct (S1 tr r mo' Hp) as (Etr & a & s' & Er & (p & Ea & HO' & Hn63 & Hso & Hfa & Hfds & Hfs)).
  pose proof (twf_tpath _ _ _ _ _ _ W Hp) as HQ. subst r a. cbn [fst snd] in HQ.
  destruct HQ as (_ & HF' & _ & FR).
  split; [exact Etr|]. exists (Some p), s'. split; [reflexivity|]. exists p. split; [reflexivity|]. split; [exact HO'|]. split; [exact HF'|]. split; [exact Hn63|].
  split; [intros HK; apply fresh_topb_true; destruct (KREQ_KC30 n HK) as [Hlt HKc]; exact (FR Hlt HKc)|]. auto.
Qed.


Theorem raw_free_specF (X : list (bptr * Z)) G p n k : frame_ok G ->
  mspec (fun s mo => OWN (p :: bptrs X) G s mo /\ FF ((p, n) :: X) k (ps_m s)) (raw_free p)
        (fun _ s mo => OWN (bptrs X) G s mo /\ FF X k (ps_m s)).
Proof.
  intros HG. unfold raw_free.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 (-> & [(L & Hc & HK & Hi) [Hnd HGs]] & HF).
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  destruct (creach_sim _ _ Hc) as (st & BL & LS & Est & INV & LIVE).
  assert (HFst : FF ((p, n) :: X) k st) by (rewrite <- FF_strip, Est; exact HF).
  rewrite LIVE in Hin. destruct (In_bslot _ _ Hin) as (off & n' & Hk).
  eapply mspec_bind.
  { rewrite (MI_Contracts.creach_atop _ _ Hc).
    eapply mspec_pre; [apply (membed_spec (cfree (ps_m s1) (Some (fst p))) _ G L s1 HG (MI_Contracts.cfree_contract_proof _ _ _ Hc ltac:(rewrite LIVE; exact Hin)))|].
    intros s mo [-> ->]. auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & _ & HK' & HG' & Hm & Hfa & Hso).
  pose proof (KEv.cpath_live _ _ _ _ Hp) as Hlive.
  apply mspec_upd'. intros s mo [-> ->].
  assert (Hcr : creach st' (set_live (ap_remove (fst p) (ld_live L')) L')).
  { exact (creach_free _ _ _ _ _ Hc ltac:(rewrite LIVE; exact Hin) Hp). }
  split.
  { split; [|split; [inversion Hnd; assumption| apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']]].
    exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
    cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
    - apply Hi. right. exact Hx.
    - inversion Hnd; subst. intros ->. apply H1. exact Hx. }
  destruct (cpath_follow _ _ _ _ Hp) as (ans & Hf & HL2). rewrite <- Est in Hf.
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd (fst p) (UNIT * off)) (fst p) tt (INVL_hdr_ok pans0 pupd0 st L BL LS (fst p) off n' INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd (fst p) (UNIT * off))))) ans) as [[o' stf]|] eqn:FF'; [| destruct SF].
  unfold FREL in SF. cbn in SF.
  pose proof (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_FF st L BL LS (fst p) off n' X k (p, n) INV Hk HFst eq_refl)) as PT.
  destruct (ptree_follow_lafter _ L _ ans PT FF') as [_ HF']. cbn [snd] in HF'.
  cbn [ps_m set_m]. rewrite <- SF, FF_strip. exact HF'.
Qed.

Theorem raw_free_specFP (X : list (bptr * Z)) G p n k : frame_ok G ->
  mspecP (fun s mo => OWN (p :: bptrs X) G s mo /\ FF ((p, n) :: X) k (ps_m s)) (raw_free p) (fun _ s mo => OWN (bptrs X) G s mo /\ FF X k (ps_m s)).
Proof. intros HG. apply mspec_mspecP. apply raw_free_specF. exact HG. Qed.

Theorem raw_free_stotF (X : list (bptr * Z)) G p n k s mo : frame_ok G -> OWN (p :: bptrs X) G s mo -> FF ((p, n) :: X) k (ps_m s) ->
  tglob nstep PhiP (raw_free p s) mo ->
  STOTP (raw_free p s) mo
        (fun _ s' mo' => OWN (bptrs X) G s' mo' /\ FF X k (ps_m s') /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros HG HO HF HT.
  destruct (raw_free_STOT (bptrs X) G p s mo HG HO HT) as (S1 & S2 & S3).
  pose proof (raw_free_specF X G p n k HG s mo (conj HO HF)) as W.
  split; [| split; [exact S2| exact S3]].
  intros tr r mo' Hp. destruct (S1 tr r mo' Hp) as (Etr & a & s' & Er & (HO' & Hso & Hfa & Hfds & Hfs)).
  pose proof (twf_tpath _ _ _ _ _ _ W Hp) as HQ. subst r. cbn [fst snd] in HQ. destruct HQ as [_ HF'].
  split; [exact Etr|]. exists a, s'. split; [reflexivity|]. split; [exact HO'|]. split; [exact HF'|]. auto.
Qed.
End RAW.
