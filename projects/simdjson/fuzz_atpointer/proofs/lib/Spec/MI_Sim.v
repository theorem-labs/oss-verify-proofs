(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import STree Malloc Zej KInv Zdy MI_Inv MI_Kit Zdk Zdp Zdr MI_Ext Zdx
  Zds Zdt Zdw Ze5 Ze6 Zeb Ze7 MI_Cnt MI_TF2 Zec Zed Zee Ze3 Ze4 Ze9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Set Implicit Arguments.

Fixpoint lafter {R} (L : mled) (t : M R) (ans : list Z) {struct t} : mled :=
  match t, ans with
  | SRet _, _ => L
  | SVis (EUndef _) _, _ => L
  | SVis e k, a :: ans' => lafter (event_post L e a) (k a) ans'
  | SVis _ _, [] => L
  end.

Fixpoint followk {R} (t : M R) (ans : list Z) {struct t} : option (R * list Z) :=
  match t, ans with
  | SRet r, _ => Some (r, ans)
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => followk (k a) ans'
  | SVis _ _, [] => None
  end.

Lemma ptree_follow_lafter {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> cpath L t (lafter L t ans) r /\ Post (lafter L t ans) r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ptree follow lafter] in *.
  - inversion Hf; subst. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as [Hp HP]; split; [econstructor; eauto| exact HP]
      | destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

Lemma followk_follow {R} : forall (t : M R) ans x rest, followk t ans = Some (x, rest) -> follow t ans = Some x.
Proof.
  induction t as [r0|e k IH]; intros ans x rest H; cbn [followk follow] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma follow_sbind {R S} : forall (t : M R) (k : R -> M S) ans,
  follow (sbind t k) ans = match followk t ans with Some (x, rest) => follow (k x) rest | None => None end.
Proof.
  induction t as [r0|e k0 IH]; intros k ans; cbn [sbind followk follow]; [reflexivity|].
  destruct e; destruct ans as [|a ans']; cbn [follow]; try reflexivity; apply IH.
Qed.

Lemma lafter_sbind {R S} : forall (t : M R) (k : R -> M S) L ans x rest,
  followk t ans = Some (x, rest) -> lafter L (sbind t k) ans = lafter (lafter L t ans) (k x) rest.
Proof.
  induction t as [r0|e k0 IH]; intros k L ans x rest H; cbn [sbind followk lafter] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; cbn [lafter]; apply IH; exact H.
Qed.

Lemma strel_followk {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans x1 rest, followk t1 ans = Some (x1, rest) ->
  exists x2, followk t2 ans = Some (x2, rest) /\ RR x1 x2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans x1 rest H; cbn [followk] in *.
  - inversion H. subst. eauto.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma strel_lafter {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L ans; cbn [lafter]; [reflexivity|].
  destruct e; destruct ans; try reflexivity; apply IH.
Qed.

Lemma strel_follow_some {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) ans r1 :
  strel RR t1 t2 -> follow t1 ans = Some r1 -> exists r2, follow t2 ans = Some r2 /\ RR r1 r2.
Proof.
  intros H Hf. pose proof (strel_follow H ans) as F. rewrite Hf in F.
  destruct (follow t2 ans) as [r2|]; [exists r2; auto| destruct F].
Qed.

Lemma steq_follow {R} (t1 t2 : M R) ans : steq t1 t2 -> follow t1 ans = follow t2 ans.
Proof.
  intros H. apply strel_eq_steq in H. pose proof (strel_follow H ans) as F.
  destruct (follow t1 ans), (follow t2 ans); cbn in F; try reflexivity; [congruence| destruct F| destruct F].
Qed.

Lemma steq_followk {R} (t1 t2 : M R) : steq t1 t2 -> forall ans, followk t1 ans = followk t2 ans.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros ans; cbn [followk]; [reflexivity|].
  destruct e; destruct ans; try reflexivity; apply IH.
Qed.

Lemma steq_lafter {R} (t1 t2 : M R) : steq t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof. intros H. apply strel_eq_steq in H. apply (strel_lafter H). Qed.

Lemma ptree_followk {R} (t : M R) L Post ans x rest :
  ptree L t Post -> followk t ans = Some (x, rest) -> Post (lafter L t ans) x.
Proof. intros HP Hf. exact (proj2 (ptree_follow_lafter t L Post ans HP (followk_follow _ _ Hf))). Qed.

Lemma event_post_live L e z : ld_live (event_post L e z) = ld_live L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.

Lemma cpath_live {R} L (t : M R) L' r : cpath L t L' r -> ld_live L' = ld_live L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

Unset Implicit Arguments.

Section SIM.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Local Notation PRUN := (prun pans pupd).

Lemma prun_ret {R} o (x : R) : PRUN o (SRet x) = SRet (o, x).
Proof. reflexivity. Qed.

Lemma free_prefix st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  exists m bm i,
    let p := aadd c (UNIT * off) in
    let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
    free_hdr st p = SRet (Some (st1, m, i))
    /\ ctrl_eq st st1 /\ strip st1 = strip st /\ s_slots st !! c = Some (m, i)
    /\ INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS /\ hosts st1 bm m
    /\ 0 <= i <= m_last_idx (MR st1 m) /\ c = (fst bm, sstart (MR st1 m) i)
    /\ tbit (m_avail (MR st1 m)) i = false /\ tbit (m_freed (MR st1 m)) i = false
    /\ (0 <= m_sizeclass (MR st1 m) < 48 \/ m_sizeclass (MR st1 m) = 63)
    /\ free_tail dec_hdr st1 m i = free_tail dec_slots st1 m i.
Proof.
  intros INV Hk.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  exists m, bm, i. cbn zeta.
  set (p := aadd c (UNIT * off)).
  set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
  pose proof (free_hdr_eq st c off n m bm i ai a ar ka BF) as FH. fold p in FH. fold st1 in FH.
  assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
  assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hm. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  assert (STR1 : strip st1 = strip st).
  { destruct CE1 as [C1 C2 C3 C4 C5 C6 C7 C8 C9]. unfold strip. rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9. reflexivity. }
  assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
    - intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
      subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
        intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ;
        pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _]; pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF); pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF);
        pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF); unfold UNIT, IB in *; lia.
    - subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
      change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
      assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ Hm) as (r & Hr & Hkr); exists r; auto).
      assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
    - subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
  assert (Hm1 : hosts st1 bm m). { exists ai. rewrite (ce_groups _ _ CE1). exact Hm. }
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE1)).
  assert (SC : 0 <= m_sizeclass (MR st1 m) < 48 \/ m_sizeclass (MR st1 m) = 63).
  { rewrite MR1. destruct (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hm)) as [[? ?]|[? ?]]; lia. }
  split; [exact FH|]. split; [exact CE1|]. split; [exact STR1|]. split; [exact Hs|]. split; [exact INV1|]. split; [exact Hm1|].
  rewrite !MR1. split; [exact Hi|]. split; [exact Ec|].
  split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [rewrite <- MR1; exact SC|].
  unfold free_tail.
  rewrite (ntf_slots_agree mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i _ (ret st1) INV1 Hm1); [reflexivity| | | | | |].
  - rewrite MR1. exact Hi.
  - cbn. rewrite MR1, Ec. reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold FUEL. lia.
  - unfold FUEL. lia.
Qed.

Theorem INVL_hdr_ok st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL -> hdr_ok pans pupd st (aadd c (UNIT * off)) c.
Proof.
  intros INV Hk. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in FH, AGREE, STR1.
  eexists _, m, i. split; [| split; [exact STR1| split; [exact Hs|]]].
  - intros o. rewrite FH. reflexivity.
  - intros o. rewrite AGREE, <- STR1. apply free_tail_slots_control.
Qed.

Theorem free_leaf_facts st L BL LS c off n o ans o' st' :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  follow (PRUN o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  (forall rid r, s_regions st' !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st' = s_secret st.
Proof.
  intros INV Hk Hf. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in *.
  set (st1 := wr16 (aadd (aadd c (UNIT * off)) (-2)) 0 (wr8 (aadd (aadd c (UNIT * off)) (-3)) 255 st)) in *.
  unfold free in Hf. rewrite FH in Hf. cbn [sbind] in Hf. unfold free_tail in Hf.
  rewrite (guard_true 60) in Hf by (unfold testbit; rewrite Z.lor_spec; fold (MR st1 m); unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
  fold (MR st1 m) in Hf.
  pose proof (ce_regions _ _ CE1) as RG1. pose proof (ce_secret _ _ CE1) as SE1.
  destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))).
  - rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. split; [intros rid r H; rewrite <- RG1; exact H| rewrite <- SE1; reflexivity].
  - destruct (ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
      as (st2 & mi & LS2 & EQ & _ & [RG2 SE2] & _).
    rewrite EQ in Hf.
    assert (K2 : (forall rid r, s_regions st2 !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st2 = s_secret st).
    { split; [intros rid r H; rewrite <- RG1, <- RG2; exact H| rewrite <- SE1, <- SE2; reflexivity]. }
    destruct mi as [[base len]|].
    + destruct (negb (len =? 0)).
      * unfold prun in Hf. rewrite (eruns_vis_keep) in Hf by reflexivity. destruct ans as [|a ans']; [cbn [follow] in Hf; discriminate Hf|]. cbn [follow] in Hf.
        destruct (munmap_answer_ok a).
        -- change (eruns (psel pans) pupd (pupd o (EMunmap (conc st2 base) len) a) (ret (drop_region (fst base) st2))) with
             (PRUN (pupd o (EMunmap (conc st2 base) len) a) (SRet (drop_region (fst base) st2))) in Hf.
           rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'.
           split; [| exact (proj2 K2)]. intros rid r H. unfold drop_region in H. cbn in H.
           destruct (N.eq_dec rid (fst base)) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate H|]. rewrite lookup_delete_ne in H by congruence. apply (proj1 K2). exact H.
        -- unfold bad_answer in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate Hf.
      * rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
    + rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
Qed.

Theorem free_sim st L BL LS c off n o ans o' st' :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  follow (PRUN o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  let t := cfree (strip st) (Some c) in
  let L' := lafter L t ans in
  follow t ans = Some (strip st') /\ cpath L t L' (strip st') /\ ld_live L' = ld_live L
  /\ exists LS', INVL x0 st' L' (bl_remove c BL) LS'.
Proof.
  intros INV Hk Hf. cbn zeta.
  pose proof (free_control pans pupd st (aadd c (UNIT * off)) c o (INVL_hdr_ok st L BL LS c off n INV Hk)) as REL.
  pose proof (ftree_prun pans pupd Hpans (free st (Some (aadd c (UNIT * off)))) L _ o (free_INVL_closed st L BL LS c off n INV Hk)) as PT.
  destruct (strel_follow_some ans REL Hf) as (cs' & Hf2 & FR). unfold FREL in FR. cbn in FR. subst cs'.
  split; [exact Hf2|].
  pose proof (ptree_strel REL L _ (fun _ _ => True) ltac:(intros; exact I) PT) as PT2.
  destruct (ptree_follow_lafter _ L _ ans PT2 Hf2) as [CP _].
  split; [exact CP|]. split; [exact (cpath_live CP)|].
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ POST]. cbn in POST.
  rewrite <- (strel_lafter REL L ans). exact POST.
Qed.

Theorem malloc_sim st L BL LS n o ans o' st' r :
  INVL x0 st L BL LS -> 0 <= n ->
  follow (PRUN o (malloc st n)) ans = Some (o', (st', r)) ->
  let t := cmalloc (strip st) n in
  let L' := lafter L t ans in
  exists rc, follow t ans = Some (strip st', rc) /\ cpath L t L' (strip st', rc) /\ ld_live L' = ld_live L /\ GP st st' /\
    match r, rc with
    | None, None => exists LS', INVL x0 st' L' BL LS'
    | Some pf, Some c => exists off LS', pf = aadd c (UNIT * off) /\ 0 <= off <= 255
                         /\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
    | _, _ => False
    end.
Proof.
  intros INV Hn Hf. cbn zeta.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  set (K := fun x : mstate * option (aptr * Z) => let '(st1, r) := x in
        match r with
        | None => ret (st1, @None aptr)
        | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
        end).
  assert (E1 : steq (PRUN o (malloc st n)) (sbind (PRUN o (malloc_core full_lay st0 n)) (fun x => PRUN (fst x) (K (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (PRUN o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].

  pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  set (L1 := lafter L (PRUN o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & CP).

  pose proof (malloc_core_ctrl pans pupd n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.

  assert (PT2 : ptree L (cmalloc (strip st) n) (fun _ _ => True)).
  { eapply (ptree_strel (malloc_control pans pupd Hpans st n o)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans pupd Hpans (malloc st n) L _ o (malloc_INVL st L BL LS n INV Hn)). }
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.

    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, 0 <= off <= 255 /\ snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ GP st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [exact Ho|]; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9; reflexivity| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]])).
    pose proof (ftree_prun pans pupd Hpans _ L1 _ o1 EF) as PTE.
    cbn [K fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Ho & Er & INV2 & SS2 & GP2)]. cbn [fst snd] in Er, INV2, SS2, GP2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; rewrite SS2; exact C|].
    split; [exact LIVE1|]. split; [exact (GP_trans _ _ _ GP0 GP2)|].
    exists off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV2|].
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV2))))))) as ND. cbn [map bslot fst] in ND.
    apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
  - destruct CP as (LS1 & INV1). cbn [K fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity|].
    split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; exact C|].
    split; [exact LIVE1|]. split; [exact GP0|]. exists LS1. exact INV1.
Qed.
End SIM.
