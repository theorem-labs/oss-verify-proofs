(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wk_yields : forall segs FORB HTOP {fx : FPState} rom {R : Type} (t : itree astate R) L regs pc m (Q : @wpost R),
  wk segs FORB HTOP rom L regs pc m t Q ->
  wk segs FORB HTOP rom L regs pc m t (fun L' r regs' pc' m' => Q L' r regs' pc' m' /\ exists tr, yields t tr r).
Proof.
  intros segs FORB HTOP fx rom R t. induction t as [r | q s k IH | f]; intros L regs pc m Q H; cbn in *.
  - destruct H as (regs' & pc' & m' & Hm & Hq). exists regs', pc', m'. split; [exact Hm|]. split; [exact Hq|].
    exists []. reflexivity.
  - destruct q as [| n | | len | len | p | r len | b].
    1-7: (destruct H as (regs1 & pc1 & m1 & Hm & He & Hk); exists regs1, pc1, m1; split; [exact Hm|]; split; [exact He|];
           intros eff ans L' Ho; eapply wk_mono; [| apply (IH ans); apply Hk; exact Ho];
           intros L2 r' regs2 pc2 m2 (Hq & tr & Hy); split; [exact Hq|]; refine (ex_intro _ ((_, ans) :: tr) _); cbn [yields]; split; [reflexivity|];
           split; [exact I | exact Hy]).
    destruct H as (z & Hz & Hr). exists z. split; [exact Hz|]. eapply wk_mono; [| apply (IH z); exact Hr].
    intros L2 r regs2 pc2 m2 (Hq & tr & Hy). split; [exact Hq|]. exists ((KJunk b, z) :: tr). cbn. split; [reflexivity|].
    split; [exact Hz | exact Hy].
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma wk_itok : forall segs FORB HTOP {fx : FPState} rom {R : Type} (t : itree astate R) L regs pc m (Q : @wpost R) (QM : R -> Prop),
  wk segs FORB HTOP rom L regs pc m t Q -> itok t QM ->
  wk segs FORB HTOP rom L regs pc m t (fun L' r regs' pc' m' => Q L' r regs' pc' m' /\ QM r).
Proof.
  intros segs FORB HTOP fx rom R t. induction t as [r | q s k IH | f]; intros L regs pc m Q QM H HT; cbn in *.
  - destruct H as (regs' & pc' & m' & Hm & Hq). exists regs', pc', m'. split; [exact Hm|]. split; [exact Hq | exact HT].
  - destruct HT as (_ & HT). destruct q as [| n | | len | len | p | r len | b].
    1-7: (destruct H as (regs1 & pc1 & m1 & Hm & He & Hk); exists regs1, pc1, m1; split; [exact Hm|]; split; [exact He|];
           intros eff ans L' Ho; apply (IH ans); [apply Hk; exact Ho | apply HT; exact I]).
    destruct H as (z & Hz & Hr). exists z. split; [exact Hz|]. apply (IH z); [exact Hr | apply HT; exact Hz].
  - exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rgeoA (HTOP : Z) (L : layout) (s : astate) : Prop :=
  forall r rg, region_of s r = Some rg -> rg_live rg = true ->
    PGSZ <= ly_reg L r /\ ly_reg L r mod PGSZ = 0 /\ ly_reg L r + rg_len rg <= HTOP /\
    ranges_disjoint (ly_reg L r, rg_len rg) (0x10000, 0x87000).

Lemma rgeo_of_A : forall HTOP L s, rgeoA HTOP L s -> rgeo HTOP L s.
Proof. intros HTOP L s H r rg Hr Hl. destruct (H r rg Hr Hl) as (A & _ & C & D). split; [exact A|]. split; [exact C | exact D]. Qed.

(* [comment removed for export] *)
Definition rdisj (L : layout) (s : astate) : Prop :=
  forall r1 r2 rg1 rg2, r1 <> r2 -> region_of s r1 = Some rg1 -> region_of s r2 = Some rg2 -> rg_live rg1 = true -> rg_live rg2 = true ->
    ranges_disjoint (ly_reg L r1, rg_len rg1) (ly_reg L r2, rg_len rg2).

Lemma lext_refl : forall L s, lext L L s.
Proof. intros L s. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros r _. reflexivity. Qed.

Lemma lext_set_new : forall L s a, lext L (set_reg_addr L (length (st_regions s)) a) s.
Proof.
  intros L s a. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros r Hr. unfold set_reg_addr. cbn [ly_reg].
  destruct (Nat.eqb r (length (st_regions s))) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
Qed.

Lemma lext_trans : forall L1 L2 L3 s1 s2, lext L1 L2 s1 -> lext L2 L3 s2 -> (length (st_regions s1) <= length (st_regions s2))%nat ->
  lext L1 L3 s1.
Proof.
  intros L1 L2 L3 s1 s2 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2) Hl. split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite D2 by lia. exact (D1 r Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_after_zu : forall m r zs us (x : word),
  mem_after m (mkEffectU r [] zs us [] []) x = if zeros_cover zs x then Some (Z_to_bv 8 0) else if zeros_cover us x then None else m x.
Proof.
  intros m r zs us x. unfold mem_after. cbn [eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold apply_zeros, apply_unmaps. destruct zs as [|z zs']; destruct us as [|u us']; reflexivity.
Qed.

Lemma zeros_cover1 : forall a n x, 0 <= a < 2^64 -> 0 <= n < 2^64 -> 0 <= x < 2^64 ->
  zeros_cover [(w64 a, w64 n)] (wa x) = ((a <=? x) && (x <? a + n)).
Proof.
  intros a n x Ha Hn Hx. unfold zeros_cover. cbn [existsb fst snd]. unfold w64. rewrite !u_wa_small by lia.
  rewrite Bool.orb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mem_after_zero : forall m r a n x, 0 <= a < 2^64 -> 0 <= n < 2^64 -> 0 <= x < 2^64 ->
  mem_after m (mkEffect r [] [(w64 a, w64 n)]) (wa x) = if (a <=? x) && (x <? a + n) then Some (Z_to_bv 8 0) else m (wa x).
Proof.
  intros m r a n x Ha Hn Hx. rewrite mem_after_zu, zeros_cover1 by assumption. unfold zeros_cover. cbn [existsb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mem_after_unmap : forall m r a n x, 0 <= a < 2^64 -> 0 <= n < 2^64 -> 0 <= x < 2^64 ->
  mem_after m (mkEffectU r [] [] [(w64 a, w64 n)] [] []) (wa x) = if (a <=? x) && (x <? a + n) then None else m (wa x).
Proof.
  intros m r a n x Ha Hn Hx. rewrite mem_after_zu, zeros_cover1 by assumption. unfold zeros_cover. cbn [existsb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mem_after_none : forall m r x, mem_after m (mkEffect r [] []) x = m x.
Proof. intros m r x. rewrite mem_after_zu. reflexivity. Qed.

Lemma mem_after_out : forall m eff x, eff_writes eff = [] -> eff_copies eff = [] ->
  zeros_cover (eff_zeros eff) x = false -> zeros_cover (eff_unmaps eff) x = false -> mem_after m eff x = m x.
Proof.
  intros m [r ws zs us cs ci] x Hw Hc Hz Hu. cbn [eff_writes eff_copies eff_zeros eff_unmaps] in *. subst ws cs.
  unfold mem_after. cbn [eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold apply_zeros, apply_unmaps. destruct zs as [|z zs']; destruct us as [|u us']; try reflexivity.
  - rewrite Hu. reflexivity.
  - rewrite Hz. reflexivity.
  - rewrite Hz, Hu. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma footprint_inv : forall s rg, In rg (footprint s) ->
  rg = (LCtx 0, CTX_SIZE) \/ (exists a, In a (st_areas s) /\ rg = (LMem a, PGSZ)) \/
  (exists k rgk, region_of s k = Some rgk /\ rg_kind rgk = RkMap /\ rg_live rgk = true /\ rg = (LMem (SP k 0), rg_len rgk)).
Proof.
  intros s rg H. unfold footprint in H. destruct H as [<-|H]; [left; reflexivity|]. right.
  apply in_app_iff in H as [H|H].
  - left. apply in_map_iff in H as (a & <- & Ha). exists a. split; [exact Ha | reflexivity].
  - right. apply in_flat_map in H as (k & _ & H). destruct (region_of s k) as [rgk|] eqn:E; [|destruct H].
    destruct (rg_kind rgk) eqn:K; try destruct H. destruct (rg_live rgk) eqn:Lv; [|destruct H]. destruct H as [<-|[]].
    exists k, rgk. auto.
Qed.

Lemma pairwise_of_nodup : forall {A} (R : A -> A -> Prop) (l : list A), List.NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> R x y) -> pairwise R l.
Proof.
  intros A R l. induction l as [|x t IH]; intros ND H; cbn; [exact I|]. inversion ND as [|x' t' Hx Ht]; subst.
  split; [intros y Hy; apply H; [left; reflexivity | right; exact Hy | intros <-; exact (Hx Hy)]|].
  apply IH; [exact Ht|]. intros a b Ha Hb Hne. apply H; [right; exact Ha | right; exact Hb | exact Hne].
Qed.

Lemma NoDup_map_inj : forall {A B} (f : A -> B) l, List.NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup (map f l).
Proof.
  intros A B f l. induction l as [|x t IH]; intros ND H; cbn; [constructor|]. inversion ND as [|x' t' Hx Ht]; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Ey & Hy). apply Hx. rewrite (H x y (or_introl eq_refl) (or_intror Hy) (eq_sym Ey)). exact Hy.
  - apply IH; [exact Ht|]. intros a b Ha Hb E. apply H; [right; exact Ha | right; exact Hb | exact E].
Qed.

Lemma footprint_NoDup : forall X R U s, Inv X R U s -> List.NoDup (footprint s).
Proof.
  intros X R U s HI. pose proof (inv_areas HI) as (AND & A2 & _).
  unfold footprint. constructor.
  - intros H. apply in_app_iff in H as [H|H].
    + apply in_map_iff in H as (a & E & _). discriminate E.
    + apply in_flat_map in H as (k & _ & H). destruct (region_of s k) as [rgk|]; [|destruct H].
      destruct (rg_kind rgk); try destruct H. destruct (rg_live rgk); [|destruct H]. destruct H as [E|[]]. discriminate E.
  - apply NoDup_app.
    + apply NoDup_map_inj; [exact AND|]. intros x y _ _ E. injection E as E. exact E.
    + assert (G : forall l, List.NoDup l -> List.NoDup (flat_map (fun k => match region_of s k with
                        | Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else [] | _ => [] end
                        | None => [] end) l)).
      { intros l. induction l as [|k t IH]; intros ND; cbn [flat_map]; [constructor|]. inversion ND as [|k' t' Hk Ht]; subst.
        apply NoDup_app; [| exact (IH Ht) |].
        - destruct (region_of s k) as [rgk|]; [|constructor]. destruct (rg_kind rgk); try constructor.
          destruct (rg_live rgk); [|constructor]. constructor; [intros []|constructor].
        - intros y Hy Hy'. destruct (region_of s k) as [rgk|]; [|destruct Hy]. destruct (rg_kind rgk); try destruct Hy.
          destruct (rg_live rgk); [|destruct Hy]. destruct Hy as [<-|[]].
          apply in_flat_map in Hy' as (k2 & Hk2 & H2). destruct (region_of s k2) as [rg2|]; [|destruct H2].
          destruct (rg_kind rg2); try destruct H2. destruct (rg_live rg2); [|destruct H2]. destruct H2 as [E|[]].
          injection E as E _. subst k2. exact (Hk Hk2). }
      apply G. apply seq_NoDup.
    + intros y Hy Hy'. apply in_map_iff in Hy as (a & <- & Ha). destruct (A2 a Ha) as (r & o & rga & -> & _ & Ho & _).
      apply in_flat_map in Hy' as (k & _ & H). destruct (region_of s k) as [rgk|]; [|destruct H].
      destruct (rg_kind rgk); try destruct H. destruct (rg_live rgk); [|destruct H]. destruct H as [E|[]].
      injection E as _ Eo _. unfold PGSZ in Ho. lia.
Qed.

Section GEO.
Variable HTOP : Z.
Hypothesis HTOPB : HTOP <= 2^47.

#[using="Type"] Lemma area_range : forall X R U s L a, Inv X R U s -> rgeoA HTOP L s -> In a (st_areas s) ->
  exists r rg, prid a = r /\ region_of s r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\
    ly_reg L r <= loc_addr L (LMem a) /\ loc_addr L (LMem a) + PGSZ <= ly_reg L r + rg_len rg /\
    PGSZ <= poff a /\ poff a mod PGSZ = 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X R U s L a HI HG Ha. pose proof (inv_areas HI) as (_ & A2 & _).
  destruct (A2 a Ha) as (r & o & rga & -> & Hom & Ho & Hr & Hl & Hlen & Hk).
  exists r, rga. split; [reflexivity|]. split; [exact Hr|]. split; [exact Hl|]. split; [destruct (rg_kind rga); [discriminate | discriminate | exact (False_ind _ Hk)]|].
  cbn [loc_addr prid poff]. split; [unfold PGSZ in *; lia|]. split; [unfold PGSZ in *; lia|]. split; [exact Ho | exact Hom].
Qed.

#[using="HTOPB"] Theorem layout_of_geo : forall X R U s L, Inv X R U s -> ly_ctx L = 0x95ed8 -> rgeoA HTOP L s -> rdisj L s -> layout_ok L s.
Proof. LiaFast.lf_pins (fun (HTOPB : LiaFast.U) => LiaFast.u0).
  intros X R U s L HI Hctx HG HD. split; [rewrite Hctx; reflexivity|]. split; [intros k rg Hk Hl; exact (proj1 (proj2 (HG k rg Hk Hl)))|].
  split.
  - apply (proj1 (MallocWfRepr.pairwise_map_iff ranges_disjoint (crange L) (footprint s))).
    apply pairwise_of_nodup; [exact (footprint_NoDup X R U s HI)|].
    assert (CTXD : forall rg, In rg (footprint s) -> rg <> (LCtx 0, CTX_SIZE) -> ranges_disjoint (crange L (LCtx 0, CTX_SIZE)) (crange L rg)).
    { intros rg Hin Hne. destruct (footprint_inv s rg Hin) as [E | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]]; [exact (False_ind _ (Hne E))| |].
      - destruct (area_range X R U s L a HI HG Ha) as (r & rg & _ & Hr & Hl & _ & B1 & B2 & _).
        destruct (HG r rg Hr Hl) as (G1 & _ & G3 & G4). unfold crange, ranges_disjoint in *. cbn [fst snd loc_addr] in *. rewrite Hctx.
        unfold CTX_SIZE, PGSZ in *. lia.
      - destruct (HG k rgk Hk Lk) as (G1 & _ & G3 & G4). unfold crange, ranges_disjoint in *. cbn [fst snd loc_addr] in *. rewrite Hctx.
        unfold CTX_SIZE, PGSZ in *. lia. }
    intros x y Hx Hy Hne.
    destruct (footprint_inv s x Hx) as [Ex | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
    + subst x. apply CTXD; [exact Hy | intros E; exact (Hne (eq_sym E))].
    + destruct (footprint_inv s y Hy) as [Ey | [(b & Hb & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
      * subst y. apply ranges_disjoint_sym. apply CTXD; [exact Hx | exact Hne].
      * assert (Hab : a <> b) by (intros ->; exact (Hne eq_refl)).
        destruct (area_range X R U s L a HI HG Ha) as (r1 & rg1 & Ep1 & Hr1 & Hl1 & _ & A1 & A2' & A3 & A4).
        destruct (area_range X R U s L b HI HG Hb) as (r2 & rg2 & Ep2 & Hr2 & Hl2 & _ & B1 & B2 & B3 & B4).
        unfold crange, ranges_disjoint. cbn [fst snd].
        destruct (Nat.eq_dec r1 r2) as [Er|Er].
        -- subst r2. destruct a as [ra oa]; destruct b as [rb ob]. cbn [prid poff loc_addr] in *. subst ra rb.
           assert (Hoab : oa <> ob) by (intros ->; exact (Hab eq_refl)).
           apply Z.mod_divide in A4; [|unfold PGSZ; lia]. apply Z.mod_divide in B4; [|unfold PGSZ; lia].
           destruct A4 as (ka & Ea). destruct B4 as (kb & Eb). subst oa ob.
           assert (ka <> kb) by (intros ->; exact (Hoab eq_refl)). unfold PGSZ in *. nia.
        -- pose proof (HD r1 r2 rg1 rg2 Er Hr1 Hr2 Hl1 Hl2) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
      * destruct (area_range X R U s L a HI HG Ha) as (r1 & rg1 & Ep1 & Hr1 & Hl1 & K1 & A1 & A2' & A3 & A4).
        assert (Er : r1 <> k) by (intros ->; rewrite Hk in Hr1; injection Hr1 as <-; exact (K1 Kk)).
        pose proof (HD r1 k rg1 rgk Er Hr1 Hk Hl1 Lk) as D. unfold crange, ranges_disjoint in *. cbn [fst snd loc_addr] in *. lia.
    + destruct (footprint_inv s y Hy) as [Ey | [(b & Hb & ->) | (k2 & rg2 & Hk2 & Kk2 & Lk2 & ->)]].
      * subst y. apply ranges_disjoint_sym. apply CTXD; [exact Hx | exact Hne].
      * destruct (area_range X R U s L b HI HG Hb) as (r2 & rg2 & Ep2 & Hr2 & Hl2 & K2 & B1 & B2 & B3 & B4).
        assert (Er : k <> r2) by (intros ->; rewrite Hk in Hr2; injection Hr2 as <-; exact (K2 Kk)).
        pose proof (HD k r2 rgk rg2 Er Hk Hr2 Lk Hl2) as D. unfold crange, ranges_disjoint in *. cbn [fst snd loc_addr] in *. lia.
      * assert (Er : k <> k2) by (intros ->; rewrite Hk in Hk2; injection Hk2 as <-; exact (Hne eq_refl)).
        pose proof (HD k k2 rgk rg2 Er Hk Hk2 Lk Lk2) as D. unfold crange, ranges_disjoint in *. cbn [fst snd loc_addr] in *. lia.
  - intros rg Hin. destruct (footprint_inv s rg Hin) as [-> | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
    + unfold crange. cbn [fst snd loc_addr]. rewrite Hctx. unfold CTX_SIZE. lia.
    + destruct (area_range X R U s L a HI HG Ha) as (r & rg & _ & Hr & Hl & _ & B1 & B2 & _).
      destruct (HG r rg Hr Hl) as (G1 & _ & G3 & G4). unfold crange. cbn [fst snd]. unfold PGSZ in *. lia.
    + destruct (HG k rgk Hk Lk) as (G1 & _ & G3 & G4). unfold crange. cbn [fst snd loc_addr]. unfold PGSZ in *. lia.
Qed.
End GEO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_eqm : forall n m m' (a : word), bv_unsigned a + Z.of_nat n <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m' x = m x) ->
  store_ok SEGS m a n = true -> store_ok SEGS m' a n = true.
Proof.
  intros n; induction n as [|n IH]; intros m m' a Hr Hg H; [reflexivity|].
  cbn [store_ok] in *.
  assert (Ev : wview SEGS m' a = wview SEGS m a) by (unfold wview; rewrite (Hg a) by lia; reflexivity).
  rewrite Ev. destruct (wview SEGS m a) as [b|]; [|discriminate].
  destruct n as [|n']; [reflexivity|].
  pose proof (bv_unsigned_in_range _ a) as Ra. unfold bv_modulus in Ra.
  assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
  apply (IH m m' (a + 1)%bv); [rewrite Hu1; lia | | exact H].
  intros x Hx. rewrite Hu1 in Hx. apply Hg. lia.
Qed.

Lemma stk_ok_eqm : forall m m' sp K, stk_ok SEGS m (wa sp) K -> 0 <= sp <= 2^47 ->
  (forall x, sp - K <= x < sp -> m' (wa x) = m (wa x)) -> stk_ok SEGS m' (wa sp) K.
Proof.
  intros m m' sp K H Hsp Hg a n H1 H2. rewrite u_wa_small in H1, H2 by lia.
  apply (store_ok_eqm n m m' a); [pose proof (bv_unsigned_in_range _ a); lia | | exact (H a n ltac:(rewrite u_wa_small by lia; exact H1) ltac:(rewrite u_wa_small by lia; exact H2))].
  intros x Hx. rewrite <- (wa_u x). apply Hg. lia.
Qed.

Section TRANSPORT.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L L' : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HX : XNM X s.
Hypothesis HE : lext L L' s.

#[using="HE"] Lemma loc_addr_ext : forall l, loclt (length (st_regions s)) l -> loc_addr L' l = loc_addr L l.
Proof. LiaFast.lf_pins (fun (HE : LiaFast.U) => LiaFast.u0).
  intros [o|[r o]] H; cbn [loc_addr]; [rewrite (proj1 HE); reflexivity|]. unfold loclt, plt in H. cbn [prid] in H.
  rewrite (proj2 (proj2 (proj2 HE)) r H). reflexivity.
Qed.

#[using="HE"] Lemma sval_num_ext : forall v, svlt (length (st_regions s)) v -> sval_num L' v = sval_num L v.
Proof. LiaFast.lf_pins (fun (HE : LiaFast.U) => LiaFast.u0).
  intros [z|p|z|] H; cbn [sval_num]; try reflexivity.
  - apply loc_addr_ext. exact H.
  - exact (proj1 (proj2 (proj2 HE))).
Qed.

#[using="X R U HI HX HE"] Lemma cell_holds_ext : forall bv c, In c (image s) -> cell_holds L bv c -> cell_holds L' bv c.
Proof. LiaFast.lf_pins (fun (X R U HI HX HE : LiaFast.U) => LiaFast.u0).
  intros bv c Hc H. destruct (image_lt X R U s HI HX c Hc) as (L1 & V1).
  destruct c as [l w v]. unfold cell_holds in *. cbn [mc_loc mc_w mc_val] in *. rewrite (loc_addr_ext _ L1).
  destruct v as [z|p|z|]; [rewrite (sval_num_ext (VZ z) I) | rewrite (sval_num_ext (VP p) V1) | | rewrite (sval_num_ext VSec I)]; exact H.
Qed.

#[using="X R U HI HX HE"] Lemma cell_range_ext : forall c, In c (image s) -> cell_range L' c = cell_range L c.
Proof. LiaFast.lf_pins (fun (X R U HI HX HE : LiaFast.U) => LiaFast.u0).
  intros c Hc. destruct (image_lt X R U s HI HX c Hc) as (L1 & _). unfold cell_range. rewrite (loc_addr_ext _ L1). reflexivity.
Qed.

#[using="X R U HI HE"] Lemma crange_ext : forall rg, In rg (footprint s) -> crange L' rg = crange L rg.
Proof. LiaFast.lf_pins (fun (X R U HI HE : LiaFast.U) => LiaFast.u0). intros rg H. unfold crange. rewrite (loc_addr_ext _ (footprint_lt X R U s HI rg H)). reflexivity. Qed.

#[using="HE"] Lemma rgeo_ext : forall HTOP, rgeoA HTOP L s -> rgeoA HTOP L' s.
Proof. LiaFast.lf_pins (fun (HE : LiaFast.U) => LiaFast.u0).
  intros HTOP H r rg Hr Hl. rewrite (proj2 (proj2 (proj2 HE)) r (region_lt s r rg Hr)). exact (H r rg Hr Hl).
Qed.

#[using="HE"] Lemma rdisj_ext : rdisj L s -> rdisj L' s.
Proof. LiaFast.lf_pins (fun (HE : LiaFast.U) => LiaFast.u0).
  intros H r1 r2 rg1 rg2 Hne H1 H2 L1 L2.
  rewrite (proj2 (proj2 (proj2 HE)) r1 (region_lt s r1 rg1 H1)), (proj2 (proj2 (proj2 HE)) r2 (region_lt s r2 rg2 H2)).
  exact (H r1 r2 rg1 rg2 Hne H1 H2 L1 L2).
Qed.

#[using="X R U HI HX HE"] Theorem NC_transport : forall HTOP m m' sp0 K, HTOP <= 2^47 ->
  NC L [] [] s m sp0 K -> rgeoA HTOP L s -> rdisj L s ->
  (forall rg, In rg (footprint s) -> forall x, loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg -> m' (wa x) = m (wa x)) ->
  (forall x, sp0 - K <= x < sp0 -> m' (wa x) = m (wa x)) ->
  (forall x, 0x10000 <= x < 0x97000 -> m' (wa x) = m (wa x)) ->
  NC L' [] [] s m' sp0 K /\ rgeoA HTOP L' s /\ rdisj L' s.
Proof. LiaFast.lf_pins (fun (X R U HI HX HE : LiaFast.U) => LiaFast.u0).
  intros HTOP m m' sp0 K HTB N HG HD HFP HSK HIMG.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof HR as (HL & HPW & HCS & HFM).
  pose proof (rgeo_ext HTOP HG) as HG'. pose proof (rdisj_ext HD) as HD'.
  assert (Hctx' : ly_ctx L' = 0x95ed8) by (rewrite (proj1 HE); exact Hctx).
  pose proof (layout_of_geo HTOP HTB X R U s L' HI Hctx' HG' HD') as HL'.
  assert (KEYA : forall q, In q (keys s) -> loc_addr L' (LMem q) = loc_addr L (LMem q)) by (intros q Hq; apply loc_addr_ext; exact (key_lt X R U s HI q Hq)).
  split; [|split; [exact HG' | exact HD']].
  constructor.
  - split; [exact HL'|]. split; [exact (image_cells_disjoint_X X R U s L' HI (XNU_of_XNM X s HX) HL')|]. split.
    + apply Forall_forall. intros c Hc. right. destruct (proj1 (Forall_forall _ _) HCS c Hc) as [[]|H].
      apply (cell_holds_ext _ c Hc). destruct (image_in_footprint_X X R U s L c HI (XNU_of_XNM X s HX) HL Hc) as (rg & Hrg & Hinc).
      apply (cell_holds_frame L (bview SEGS m) (bview SEGS m') c (image_cell_width s c Hc) H).
      intros a Ha. apply MngWb.bview_ext. apply (HFP rg Hrg). unfold range_incl, in_rng, crange, cell_range in *. cbn [fst snd] in *. lia.
    + apply Forall_forall. intros rg Hrg x Hx. rewrite (loc_addr_ext _ (footprint_lt X R U s HI rg Hrg)) in Hx.
      rewrite (MngWb.bview_ext SEGS m m' x (HFP rg Hrg x Hx)). exact (proj1 (Forall_forall _ _) HFM rg Hrg x Hx).
  - exact HEX.
  - exact HZU.
  - exact HK.
  - exact Hctx'.
  - destruct Henv as (E1 & E2 & can & Rc & E3). split; [|split].
    + rewrite (rdn_frame_n m m' 408992 8) by (try lia; intros x Hx; apply HIMG; cbn in Hx; lia). exact E1.
    + intros sc Hsc. rewrite (rdn_frame_n m m' (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply HIMG; cbn in Hx; lia). exact (E2 sc Hsc).
    + exists can. split; [exact Rc|]. rewrite (rdn_frame_n m m' 613952 8) by (try lia; intros x Hx; apply HIMG; cbn in Hx; lia). exact E3.
  - apply (stk_ok_eqm m m' sp0 K HSTK ltac:(lia) HSK).
  - exact HK1.
  - exact Hsp1.
  - exact Hsp2.
  - exact Hsp3.
  - intros c Hc. pose proof (HC c Hc) as P. unfold cplace in *. destruct (image_lt X R U s HI HX c Hc) as (L1 & _).
    rewrite (loc_addr_ext _ L1). exact P.
  - intros q Hq. rewrite (KEYA q Hq). exact (HMP q Hq).
  - intros q1 q2 H1 H2 Hne. rewrite (KEYA q1 H1), (KEYA q2 H2). exact (HMD q1 q2 H1 H2 Hne).
Qed.
End TRANSPORT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KS_of_Inv : forall X R U s, Inv X R U s -> KS s.
Proof. intros X R U s HI. split; [exact (proj1 (inv_keys HI)) | intros g Hg; exact (key_once_inv X R U s g HI Hg)]. Qed.

Lemma handed_range : forall X R U s a, Inv X R U s -> 0 <= handed s a <= METAS_PER_AREA.
Proof.
  intros X R U s a HI. pose proof (inv_keys HI) as (_ & _ & _ & _ & C). unfold handed.
  destruct (sptr_eqb a (last (st_areas s) (SP 0%nat 0))); unfold METAS_PER_AREA in *; lia.
Qed.

Section NCGEO.
Variable HTOP : Z.
Hypothesis HTOPB : HTOP <= 2^47.

(* [comment removed for export] *)
#[using="Type"] Lemma key_slot_range : forall X R U s L q, Inv X R U s -> rgeoA HTOP L s -> In q (keys s) ->
  exists a j r rg, In a (st_areas s) /\ 0 <= j < METAS_PER_AREA /\ q = padd a (AREA_HDR + META_SIZE * j) /\
    prid a = r /\ region_of s r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\
    loc_addr L (LMem a) mod PGSZ = 0 /\ ly_reg L r <= loc_addr L (LMem a) /\ loc_addr L (LMem a) + PGSZ <= ly_reg L r + rg_len rg /\
    loc_addr L (LMem q) = loc_addr L (LMem a) + AREA_HDR + META_SIZE * j.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X R U s L q HI HG Hq. pose proof (inv_keys HI) as (_ & KP & _). destruct (KP q Hq) as (a & j & Ha & Hj & ->).
  pose proof (handed_range X R U s a HI) as Hh.
  destruct (area_range HTOP X R U s L a HI HG Ha) as (r & rg & Ep & Hr & Hl & Hk & B1 & B2 & B3 & B4).
  exists a, j, r, rg. split; [exact Ha|]. split; [lia|]. split; [reflexivity|]. split; [exact Ep|]. split; [exact Hr|].
  split; [exact Hl|]. split; [exact Hk|].
  destruct (HG r rg Hr Hl) as (G1 & G2 & _).
  split.
  { rewrite loc_addr_LMem. rewrite Ep. unfold PGSZ in *.
    apply Z.mod_divide in G2; [|lia]. apply Z.mod_divide in B4; [|lia]. destruct G2 as (k1 & E1). destruct B4 as (k2 & E2).
    rewrite E1, E2. replace (k1 * 4096 + k2 * 4096) with ((k1 + k2) * 4096) by ring. apply Z.mod_mul. lia. }
  split; [exact B1|]. split; [exact B2|].
  rewrite !loc_addr_LMem, prid_padd, poff_padd. ring.
Qed.

#[using="HTOPB"] Theorem NC_of_geo : forall X R U s L m sp0 K,
  Inv X R U s -> XNM X s -> rgeoA HTOP L s -> rdisj L s -> ly_ctx L = 0x95ed8 -> HTOP <= sp0 - K ->
  Forall (cell_holds L (bview SEGS m)) (image s) -> Forall (range_mapped L (bview SEGS m)) (footprint s) ->
  nenv m -> stk_ok SEGS m (wa sp0) K -> 1024 <= K -> 2^20 <= sp0 - K -> sp0 <= 2^47 -> sp0 mod 16 = 0 ->
  NC L [] [] s m sp0 K.
Proof. LiaFast.lf_pins (fun (HTOPB : LiaFast.U) => LiaFast.u0).
  intros X R U s L m sp0 K HI HX HG HD Hctx HT HCS HFM Henv HSTK HK1 Hsp1 Hsp2 Hsp3.
  pose proof (layout_of_geo HTOP HTOPB X R U s L HI Hctx HG HD) as HL.
  assert (CELLS : forall c, In c (image s) -> cplace L (sp0 - K) c).
  { intros c Hc. destruct (image_in_footprint_X X R U s L c HI (XNU_of_XNM X s HX) HL Hc) as (rg & Hrg & Hinc).
    pose proof (image_cell_width s c Hc) as Hw.
    unfold cplace, range_incl, cell_range, crange in *. cbn [fst snd] in *.
    destruct (footprint_inv s rg Hrg) as [-> | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
    - cbn [fst snd loc_addr] in Hinc. rewrite Hctx in Hinc. unfold CTX_SIZE in Hinc. lia.
    - destruct (area_range HTOP X R U s L a HI HG Ha) as (r & rg & _ & Hr & Hl & _ & B1 & B2 & _).
      destruct (HG r rg Hr Hl) as (G1 & _ & G3 & G4). cbn [fst snd] in Hinc. unfold ranges_disjoint in G4. cbn [fst snd] in G4.
      unfold PGSZ in *. lia.
    - destruct (HG k rgk Hk Lk) as (G1 & _ & G3 & G4). cbn [fst snd loc_addr] in Hinc. unfold ranges_disjoint in G4. cbn [fst snd] in G4.
      unfold PGSZ in *. lia. }
  constructor.
  - split; [exact HL|]. split; [exact (image_cells_disjoint_X X R U s L HI (XNU_of_XNM X s HX) HL)|]. split; [|exact HFM].
    apply Forall_forall. intros c Hc. right. exact (proj1 (Forall_forall _ _) HCS c Hc).
  - intros l [].
  - intros x [].
  - exact (KS_of_Inv X R U s HI).
  - exact Hctx.
  - exact Henv.
  - exact HSTK.
  - exact HK1.
  - exact Hsp1.
  - exact Hsp2.
  - exact Hsp3.
  - exact CELLS.
  - intros q Hq. destruct (key_slot_range X R U s L q HI HG Hq) as (a & j & r & rg & Ha & Hj & Eq & Ep & Hr & Hl & _ & A0 & A1 & A2 & Aq).
    destruct (HG r rg Hr Hl) as (G1 & _ & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
    rewrite Aq. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. split; [lia|]. split; [lia|]. split; [lia|].
    apply Z.mod_divide in A0; [|lia]. destruct A0 as (k1 & E1). rewrite E1.
    replace (k1 * 4096 + 24 + 40 * j) with ((k1 * 512 + 3 + 5 * j) * 8) by ring. apply Z.mod_mul. lia.
  - intros q1 q2 H1 H2 Hne.
    destruct (key_slot_range X R U s L q1 HI HG H1) as (a1 & j1 & r1 & rg1 & Ha1 & Hj1 & Eq1 & _ & _ & _ & _ & P0 & _ & _ & Pq).
    destruct (key_slot_range X R U s L q2 HI HG H2) as (a2 & j2 & r2 & rg2 & Ha2 & Hj2 & Eq2 & _ & _ & _ & _ & Q0 & _ & _ & Qq).
    rewrite Pq, Qq. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
    destruct (sptr_eq_dec a1 a2) as [<-|Ha].
    + assert (j1 <> j2) by (intros ->; apply Hne; rewrite Eq1, Eq2; reflexivity). lia.
    + pose proof HL as (_ & _ & PWf & _).
      assert (Din : forall a, In a (st_areas s) -> In (LMem a, PGSZ) (footprint s)) by (intros a Ha'; right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
      pose proof (pairwise_map_In _ (crange L) _ _ _ PWf (Din a1 Ha1) (Din a2 Ha2) ltac:(intros E; injection E as E; exact (Ha E))) as D.
      unfold crange, ranges_disjoint in D. cbn [fst snd] in D. unfold PGSZ in D. lia.
Qed.
End NCGEO.
