(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ MngNtfM MngNtfS.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma count_disjoint : forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (f : A -> Z) (l : list A) (w B : Z), 1 <= w -> 0 <= B ->
  List.NoDup l -> (forall x, In x l -> 0 <= f x /\ f x + w <= B) ->
  (forall x y, In x l -> In y l -> x <> y -> f x + w <= f y \/ f y + w <= f x) ->
  Z.of_nat (length l) <= B / w + 1.
Proof.
  intros A dec f l w B Hw HB ND Hr Hd.
  set (idx := fun x => Z.to_nat ((f x + w - 1) / w)).
  assert (Hj : forall x, In x l -> f x <= w * ((f x + w - 1) / w) < f x + w /\ 0 <= (f x + w - 1) / w <= B / w).
  { intros x Hx. pose proof (Hr x Hx) as (R1 & R2). pose proof (Z.div_mod (f x + w - 1) w ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (f x + w - 1) w ltac:(lia)) as M.
    split; [lia|]. split; [apply Z.div_pos; lia|]. apply Z.div_le_mono; lia. }
  assert (HND : List.NoDup (map idx l)).
  { apply NoDup_map_NoDup_ForallPairs; [|exact ND]. intros x y Hx Hy E.
    destruct (dec x y) as [Exy|Nxy]; [exact Exy|]. exfalso.
    pose proof (Hj x Hx) as (J1 & J2). pose proof (Hj y Hy) as (K1 & K2).
    unfold idx in E. apply Z2Nat.inj in E; [|lia|lia]. rewrite <- E in K1.
    destruct (Hd x y Hx Hy Nxy) as [D|D]; lia. }
  assert (Hincl : incl (map idx l) (seq 0 (Z.to_nat (B / w + 1)))).
  { intros n Hn. apply in_map_iff in Hn as (x & <- & Hx). apply in_seq. pose proof (Hj x Hx) as (_ & J2). unfold idx. lia. }
  pose proof (NoDup_incl_length HND Hincl) as HL. rewrite length_map, length_seq in HL.
  assert (0 <= B / w) by (apply Z.div_pos; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma contrib_range : forall X R U s sc q, Inv X R U s -> 0 <= contrib X s sc q <= 32.
Proof.
  intros X R U s sc q HI. unfold contrib. destruct (MTX X s q) as [[pr nx| |am]|] eqn:E; try lia.
  assert (Hu : usedX X s q am) by exact E.
  pose proof (inv_groups HI q am Hu) as ((Glast & _) & _). destruct (am_sc am =? sc); lia.
Qed.

Lemma class_sum_le : forall X R U s sc, Inv X R U s -> 0 <= class_sum X s sc <= 32 * Z.of_nat (length (keys s)).
Proof.
  intros X R U s sc HI. unfold class_sum. induction (keys s) as [|q t IH]; cbn [fold_right length]; [lia|].
  pose proof (contrib_range X R U s sc q HI). lia.
Qed.

Lemma keys_len_NC : forall L X EXC s m sp0 K, NC L X EXC s m sp0 K -> Z.of_nat (length (keys s)) <= 2^47 / 40 + 1.
Proof.
  intros L X EXC s m sp0 K N. pose proof N as [_ _ _ HK _ _ _ HK1 Hsp1 Hsp2 _ _ HMP HMD].
  apply (count_disjoint sptr sptr_eq_dec (fun q => loc_addr L (LMem q)) (keys s) 40 (2^47) ltac:(lia) ltac:(lia) (proj1 HK)).
  - intros q Hq. destruct (HMP q Hq) as (A1 & A2 & _). lia.
  - intros x y Hx Hy Hne. exact (HMD x y Hx Hy Hne).
Qed.

Lemma usage_bound : forall L X EXC R U s m sp0 K sc, NC L X EXC s m sp0 K -> Inv X R U s -> 0 <= U sc <= 2^40 -> 0 <= sc < 48 ->
  0 <= usage_of s sc <= 2^60.
Proof.
  intros L X EXC R U s m sp0 K sc N HI HU Hsc. rewrite (inv_usage HI sc Hsc).
  pose proof (class_sum_le X R U s sc HI) as B1. pose proof (keys_len_NC L X EXC s m sp0 K N) as B2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ring_next_In : forall lk h0 ms x pr q, ring_ok lk h0 ms -> In x ms -> lk x = Some (pr, Some q) -> In q ms.
Proof.
  intros lk h0 ms x pr q [[ND Hc] _] Hx Hl. destruct ms as [|m0 rest]; [destruct Hx|].
  destruct (chain_next lk _ _ _ x pr (Some q) Hc Hx Hl) as (l1 & l2 & E & Hn & _). injection Hn as ->.
  destruct l2 as [|y l2']; cbn [hd]; [left; reflexivity|]. rewrite E. apply in_app_iff. right. right. left. reflexivity.
Qed.

Lemma ring_prev_In : forall lk h0 ms x p nx, ring_ok lk h0 ms -> In x ms -> lk x = Some (Some p, nx) -> In p ms.
Proof.
  intros lk h0 ms x p nx [[ND Hc] _] Hx Hl. destruct ms as [|m0 rest]; [destruct Hx|].
  destruct (chain_next lk _ _ _ x (Some p) nx Hc Hx Hl) as (l1 & l2 & E & _ & Hp). injection Hp as Hp.
  destruct l1 as [|y l1'].
  - rewrite Hp. change (In (last (m0 :: rest) m0) (m0 :: rest)). apply In_last. discriminate.
  - rewrite Hp, E. apply in_app_iff. left. apply In_last. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ntf_facts : forall L X EXC U s m sp0 K g i am,
  NC L X EXC s m sp0 K -> Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= c < 48 -> 0 <= U c <= 2^40) ->
  MT s g = Some (MUsed am) /\ ~ In g X /\ 0 <= i <= am_last am /\ 0 <= am_last am <= 31 /\
  (am_sc am = 63 \/ 0 <= am_sc am < 48) /\ 0 <= am_maplen am /\ 0 <= meta_bits am <= 2^64-1 /\
  0 <= am_avail am <= 2^32-1 /\ 0 <= am_freed am <= 2^32-1 /\ Z.testbit (am_avail am) i = false /\ Z.testbit (am_freed am) i = false /\
  (forall q, am_next am = Some q -> In q (keys s)) /\ (0 <= am_sc am < 48 -> 0 <= usage_of s (am_sc am) <= 2^60) /\
  (7 <= am_sc am < 39 -> 0 <= znth (am_sc am - 7) (st_bounces s) <= 255) /\
  (am_sc am = 63 -> am_last am = 0 /\ 1 <= am_maplen am /\ am_avail am = 0 /\ am_freed am = 0 /\ i = 0).
Proof.
  intros L X EXC U s m sp0 K g i am N HI Hu HU.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. apply memb_false_notIn in NXg.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  destruct (masks_range_inv _ _ _ s g am HI Hu) as (RA & RF & Rl & Rs & Rm).
  pose proof (meta_bits_range_inv _ _ _ s g am L HI Hu (proj1 (nc_repr _ _ _ _ _ _ _ N))) as RW.
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _ & _).
  assert (Hsc : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  assert (TB : Z.testbit (am_avail am) i = false /\ Z.testbit (am_freed am) i = false).
  { unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) i), (Z.testbit (am_freed am) i); cbn in Hal; try discriminate. split; reflexivity. }
  pose proof (inv_ctx HI) as (Cla & Clu & Clm & Clb & Cu & Cm & Cb & Cseq & _).
  split; [exact Mg|]. split; [exact NXg|]. split; [exact Hi|]. split; [exact Rl|]. split; [exact Hsc|]. split; [exact Rm|].
  split; [exact RW|]. split; [exact RA|]. split; [exact RF|]. split; [exact (proj1 TB)|]. split; [exact (proj2 TB)|].
  split.
  { intros q Hq. destruct (inv_rings HI) as (_ & A & D). destruct Hsc as [H63|H48].
    - destruct (D g am Hu H63) as [_ En]. rewrite En in Hq. discriminate.
    - destruct (A (am_sc am) H48) as (ms & Rg & Mem & _). assert (Hg : In g ms) by (apply (Mem g am Hu eq_refl); rewrite Hq; intros E; discriminate).
      assert (Lg : alinks X s (am_sc am) g = Some (am_prev am, Some q)) by (unfold alinks; rewrite Hu, Z.eqb_refl, Hq; reflexivity).
      pose proof (ring_next_In _ _ _ g _ q Rg Hg Lg) as Hqm. destruct (ring_links _ _ _ q Rg Hqm) as (pr' & nx' & Lq).
      unfold alinks, MTX in Lq. destruct (memb q X); [discriminate|]. destruct (MT s q) as [y|] eqn:Mq; [|discriminate]. exact (MT_Some_In_keys s q y Mq). }
  split; [intros H48; exact (usage_bound L X EXC _ U s m sp0 K (am_sc am) N HI (HU _ H48) H48)|].
  split.
  { intros Hb. unfold znth. apply Cb. apply nth_In. rewrite Clb. lia. }
  intros H63. destruct Gcl as [(C63 & Cl0 & Cml & Cav & Cfr & _) | (C & _)]; [|lia]. repeat split; try assumption. lia.
Qed.

Lemma chain_last : forall lk prev l y first, chain lk prev (l ++ [y]) first -> lk y = Some (Some (last l prev), Some first).
Proof. intros lk prev l y first H. apply chain_app in H as [_ H]. cbn [chain hd] in H. exact (proj1 H). Qed.

(* [comment removed for export] *)
Lemma ring_prev_next : forall lk h0 ms x p nx, ring_ok lk h0 ms -> In x ms -> lk x = Some (Some p, nx) -> exists pp, lk p = Some (pp, Some x).
Proof.
  intros lk h0 ms x p nx [[ND Hc] _] Hx Hl. destruct ms as [|m0 rest]; [destruct Hx|].
  destruct (chain_next lk _ _ _ x (Some p) nx Hc Hx Hl) as (l1 & l2 & E & _ & Hp). injection Hp as Hp.
  destruct l1 as [|y l1'].
  - cbn [app] in E. injection E as Ex Er. subst m0 rest. change (last [] (last (x :: l2) x)) with (last (x :: l2) x) in Hp.
    destruct l2 as [|z0 l2''].
    + cbn [last] in Hp. subst p. cbn [chain hd] in Hc. destruct Hc as [Hc _]. eexists. exact Hc.
    + destruct (exists_last (l := z0 :: l2'') ltac:(discriminate)) as (l2' & z & Ez). rewrite Ez in Hc, Hp.
      assert (Ep : p = z) by (rewrite Hp; change (last [] (last (l2' ++ [z]) x)) with (last (l2' ++ [z]) x); apply last_app_single).
      subst p. rewrite app_comm_cons in Hc.
      pose proof (chain_last lk _ (x :: l2') z x Hc) as Hz. rewrite Ep. eexists. exact Hz.
  - destruct (exists_last (l := y :: l1') ltac:(discriminate)) as (l1'' & yl & El1). rewrite El1 in Hp, E.
    rewrite last_app_single in Hp. subst p. rewrite E in Hc.
    apply chain_app in Hc as [Hc _]. cbn [hd] in Hc. pose proof (chain_last lk _ l1'' yl x Hc) as Hy. eexists. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma ring_self : forall lk h0 ms x pr, ring_ok lk h0 ms -> In x ms -> lk x = Some (pr, Some x) -> h0 = Some x.
Proof.
  intros lk h0 ms x pr [[ND Hc] Hh] Hx Hl. destruct ms as [|m0 rest]; [destruct Hx|].
  destruct (chain_next lk _ _ _ x pr (Some x) Hc Hx Hl) as (l1 & l2 & E & Hn & _). injection Hn as Hn.
  destruct l2 as [|z l2'].
  - cbn [hd] in Hn. subst x. rewrite Hh. cbn [hd_error]. destruct l1 as [|y l1']; [reflexivity|].
    exfalso. cbn [app] in E. injection E as Ey Er. subst y. rewrite Er in ND. apply NoDup_cons_iff in ND as [Hn _].
    apply Hn. apply in_app_iff. right. left. reflexivity.
  - exfalso. cbn [hd] in Hn. subst z. rewrite E in ND. apply NoDup_remove_2 in ND. apply ND. apply in_app_iff. right. left. reflexivity.
Qed.
