(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mremap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState ITree RelSpec RelSpecX Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KRemapDef KStep KStepK
  MI_Inv MI_Kit MI_Ledger MI_WFree2 MI_Contracts MRemapOp MI_WRemap KRemap.
Import ListNotations.
Local Open Scope Z_scope.

Definition pcovered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  fst iv < snd iv /\ forall x, fst iv <= x < snd iv -> exists e sz, In (e, sz) maps /\ bv_unsigned e <= x < bv_unsigned e + bv_unsigned sz.

Lemma avoids_of_region_free_p : forall maps a n avoid,
  region_free maps a n = true -> Forall (pcovered maps) avoid -> 0 < bv_unsigned n ->
  avoids (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros maps a n avoid Hrf Hc Hn0. unfold avoids. apply forallb_forall. intros [lo hi] Hin. cbn [fst snd].
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as [NE PC]. cbn [fst snd] in NE, PC.
  destruct (Z.leb_spec (bv_unsigned a + bv_unsigned n) lo) as [|H1]; [reflexivity|].
  destruct (Z.leb_spec hi (bv_unsigned a)) as [|H2]; [reflexivity|]. exfalso.
  assert (HX : lo <= Z.max (bv_unsigned a) lo < hi) by lia.
  destruct (PC (Z.max (bv_unsigned a) lo) HX) as (e & sz & He & R).
  pose proof (region_free_In _ _ _ _ _ Hrf He) as [H|H]; lia.
Qed.

Lemma Forall_pcovered_app_l : forall l1 l2 avoid, Forall (pcovered l1) avoid -> Forall (pcovered (l1 ++ l2)) avoid.
Proof.
  intros l1 l2 avoid H. eapply Forall_impl; [| exact H]. intros iv [NE PC]. split; [exact NE|]. intros x Hx. destruct (PC x Hx) as (e & sz & Hin & R).
  exists e, sz. split; [apply in_or_app; left; exact Hin| exact R].
Qed.

Lemma nstep_dec_mremap2 : forall old old_len new_len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  let on := mmap_len old_len in let nn := mmap_len new_len in let OLD := Z_to_bv 64 old in
  (0 <= old <= 2^64 - 4096)%Z -> (0 < old_len < 2^64)%Z -> (0 < new_len < 2^64)%Z ->
  minv mo ->
  Forall (pcovered (vm_reserved h ++ map_remove (vm_maps h) OLD)) avoid ->
  nstep (NMremap old old_len new_len) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
  exists x, dec_mremap old old_len new_len avoid rsp = Some x /\
  match x with
  | MrErr e => e = ENOMEM /\ mo' = mo /\ on <> nn
  | MrSame => (on = nn /\ mo' = mo)
      \/ (nn < on /\ mo' = mremap_model_next mo OLD (Z_to_bv 64 on) OLD (Z_to_bv 64 nn))
      \/ (on < nn /\ mremap_inplace_grow_b mo OLD (Z_to_bv 64 on) (Z_to_bv 64 nn) on nn = true
             /\ mo' = mremap_model_next mo OLD (Z_to_bv 64 on) OLD (Z_to_bv 64 nn))
  | MrMoved dst => (on < nn)%Z /\ mremap_fresh_b mo on nn OLD (Z_to_bv 64 on) (Z_to_bv 64 dst) (Z_to_bv 64 nn) = true
      /\ mo' = mremap_model_next mo OLD (Z_to_bv 64 on) (Z_to_bv 64 dst) (Z_to_bv 64 nn)
  end.
Proof.
  intros old old_len new_len avoid mo rsp mo' evs h on nn OLD Hold Hol Hnl Hminv Hcov H.
  pose proof (minv_nolazy _ Hminv) as Hlazy. pose proof (minv_alloc_top _ Hminv) as [_ Htop]. fold h in Htop.
  destruct H as (-> & (core & Hs & Hout) & _). split; [reflexivity|].
  assert (FR : mm_frame mo mo').
  { pose proof (mremap_out_shape _ _ _ _ _ _ _ Hout) as (_ & _ & [->|(d & k & ->)]); [apply mm_frame_refl|apply mm_frame_mremap_model_next; exact Hlazy]. }
  split; [exact FR|].
  unfold mremap_out in Hout. cbv zeta in Hout. rewrite (unsigned_lit old_len), (unsigned_lit new_len) in Hout by lia.
  fold (mmap_len old_len) (mmap_len new_len) in Hout. fold on nn OLD h in Hout.
  assert (Eold : errno_of OLD = None) by (subst OLD; apply errno_of_lit; lia).
  destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. subst core. unfold dec_mremap. cbv zeta. fold on nn OLD.
  destruct Hout as [(E & H)|[(NE & e & He & H)|[(L & H)|[(L & G & H)|(L & dst & Hd & H)]]]]; apply Ok_inj in H as (H & -> & _).
  - inversion H; subst. rewrite Eold, bv_eqb_refl.
    exists MrSame. split; [|left; auto].
    unfold mremap_inplace_effect, mremap_tail. rewrite E, Z.ltb_irrefl. cbn [eff_zeros eff_unmaps listWW_eqb andb]. rewrite Z.leb_refl. reflexivity.
  - unfold efferr, eff0 in H. inversion H; subst. cbn in He. destruct He as [<-|[]].
    rewrite errno_of_errno_ret by (unfold ENOMEM; lia). exists (MrErr ENOMEM). split; [reflexivity|auto].
  - exists MrSame. split; [|right; left; auto with zarith].
    unfold mremap_inplace_effect in H |- *. rewrite (proj2 (Z.ltb_lt _ _) L) in H |- *. inversion H; subst.
    rewrite Eold, bv_eqb_refl. cbn [eff_zeros eff_unmaps]. rewrite !listWW_eqb_refl. rewrite (proj2 (Z.leb_le nn on) ltac:(lia)). reflexivity.
  - exists MrSame. split; [|right; right; split; [lia| split; [exact G| reflexivity]]].
    assert (GE : (nn <? on)%Z = false) by (apply Z.ltb_ge; lia).
    unfold mremap_inplace_effect in H |- *. rewrite GE in H |- *. inversion H; subst.
    rewrite Eold, bv_eqb_refl. cbn [eff_zeros eff_unmaps]. rewrite !listWW_eqb_refl.
    pose proof G as G'. unfold mremap_inplace_grow_b in G. cbv zeta in G. fold h in G.
    apply andb_prop in G as [G _]. apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1.
    assert (AV : avoids old nn avoid = true).
    { pose proof (mmap_len_bound new_len ltac:(lia)) as NB0. fold nn in NB0.
      assert (G1' : old + nn <= alloc_top h) by (subst OLD; rewrite unsigned_lit in G1 by lia; exact G1).
      pose proof Htop as ACL. unfold alloc_ceiling_max in ACL.
      rewrite <- (unsigned_lit old) by lia. rewrite <- (unsigned_lit nn) by lia.
      fold OLD. apply (avoids_of_region_free_p (vm_reserved h ++ map_remove (vm_maps h) OLD)); [exact G2|exact Hcov| rewrite unsigned_lit by lia; lia]. }
    subst OLD. rewrite unsigned_lit in G1 by lia. rewrite (proj2 (Z.leb_le (old + nn) alloc_ceiling_max) ltac:(unfold alloc_ceiling_max in Htop |- *; lia)), AV.
    rewrite orb_true_r. reflexivity.
  - unfold mremap_move_effect in H. inversion H; subst.
    pose proof Hd as Hd'. unfold mremap_fresh_b in Hd. cbv zeta in Hd. fold h in Hd.
    apply andb_prop in Hd as [Hd P6]. apply andb_prop in Hd as [Hd P5].
    apply andb_prop in Hd as [Hd P4]. apply andb_prop in Hd as [Hd P3]. apply andb_prop in Hd as [P1 P2].
    apply Z.leb_le in P4. apply Z.ltb_lt in P3. apply Z.eqb_eq in P2.
    pose proof (mmap_len_bound new_len ltac:(lia)) as NB. fold nn in NB.
    assert (P4' : bv_unsigned dst + nn <= alloc_top h) by exact P4. pose proof Htop as ACL. unfold alloc_ceiling_max in ACL.
    assert (Edst : errno_of dst = None).
    { apply errno_of_small. lia. }
    assert (AV : avoids (bv_unsigned dst) nn avoid = true).
    { rewrite <- (unsigned_lit nn) by (pose proof (bv_unsigned_in_range 64 dst); lia).
      apply (avoids_of_region_free_p (vm_reserved h ++ map_remove (vm_maps h) OLD)); [|exact Hcov| rewrite unsigned_lit by (pose proof (bv_unsigned_in_range 64 dst); lia); lia].
      apply region_free_remove. exact P5. }
    rewrite Edst. apply negb_true_iff in P1. rewrite P1.
    rewrite !listWW_eqb_refl, !bv_eqb_refl, (proj2 (Z.eqb_eq _ _) P2), (proj2 (Z.ltb_lt _ _) P3), (proj2 (Z.leb_le (bv_unsigned dst + nn) alloc_ceiling_max) ltac:(lia)), (proj2 (Z.ltb_lt _ _) L), AV.
    cbn [andb]. exists (MrMoved (bv_unsigned dst)). split; [reflexivity|].
    rewrite Z_to_bv_bv_unsigned. split; [exact L|]. split; [exact Hd'|reflexivity].
Qed.

Lemma m_vmmaps_mremap_model_next : forall m OLD ON DST NN,
  m_vmmaps (mremap_model_next m OLD ON DST NN) = mremap_maps_next (m_vmmaps m) OLD DST NN.
Proof. intros. unfold mremap_model_next, vm_resize_backing. cbv zeta. destruct m; reflexivity. Qed.

Lemma region_free_of_disj : forall maps aw nw,
  (forall e, In e maps -> bv_unsigned aw + bv_unsigned nw <= elo e \/ ehi e <= bv_unsigned aw) ->
  region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; cbn; [reflexivity|].
  rewrite IH by (intros e' He'; apply H; right; exact He'). rewrite andb_true_r.
  specialize (H (e, sz) (or_introl eq_refl)). unfold elo, ehi in H. cbn [fst snd] in H.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff.
  destruct H as [H|H]; [right| left]; apply Z.ltb_ge; lia.
Qed.

Section MREMAP.
Variables (cs : mstate) (L : mled) (pbrk : Z) (mo : Model) (c : cptr) (g : aptr) (rg : region).
Hypothesis CR : creach2 cs L.
Hypothesis HK : KL L pbrk mo.
Hypothesis Hc : In c (ld_live L).
Hypothesis Hs : s_slots cs !! c = Some (g, 0).
Hypothesis SC : m_sizeclass (MR cs g) = 63.
Hypothesis Hrg : s_regions cs !! fst c = Some rg.

Definition rold : Z := r_base rg.
Definition ron : Z := round_up_pg (r_len rg).
Let h := m_vmmaps mo.
Let OLD := Z_to_bv 64 rold.

#[using="CR Hc"] Lemma sim_facts : exists st BL LS off n, strip st = cs /\ INVL x0 st L BL LS /\ In ((c, off), n) BL /\ ld_live L = map bslot BL.
Proof.
  destruct (creach2_sim cs L CR) as (st & BL & LS & E & INV & LIVE).
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk). exists st, BL, LS, off, n. auto.
Qed.

#[using="pbrk CR HK Hc Hs SC Hrg"] Lemma grp_facts : r_kind rg = RKGroup /\ In (rold, r_len rg) (ld_groups L) /\ 0 < r_len rg < LEN_MAX
  /\ 0 < rold /\ rold mod PGSZ = 0 /\ rold + ron <= ld_ceil L /\ m_maplen (MR cs g) * 4096 = ron
  /\ In (went rold ron) (vm_maps h) /\ brk_quiet L /\ mmap_len (r_len rg) = ron /\ brk_disj L rold ron
  /\ ld_resv L = s_reserved cs /\ c = (fst c, 16).
Proof.
  destruct sim_facts as (st & BL & LS & off & n & E & INV & Hk & LIVE). subst cs.
  cbn [s_slots strip] in Hs. cbn [s_regions strip] in Hrg.
  pose proof (g_facts' x0 st L BL LS c g off n 0 0 INV Hk eq_refl Hs SC) as (HG & EC & LI & ML & _ & STR & GB & rg' & Hrg' & K' & EON).
  rewrite Hrg in Hrg'. injection Hrg' as <-.
  pose proof (proj1 INV) as IR.
  pose proof (group_region_in_ledger x0 st L (fst c) rg IR Hrg K') as HIN. fold rold in HIN.
  pose proof (kl_groups _ _ _ HK _ _ HIN) as (A1 & A2 & A3 & A4 & A5 & A6).
  assert (EM : mmap_len (r_len rg) = ron) by (unfold ron, mmap_len; rewrite round_up_pg_eq; reflexivity).
  rewrite EM in A4, A5, A6. destruct A1 as [A1a A1b].
  repeat split; auto; try lia.
  all: try (cbn [s_metas strip MR get_meta_rec]; exact EON).
  all: try (eapply brk_quiet_of; exact IR).
  all: try exact (ir_resv _ _ _ IR).
Qed.

#[using="c g rg CR Hc Hs SC Hrg"] Lemma ceil_fact : ld_ceil L = s_ceil cs.
Proof.
  destruct sim_facts as (st & BL & LS & off & n & E & INV & Hk & LIVE). subst cs.
  rewrite s_ceil_strip. exact (proj1 (ir_ceil _ _ _ (proj1 INV))).
Qed.

#[using="cs L pbrk c g CR HK Hc Hs SC Hrg"] Lemma old_entry : In (went rold ron) (vm_maps h) /\ elo (went rold ron) = rold /\ ehi (went rold ron) = rold + ron /\ 0 < ron
  /\ fst (went rold ron) = OLD.
Proof.
  pose proof grp_facts as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & _).
  pose proof (KL_ceil_lt63 _ _ _ HK). pose proof (mmap_len_ge (r_len rg) ltac:(lia)). rewrite EM in *.
  split; [exact HM|]. split; [apply elo_went; lia|]. split; [apply ehi_went; lia|]. split; [lia| reflexivity].
Qed.

#[using="cs L pbrk mo c g CR HK Hc Hs SC Hrg h"] Lemma went_ne_old : forall b n, 0 < b < 2^64 -> b <> rold -> fst (went b n) <> OLD.
Proof.
  intros b n Hb Hne E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. pose proof (KL_ceil_lt63 _ _ _ HK).
  pose proof grp_facts as (_ & _ & _ & R0 & _ & RC & _). pose proof old_entry as (_ & _ & _ & RON & _).
  unfold OLD in E. rewrite unsigned_wz in E by lia. rewrite unsigned_lit in E by lia. exact E.
Qed.

#[using="cs L pbrk c g CR HK Hc Hs SC Hrg"] Lemma cover_not_old : forall e z, In e (vm_maps h) -> elo e <= z < ehi e -> ~ (rold <= z < rold + ron) -> In e (map_remove (vm_maps h) OLD).
Proof.
  intros e z He Hz Hnot. unfold map_remove. apply filter_In. split; [exact He|].
  destruct (bv_eqb (fst e) OLD) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E.
  pose proof old_entry as (HM & EL & EH & RON & FO).
  destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He HM) as [->|D].
  - rewrite EL, EH in Hz. apply Hnot. exact Hz.
  - pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj in D. rewrite EL, EH in D.
    assert (EE : elo e = rold). { unfold elo. rewrite E. unfold OLD. pose proof grp_facts as (_ & _ & _ & R0 & _ & RC & _). pose proof (KL_ceil_lt63 _ _ _ HK). apply unsigned_lit. lia. }
    lia.
Qed.

#[using="Type"] Lemma nodup_app_disj {A} (l1 l2 : list A) x : List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn in ND. inversion ND; subst.
  destruct H1 as [<-|H1]; [apply H3; apply in_or_app; right; exact H2| exact (IH H4 H1 H2)].
Qed.

#[using="cs pbrk mo c g CR HK Hc Hs SC Hrg h"] Lemma other_base : forall b l, (In (b, l) (ld_groups L) /\ (b, l) <> (rold, r_len rg)) \/ (exists k, In (b, l, k) (ld_metas L)) -> b <> rold.
Proof.
  pose proof grp_facts as (_ & HIN & _). pose proof (kl_distinct _ _ _ HK) as ND.
  intros b l [[Hin Hne]|[k Hin]] ->; [apply Hne; f_equal|].
  - apply (nodup_map_inj fst (ld_groups L) (rold, l) (rold, r_len rg)) in Hin; [injection Hin as ->; reflexivity| | exact HIN| reflexivity].
    eapply List.NoDup_app_remove_r. exact ND.
  - apply (nodup_app_disj _ _ rold ND); apply in_map_iff; [exists (rold, r_len rg)| exists (rold, l, k)]; auto.
Qed.

Section FRESH.
Variables (dst nn : Z) (mo' : Model).
Let DST := Z_to_bv 64 dst. Let NN := Z_to_bv 64 nn.
Hypothesis D0 : 0 < dst.
Hypothesis DA : dst mod PGSZ = 0.
Hypothesis NA : nn mod PGSZ = 0.
Hypothesis N2 : 2 * PGSZ <= nn.
Hypothesis NL : nn < LEN_MAX.
Hypothesis DC : dst + nn <= ld_ceil L.
Hypothesis FRESH : region_free (vm_reserved h ++ map_remove (vm_maps h) OLD) DST NN = true.
Hypothesis Hmi' : minv mo'.
Hypothesis Hh' : m_halted mo' = None.
Hypothesis Evm : m_vmmaps mo' = mremap_maps_next h OLD DST NN.

#[using="L pbrk mo HK nn D0 DA NA N2 DC"] Lemma Udst : bv_unsigned DST = dst. Proof. unfold DST. pose proof (KL_ceil_lt63 _ _ _ HK). apply unsigned_lit. lia. Qed.
#[using="dst N2 NL"] Lemma Unn : bv_unsigned NN = nn. Proof. unfold NN, LEN_MAX in *. apply unsigned_lit. unfold PGSZ in *. lia. Qed.

#[using="cs pbrk mo c g CR HK Hc Hs SC Hrg h OLD DST NN D0 DA NA N2 NL DC FRESH"] Lemma fresh_groups : forall b l, In (b, l) (ld_groups L) -> (b, l) <> (rold, r_len rg) -> dst + nn <= b \/ b + mmap_len l <= dst.
Proof.
  intros b l Hin Hne. pose proof (went_In_bounds _ _ _ b l HK (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (other_base b l (or_introl (conj Hin Hne))) as NE.
  assert (HR : In (went b (mmap_len l)) (map_remove (vm_maps h) OLD)).
  { unfold map_remove. apply filter_In. split; [exact B4|]. destruct (bv_eqb (fst (went b (mmap_len l))) OLD) eqn:E; [| reflexivity].
    exfalso. apply bv_eqb_eq in E. pose proof (KL_ceil_lt63 _ _ _ HK). exact (went_ne_old b _ ltac:(lia) NE E). }
  pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ FRESH) HR) as D. rewrite B5, B6, Udst, Unn in D. exact D.
Qed.
#[using="cs pbrk mo c g rg CR HK Hc Hs SC Hrg h OLD DST NN D0 DA NA N2 NL DC FRESH"] Lemma fresh_metas : forall b l k, In (b, l, k) (ld_metas L) -> dst + nn <= b \/ b + mmap_len l <= dst.
Proof.
  intros b l k Hin. pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (other_base b l (or_intror (ex_intro _ k Hin))) as NE.
  assert (HR : In (went b (mmap_len l)) (map_remove (vm_maps h) OLD)).
  { unfold map_remove. apply filter_In. split; [exact B4|]. destruct (bv_eqb (fst (went b (mmap_len l))) OLD) eqn:E; [| reflexivity].
    exfalso. apply bv_eqb_eq in E. pose proof (KL_ceil_lt63 _ _ _ HK). exact (went_ne_old b _ ltac:(lia) NE E). }
  pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ FRESH) HR) as D. rewrite B5, B6, Udst, Unn in D. exact D.
Qed.
#[using="L pbrk rg HK OLD DST NN D0 DA NA N2 NL DC FRESH"] Lemma fresh_resv : forall e, In e (vm_reserved h) -> dst + nn <= elo e \/ ehi e <= dst.
Proof.
  intros [e sz] He. pose proof (region_free_In _ _ _ _ _ FRESH (in_or_app _ _ _ (or_introl He))) as D. rewrite Udst, Unn in D. exact D.
Qed.
#[using="cs pbrk mo c g rg CR HK Hc Hs SC Hrg h OLD DST NN D0 DA NA N2 NL DC FRESH"] Lemma fresh_brk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> dst + nn <= b0 + PGSZ \/ b0 + l0 <= dst.
Proof.
  intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
  pose proof grp_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BD & _). specialize (BD b0 l0 E).
  assert (WC : wcov (map_remove (vm_maps h) OLD) (b0 + PGSZ) (b0 + l0)).
  { intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [| exact Hr]. eapply cover_not_old; [exact He| exact Hr|]. clear -BD Hz. unfold PGSZ in *. lia. }
  pose proof (wcov_rf_disj _ _ _ _ _ WC (region_free_app_r _ _ _ _ FRESH) ltac:(rewrite Unn; unfold PGSZ in *; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D.
  rewrite Udst, Unn in D. exact D.
Qed.

#[using="cs mo c g CR HK Hc Hs SC Hrg h OLD DST NN D0 DA NA N2 NL DC FRESH Hmi' Hh' Evm"] Lemma KL_remap : KL (lremap L rold dst nn) pbrk mo'.
Proof.
  pose proof grp_facts as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & _).
  pose proof old_entry as (_ & EL & EH & RON & FO). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl. pose proof Udst as Ud. pose proof Unn as Un.
  assert (NNM : mmap_len nn = nn) by (apply mmap_len_of_aligned; [unfold PGSZ in *; lia| unfold PGSZ in NA; exact NA]).
  pose proof (kl_distinct _ _ _ HK) as Kd.
  destruct (KStepK.g_remove_split rold (r_len rg) (ld_groups L) _ HIN Kd) as (g1 & g2 & Eg & Ezz).
  rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
  pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
  assert (Hg' : forall b l, In (b, l) (g_remove rold (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> rold /\ (b, l) <> (rold, r_len rg)).
  { intros b l H. rewrite Ezz in H. assert (NE : b <> rold).
    { intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (rold, l). split; [reflexivity| exact H]. }
    rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|]. split; [exact NE| congruence]. }
  assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> rold).
  { intros b l k H. apply (other_base b l). right. exists k. exact H. }
  assert (Hph' : phase_inv (ld_brk (lremap L rold dst nn)) (lremap L rold dst nn) pbrk mo').
  { eapply phase_quiet; [exact HK| exact HQ| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]. }
  assert (KEEP : forall e, In e (vm_maps h) -> fst e <> OLD -> In e (vm_maps (m_vmmaps mo'))).
  { intros e He Hne. rewrite Evm. cbn. right. unfold map_remove. apply filter_In. split; [exact He|].
    destruct (bv_eqb (fst e) OLD) eqn:E; [| reflexivity]. apply bv_eqb_eq in E. contradiction. }
  assert (NEW : In (went dst nn) (vm_maps (m_vmmaps mo'))) by (rewrite Evm; cbn; left; reflexivity).
  pose proof HK as HK0. kl_open HK.
  constructor; try exact Hph'; rewrite ?Evm; cbn [mremap_maps_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk lremap set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto; try kl_ceil_close Kceil.
  -   apply vmwf_cons; [apply vmwf_remove; exact Kwf| rewrite Ud, Un; lia| eapply region_free_app_r; exact FRESH].
  -   intros b l [E|Hin].
    + injection E as <- <-. rewrite NNM. split; [unfold LEN_MAX, PGSZ in *; lia|]. split; [lia|]. split; [exact DA|]. split; [lia|].
      split; [left; reflexivity|]. unfold brk_disj. cbn. exact fresh_brk.
    + destruct (Hg' b l Hin) as (Hin1 & NE & _). specialize (Kgr b l Hin1). destruct Kgr as (G1 & G2 & G3 & G4 & G5 & G6).
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [| exact G6].
      right. unfold map_remove. apply filter_In. split; [exact G5|]. destruct (bv_eqb _ OLD) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. pose proof (mmap_len_ge l ltac:(lia)). exact (went_ne_old b _ ltac:(lia) NE E).
  -   intros b l k Hin. pose proof (Hm' b l k Hin) as NE. specialize (Kme b l k Hin). destruct Kme as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [| split; [exact G8| exact G9]].
    right. unfold map_remove. apply filter_In. split; [exact G7|]. destruct (bv_eqb _ OLD) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. pose proof (mmap_len_ge l ltac:(lia)). exact (went_ne_old b _ ltac:(lia) NE E).
  -   cbn [map fst app]. rewrite Ezz, map_app, <- app_assoc. constructor; [| exact Kd1].
    intros Hin. apply in_app_or in Hin as [Hin|Hin]; [| apply in_app_or in Hin as [Hin|Hin]].
    + apply in_map_iff in Hin as ([b l] & E & Hin). cbn in E. subst b.
      assert (Hin' : In (dst, l) (g_remove rold (ld_groups L))) by (rewrite Ezz; apply in_or_app; left; exact Hin).
      destruct (Hg' dst l Hin') as (Hin1 & _ & NE1). pose proof (fresh_groups dst l Hin1 NE1). pose proof (went_In_bounds _ _ _ dst l HK0 (or_introl Hin1)) as (_ & B2 & _). lia.
    + apply in_map_iff in Hin as ([b l] & E & Hin). cbn in E. subst b.
      assert (Hin' : In (dst, l) (g_remove rold (ld_groups L))) by (rewrite Ezz; apply in_or_app; right; exact Hin).
      destruct (Hg' dst l Hin') as (Hin1 & _ & NE1). pose proof (fresh_groups dst l Hin1 NE1). pose proof (went_In_bounds _ _ _ dst l HK0 (or_introl Hin1)) as (_ & B2 & _). lia.
    + apply in_map_iff in Hin as ([[b l] k] & E & Hin). cbn in E. subst b.
      pose proof (fresh_metas dst l k Hin). pose proof (went_In_bounds _ _ _ dst l HK0 (or_intror (ex_intro _ k Hin))) as (_ & B2 & _). lia.
  -   intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov).
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
    intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [| exact Hr]. right.
    eapply cover_not_old; [exact He| exact Hr|]. specialize (BD b0 l0 E). clear -BD Hz. unfold PGSZ in *. lia.
  -   intros b l [E|Hin]; [| destruct (Hg' b l Hin) as (Hin1 & _); exact (Kgrv b l Hin1)].
    injection E as <- <-. rewrite NNM. exact fresh_resv.
  -   intros e He. destruct (Kna e He) as (NZ & e' & He' & U1 & U2 & U3). split; [exact NZ|]. exists e'.
    assert (NE' : fst e' <> OLD). { intros E. apply (U3 rold (r_len rg) HIN). unfold elo. rewrite E. unfold OLD. apply unsigned_lit. lia. }
    split; [right; unfold map_remove; apply filter_In; split; [exact He'|]; destruct (bv_eqb _ OLD) eqn:E; [apply bv_eqb_eq in E; contradiction| reflexivity]|].
    split; [exact U1|]. split; [exact U2|].
    intros b l [E|Hin]; [| destruct (Hg' b l Hin) as (Hin1 & _); exact (U3 b l Hin1)].
    injection E as <- <-. intros EQ.
    assert (HR : In e' (map_remove (vm_maps h) OLD)).
    { unfold map_remove. apply filter_In. split; [exact He'|]. destruct (bv_eqb _ OLD) eqn:E; [apply bv_eqb_eq in E; contradiction| reflexivity]. }
    pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ FRESH) HR) as D. rewrite Ud, Un in D.
    pose proof (proj1 Kwf e' He'). lia.
Qed.

#[using="L pbrk mo g rg CR HK Hc Hs SC Hrg h OLD DST NN D0 DA NA N2 NL DC FRESH"] Lemma cremap_ok_fresh : cremap_ok cs c dst nn.
Proof.
  pose proof grp_facts as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & _).
  destruct sim_facts as (st & BL & LS & off & n & E & INV & Hk & LIVE).
  split; [exact D0|]. split; [exact DA|]. split; [exact NA|]. split; [exact N2|]. split; [exact NL|]. split; [rewrite <- ceil_fact; exact DC|]. split.
  -   rewrite <- RSV, (kl_resv _ _ _ HK). unfold ranges_free. apply List.forallb_forall. intros [b m] Hin.
    apply in_map_iff in Hin as ([e sz] & EW & He). unfold wwZ in EW. cbn [fst snd] in EW. injection EW as <- <-. cbn [fst snd].
    pose proof (fresh_resv _ He) as D. unfold elo, ehi in D. cbn [fst snd] in D. unfold iv_disjoint.
    destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r].
  -   intros rid2 r2 Hr2 NE.
    assert (HLR : In (region_live_range r2) (live_ranges cs)).
    { unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid2, r2). split; [reflexivity|].
      apply (proj2 (In_map_to_list_regions _ _ _)). exact Hr2. }
    pose proof (proj1 INV) as IR. rewrite <- E in HLR. change (live_ranges (strip st)) with (live_ranges st) in HLR.
    apply (proj2 (lranges_iff x0 st L IR _)) in HLR.

    assert (NEQ : region_live_range r2 <> (rold, ron)).
    { intros EQ. pose proof Hrg as Hrg1. pose proof Hr2 as Hr21. rewrite <- E in Hrg1, Hr21. cbn [s_regions strip] in Hrg1, Hr21.
      pose proof (ir_disj _ _ _ IR rid2 (fst c) r2 rg Hr21 Hrg1 NE) as D. rewrite EQ in D.
      unfold region_live_range in D. rewrite K' in D. fold rold ron in D. pose proof old_entry as (_ & _ & _ & RON & _). lia. }
    destruct (region_live_range r2) as [b2 l2] eqn:ER.
    apply In_lranges in HLR as [H|[(b & l & H & E2)|[(b & l & k & H & E2)|(b & l & H & E2)]]].
    + rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & EW & He). unfold wwZ in EW. cbn [fst snd] in EW. injection EW as <- <-.
      pose proof (fresh_resv _ He) as D. unfold elo, ehi in D. cbn [fst snd] in D. lia.
    + injection E2 as -> ->. assert (NEP : (b, l) <> (rold, r_len rg)) by (intros EE; injection EE as -> ->; apply NEQ; reflexivity).
      pose proof (fresh_groups b l H NEP) as D. unfold mmap_len in D. rewrite <- round_up_pg_eq in D. lia.
    + injection E2 as -> ->. pose proof (fresh_metas b l k H) as D. unfold mmap_len in D. rewrite <- round_up_pg_eq in D. lia.
    + injection E2 as -> ->. pose proof (fresh_brk b l H) as D. pose proof (kl_brkreg _ _ _ HK b l H) as (_ & _ & R3 & R4 & _).
      rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). lia.
Qed.
End FRESH.

#[using="cs L pbrk c g CR HK Hc Hs SC Hrg"] Lemma fresh_same : forall nn, 0 < nn <= ron -> region_free (vm_reserved h ++ map_remove (vm_maps h) OLD) OLD (Z_to_bv 64 nn) = true.
Proof.
  intros nn Hnn. pose proof grp_facts as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & _).
  pose proof old_entry as (_ & EL & EH & RON & FO). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
  assert (Uo : bv_unsigned OLD = rold) by (unfold OLD; apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 nn) = nn) by (apply unsigned_lit; lia).
  apply region_free_of_disj. rewrite Uo, Un. intros e He. apply in_app_or in He as [He|He].
  - pose proof (kl_grp_resv _ _ _ HK _ _ HIN e He) as D. rewrite EM in D. lia.
  - unfold map_remove in He. apply filter_In in He as [He Hne]. apply negb_true_iff in Hne.
    destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He HM) as [->|D]; [rewrite FO, bv_eqb_refl in Hne; discriminate|].
    unfold edisj in D. rewrite EL, EH in D. lia.
Qed.

#[using="cs c g CR HK Hc Hs SC Hrg h OLD"] Lemma KL_same : KL (lremap L rold rold ron) pbrk mo.
Proof.
  pose proof grp_facts as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & _).
  pose proof old_entry as (_ & EL & EH & RON & FO). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
  assert (NNM : mmap_len ron = ron) by (rewrite <- EM; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  pose proof (kl_distinct _ _ _ HK) as Kd.
  destruct (KStepK.g_remove_split rold (r_len rg) (ld_groups L) _ HIN Kd) as (g1 & g2 & Eg & Ezz).
  assert (Hg' : forall b l, In (b, l) (g_remove rold (ld_groups L)) -> In (b, l) (ld_groups L)).
  { intros b l H. rewrite Ezz in H. rewrite Eg. apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]. }
  assert (Hph' : phase_inv (ld_brk (lremap L rold rold ron)) (lremap L rold rold ron) pbrk mo).
  { eapply phase_quiet; [exact HK| exact HQ| reflexivity| reflexivity| reflexivity| reflexivity]. }
  pose proof HK as HK0. kl_open HK.
  constructor; try exact Hph'; cbn [lremap set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto.
  - intros b l [E|Hin]; [| exact (Kgr b l (Hg' b l Hin))]. injection E as <- <-. rewrite NNM.
    split; [unfold LEN_MAX in *; lia|]. split; [lia|]. split; [exact RA|]. split; [lia|]. split; [exact HM| exact BD].
  - cbn [map fst app]. rewrite Ezz, map_app. rewrite Eg, map_app in Kd. cbn [map fst] in Kd.
    eapply Permutation_NoDup; [| exact Kd]. rewrite <- !app_assoc. apply Permutation_sym. apply Permutation_middle.
  - intros b l [E|Hin]; [| exact (Kgrv b l (Hg' b l Hin))]. injection E as <- <-. rewrite NNM. intros e He. pose proof (Kgrv _ _ HIN e He) as D. rewrite EM in D. exact D.
  - intros e He. destruct (Kna e He) as (NZ & e' & He' & U1 & U2 & U3). split; [exact NZ|]. exists e'. split; [exact He'|]. split; [exact U1|]. split; [exact U2|].
    intros b l [E|Hin]; [| exact (U3 b l (Hg' b l Hin))]. injection E as <- <-. exact (U3 _ _ HIN).
Qed.

#[using="cs L pbrk c g CR HK Hc Hs SC Hrg h OLD"] Lemma mremap_nsafe : forall nn, 0 < nn -> nsafe (NMremap rold ron nn) mo.
Proof.
  intros nn Hnn. pose proof grp_facts as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & _).
  pose proof old_entry as (_ & EL & EH & RON & FO). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
  assert (Uo : bv_unsigned OLD = rold) by (unfold OLD; apply unsigned_lit; lia).
  assert (RONA : ron mod 4096 = 0) by (rewrite <- EM; apply mmap_len_aligned).
  unfold nsafe. cbv zeta. fold OLD h. rewrite (unsigned_lit ron) by lia.
  replace (page_round_up_Z ron) with ron by (symmetry; rewrite <- round_up_pg_eq; apply round_up_pg_aligned; exact RONA).
  assert (Ur : bv_unsigned (Z_to_bv 64 ron) = ron) by (apply unsigned_lit; lia).
  unfold mremap_source_b. fold h. rewrite Uo.
  rewrite (proj2 (Z.leb_le _ _)) by (pose proof (kl_ceil _ _ _ HK) as KC; change (m_vmmaps mo) with h in KC; rewrite <- ?KC; lia). cbn [andb].
  rewrite (region_free_of_disj (vm_reserved h)).
  2:{ rewrite Uo, Ur. intros e He. pose proof (kl_grp_resv _ _ _ HK _ _ HIN e He) as D. rewrite EM in D. exact D. }
  rewrite (region_free_of_disj (vm_noaccess h)).
  2:{ rewrite Uo, Ur. intros e He. destruct (kl_noacc _ _ _ HK e He) as (NZ & e' & He' & U1 & U2 & U3).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He' HM) as [->|D]; [exfalso; apply (U3 _ _ HIN); exact EL|].
      unfold edisj in D. rewrite EL, EH in D. lia. }
  replace (map_has (vm_maps h) OLD (Z_to_bv 64 ron)) with true; [reflexivity|]. symmetry.
  unfold map_has. apply existsb_exists. exists (went rold ron). split; [exact HM|]. unfold went, wz. fold OLD. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma Forall_covered_app_l : forall l1 l2 avoid, Forall (covered l1) avoid -> Forall (covered (l1 ++ l2)) avoid.
Proof.
  intros l1 l2 avoid H. eapply Forall_impl; [| exact H]. intros iv (e & sz & Hin & A & B). exists e, sz. split; [apply in_or_app; left; exact Hin| auto].
Qed.

#[using="g CR HK Hc Hs SC Hrg OLD"] Theorem mremap_kstep : forall nn avoid rsp mo' evs,
  nn mod PGSZ = 0 -> 2 * PGSZ <= nn -> nn < LEN_MAX ->
  Forall (pcovered (vm_reserved h)) avoid ->
  nstep (NMremap rold ron nn) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\ minv mo' /\ m_halted mo' = None /\
  exists a, dec_mremap rold ron nn avoid rsp = Some a /\
  match a with
  | MrErr _ => KL L pbrk mo'
  | MrSame => (ron = nn /\ KL L pbrk mo') \/ (ron <> nn /\ rold + nn <= ld_ceil L /\ KL (lremap L rold rold nn) pbrk mo' /\ cremap_ok cs c rold nn)
  | MrMoved dst => ron < nn /\ KL (lremap L rold dst nn) pbrk mo' /\ cremap_ok cs c dst nn
  end.
Proof.
  intros nn avoid rsp mo' evs NA N2 NL COV Hst.
  pose proof grp_facts as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & _).
  pose proof old_entry as (_ & EL & EH & RON & FO). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
  pose proof (mmap_len_pos_pg (r_len rg) ltac:(lia)) as RPG. rewrite EM in RPG.
  assert (RONM : mmap_len ron = ron) by (rewrite <- EM at 1; rewrite <- EM; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  assert (NNM : mmap_len nn = nn) by (apply mmap_len_of_aligned; [unfold PGSZ in *; lia| unfold PGSZ in NA; exact NA]).
  pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
  pose proof (nstep_dec_mremap2 rold ron nn avoid mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(lia) ltac:(unfold LEN_MAX, PGSZ in *; lia)
                (kl_minv _ _ _ HK) (Forall_pcovered_app_l _ _ _ COV) Hst) as (Eevs & FR & x & Hd & Hx).
  pose proof (kl_ceil _ _ _ HK) as KC. change (m_vmmaps mo) with h in KC.
  cbv zeta in Hx. rewrite RONM, NNM in Hx. fold OLD in Hx.
  split; [exact Eevs|]. split; [exact FR|]. split; [exact Hmi'|]. split; [exact Hh'|]. exists x. split; [exact Hd|].
  destruct x as [e| |dst].
  - destruct Hx as (_ & -> & _). exact HK.
  - destruct Hx as [[E ->]|[[LT Emo]|(LT & GB & Emo)]].
    + left. auto.
    + right. assert (EV : m_vmmaps mo' = mremap_maps_next h OLD OLD (Z_to_bv 64 nn)) by (rewrite Emo; apply m_vmmaps_mremap_model_next).
      pose proof (fresh_same nn ltac:(unfold PGSZ in *; lia)) as FRESH.
      split; [lia|]. split; [lia|]. split.
      * exact (KL_remap rold nn mo' R0 RA NA N2 NL ltac:(lia) FRESH Hmi' Hh' EV).
      * exact (cremap_ok_fresh rold nn R0 RA NA N2 NL ltac:(lia) FRESH).
    + right. assert (EV : m_vmmaps mo' = mremap_maps_next h OLD OLD (Z_to_bv 64 nn)) by (rewrite Emo; apply m_vmmaps_mremap_model_next).
      unfold mremap_inplace_grow_b in GB. cbv zeta in GB. fold h in GB. apply andb_prop in GB as [GB _]. apply andb_prop in GB as [G1 FRESH].
      apply Z.leb_le in G1. unfold OLD in G1 at 1. rewrite unsigned_lit in G1 by lia. rewrite <- KC in G1.
      split; [lia|]. split; [exact G1|]. split.
      * exact (KL_remap rold nn mo' R0 RA NA N2 NL G1 FRESH Hmi' Hh' EV).
      * exact (cremap_ok_fresh rold nn R0 RA NA N2 NL G1 FRESH).
  - destruct Hx as (LT & FB & Emo).
    assert (EV : m_vmmaps mo' = mremap_maps_next h OLD (Z_to_bv 64 dst) (Z_to_bv 64 nn)) by (rewrite Emo; apply m_vmmaps_mremap_model_next).
    unfold mremap_fresh_b in FB. cbv zeta in FB. fold h in FB.
    apply andb_prop in FB as [FB _]. apply andb_prop in FB as [FB P5].
    apply andb_prop in FB as [FB P4]. apply andb_prop in FB as [FB P3]. apply andb_prop in FB as [_ P2].
    apply Z.leb_le in P4. apply Z.ltb_lt in P3. apply Z.eqb_eq in P2. rewrite page_size_eq in P2. rewrite <- KC in P4.
    pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 dst)) as DR.
    assert (Ud : bv_unsigned (Z_to_bv 64 dst) = dst).
    {
      apply dec_mremap_Some in Hd. cbv zeta in Hd. destruct Hd as (_ & (DA0 & D00 & DC0 & _) & _). unfold alloc_ceiling_max in DC0. apply unsigned_lit. unfold mmap_len in DC0. pose proof (Decode.mmap_len_bound nn ltac:(unfold PGSZ in *; lia)). unfold mmap_len in *. lia. }
    rewrite Ud in P2, P3, P4. pose proof (region_free_remove _ _ OLD _ _ P5) as FRESH.
    split; [exact LT|]. split.
    + exact (KL_remap dst nn mo' P3 P2 NA N2 NL P4 FRESH Hmi' Hh' EV).
    + exact (cremap_ok_fresh dst nn P3 P2 NA N2 NL P4 FRESH).
Qed.
End MREMAP.

Section OWNED.
Variables (X : list bptr) (G : PState -> Model -> Prop) (s : PState) (mo : Model) (c : cptr) (off : Z) (g : aptr) (rg : region).
Hypothesis HO : OWN X G s mo.
Hypothesis HG : frame_ok G.
Hypothesis HX : In (c, off) X.
Hypothesis Hs : s_slots (ps_m s) !! c = Some (g, 0).
Hypothesis SC : m_sizeclass (MR (ps_m s) g) = 63.
Hypothesis Hrg : s_regions (ps_m s) !! fst c = Some rg.

#[using="off HO HX"] Lemma own_open : exists L, creach2 (ps_m s) L /\ KL L (ps_brk s) mo /\ incl (map fst X) (ld_live L) /\ In c (ld_live L)
  /\ List.NoDup (map fst X) /\ G s mo.
Proof.
  destruct HO as [(L & CR & HK & HI) [ND HGs]]. exists L. split; [exact CR|]. split; [exact HK|]. split; [exact HI|]. split; [| split; [exact ND| exact HGs]].
  apply HI. apply in_map_iff. exists (c, off). auto.
Qed.

#[using="X G off HO HX Hs SC Hrg"] Theorem own_group_facts : r_kind rg = RKGroup /\ 0 < (rold rg) /\ (rold rg) mod PGSZ = 0 /\ 0 < r_len rg /\ (rold rg) + (ron rg) <= s_ceil (ps_m s)
  /\ m_maplen (MR (ps_m s) g) * 4096 = (ron rg) /\ PGSZ <= (ron rg) /\ (ron rg) mod PGSZ = 0 /\ c = (fst c, 16)
  /\ (forall b l, In (b, l) (s_reserved (ps_m s)) -> (rold rg) + (ron rg) <= b \/ b + l <= (rold rg))
  /\ map wwZ (vm_reserved (m_vmmaps mo)) = s_reserved (ps_m s)
  /\ minv mo /\ m_halted mo = None.
Proof.
  destruct own_open as (L & CR & HK & HI & Hc & ND & HGs).
  pose proof (grp_facts (ps_m s) L (ps_brk s) mo c g rg CR HK Hc Hs SC Hrg) as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & EC).
  pose proof (mmap_len_pos_pg (r_len rg) ltac:(lia)) as RPG. rewrite EM in RPG.
  split; [exact K'|]. split; [exact R0|]. split; [exact RA|]. split; [lia|]. split; [rewrite <- (ceil_fact (ps_m s) L c g rg CR Hc Hs SC Hrg); exact RC|]. split; [exact EON|]. split; [exact RPG|].
  split; [rewrite <- EM; unfold PGSZ; apply mmap_len_aligned|]. split; [exact EC|]. split; [| split; [rewrite <- RSV; symmetry; exact (kl_resv _ _ _ HK)| split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]]].
  intros b l Hin. rewrite <- RSV, (kl_resv _ _ _ HK) in Hin. apply in_map_iff in Hin as ([e sz] & EW & He). unfold wwZ in EW. cbn [fst snd] in EW. injection EW as <- <-.
  pose proof (kl_grp_resv _ _ _ HK _ _ HIN _ He) as D. rewrite EM in D. unfold elo, ehi in D. cbn [fst snd] in D. exact D.
Qed.

#[using="X G s c off g HO HX Hs SC Hrg"] Theorem own_mremap_nsafe : forall nn, 0 < nn -> nsafe (NMremap (rold rg) (ron rg) nn) mo.
Proof.
  intros nn Hnn. destruct own_open as (L & CR & HK & HI & Hc & ND & HGs).
  exact (mremap_nsafe (ps_m s) L (ps_brk s) mo c g rg CR HK Hc Hs SC Hrg nn Hnn).
Qed.

#[using="HG Hs SC Hrg"] Lemma own_rebase : forall L dst nn mo',
  creach2 (ps_m s) L -> In c (ld_live L) -> incl (map fst X) (ld_live L) -> List.NoDup (map fst X) ->
  cremap_ok (ps_m s) c dst nn -> KL (lremap L (rold rg) dst nn) (ps_brk s) mo' -> G s mo' ->
  OWN X G (set_m (cremap (ps_m s) (fst c) g dst nn) s) mo'.
Proof.
  intros L dst nn mo' CR Hc HI ND OK HK' HGs'. split; [| split; [exact ND|]].
  - exists (set_live (c :: ap_remove c (ld_live L)) (lremap L (rold rg) dst nn)). split; [| split].
    + cbn [ps_m set_m]. exact (c2_remap _ _ _ _ _ _ _ CR Hc Hs SC Hrg OK).
    + cbn [ps_brk set_m]. apply KL_set_live. exact HK'.
    + intros x Hx. cbn. destruct (MI_Kit.aptr_eqb_spec x c) as [->|NE]; [left; reflexivity| right]. apply in_ap_remove; [apply HI; exact Hx| exact NE].
  - eapply HG; [| | apply mm_frame_refl| exact HGs']; reflexivity.
Qed.

#[using="off HO HG HX Hs SC Hrg"] Theorem own_mremap : forall nn avoid rsp mo' evs,
  nn mod PGSZ = 0 -> 2 * PGSZ <= nn -> nn < LEN_MAX ->
  Forall (pcovered (vm_reserved (m_vmmaps mo))) avoid ->
  nstep (NMremap (rold rg) (ron rg) nn) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\ minv mo' /\ m_halted mo' = None /\
  exists a, dec_mremap (rold rg) (ron rg) nn avoid rsp = Some a /\
  match a with
  | MrErr _ => OWN X G s mo'
  | MrSame => ((ron rg) = nn /\ OWN X G s mo')
      \/ ((ron rg) <> nn /\ (rold rg) + nn <= s_ceil (ps_m s) /\ cremap_ok (ps_m s) c (rold rg) nn /\ OWN X G (set_m (cremap (ps_m s) (fst c) g (rold rg) nn) s) mo')
  | MrMoved dst => (ron rg) < nn /\ cremap_ok (ps_m s) c dst nn /\ OWN X G (set_m (cremap (ps_m s) (fst c) g dst nn) s) mo'
  end.
Proof.
  intros nn avoid rsp mo' evs NA N2 NL COV Hst. destruct own_open as (L & CR & HK & HI & Hc & ND & HGs).
  destruct (mremap_kstep (ps_m s) L (ps_brk s) mo c g rg CR HK Hc Hs SC Hrg nn avoid rsp mo' evs NA N2 NL COV Hst) as (Eevs & FR & Hmi' & Hh' & a & Hd & Ha).
  assert (HGs' : G s mo') by (eapply HG; [reflexivity| reflexivity| exact FR| exact HGs]).
  assert (OWNK : forall mo1, KL L (ps_brk s) mo1 -> G s mo1 -> OWN X G s mo1).
  { intros mo1 HK1 HG1. split; [exists L; auto| auto]. }
  split; [exact Eevs|]. split; [exact FR|]. split; [exact Hmi'|]. split; [exact Hh'|]. exists a. split; [exact Hd|].
  destruct a as [e| |dst].
  - exact (OWNK _ Ha HGs').
  - destruct Ha as [[E HK']|(NE & DC & HK' & OK)]; [left; split; [exact E| exact (OWNK _ HK' HGs')]| right].
    split; [exact NE|]. split; [rewrite <- (ceil_fact (ps_m s) L c g rg CR Hc Hs SC Hrg); exact DC|]. split; [exact OK|]. exact (own_rebase L (rold rg) nn mo' CR Hc HI ND OK HK' HGs').
  - destruct Ha as (LT & HK' & OK). split; [exact LT|]. split; [exact OK|]. exact (own_rebase L dst nn mo' CR Hc HI ND OK HK' HGs').
Qed.

#[using="off HO HG HX Hs SC Hrg"] Theorem own_remap_inplace : 2 * PGSZ <= (ron rg) ->
  cremap_ok (ps_m s) c (rold rg) (ron rg) /\ OWN X G (set_m (cremap (ps_m s) (fst c) g (rold rg) (ron rg)) s) mo.
Proof.
  intros R2. destruct own_open as (L & CR & HK & HI & Hc & ND & HGs).
  pose proof (grp_facts (ps_m s) L (ps_brk s) mo c g rg CR HK Hc Hs SC Hrg) as (K' & HIN & LN & R0 & RA & RC & EON & HM & HQ & EM & BD & RSV & EC).
  pose proof (mmap_len_pos_pg (r_len rg) ltac:(lia)) as RPG. rewrite EM in RPG. pose proof (KL_ceil_lt63 _ _ _ HK).
  assert (RONA : (ron rg) mod PGSZ = 0) by (rewrite <- EM; unfold PGSZ; apply mmap_len_aligned).
  assert (RL : (ron rg) < LEN_MAX) by (unfold LEN_MAX; lia).
  pose proof (fresh_same (ps_m s) L (ps_brk s) mo c g rg CR HK Hc Hs SC Hrg (ron rg) ltac:(lia)) as FRESH.
  pose proof (cremap_ok_fresh (ps_m s) L (ps_brk s) mo c g rg CR HK Hc Hs SC Hrg (rold rg) (ron rg) R0 RA RONA R2 RL RC FRESH) as OK.
  split; [exact OK|]. apply (own_rebase L (rold rg) (ron rg) mo CR Hc HI ND OK); [| exact HGs].
  exact (KL_same (ps_m s) L (ps_brk s) mo c g rg CR HK Hc Hs SC Hrg).
Qed.
End OWNED.
