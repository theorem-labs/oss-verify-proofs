(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesMat NodesCfg Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe MSil STree Malloc MallocCtrl Realloc ReallocProto RawAlloc
  KArith KInv KLink KStep KStepX KLive KArena
  MI_Tree MI_Inv MI_Kit MI_Geom MI_Ext MI_WFree MI_WRealloc MI_WRealloc2 MI_Sim MI_Contracts MI_LedgerAgree
  LB_Kernel LB_Embed LB_Tables LB_Inv LB_Sum LB_Bound LB_Tree LB_StmtA LB_WFree LB_Raw LB_WMalloc LB_Alloc LB_TreeX LB_EmbedX LB_Realloc
  KLiveCfg MSuccIface MSucc MLen MSuccTall MSuccEmbed MSuccRaw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks MallocHINV MallocFacts_A MallocFacts_inv MallocFacts_inv2 MallocOracle MallocKown MallocRealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sig (b : block) : cptr * Z := (blk_slot b, blk_size b).

Lemma CORR_map_sig st LB BL : CORR st LB BL -> map sig LB = map bs BL.
Proof.
  induction 1 as [|b k LB BL [C1 [C2 _]] _ IH]; [reflexivity|]. cbn [map]. rewrite IH.
  unfold sig, bs. rewrite C1, C2. reflexivity.
Qed.

Lemma zcount_bs (p : cptr * Z -> bool) BL : zcount (fun k => p (bs k)) BL = zcount p (map bs BL).
Proof. induction BL as [|k BL IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

Lemma LR_bs BL c : LR BL c = zcount (fun sb : cptr * Z => negb (MMAP_THRESHOLD <=? snd sb) && (size_to_class (snd sb) =? c)) (map bs BL).
Proof. unfold LR, isbig. rewrite <- zcount_bs. apply zcount_ext. intros k _. reflexivity. Qed.
Lemma n63_bs BL : n63 BL = zcount (fun sb : cptr * Z => MMAP_THRESHOLD <=? snd sb) (map bs BL).
Proof. unfold n63, isbig. rewrite <- zcount_bs. reflexivity. Qed.

Lemma SINV_bs_perm X st BL BL' : Permutation (map bs BL') (map bs BL) -> SINV X st BL' -> SINV X st BL.
Proof.
  intros HP S. destruct S. constructor; auto.
  - intros k Hk. assert (Hin : In (bs k) (map bs BL')) by (eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_map; exact Hk]).
    apply in_map_iff in Hin as (k' & E & Hk'). destruct (qb_cls k' Hk') as (m & i & Hs & C1 & C2).
    unfold bs in E. injection E as E1 E2. rewrite <- E1, <- E2. exists m, i. auto.
  - intros b m ai Hg C. pose proof (qg_63 _ _ _ Hg C) as Hin.
    replace (map bslot BL) with (map fst (map bs BL)) by (rewrite map_map; reflexivity).
    replace (map bslot BL') with (map fst (map bs BL')) in Hin by (rewrite map_map; reflexivity).
    eapply Permutation_in; [apply Permutation_map; exact HP| exact Hin].
Qed.

Lemma AQ_bs_perm st BL BL' P : Permutation (map bs BL') (map bs BL) -> AQ st BL' P -> AQ st BL P.
Proof.
  intros HP A. destruct A as [A1 A2 A3 A4 A5 A6]. constructor; auto.
  - intros c Hc. rewrite LR_bs, <- (zcount_perm _ _ _ HP), <- LR_bs. exact (A1 c Hc).
  - rewrite n63_bs, <- (zcount_perm _ _ _ HP), <- n63_bs. exact A3.
  - unfold zlen in *. rewrite <- (length_map bs BL), <- (Permutation_length HP), length_map. exact A6.
Qed.

Lemma gm_agree L L' : ledger_agree L L' -> gm L' = gm L /\ BB L' = BB L.
Proof.
  intros (Er & Pg & Pm & Ebr & Ebk). split.
  - unfold gm. change (fold_right Z.add 0 ?l) with (zsum l).
    fold (zsum (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L))).
    fold (zsum (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L))).
    fold (zsum (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L'))).
    rewrite (zsum_map_perm _ _ _ Pg), (zsum_map_perm _ _ _ Pm). reflexivity.
  - unfold BB. rewrite Ebk, Ebr. reflexivity.
Qed.

Lemma LI_agree L L' mo : ledger_agree L L' -> LI L mo -> LI L' mo.
Proof. intros HA H. unfold LI in *. destruct (gm_agree L L' HA) as [E1 E2]. rewrite E1, E2. exact H. Qed.

(* [comment removed for export] *)
Lemma bs_remove_perm BL (k : blk) : NoDup (map bslot BL) -> In k BL ->
  Permutation (map bs BL) (bs k :: map bs (bl_remove (bslot k) BL)).
Proof.
  induction BL as [|b BL IH]; intros ND Hin; [destruct Hin|].
  cbn [map] in ND. apply list.NoDup_cons in ND as [N1 N2]. cbn [bl_remove map].
  destruct Hin as [<-|Hin]; [rewrite aptr_eqb_refl; apply Permutation_refl|].
  destruct (aptr_eqb_spec (bslot b) (bslot k)) as [E|NE].
  - exfalso. apply N1. rewrite E. apply list_elem_of_In. apply in_map. exact Hin.
  - cbn [map]. etransitivity; [apply perm_skip; apply (IH N2 Hin)|]. apply perm_swap.
Qed.

(* [comment removed for export] *)
Lemma QI_transport G resv st LB0 s mo X P :
  KOWN G s mo -> strip st = ps_m s -> HINV_from resv st (ps_brk s) LB0 ->
  Permutation (map xs X) (map sig LB0) -> QI X P s mo ->
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ CORR st LB0 BL /\ KL L (ps_brk s) mo
    /\ SINV x0 st BL /\ AQ st BL P /\ LI L mo /\ Permutation (map xs X) (map bs BL) /\ PHI P + R63 BL <= LBUDGET.
Proof.
  intros HO Es HH HX [(st' & L' & BL' & LS' & E' & INV' & SI' & HAQ' & HK' & HLI' & HP' & HLV') HB].
  destruct (KL_of_HINV _ _ _ _ _ _ HO Es HH) as (L & LS & BL & INV & LIVE & RESV & SEC & CR & HK).
  assert (PX : Permutation (map xs X) (map bs BL)) by (rewrite <- (CORR_map_sig _ _ _ CR); exact HX).
  assert (PB : Permutation (map bs BL') (map bs BL)) by (etransitivity; [apply Permutation_sym; exact HP'| exact PX]).
  assert (CE : ctrl_eq st' st) by (apply ctrl_eq_strip; rewrite Es, E'; reflexivity).
  exists L, LS, BL. split; [exact INV|]. split; [exact LIVE|]. split; [exact CR|]. split; [exact HK|].
  split; [exact (SINV_bs_perm x0 st BL BL' PB (SINV_ctrl x0 st' st _ CE SI'))|].
  split; [exact (AQ_bs_perm st BL BL' P PB (AQ_ctrl st' st _ P CE HAQ'))|].
  split; [exact (LI_agree L' L mo (INVL_ledger_agree _ _ _ _ _ _ _ _ _ _ INV' INV ltac:(rewrite E', Es; reflexivity)) HLI')|].
  split; [exact PX|]. rewrite <- (R63X_eq _ _ PX). exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slotfit (st : mstate) (c : cptr) (off n : Z) : Prop :=
  exists m bm i, hosts st bm m /\ 0 <= i <= m_last_idx (MR st m) /\ c = (fst bm, sstart (MR st m) i)
    /\ s_groups st !! c = None /\ 0 <= off /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB.

Lemma slotfit_of_INVL X st L BL LS c off n : INVL X st L BL LS -> In ((c, off), n) BL -> slotfit st c off n.
Proof.
  intros INV Hk. destruct (block_facts X st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  exists m, bm, i. split; [exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)|].
  split; [exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_c _ _ _ _ _ _ _ _ _ _ _ BF)|].
  split; [exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF)|]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF).
  split; [lia|]. split; [exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF)| exact (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF)].
Qed.

Lemma MR_strip st st2 m : strip st2 = strip st -> MR st2 m = MR st m.
Proof. intros Es. unfold MR, get_meta_rec. apply (f_equal s_metas) in Es. cbn in Es. rewrite Es. reflexivity. Qed.

Lemma conc_strip st st2 p : strip st2 = strip st -> conc st2 p = conc st p.
Proof. intros Es. unfold conc, get_region. apply (f_equal s_regions) in Es. cbn in Es. rewrite Es. reflexivity. Qed.

Lemma slotfit_strip st st2 c off n : strip st2 = strip st -> slotfit st c off n -> slotfit st2 c off n.
Proof.
  intros Es (m & bm & i & Hm & Hi & Ec & NH & Ho & Hn & F).
  assert (Eg : s_groups st2 = s_groups st) by (apply (f_equal s_groups) in Es; cbn in Es; exact Es).
  exists m, bm, i. unfold hosts. rewrite (MR_strip st st2 m Es), Eg. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma slot_of_addr resv st LB (b' : block) c off n :
  AREACH_from resv st LB -> In b' LB -> slotfit st c off n ->
  blk_addr b' = conc st (aadd c (UNIT * off)) -> blk_slot b' = c.
Proof.
  intros AR Hb (m & bm & i & Hm & Hi & Ec & NH & Ho & Hn & F) Ha.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  pose proof (proj1 INV) as IR. pose proof (proj1 (proj2 (proj2 INV))) as IM.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) as IG. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) as IS.
  destruct (LB_geo x0 st L BL LS INV LB CR b' Hb) as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & _ & Ec2 & _ & Hm2 & Hi2 & Ecc2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & F2).
  destruct (group_in_region x0 st L BL LS INV bm m Hm) as (r & Hr & Kr & B0 & GE).
  destruct (group_in_region x0 st L BL LS INV bm2 m2 Hm2) as (r2' & Hr2' & _ & B02 & GE2). rewrite Hr2 in Hr2'. injection Hr2' as <-.
  assert (Ea : blk_addr b' = r_base r + sstart (MR st m) i + UNIT * off).
  { rewrite Ha, Ec. unfold conc, get_region, aadd. cbn [fst snd]. rewrite Hr. lia. }
  pose proof (sstart_succ st m i) as SS. pose proof (sstart_succ st m2 i2) as SS2.
  rewrite Ec2, Ecc2. rewrite Ecc2 in NH2. rewrite Ec in NH.
  destruct (N.eq_dec (fst bm) (fst bm2)) as [Ef|NEf].
  - rewrite Ef, Hr2 in Hr. injection Hr as ->.
    destruct (aptr_eq_dec m m2) as [Em|NEm]; [destruct (Z.eq_dec i i2) as [Ei|NEi]|].
    + subst m2 i2. rewrite Ec, Ef. reflexivity.
    + exfalso. destruct (sep_ext x0 st BL LS IM IG IS m2 bm2 i2 Hm2 Hi2 NH2 m bm i Hm Ef Hi ltac:(right; exact NEi) NH); unfold UNIT, IB in *; lia.
    + exfalso. destruct (sep_ext x0 st BL LS IM IG IS m2 bm2 i2 Hm2 Hi2 NH2 m bm i Hm Ef Hi ltac:(left; exact NEm) NH); unfold UNIT, IB in *; lia.
  - exfalso. pose proof (ir_disj _ _ _ IR _ _ _ _ Hr Hr2 NEf) as D. unfold region_live_range in D. rewrite Kr, Kr2 in D.
    pose proof (sstart_mono x0 st LS IG bm m 0 i Hm ltac:(lia)) as M0. pose proof (sstart0 x0 st LS IM bm m Hm) as Z0.
    pose proof (sstart_mono x0 st LS IG bm m (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)) as M1. rewrite <- gend_eq in M1.
    pose proof (sstart_mono x0 st LS IG bm2 m2 0 i2 Hm2 ltac:(lia)) as M02. pose proof (sstart0 x0 st LS IM bm2 m2 Hm2) as Z02.
    pose proof (sstart_mono x0 st LS IG bm2 m2 (i2 + 1) (m_last_idx (MR st m2) + 1) Hm2 ltac:(lia)) as M12. rewrite <- gend_eq in M12.
    unfold UNIT, IB in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pf_of_block st L BL LS LB0 (b : block) (pf : aptr) :
  INVL x0 st L BL LS -> ld_live L = map bslot BL -> CORR st LB0 BL -> In b LB0 ->
  fst pf = fst (blk_slot b) -> conc st pf = blk_addr b ->
  exists off, In ((blk_slot b, off), blk_size b) BL /\ pf = aadd (blk_slot b) (UNIT * off).
Proof.
  intros INV LIVE CR Hb Hfst Hconc.
  destruct (live_of_HINV _ _ _ _ _ _ INV LIVE CR Hb) as (off & n0 & Hk & Hin & Haddr & Hsz).
  destruct (MI_WRealloc2.blk_region _ _ _ _ _ _ INV Hk) as (rg & Hrg & _). cbn [bslot fst snd] in Hrg.
  exists off. rewrite Hsz. split; [exact Hk|].
  unfold conc, get_region in Hconc, Haddr. rewrite Hfst in Hconc. rewrite Hrg in Hconc, Haddr. rewrite Haddr in Hconc.
  apply injective_projections; unfold aadd; cbn [fst snd]; [exact Hfst| lia].
Qed.

Theorem raw_realloc_LQ : forall G resv st LB0 (b : block) (pb : bptr) X0 (pf : aptr) n (o : mem) s0 mo0 P B,
  frame_ok G -> KOWN G s0 mo0 -> strip st = ps_m s0 -> HINV_from resv st (ps_brk s0) LB0 ->
  In b LB0 -> fst pf = fst (blk_slot b) -> conc st pf = blk_addr b -> fst pb = blk_slot b ->
  0 <= n -> size_overflows n = false ->
  QI ((pb, blk_size b) :: X0) P s0 mo0 -> Permutation (map xs ((pb, blk_size b) :: X0)) (map sig LB0) ->
  ROOMX ((pb, blk_size b) :: X0) P n -> PHI P + R63X ((pb, blk_size b) :: X0) + bigb n <= B + 3 * PGSZ -> B + 3 * PGSZ <= LBUDGET ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_realloc o st pf n)
        (fun r s mo => match snd r with
           | Some q => exists c' off', q = aadd c' (UNIT * off')
                        /\ (forall p', fst p' = c' -> QI ((p', n) :: X0) P s mo)
                        /\ G s mo /\ ps_m s = strip (fst r) /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0
                        /\ slotfit (fst r) c' off' n
           | None => QI ((pb, blk_size b) :: X0) P s mo /\ G s mo /\ ps_m s = strip (fst r) /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0
           end).
Proof.
  intros G resv st LB0 b pb X0 pf n o s0 mo0 P B HG HO Es HH Hb Hfst Hconc Hpb Hn OV HQ HX HRX HB HBL.
  destruct (QI_transport G resv st LB0 s0 mo0 _ P HO Es HH HX HQ) as (L & LS & BL & INV & LIVE & CR & HK & SI & HAQ & HLI & PX & _).
  destruct (pf_of_block st L BL LS LB0 b pf INV LIVE CR Hb Hfst Hconc) as (off & Hk & ->).
  set (c := blk_slot b) in *. set (n0 := blk_size b) in *.
  pose proof (KOWN_G _ _ _ HO) as HGs.
  pose proof (R63X_eq _ _ PX) as R63E. pose proof (ROOMX_eq _ BL P n PX HRX) as HR.
  assert (HBB : PHI P + R63 BL + bigb n <= B + 3 * PGSZ) by lia.
  (* [comment removed for export] *)
  destruct (block_facts x0 (set_tick (N.succ (s_tick st)) st) L BL LS (m_INV0 st L BL LS INV) c off n0 Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof (realloc_fq_main st L BL LS c off n0 n P B INV Hk Hn OV SI HAQ HR HBB m bm i ai a ar ka BF) as FQ.
  pose proof (xqtree_of_full8 pans_mem pupd_mem pans_mem_range B _ L _ o FQ) as XQ.
  unfold raw_realloc. unfold xmrun.
  eapply mspec_bind.
  { eapply mspec_pre; [apply (xmembedL B _ _ G L s0 HG XQ)|]. intros s mo [-> ->]. auto. }
  intros [o' [st' q]]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hpth & HPost & HK' & HLI' & HG' & Hm & Hfa & Hso).
  eapply mspec_seq with (R := fun s mo => s = set_m (strip st') s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  cbn [snd fst] in HPost. unfold RPOSTQ in HPost. cbn [fst snd] in HPost |- *.
  pose proof (xcpath_live Hpth) as Hlive.
  assert (HG2 : G (set_m (strip st') s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  assert (ND : NoDup (map bslot BL)) by (exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
  destruct q as [q|].
  - destruct HPost as (c' & off' & LS' & Eq & Hoff' & INV' & SI' & AQ').
    exists c', off'. split; [exact Eq|]. split; [| cbn; repeat split; auto; exact (slotfit_of_INVL _ _ _ _ _ _ _ _ INV' (or_introl eq_refl))].
    intros p' Hp'. split.
    + exists st', (set_live (map bslot (((c', off'), n) :: bl_remove c BL)) L'), (((c', off'), n) :: bl_remove c BL), LS'. cbn [ps_m ps_brk set_m].
      split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. split; [exact SI'|]. split; [exact AQ'|].
      split; [apply KL_set_live; exact HK'|]. split; [unfold LI in *; rewrite gm_set_live, BB_set_live; exact HLI'|]. split; [| reflexivity].
      cbn [map xs bs fst snd]. unfold xs at 1, bs at 1. cbn [fst snd bslot bsize]. rewrite Hp'. apply perm_skip.
      pose proof (bs_remove_perm BL ((c, off), n0) ND Hk) as PR. cbn [bs bslot bsize fst snd] in PR.
      cbn [map] in PX. unfold xs at 1 in PX. cbn [fst snd] in PX. rewrite Hpb in PX. fold c n0 in PX.
      eapply Permutation_cons_inv. etransitivity; [exact PX| exact PR].
    + rewrite R63X_cons. rewrite R63X_cons in HB. pose proof (proj1 (bigb_le' n0 ltac:(pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF); lia))). lia.
  - destruct HPost as (LS' & INV' & SI' & AQ'). split; [| cbn; auto].
    split; [| rewrite R63E in *; pose proof (proj1 (bigb_le' n Hn)); lia].
    exists st', (set_live (map bslot BL) L'), BL, LS'. cbn [ps_m ps_brk set_m].
    split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. split; [exact SI'|]. split; [exact AQ'|].
    split; [apply KL_set_live; exact HK'|]. split; [unfold LI in *; rewrite gm_set_live, BB_set_live; exact HLI'|]. split; [exact PX| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section REALLOC.
Variables (G : PState -> Model -> Prop) (resv : list (Z * Z)) (st : mstate) (LB0 : list block) (b : block) (pb : bptr) (X0 : list (bptr * Z))
          (pf : aptr) (n : Z) (o : mem) (s : PState) (mo : Model).
Hypothesis HG : frame_ok G.
Hypothesis HO : KOWN G s mo.
Hypothesis Es : strip st = ps_m s.
Hypothesis HH : HINV_from resv st (ps_brk s) LB0.
Hypothesis Hb : In b LB0.
Hypothesis Hfst : fst pf = fst (blk_slot b).
Hypothesis Hconc : conc st pf = blk_addr b.
Hypothesis Hpb : fst pb = blk_slot b.
Hypothesis HX : Permutation (map xs ((pb, blk_size b) :: X0)) (map sig LB0).
Hypothesis HE : HEADc ((pb, blk_size b) :: X0) s mo.
(* [comment removed for export] *)
Hypothesis HL : Z.of_nat (length X0) + 2 <= NHELDc.
Hypothesis Hn : 0 <= n <= NUSERc.

Let X := (pb, blk_size b) :: X0.

Lemma rs_ov : size_overflows n = false.
Proof. unfold size_overflows. apply Z.leb_gt. rewrite NUSERc_val in Hn. lia. Qed.

Lemma rs_budget : PHI P16 + R63X X + bigb n <= (LMAXc - 3 * PGSZ) + 3 * PGSZ /\ (LMAXc - 3 * PGSZ) + 3 * PGSZ <= LBUDGET.
Proof.
  destruct HE as [(HQ & HL0 & HF) _]. pose proof (R63X_le X HF) as RX. pose proof (bigb_le n Hn) as BN.
  assert (LX : Z.of_nat (length X) <= NHELDc - 1) by (unfold X; cbn [length]; rewrite Nat2Z.inj_succ; lia).
  assert (A0 : 0 <= ABLKc) by (rewrite ABLKc_val; lia).
  assert (RX' : R63X X <= (NHELDc - 1) * ABLKc) by nia.
  unfold LMAXc, LBUDGET. rewrite PHI16_val, ABLKc_val, NHELDc_val in *. unfold PGSZ. split; lia.
Qed.

Theorem HEADc_realloc :
  mspec (fun s' mo' => s' = s /\ mo' = mo) (raw_realloc o st pf n)
        (fun r s' mo' => match snd r with
           | Some q => exists c' off', q = aadd c' (UNIT * off') /\ (forall p', fst p' = c' -> HEADc ((p', n) :: X0) s' mo')
                       /\ G s' mo' /\ ps_m s' = strip (fst r) /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
                       /\ slotfit (fst r) c' off' n
           | None => HEADc X s' mo' /\ G s' mo' /\ ps_m s' = strip (fst r) /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
           end).
Proof.
  destruct HE as [(HQ & HL0 & HF) [HV HR]] eqn:EHE. clear EHE.
  destruct rs_budget as [B1 B2].
  assert (HRX : ROOMX X P16 n) by (apply ROOMX_P16; unfold X; cbn [length]; rewrite Nat2Z.inj_succ; lia).
  eapply mspec_conseq; [apply (mspec_vmc _ _ _ (vmc mo) (raw_realloc_LQ G resv st LB0 b pb X0 pf n o s mo P16 (LMAXc - 3 * PGSZ)
                                                       HG HO Es HH Hb Hfst Hconc Hpb ltac:(lia) rs_ov HQ HX HRX B1 B2))| |].
  - intros s' mo' [-> ->]. split; [split; reflexivity| reflexivity].
  - intros [st' q] s' mo' [HP Ev]. unfold vmc in Ev. injection Ev as E1 E2. cbn [fst snd] in HP |- *.
    destruct q as [q|].
    + destruct HP as (c' & off' & Eq & HQ' & Hrest). exists c', off'. split; [exact Eq|]. split; [| exact Hrest].
      intros p' Hp'. split; [| rewrite E1, E2; split; [exact HV| exact HR]].
      split; [exact (HQ' p' Hp')|]. split; [cbn [length] in *; lia|]. constructor; [cbn; lia| inversion HF; assumption].
    + destruct HP as (HQ' & Hrest). split; [| exact Hrest]. split; [| rewrite E1, E2; split; [exact HV| exact HR]].
      split; [exact HQ'|]. split; [exact HL0| exact HF].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem raw_realloc_ctall :
  ctall (raw_realloc o st pf n s) mo (fun r _ => exists q, snd (fst r) = Some q).
Proof.
  destruct HE as [(HQ & HL0 & HF) [HV HR]] eqn:EHE. clear EHE.
  destruct rs_budget as [B1 B2].
  assert (HRX : ROOMX X P16 n) by (apply ROOMX_P16; unfold X; cbn [length]; rewrite Nat2Z.inj_succ; lia).
  destruct (QI_transport G resv st LB0 s mo _ P16 HO Es HH HX HQ) as (L & LS & BL & INV & LIVE & CR & HK & SI & HAQ & HLI & PX & _).
  destruct (pf_of_block st L BL LS LB0 b pf INV LIVE CR Hb Hfst Hconc) as (off & Hk & Epf).
  pose proof (R63X_eq _ _ PX) as R63E. pose proof (ROOMX_eq _ BL P16 n PX HRX) as HRM.
  assert (HBB : PHI P16 + R63 BL + bigb n <= LMAXc + 3 * PGSZ) by (unfold X in *; unfold PGSZ in *; lia).
  destruct (block_facts x0 (set_tick (N.succ (s_tick st)) st) L BL LS (m_INV0 st L BL LS INV) (blk_slot b) off (blk_size b) Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof (realloc_fq_main st L BL LS (blk_slot b) off (blk_size b) n P16 LMAXc INV Hk ltac:(lia) rs_ov SI HAQ HRM HBB m bm i ai a ar ka BF) as FQ.
  pose proof (xqtree_of_full8 pans_mem pupd_mem pans_mem_range LMAXc _ L _ o FQ) as XQ. rewrite <- Epf in XQ.
  (* [comment removed for export] *)
  destruct (shift_bound st L BL LS INV SI HAQ) as [S0 SH].
  assert (LK : xlok ABLKc (fun x => TrueP (snd x)) (xprun pans_mem pupd_mem o (realloc st (Some pf) n))).
  { apply xlok_xprun. apply (realloc_xlok ABLKc NUSERc (c_meta_alloc_shift (s_ctx st))).
    - exact S0.
    - unfold GLEN, ABLKc, PGSZ. rewrite NUSERc_val. lia.
    - exact SH.
    - unfold ABLKc, IB, UNIT, PGSZ. lia.
    - unfold shf, ctx. lia.
    - exact Hn. }
  assert (SK : xsok (fun x => SOMEP (snd x)) (xprun pans_mem pupd_mem o (realloc st (Some pf) n))).
  { apply xsok_xprun. apply realloc_sok. exact rs_ov. }
  assert (GB : gm L + BB L <= LMAXc).
  { pose proof (regions_bound x0 st L BL LS P16 INV SI HAQ eq_refl) as RB. pose proof (ledger_bound x0 st L BL LS INV) as LBd.
    unfold ORPH in RB. cbn [x_orph x0] in RB. pose proof (proj1 (bigb_le' n ltac:(lia))). unfold PGSZ in *. lia. }
  unfold raw_realloc, xmrun, mbind. apply ctall_ebind.
  eapply ctall_mono.
  { apply (xmembed_cfg LMAXc ABLKc RCMAXc VMINc) with (v := vmc mo) (Post := fun L' x => RPOSTQ BL (blk_slot b) n P16 L' (snd x)) (G := G) (L := L).
    - rewrite LMAXc_val. lia.
    - rewrite ABLKc_val. split; [lia| reflexivity].
    - exact window_numerics.
    - unfold VMINc. lia.
    - unfold vmc. cbn [fst snd]. split; [exact HR| exact HV].
    - exact HG.
    - exact XQ.
    - exact LK.
    - exact SK.
    - exact HK.
    - exact HLI.
    - exact (KOWN_G _ _ _ HO).
    - exact GB.
    - reflexivity. }
  intros [[o' [st' q]] s1] mo' Hs. cbn [fst snd] in Hs |- *.
  unfold mupd, mret, ctall. cbn. destruct q as [q|]; [eexists; reflexivity| destruct Hs].
Qed.

(* [comment removed for export] *)
Theorem realloc_succ :
  ctall (raw_realloc o st pf n s) mo
        (fun r mo' => exists q c' off', snd (fst r) = Some q /\ q = aadd c' (UNIT * off')
                      /\ (forall p', fst p' = c' -> HEADc ((p', n) :: X0) (snd r) mo')
                      /\ G (snd r) mo' /\ ps_m (snd r) = strip (fst (fst r))).
Proof.
  pose proof (HEADc_realloc s mo (conj eq_refl eq_refl)) as M. apply ctall_of_etwf in M.
  pose proof raw_realloc_ctall as C.
  eapply ctall_mono; [exact (ctall_conj _ _ _ _ C M)|].
  intros [[st' q] s'] mo' [[q0 Hq] HM]. cbn [fst snd] in *. subst q.
  destruct HM as (c' & off' & Eq & HH' & HG' & Hm & _). exists q0, c', off'. auto.
Qed.

(* [comment removed for export] *)
Theorem realloc_succB :
  ctall (raw_realloc o st pf n s) mo
        (fun r mo' => exists q, snd (fst r) = Some q
                      /\ (forall resv' st2 LB2 (b' : block), strip st2 = strip (fst (fst r)) -> AREACH_from resv' st2 LB2 -> In b' LB2 ->
                            blk_addr b' = conc (fst (fst r)) q -> HEADc ((blk_id b', n) :: X0) (snd r) mo')
                      /\ G (snd r) mo' /\ ps_m (snd r) = strip (fst (fst r))).
Proof.
  pose proof (HEADc_realloc s mo (conj eq_refl eq_refl)) as M. apply ctall_of_etwf in M.
  pose proof raw_realloc_ctall as C.
  eapply ctall_mono; [exact (ctall_conj _ _ _ _ C M)|].
  intros [[st' q] s'] mo' [[q0 Hq] HM]. cbn [fst snd] in *. subst q.
  destruct HM as (c' & off' & Eq & HH' & HG' & Hm & _ & _ & SF). exists q0. split; [reflexivity|]. split; [| auto].
  intros resv' st2 LB2 b' Es2 AR Hb' Ha. apply HH'.
  apply (slot_of_addr resv' st2 LB2 b' c' off' n AR Hb' (slotfit_strip _ _ _ _ _ Es2 SF)).
  rewrite Ha, Eq. symmetry. apply conc_strip. exact Es2.
Qed.

End REALLOC.

End RC__.
