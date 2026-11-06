(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ws22 MI_Wp9i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma LB_T80p LB_Inv LB_Sum LB_Ljn7 LB_Bound LB_Tree LB_StmtA LB_WFree LB_Wazc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_W9kq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_StmtA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bs (k : blk) : cptr * Z := (bslot k, bsize k).
Definition xs (xb : (cptr * Z) * Z) : cptr * Z := (fst (fst xb), snd xb).

(* [comment removed for export] *)
Definition LRX (X : list ((cptr * Z) * Z)) (c : Z) : Z := zcount (fun xb => negb (MMAP_THRESHOLD <=? snd xb) && (size_to_class (snd xb) =? c)) X.
Definition n63X (X : list ((cptr * Z) * Z)) : Z := zcount (fun xb => MMAP_THRESHOLD <=? snd xb) X.
Definition R63X (X : list ((cptr * Z) * Z)) : Z := zsum (map (fun xb => if MMAP_THRESHOLD <=? snd xb then bigmap (snd xb) else 0) X).
Definition ROOMX (X : list ((cptr * Z) * Z)) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LRX X (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63X X + 1 <= P 63)
  /\ zlen X + 1 <= NBCAP.

Lemma zcount_map {A B} (f : A -> B) (p : B -> bool) l : zcount p (map f l) = zcount (fun x => p (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma R63X_eq X BL : Permutation (map xs X) (map bs BL) -> R63X X = R63 BL.
Proof.
  intros HP. unfold R63X, R63, isbig.
  transitivity (zsum (map (fun q : cptr * Z => if MMAP_THRESHOLD <=? snd q then bigmap (snd q) else 0) (map xs X))); [rewrite map_map; reflexivity|].
  rewrite (zsum_map_perm _ _ _ HP), map_map. reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma R63X_nonneg X : 0 <= R63X X.
Proof.
  unfold R63X. apply zsum_map_nonneg. intros xb _. destruct (Z.leb_spec MMAP_THRESHOLD (snd xb)); [apply bigmap_nonneg_big; assumption| lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SINV_ctrl X st st1 BL : ctrl_eq st st1 -> SINV X st BL -> SINV X st1 BL.
Proof.
  intros CE S.
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (NC : ncarved st1 = ncarved st) by (unfold ncarved; rewrite (ce_metas _ _ CE); reflexivity).
  assert (AP : apages st1 = apages st).
  { unfold apages, regions_l, frontier. rewrite (ce_regions _ _ CE), (ce_ctx _ _ CE). reflexivity. }
  assert (SCL : forall s, slotcls st1 s = slotcls st s) by (intros s; unfold slotcls, cls; rewrite (ce_slots _ _ CE); destruct (s_slots st !! s) as [[? ?]|]; [rewrite MR1|]; reflexivity).
  assert (STD : forall x, stdg st1 x = stdg st x) by (intros x; unfold stdg, cls; rewrite !MR1; reflexivity).
  destruct S as [qb_cls qb_cnt qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor; rewrite ?(ce_slots _ _ CE), ?(ce_groups _ _ CE), ?(ce_metas _ _ CE), ?(ce_regions _ _ CE), ?(ce_ctx _ _ CE), ?NC, ?AP; auto.
  - intros k Hk. destruct (qb_cls k Hk) as (m0 & i0 & H0 & H1 & H2). exists m0, i0. rewrite !MR1. auto.
  - intros b m' ai Hg. rewrite !MR1. intros A1 A2. exact (qg_map _ _ _ Hg A1 A2).
  - intros b m' ai Hg. rewrite STD, !MR1. intros SG. destruct (qg_std _ _ _ Hg SG) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p' & i' & Hs' & E'). exists p', i'. rewrite (MR1 p'). auto.
  - intros c' Hc'. replace (nsc st1 c') with (nsc st c'); [apply qg_small; exact Hc'|].
    unfold nsc, gmetas, groups_l, cls. rewrite (ce_groups _ _ CE). apply zsum_map_ext. intros mb _. rewrite STD, MR1. reflexivity.
  - intros b m' ai Hg. rewrite !MR1. intros C63. exact (qg_63 _ _ _ Hg C63).
  - intros b m' ai p' i' Hg. rewrite !MR1. intros Z0 Hs'. exact (qg_host _ _ _ _ _ Hg Z0 Hs').
Qed.

Lemma bl_remove_perm k BL : In k BL -> List.NoDup (map bslot BL) ->
  Permutation (map bs BL) (bs k :: map bs (bl_remove (bslot k) BL)).
Proof.
  induction BL as [|k' BL IH]; intros Hin ND; [destruct Hin|]. cbn [map bl_remove].
  inversion ND as [|x l NI ND']; subst.
  destruct (aptr_eqb_spec (bslot k') (bslot k)) as [E|NE].
  - destruct Hin as [->|Hin]; [apply Permutation_refl|].
    exfalso. apply NI. rewrite E. apply in_map_iff. exists k. auto.
  - destruct Hin as [->|Hin]; [congruence|]. cbn [map]. etransitivity; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

Lemma INVL_nodup_slots X st L BL LS : INVL X st L BL LS -> List.NoDup (map bslot BL).
Proof. intros INV. apply NoDup_ListNoDup. exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ORACLE.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma free_simQ st L BL LS P c off n (o : O) ans o' st' :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> In ((c, off), n) BL ->
  follow (prun pans pupd o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  SINV x0 st' (bl_remove c BL) /\ AQ st' (bl_remove c BL) P.
Proof.
  intros INV SI HAQ Hk Hf.
  pose proof (free_fq st L BL LS P c off n (PHI P + R63 BL) INV SI HAQ Hk ltac:(unfold PGSZ; lia)) as FQ.
  pose proof (ftree_prun pans pupd Hpans _ L _ o (@fqtree_ftree _ _ _ _ _ _ FQ)) as PT.
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ (LS' & _ & S' & A')]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition mallocK (n : Z) (x : mstate * option (aptr * Z)) : M (mstate * optr) :=
  let '(st1, r) := x in
  match r with
  | None => ret (st1, @None aptr)
  | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
  end.

Lemma malloc_unfold st n : malloc st n = sbind (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n) (mallocK n).
Proof. reflexivity. Qed.

Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st).
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Lemma malloc_fbnd8 st L BL LS P n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ -> fbnd8 B L (malloc st n).
Proof.
  intros INV SI HAQ Hn HR HB. rewrite malloc_unfold.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  eapply fbnd8_bind; [exact (malloc_core_fq_proof st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB)|].
  intros L1 [st1 [[g idx]|]] _; cbn [mallocK].
  - apply fbnd8_enframe_full. intros st' p. exact I.
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma malloc_simQ st L BL LS P n B (o : O) ans o' st' r :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ ->
  follow (prun pans pupd o (malloc st n)) ans = Some (o', (st', r)) ->
  let t := cmalloc (strip st) n in
  let L' := lafter L t ans in
  exists rc, follow t ans = Some (strip st', rc) /\
    match r, rc with
    | None, None => (exists LS', INVL x0 st' L' BL LS') /\ SINV x0 st' BL /\ AQ st' BL P
    | Some pf, Some c => exists off LS', pf = aadd c (UNIT * off)
                         /\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ SINV x0 st' (((c, off), n) :: BL) /\ AQ st' (((c, off), n) :: BL) P
    | _, _ => False
    end.
Proof.
  intros INV SI HAQ Hn HR HB Hf. cbn zeta.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  assert (E1 : steq (prun pans pupd o (malloc st n)) (sbind (prun pans pupd o (malloc_core full_lay st0 n)) (fun x => prun pans pupd (fst x) (mallocK n (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (prun pans pupd o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].
  (* [comment removed for export] *)
  pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (@fqtree_ftree _ _ _ _ _ _ (malloc_core_fq_proof st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB))) as PTQ.
  pose proof (ptree_followk _ L _ ans PTQ FK) as CQ. unfold CORE_POSTQ in CQ. cbn [snd fst] in CQ.
  set (L1 := lafter L (prun pans pupd o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & CP).
  (* [comment removed for export] *)
  pose proof (malloc_core_ctrl pans pupd n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    specialize (CQ bg). fold c0 in CQ.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ ctrl_eq st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9; reflexivity| exact CE])).
    pose proof (ftree_prun pans pupd Hpans _ L1 _ o1 EF) as PTE.
    cbn [mallocK fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Er & INV2 & SS2 & CE2)]. cbn [fst snd] in Er, INV2, SS2, CE2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    exists off, LS1. split; [reflexivity|]. split; [exact INV2|].
    destruct (CQ off Hg) as [S1 A1].
    split; [exact (SINV_ctrl x0 st1 st' _ CE2 S1)| exact (AQ_ctrl st1 st' _ P CE2 A1)].
  - destruct CP as (LS1 & INV1). cbn [mallocK fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity|].
    split; [exists LS1; exact INV1|]. exact CQ.
Qed.

End ORACLE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem cmalloc_qtree st L BL LS P n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ ->
  qtree B L (cmalloc (strip st) n) (fun _ _ => True).
Proof.
  intros INV SI HAQ Hn HR HBB.
  eapply (qtree_of_full8 pans0 pupd0 pans0_range (RR := MREL)).
  - exact (malloc_INVL st L BL LS n INV Hn).
  - exact (malloc_fbnd8 st L BL LS P n B INV SI HAQ Hn HR HBB).
  - exact (malloc_control pans0 pupd0 pans0_range st n tt).
  - intros; exact I.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zcount_bs (f : cptr * Z -> bool) BL : zcount (fun k => f (bs k)) BL = zcount f (map bs BL).
Proof. symmetry. apply zcount_map. Qed.

Lemma In_bs_perm BL BL' k' : Permutation (map bs BL) (map bs BL') -> In k' BL' -> exists k, In k BL /\ bs k = bs k'.
Proof.
  intros HP Hk'. assert (H : In (bs k') (map bs BL)) by (eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_map; exact Hk']).
  apply in_map_iff in H as (k & E & Hk). exists k. auto.
Qed.

Lemma LR_bs BL BL' c : Permutation (map bs BL) (map bs BL') -> LR BL' c = LR BL c.
Proof.
  intros HP. unfold LR, isbig.
  rewrite (zcount_bs (fun q => negb (MMAP_THRESHOLD <=? snd q) && (size_to_class (snd q) =? c)) BL').
  rewrite (zcount_bs (fun q => negb (MMAP_THRESHOLD <=? snd q) && (size_to_class (snd q) =? c)) BL).
  symmetry. apply zcount_perm. exact HP.
Qed.
Lemma n63_bs BL BL' : Permutation (map bs BL) (map bs BL') -> n63 BL' = n63 BL.
Proof.
  intros HP. unfold n63, isbig.
  rewrite (zcount_bs (fun q => MMAP_THRESHOLD <=? snd q) BL'), (zcount_bs (fun q => MMAP_THRESHOLD <=? snd q) BL).
  symmetry. apply zcount_perm. exact HP.
Qed.
(* [comment removed for export] *)
Lemma zlen_bs BL BL' : Permutation (map bs BL) (map bs BL') -> zlen BL' = zlen BL.
Proof. intros HP. apply Permutation_length in HP. rewrite !length_map in HP. unfold zlen. lia. Qed.

Lemma SINV_bs X st BL BL' : Permutation (map bs BL) (map bs BL') -> SINV X st BL -> SINV X st BL'.
Proof.
  intros HP S. destruct S as [qb_cls qb_cnt qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor; auto.
  - intros k' Hk'. destruct (In_bs_perm BL BL' k' HP Hk') as (k & Hk & E). unfold bs in E. injection E as E1 E2.
    destruct (qb_cls k Hk) as (m & i & H0 & H1 & H2). exists m, i. rewrite <- E1, <- E2. auto.
  - rewrite (zlen_bs BL BL' HP). exact qb_cnt.
  - intros b m ai Hg H63. specialize (qg_63 b m ai Hg H63).
    assert (E : forall l, map bslot l = map fst (map bs l)) by (intros l; rewrite map_map; reflexivity).
    rewrite E in qg_63 |- *. eapply Permutation_in; [apply Permutation_map; exact HP| exact qg_63].
Qed.

Lemma AQ_bs st BL BL' P : Permutation (map bs BL) (map bs BL') -> AQ st BL P -> AQ st BL' P.
Proof.
  intros HP A. destruct A as [A1 A2 A3 A4 A5 A6]. constructor; auto.
  - intros c Hc. rewrite (LR_bs BL BL' c HP). apply A1. exact Hc.
  - rewrite (n63_bs BL BL' HP). exact A3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition NLIVE_CAP : Z := 64.
Definition PN : Z -> Z := fun _ => NLIVE_CAP.

Lemma PHI_PN : PHI PN = 320198656. Proof. vm_compute. reflexivity. Qed.
Lemma kcap_PN : NG PN + 3 * (NCAP PN / 101) + 8 <= 12288. Proof. vm_compute. discriminate. Qed.
Lemma PN_nonneg c : 0 <= PN c. Proof. unfold PN, NLIVE_CAP. lia. Qed.

(* [comment removed for export] *)
Lemma NBCAP_NLIVE : NBCAP = NLIVE_CAP. Proof. reflexivity. Qed.
Lemma ROOM_PN BL n : zlen BL + 1 <= NLIVE_CAP -> ROOM BL PN n.
Proof.
  intros H. unfold ROOM, PN. split; [| split].
  - intros _. pose proof (zcount_le_zlen (fun k => negb (isbig k) && (size_to_class (bsize k) =? size_to_class n)) BL). unfold LR. lia.
  - intros _. pose proof (zcount_le_zlen isbig BL). unfold n63. lia.
  - rewrite NBCAP_NLIVE. exact H.
Qed.

(* [comment removed for export] *)
Lemma AQ_PN_resize st BL BL' : zlen BL' <= NLIVE_CAP -> n63 BL' = n63 BL -> AQ st BL PN -> AQ st BL' PN.
Proof.
  intros H E A. destruct A as [A1 A2 A3 A4 A5 A6]. constructor; auto.
  - intros c Hc. unfold PN. pose proof (zcount_le_zlen (fun k => negb (isbig k) && (size_to_class (bsize k) =? c)) BL'). unfold LR. lia.
  - rewrite E. exact A3.
Qed.

(* [comment removed for export] *)
Definition sizesX (X : list ((cptr * Z) * Z)) : Z := zsum (map snd X).
Lemma bigmap_le n : bigmap n <= n + 8211.
Proof. unfold bigmap. pose proof (round_up_pg_spec (n + IB + UNIT)) as [[_ H] _]. unfold IB, UNIT, PGSZ in *. lia. Qed.
Lemma bigb_le n : 0 <= n -> bigb n <= n + 8211.
Proof. intros Hn. unfold bigb. destruct (MMAP_THRESHOLD <=? n); [apply bigmap_le| lia]. Qed.
Lemma R63X_le X : (forall xb, In xb X -> 0 <= snd xb) -> R63X X <= sizesX X + 8211 * zlen X.
Proof.
  unfold R63X, sizesX. induction X as [|xb X IH]; intros H; [unfold zsum, zlen; cbn; lia|].
  cbn [map]. rewrite !zsum_cons, zlen_cons. specialize (IH (fun y Hy => H y (or_intror Hy))). pose proof (H xb (or_introl eq_refl)).
  destruct (MMAP_THRESHOLD <=? snd xb); [pose proof (bigmap_le (snd xb))|]; lia.
Qed.

End LBCEIL.
