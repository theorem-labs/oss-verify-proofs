(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WEnframe2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Logic OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Kernel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Embed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Raw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Alloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Stable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma ftree_conj {R} (t : Malloc.M R) : forall L (P Q : mled -> R -> Prop),
  ftree L t P -> ftree L t Q -> ftree L t (fun L' r => P L' r /\ Q L' r).
Proof.
  induction t as [r|e k IH]; intros L P Q HP HQ; cbn [ftree] in *; [split; assumption|].
  destruct e; try (destruct HP as [He HkP]; destruct HQ as [_ HkQ]; split; [exact He|]; intros a; specialize (HkP a); specialize (HkQ a);
                   case_ans; [apply IH; assumption| exact HkP]).
  - intros v Hv. apply IH; auto.
  - exact HP.
Qed.

#[using="Type"] Lemma fbnd8_mono {R} B B' (t : Malloc.M R) : B <= B' -> forall L, fbnd8 B L t -> fbnd8 B' L t.
Proof.
  intros HB. induction t as [r|e k IH]; intros L H; cbn [fbnd8] in *; [exact I|].
  destruct e; try (destruct H as [H1 H2]; split; [eapply BOUND_mono; eauto| intros a Ha; apply IH; apply H2; exact Ha]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact I.
Qed.

(* [comment removed for export] *)
Definition malloc_postQ (st : mstate) (L : mled) (BL : list blk) (P : Z -> Z) (n : Z) (L' : mled) (r : mstate * optr) : Prop :=
  ld_live L' = ld_live L /\ GP st (fst r) /\
  match snd r with
  | None => (exists LS', INVL x0 (fst r) L' BL LS') /\ SINV x0 (fst r) BL /\ AQ (fst r) BL P
  | Some p => exists c off LS', p = aadd c (UNIT * off) /\ 0 <= off <= 255
      /\ INVL x0 (fst r) L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
      /\ SINV x0 (fst r) (((c, off), n) :: BL) /\ AQ (fst r) (((c, off), n) :: BL) P
  end.

#[using="Type"] Lemma malloc_ftq (MQ : malloc_core_fq_stmt) st L BL LS P n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ -> bigb n <= QMAX ->
  ftree L (malloc st n) (malloc_postQ st L BL P n) /\ fbnd8 B L (malloc st n).
Proof.
  intros INV SI HAQ Hn HR HB HQ. split; [| exact (malloc_fbnd8 MQ st L BL LS P n B INV SI HAQ Hn HR HB HQ)].
  unfold malloc.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  eapply ftree_bind.
  { apply ftree_conj; [exact (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)| exact (fqtree_ftree _ _ _ _ (MQ st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB HQ))]. }
  intros L1 [st1 r] [(LIVE & GP1 & RES) CQ]. cbn [fst snd] in RES, GP1, CQ |- *. unfold CORE_POSTQ in CQ. cbn [fst snd] in CQ.
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct r as [[g idx]|].
  - destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32).
    intros off st' Ho Hf INV' CEq TK. unfold malloc_postQ. cbn [fst snd]. split; [exact LIVE|].
    split; [eapply GP_trans; [exact GP0| apply GP_eq; [exact (ce_regions _ _ CEq)| exact (ce_secret _ _ CEq)]]|].
    exists (fst bg, sstart (MR st1 g) idx), off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
    split.
    + pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))))) as ND. cbn [map bslot fst] in ND.
      inversion ND as [|? ? NI ND']; subst. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
    + destruct (CQ bg off Hg) as [S1 A1]. split; [exact (SINV_ctrl x0 st1 st' _ CEq S1)| exact (AQ_ctrl st1 st' _ P CEq A1)].
  - destruct RES as (LS1 & INV1). unfold malloc_postQ. cbn [ftree ret fst snd]. split; [exact LIVE|]. split; [exact GP0|]. split; [exists LS1; exact INV1| exact CQ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition blk_ptr (b : blk) : aptr * Z := (aadd (bslot b) (UNIT * boff b), bsize b).

(* [comment removed for export] *)
Definition LRN (ns : list Z) (c : Z) : Z := zcount (fun n => negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c)) ns.
Definition n63N (ns : list Z) : Z := zcount (fun n => MMAP_THRESHOLD <=? n) ns.
Definition R63N (ns : list Z) : Z := zsum (map bigb ns).
(* [comment removed for export] *)
Definition ROOMN (ns : list Z) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LRN ns (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63N ns + 1 <= P 63).

#[using="Type"] Lemma LRN_eq X BL c : Permutation X (map blk_ptr BL) -> LRN (map snd X) c = LR BL c.
Proof.
  intros HP. unfold LRN, LR, isbig. rewrite (zcount_perm _ _ _ (Permutation_map snd HP)), map_map, !zcount_map. reflexivity.
Qed.
#[using="Type"] Lemma n63N_eq X BL : Permutation X (map blk_ptr BL) -> n63N (map snd X) = n63 BL.
Proof.
  intros HP. unfold n63N, n63, isbig. rewrite (zcount_perm _ _ _ (Permutation_map snd HP)), map_map, !zcount_map. reflexivity.
Qed.
#[using="Type"] Lemma R63N_eq X BL : Permutation X (map blk_ptr BL) -> R63N (map snd X) = R63 BL.
Proof.
  intros HP. unfold R63N, R63, isbig, bigb. rewrite (zsum_map_perm _ _ _ (Permutation_map snd HP)), !map_map. reflexivity.
Qed.
#[using="Type"] Lemma ROOMN_eq X BL P n : Permutation X (map blk_ptr BL) -> ROOMN (map snd X) P n -> ROOM BL P n.
Proof. intros HP [R1 R2]. split; [rewrite <- (LRN_eq X BL _ HP); exact R1| rewrite <- (n63N_eq X BL HP); exact R2]. Qed.

#[using="Type"] Lemma R63N_cons n ns : R63N (n :: ns) = bigb n + R63N ns.
Proof. unfold R63N. cbn [map]. rewrite zsum_cons. reflexivity. Qed.
#[using="Type"] Lemma R63N_nonneg ns : 0 <= R63N ns.
Proof. unfold R63N. apply zsum_map_nonneg. intros n _. apply bigb_nonneg. Qed.
#[using="Type"] Lemma R63N_perm ns ns' : Permutation ns ns' -> R63N ns = R63N ns'.
Proof. intros HP. unfold R63N. apply zsum_map_perm. exact HP. Qed.
#[using="Type"] Lemma LRN_perm ns ns' c : Permutation ns ns' -> LRN ns c = LRN ns' c.
Proof. intros HP. unfold LRN. apply zcount_perm. exact HP. Qed.
#[using="Type"] Lemma n63N_perm ns ns' : Permutation ns ns' -> n63N ns = n63N ns'.
Proof. intros HP. unfold n63N. apply zcount_perm. exact HP. Qed.

#[using="Type"] Lemma blk_ptr_remove_perm c off n BL : In ((c, off), n) BL -> List.NoDup (map bslot BL) ->
  Permutation (map blk_ptr BL) (blk_ptr ((c, off), n) :: map blk_ptr (bl_remove c BL)).
Proof.
  intros Hin ND. revert Hin ND. induction BL as [|k' BL IH]; intros Hin ND; [destruct Hin|]. cbn [map bl_remove].
  inversion ND as [|x l NI ND']; subst.
  destruct (aptr_eqb_spec (bslot k') c) as [E|NE].
  - destruct Hin as [->|Hin]; [apply Permutation_refl|].
    exfalso. apply NI. rewrite E. apply in_map_iff. exists ((c, off), n). auto.
  - destruct Hin as [->|Hin]; [cbn in NE; congruence|]. cbn [map]. etransitivity; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FullQ.
Context {St : Type} {AS : AllocSt St}.
Local Notation MP := (Monad.M St).

(* [comment removed for export] *)
Definition FQ (X : list (aptr * Z)) (P : Z -> Z) (G : St -> Model -> Prop) : assn St := fun s mo =>
  (exists L LS BL, INVL x0 (ps_m s) L BL LS /\ SINV x0 (ps_m s) BL /\ AQ (ps_m s) BL P /\ KL L (ps_brk s) mo /\ LI L mo
                   /\ Permutation X (map blk_ptr BL))
  /\ G s mo.

#[using="Type"] Lemma FQ_FOWN X P G s mo : FQ X P G s mo -> exists BL, Permutation X (map blk_ptr BL) /\ FOWN BL G s mo.
Proof. intros [(L & LS & BL & INV & _ & _ & HK & _ & HP) HG]. exists BL. split; [exact HP|]. split; [exists L, LS; split; assumption| exact HG]. Qed.

#[using="Type"] Lemma FQ_G X P G s mo : FQ X P G s mo -> G s mo.
Proof. intros [_ HG]. exact HG. Qed.

#[using="Type"] Lemma FQ_weakG X P G G' s mo : FQ X P G s mo -> (G s mo -> G' s mo) -> FQ X P G' s mo.
Proof. intros [H HG] HGG'. split; [exact H| apply HGG'; exact HG]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma FQ_other X P G s s' mo : FQ X P G s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> G s' mo -> FQ X P G s' mo.
Proof. intros [H _] Hm Hb HG'. split; [rewrite Hm, Hb; exact H| exact HG']. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma FQ_fds X P G s mo mo' : FQ X P G s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> G s mo' -> FQ X P G s mo'.
Proof.
  intros [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) _] Hvm Hmi Hh HG'. split; [| exact HG'].
  exists L, LS, BL. split; [exact INV|]. split; [exact SI|]. split; [exact HAQ|]. split; [| split; [| exact HP]].
  - destruct HK; constructor; rewrite ?Hvm; auto.
  - unfold LI in *. rewrite Hvm. exact HL.
Qed.

#[using="Type"] Lemma FQ_minv X P G s mo : FQ X P G s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(L & LS & BL & _ & _ & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

#[using="Type"] Lemma FQ_after_node X P G s mo n rsp mo' evs :
  FQ X P G s mo -> node_static_ok n -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> G s mo' -> FQ X P G s mo'.
Proof.
  intros HQ Hso Hst Hvm HG'. destruct (FQ_minv _ _ _ _ _ HQ) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hso Hmi Hh Hst) as [Hh' Hmi']. eapply FQ_fds; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma FQ_monoP X P P' G s mo : (forall c, P c <= P' c <= PMAX) -> FQ X P G s mo -> FQ X P' G s mo.
Proof.
  intros HPP [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HG]. split; [| exact HG].
  exists L, LS, BL. split; [exact INV|]. split; [exact SI|]. split; [exact (AQ_monoP _ BL P P' HPP HAQ)|]. split; [exact HK|]. split; assumption.
Qed.

#[using="Type"] Lemma FQ_perm X X' P G s mo : Permutation X X' -> FQ X P G s mo -> FQ X' P G s mo.
Proof.
  intros HPm [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HG]. split; [| exact HG].
  exists L, LS, BL. repeat (split; [assumption|]). etransitivity; [apply Permutation_sym; exact HPm| exact HP].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma FQ_census X P G s mo : FQ X P G s mo ->
  exists L, KL L (ps_brk s) mo /\ LI L mo /\ gm L + BB L + 3 * PGSZ <= PHI P + R63N (map snd X).
Proof.
  intros [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) _]. exists L. split; [exact HK|]. split; [exact HL|].
  pose proof (regions_bound x0 (ps_m s) L BL LS P INV SI HAQ eq_refl) as RB. pose proof (ledger_bound x0 (ps_m s) L BL LS INV) as LB0.
  rewrite (R63N_eq X BL HP). unfold ORPH in *. cbn [x_orph x0] in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma vis_flat_conj {A} n (k : resp -> itree node (exc A)) mo (Q R : A -> Model -> Prop) :
  (forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end) ->
  etwf (Vis n k) mo Q ->
  (forall rsp mo' evs a, nstep n mo rsp mo' evs -> k rsp = Ret (Ok a) -> Q a mo' -> R a mo') ->
  etwf (Vis n k) mo (fun a mo' => Q a mo' /\ R a mo').
Proof.
  intros Hf H HR. cbn in H |- *. destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst). specialize (Hf rsp).
  destruct (k rsp) as [[|a]|n' k'] eqn:Ek; cbn in Hk |- *; [destruct Hk| | destruct Hf].
  split; [exact Hk|]. exact (HR rsp mo' evs a Hst Ek Hk).
Qed.

Ltac flat_shape W :=
  unfold mbind, msys, mret, mget, mupd, enode, ebind in W |- *; cbn [ITree.bind fst snd] in W |- *.

(* [comment removed for export] *)
#[using="Type"] Theorem ev_step_LI L e G s0 : frame_ok G -> event_pre L e ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (ev_step e)
        (fun z s mo => ev_step_post L e G s0 z s mo /\ LI (event_post L e z) mo).
Proof.
  intros HG Hpre s mo (-> & HK & HLI & HGs).
  pose proof (ev_step_spec L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as W.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?|ma mol mnl]; cbn [event_pre] in Hpre; try contradiction; try (destruct Hpre as [[] ?]).
  - (* [comment removed for export] *)
    unfold ev_step in W |- *.
    destruct (Z.eqb_spec req 0) as [->|NZ].
    + flat_shape W. eapply vis_flat_conj; [| exact W|].
      { intros rsp. destruct (dec_brk0 rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk0 rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate]. assert (Ez : z = x) by congruence. subst x.
      destruct Hpre as [[_ Hph]|[(cur & Hph & E)|(b & l & Hph & Hreg & E)]].
      2:{ exfalso. pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as (Ecur & _). pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia. }
      2:{ exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia. }
      pose proof (li_brk0 L (ps_brk s0) mo rsp mo' evs z HK HLI Hph Hst) as HL'.
      change (event_post L (EBrk 0) z) with (set_brkph (BPQueried z) L). exact HL'.
    + flat_shape W. eapply vis_flat_conj; [| exact W|].
      { intros rsp. destruct (dec_brk (ps_brk s0) req rsp) as [[|]|]; reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk (ps_brk s0) req rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
      assert (Ez : z = match x with BrkGrown => req | BrkSame => ps_brk s0 end) by (destruct x; cbn in Ek; congruence).
      destruct Hpre as [[E _]|Hpre]; [exfalso; exact (NZ E)|].
      pose proof (li_brk_grow L (ps_brk s0) mo rsp mo' evs req x HK HLI Hpre Hst Hd) as HL'. rewrite <- Ez in HL'. exact HL'.
  - (* [comment removed for export] *)
    unfold ev_step in W |- *.
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in *. cbn iota in W |- *.
      destruct Hprot as [-> | ->].
      * change (PROT_NONE =? 0) with true in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_conj; [| exact W|].
        { intros rsp. destruct (dec_mmap_none len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap_none len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        exact (li_mmap_none L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd).
      * change (PROT_RW =? 0) with false in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_conj; [| exact W|].
        { intros rsp. destruct (dec_mmap len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        exact (li_mmap_rw L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd).
    + change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_conj; [| exact W|].
      { intros rsp. destruct (dec_mmap_fixed (round_up_pg cur) PGSZ rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      exact (li_mmap_fixed L (ps_brk s0) mo rsp mo' evs cur z HK HLI Hph Hst).
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & l0 & Hin & Hlen). flat_shape W. eapply vis_flat_conj; [| exact W|].
    { intros rsp. destruct (dec_munmap addr len rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    exact (li_munmap L (ps_brk s0) mo rsp mo' evs addr l0 len z HK HLI Hin Hlen Hst).
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). flat_shape W. eapply vis_flat_conj; [| exact W|].
    { intros rsp. destruct (dec_mprotect_rw (b + (1 + k) * PGSZ) PGSZ rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    exact (li_mprotect L (ps_brk s0) mo rsp mo' evs b l k z HK HLI Hin Hk Hst).
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & (l0 & Hin & Hol) & Hnl & Hal & Hne).
    rewrite round_up_pg_eq in Hol. fold (mmap_len l0) in Hol. subst mol.
    flat_shape W. eapply vis_flat_conj; [| exact W|].
    { intros rsp. destruct (dec_mremap ma (mmap_len l0) mnl [] [] rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    destruct (dec_mremap ma (mmap_len l0) mnl [] [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
    assert (Ez : z = mremap_val ma x) by congruence. subst z.
    exact (li_mremap L (ps_brk s0) mo rsp mo' evs ma l0 mnl x HK HLI Hin Hnl Hal Hne Hst Hd).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem membedF_LI {R} (t : stree ev Z R) : forall (Post : mled -> R -> Prop) (G : St -> Model -> Prop) L s0,
  frame_ok G -> ftree L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (membedF peekG t)
        (fun r s mo => exists L', fpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ LI L' mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_rest s = ps_rest s0).
Proof.
  induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [membedF]. apply mspec_ret. intros s mo (-> & HK & HL & HGs). exists L.
    split; [constructor|]. cbn in Hok. split; [exact Hok|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. split; reflexivity.
  - cbn [membedF]. cbn [ftree] in Hok.
    destruct (is_peek e) eqn:Ep.
    + destruct e as [| | | |p c h| |]; cbn in Ep; try discriminate. cbn [ev_stepF].
      eapply mspec_bind; [apply peekG_spec|].
      intros v. cbn beta. apply mspec_pointwise. intros s1 mo1 (Hv & -> & HK1 & HL1 & HG1).
      eapply mspec_conseq; [apply (IH v Post G L s0 HG (Hok v Hv))| |].
      * intros s mo [-> ->]. auto.
      * intros r s mo (L' & Hp & HP & HK & HL' & HG' & Hm & Hx). exists L'. split; [eapply fpath_peek; eauto|].
        split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HG'|]. split; assumption.
    + assert (Hev : event_pre L e /\ (forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a))
                    /\ ev_stepF peekG e = ev_step e).
      { destruct e; cbn in Ep; try discriminate; cbn [ftree] in Hok; try (destruct Hok; fail); destruct Hok as [H1 H2]; auto. }
      destruct Hev as (Hpre & Hk & ->).
      eapply mspec_bind; [apply (ev_step_LI L e G s0 HG Hpre)|].
      intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 ((Hans & HK1 & HG1 & Hm & Hx1) & HL1).
      specialize (Hk z). rewrite Hans in Hk.
      eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG Hk)| |].
      * intros s mo [-> ->]. auto.
      * intros r s mo (L' & Hp & HP & HK & HL' & HG' & Hm' & Hx'). exists L'. split; [eapply fpath_vis; eauto|].
        split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HG'|]. split; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RAWQ.
Hypothesis MQ : malloc_core_fq_stmt.

#[using="MQ"] Theorem raw_mallocF_Q X P G n : frame_ok G -> 0 <= n -> bigb n <= QMAX ->
  mspec (fun s mo => FQ X P G s mo /\ ROOMN (map snd X) P n) (raw_mallocF peekG n)
        (fun r s mo => match r with
                       | Some p => FQ ((p, n) :: X) P G s mo
                       | None => FQ X P G s mo
                       end).
Proof.
  intros HG Hn HQ. unfold raw_mallocF.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [[(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HGs] HR]].
  apply (ROOMN_eq X BL P n HP) in HR.
  destruct (malloc_ftq MQ (ps_m s1) L BL LS P n (PHI P + R63 BL + bigb n) INV SI HAQ Hn HR ltac:(unfold PGSZ; lia) HQ) as [FT _].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_LI (malloc (ps_m s1) n) _ G L s1 HG FT)|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HL' & HG' & Hm & Hx).
  unfold malloc_postQ in HPost. cbn [fst snd] in HPost. destruct HPost as (LIVE & _ & RES).
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->]. unfold FQ. autorewrite with alloc_lens.
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']. }
  destruct p as [p|].
  - destruct RES as (c & off & LS' & Hp' & Hoff & INV' & Hni & SI' & HAQ').
    split; [| exact HG2]. exists L', LS', (((c, off), n) :: BL). split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'|].
    cbn [map]. unfold blk_ptr at 1. cbn [bslot boff bsize fst snd]. rewrite <- Hp'. apply perm_skip. exact HP.
  - destruct RES as ((LS' & INV') & SI' & HAQ'). split; [| exact HG2]. exists L', LS', BL. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'| exact HP].
Qed.

#[using="Type"] Theorem raw_freeF_Q X P G p n : frame_ok G ->
  mspec (FQ ((p, n) :: X) P G) (raw_freeF peekG p) (fun _ => FQ X P G).
Proof.
  intros HG. unfold raw_freeF.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HGs]].
  assert (Hin : In (p, n) (map blk_ptr BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n'] & Ebp & Hk). unfold blk_ptr in Ebp. cbn [bslot boff bsize fst snd] in Ebp.
  assert (En : n' = n) by congruence. subst n'. assert (Ep : p = aadd c (UNIT * off)) by congruence.
  pose proof (fqtree_ftree _ _ _ _ (free_fq (ps_m s1) L BL LS P c off n (PHI P + R63 BL) INV SI HAQ Hk ltac:(unfold PGSZ; lia))) as FT.
  rewrite <- Ep in FT.
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_LI (free (ps_m s1) (Some p)) _ G L s1 HG FT)|].
    intros s mo [-> ->]. auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HL' & HG' & Hm & Hx).
  apply mspec_upd'. intros s mo [-> ->]. unfold FQ. autorewrite with alloc_lens.
  destruct HPost as (LS' & INV' & SI' & HAQ').
  split; [| apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']].
  exists L', LS', (bl_remove c BL). split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'|].
  pose proof (blk_ptr_remove_perm c off n BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP.
  apply (Permutation_cons_inv (a := (p, n))). etransitivity; [exact HP|]. rewrite Ep.
  change (blk_ptr (c, off, n)) with (aadd c (UNIT * off), n) in BP. exact BP.
Qed.
End RAWQ.

End FullQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Pinned.
Context {St : Type} {AS : AllocSt St}.

(* [comment removed for export] *)
Definition Gsince (G : St -> Model -> Prop) (s0 : St) (mo0 : Model) : St -> Model -> Prop :=
  fun s mo => G s mo /\ ps_rest s = ps_rest s0 /\ vm_only mo0 mo.

#[using="Type"] Lemma Gsince_frame G s0 mo0 : frame_ok G -> frame_ok (Gsince G s0 mo0).
Proof.
  intros HG s s' mo mo' Hr Hvo (HGs & Hr0 & Hvo0). split; [eapply HG; eauto|]. split; [congruence| eapply vm_only_trans; eauto].
Qed.

#[using="Type"] Lemma FQ_Gsince X P G s0 mo0 : FQ X P G s0 mo0 -> FQ X P (Gsince G s0 mo0) s0 mo0.
Proof. intros [H HG]. split; [exact H|]. split; [exact HG|]. split; [reflexivity| apply vm_only_refl]. Qed.

#[using="Type"] Lemma FQ_unsince X P G s0 mo0 s mo : FQ X P (Gsince G s0 mo0) s mo -> FQ X P G s mo /\ ps_rest s = ps_rest s0 /\ vm_only mo0 mo.
Proof. intros [H (HG & Hr & Hvo)]. split; [split; [exact H| exact HG]|]. auto. Qed.

#[using="Type"] Theorem raw_mallocF_Q_pt X P G n s0 mo0 : malloc_core_fq_stmt -> frame_ok G -> 0 <= n -> bigb n <= QMAX ->
  FQ X P G s0 mo0 -> ROOMN (map snd X) P n ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_mallocF peekG n)
        (fun r s mo => match r with Some p => FQ ((p, n) :: X) P G s mo | None => FQ X P G s mo end
                       /\ (forall q m, In (q, m) X -> conc (ps_m s) q = conc (ps_m s0) q)
                       /\ ps_rest s = ps_rest s0 /\ vm_only mo0 mo).
Proof.
  intros MQ HG Hn HQ HF HR. unfold raw_mallocF.
  eapply mspec_bind; [apply mspec_get|]. intros s1.
  apply mspec_pointwise. intros ? ? [-> [-> ->]].
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HGs].
  apply (ROOMN_eq X BL P n HP) in HR.
  destruct (malloc_ftq MQ (ps_m s0) L BL LS P n (PHI P + R63 BL + bigb n) INV SI HAQ Hn HR ltac:(unfold PGSZ; lia) HQ) as [FT _].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_LI (malloc (ps_m s0) n) _ (Gsince G s0 mo0) L s0 (Gsince_frame G s0 mo0 HG) FT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. split; [reflexivity| apply vm_only_refl]. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HL' & (HG' & Hr' & Hvo') & Hm & Hx).
  pose proof HPost as HPost0. unfold malloc_postQ in HPost. cbn [fst snd] in HPost. destruct HPost as (LIVE & GPx & RES).
  assert (STAB : forall q m, In (q, m) X -> conc st' q = conc (ps_m s0) q).
  { intros q m Hin. assert (Hin' : In (q, m) (map blk_ptr BL)) by (eapply Permutation_in; [exact HP| exact Hin]).
    apply in_map_iff in Hin' as ([[c0 off0] n0] & Ebp & Hk0). unfold blk_ptr in Ebp. cbn [bslot boff bsize fst snd] in Ebp.
    assert (Eq : q = aadd c0 (UNIT * off0)) by congruence. rewrite Eq.
    change c0 with (bslot (c0, off0, n0)). eapply (malloc_conc_stable n _ INV Hp FT); [| exact Hk0]. intros L1 r (_ & G1 & _). exact G1. }
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->]. unfold FQ. autorewrite with alloc_lens.
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']. }
  split; [| split; [exact STAB| split; [exact Hr'| exact Hvo']]].
  destruct p as [p|].
  - destruct RES as (c & off & LS' & Hp' & Hoff & INV' & Hni & SI' & HAQ').
    split; [| exact HG2]. exists L', LS', (((c, off), n) :: BL). split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'|].
    cbn [map]. unfold blk_ptr at 1. cbn [bslot boff bsize fst snd]. rewrite <- Hp'. apply perm_skip. exact HP.
  - destruct RES as ((LS' & INV') & SI' & HAQ'). split; [| exact HG2]. exists L', LS', BL. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'| exact HP].
Qed.

#[using="Type"] Theorem raw_freeF_Q_pt X P G p n s0 mo0 : frame_ok G ->
  FQ ((p, n) :: X) P G s0 mo0 ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_freeF peekG p)
        (fun _ s mo => FQ X P G s mo
                       /\ (forall q m, In (q, m) X -> conc (ps_m s) q = conc (ps_m s0) q)
                       /\ ps_rest s = ps_rest s0 /\ vm_only mo0 mo).
Proof.
  intros HG HF. unfold raw_freeF.
  eapply mspec_bind; [apply mspec_get|]. intros s1.
  apply mspec_pointwise. intros ? ? [-> [-> ->]].
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HGs].
  assert (Hin : In (p, n) (map blk_ptr BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n'] & Ebp & Hk). unfold blk_ptr in Ebp. cbn [bslot boff bsize fst snd] in Ebp.
  assert (En : n' = n) by congruence. subst n'. assert (Ep : p = aadd c (UNIT * off)) by congruence.
  pose proof (fqtree_ftree _ _ _ _ (free_fq (ps_m s0) L BL LS P c off n (PHI P + R63 BL) INV SI HAQ Hk ltac:(unfold PGSZ; lia))) as FT.
  rewrite <- Ep in FT.
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_LI (free (ps_m s0) (Some p)) _ (Gsince G s0 mo0) L s0 (Gsince_frame G s0 mo0 HG) FT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. split; [reflexivity| apply vm_only_refl]. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HL' & (HG' & Hr' & Hvo') & Hm & Hx).
  apply mspec_upd'. intros s mo [-> ->]. unfold FQ. autorewrite with alloc_lens.
  destruct HPost as (LS' & INV' & SI' & HAQ').
  pose proof (blk_ptr_remove_perm c off n BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP.
  assert (HPX : Permutation X (map blk_ptr (bl_remove c BL))).
  { apply (Permutation_cons_inv (a := (p, n))). etransitivity; [exact HP|]. rewrite Ep.
    change (blk_ptr (c, off, n)) with (aadd c (UNIT * off), n) in BP. exact BP. }
  split; [| split; [| split; [exact Hr'| exact Hvo']]].
  - split; [| apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']].
    exists L', LS', (bl_remove c BL). split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'| exact HPX].
  - intros q m Hin. assert (Hin' : In (q, m) (map blk_ptr (bl_remove c BL))) by (eapply Permutation_in; [exact HPX| exact Hin]).
    apply in_map_iff in Hin' as ([[c0 off0] n0] & Ebp0 & Hk0). unfold blk_ptr in Ebp0. cbn [bslot boff bsize fst snd] in Ebp0.
    assert (Eq : q = aadd c0 (UNIT * off0)) by congruence. rewrite Eq.
    change c0 with (bslot (c0, off0, n0)). rewrite Ep in Hp. eapply (free_conc_stable c off n INV Hk Hp); [| exact Hk0]. exists LS'. exact INV'.
Qed.
End Pinned.

End WithCeil.
