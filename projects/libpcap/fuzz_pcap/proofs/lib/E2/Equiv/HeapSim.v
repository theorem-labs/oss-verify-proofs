(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require NoRefuse. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_ReallocQ HeapFull Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Progress OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Logic OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Kernel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Embed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Raw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.NoRefuse OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.MI_Calloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.LB_WRealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_ReallocQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW HeapDrive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition hframe_ok (G : PS -> Model -> Prop) : Prop :=
  forall s h mo mo', vm_only mo mo' -> G s mo -> G (set_heap h s) mo'.

#[using="Type"] Lemma set_heap_eta (s : PS) : set_heap (ps_heap s) s = s.
Proof. destruct s; reflexivity. Qed.
#[using="Type"] Lemma set_heap_set_heap (h h' : fheap) (s : PS) : set_heap h (set_heap h' s) = set_heap h s.
Proof. destruct s; reflexivity. Qed.

#[using="Type"] Lemma hframe_frame G : hframe_ok G -> frame_ok G.
Proof.
  intros HG [hG lG oG tG] [hG' lG' oG' tG'] mo mo' Hr Hvo HGs. cbn in Hr. unfold set_heap in Hr. cbn in Hr.
  injection Hr. intros -> -> -> _ _. exact (HG (mkPS hG lG oG tG) hG' mo mo' Hvo HGs).
Qed.

#[using="Type"] Lemma hframe_set_heap G s h mo : hframe_ok G -> G s mo -> G (set_heap h s) mo.
Proof. intros HG H. apply (HG s h mo mo); [apply vm_only_refl| exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tok_szmap (h : fheap) : gmap N Z := snd <$> fh_blk h.
Definition tok_sizes (h : fheap) : list Z := map snd (tok_blocks h).

#[using="Type"] Lemma tok_sizes_eq h : tok_sizes h = map snd (map_to_list (tok_szmap h)).
Proof.
  unfold tok_sizes, tok_blocks, tok_szmap. rewrite map_to_list_fmap. rewrite !map_map. apply map_ext. intros [k [p n]]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition toks_agree (hG hC : fheap) : Prop := fh_next hG = fh_next hC /\ tok_szmap hG = tok_szmap hC.

#[using="Type"] Lemma toks_agree_sizes hG hC : toks_agree hG hC -> Permutation (tok_sizes hG) (tok_sizes hC).
Proof.
  intros [_ E]. rewrite !tok_sizes_eq, E. apply Permutation_refl.
Qed.

#[using="Type"] Lemma toks_agree_lookup hG hC k : toks_agree hG hC ->
  option_map snd (fh_blk hG !! k) = option_map snd (fh_blk hC !! k).
Proof.
  intros [_ E]. unfold tok_szmap in E. pose proof (f_equal (fun m => m !! k) E) as E1. cbn in E1. rewrite !lookup_fmap in E1. exact E1.
Qed.

(* [comment removed for export] *)
Definition toks_below (h : fheap) : Prop := forall k, fh_blk h !! k <> None -> (k < fh_next h)%N.

#[using="Type"] Lemma tok_blocks_insert h p n : toks_below h ->
  Permutation (tok_blocks (mkFH (fh_m h) (fh_brk h) (N.succ (fh_next h)) (<[fh_next h := (p, n)]> (fh_blk h))))
              ((p, n) :: tok_blocks h).
Proof.
  intros HB. unfold tok_blocks. cbn [fh_blk].
  assert (HN : fh_blk h !! fh_next h = None).
  { destruct (fh_blk h !! fh_next h) eqn:E; [| reflexivity]. exfalso. specialize (HB (fh_next h) ltac:(rewrite E; discriminate)). lia. }
  etransitivity; [apply Permutation_map; apply map_to_list_insert; exact HN|]. apply Permutation_refl.
Qed.

#[using="Type"] Lemma toks_below_insert h p n : toks_below h ->
  toks_below (mkFH (fh_m h) (fh_brk h) (N.succ (fh_next h)) (<[fh_next h := (p, n)]> (fh_blk h))).
Proof.
  intros HB k. cbn.
  destruct (N.eq_dec k (fh_next h)) as [->|NE].
  - intros _. lia.
  - rewrite lookup_insert_ne by (intros E; apply NE; symmetry; exact E). intros Hk. specialize (HB k Hk). lia.
Qed.

#[using="Type"] Lemma tok_blocks_delete h k p n : fh_blk h !! k = Some (p, n) ->
  Permutation (tok_blocks h) ((p, n) :: tok_blocks (mkFH (fh_m h) (fh_brk h) (fh_next h) (delete k (fh_blk h)))).
Proof.
  intros Hk. unfold tok_blocks. cbn [fh_blk].
  etransitivity; [apply Permutation_map; symmetry; apply (map_to_list_delete (fh_blk h) k (p, n)); exact Hk|].
  apply Permutation_refl.
Qed.

#[using="Type"] Lemma toks_below_delete h k : toks_below h -> toks_below (mkFH (fh_m h) (fh_brk h) (fh_next h) (delete k (fh_blk h))).
Proof.
  intros HB k'. cbn. destruct (N.eq_dec k' k) as [->|NE]; [rewrite lookup_delete_eq; intros H; exfalso; apply H; reflexivity|].
  rewrite lookup_delete_ne by (intros E; apply NE; symmetry; exact E). apply HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HQ (P : Z -> Z) (G : PS -> Model -> Prop) : assn PS := fun s mo =>
  FQ (tok_blocks (ps_heap s)) P G s mo /\ toks_below (ps_heap s).

#[using="Type"] Lemma HQ_G P G s mo : HQ P G s mo -> G s mo.
Proof. intros [[_ HG] _]. exact HG. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End WithCeil.

(* [comment removed for export] *)
Section Sim.
Context {CEG CEC : CEIL}.

Definition HR (P : Z -> Z) (GG GC : PS -> Model -> Prop) : @rel PS PS := fun sG moG sC moC =>
  HQ (CE:=CEG) P GG sG moG /\ HQ (CE:=CEC) P GC sC moC /\ toks_agree (ps_heap sG) (ps_heap sC).

Variable segs : list Segment.          (* [comment removed for export] *)
Variables (P : Z -> Z) (GG GC : PS -> Model -> Prop).
Hypothesis HGG : hframe_ok GG.
Hypothesis HGC : hframe_ok GC.
Local Notation MQ := malloc_core_fq_proof.

Let FGG : frame_ok GG := hframe_frame GG HGG.
Let FGC : frame_ok GC := hframe_frame GC HGC.

(* [comment removed for export] *)
Definition BM (ns : list Z) (n : Z) : Z := PHI P + R63N ns + bigb n - 3 * PGSZ.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_setup {CE : CEIL} X G s mo n :
  frame_ok G -> FQ X P G s mo -> 0 <= n -> bigb n <= QMAX -> ROOMN (map snd X) P n -> PHI P + R63N (map snd X) + bigb n <= BLIVE ->
  exists L LS BL, INVL x0 (ps_m s) L BL LS /\ Permutation X (map blk_ptr BL)
    /\ ftree L (malloc (ps_m s) n) (malloc_postQ (ps_m s) L BL P n)
    /\ fbnd8 (BM (map snd X) n) L (malloc (ps_m s) n)
    /\ DCTX (BM (map snd X) n) L G s mo
    /\ 0 <= BM (map snd X) n /\ BM (map snd X) n + PINB <= BLIVE.
Proof.
  intros HG HF Hn HBQ HR HB. pose proof (FQ_census X P G s mo HF) as (L0 & HK0 & HLI0 & HC0).
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HLI & HP) HGs].
  (* [comment removed for export] *)
  pose proof (regions_bound x0 (ps_m s) L BL LS P INV SI HAQ eq_refl) as RB. pose proof (ledger_bound x0 (ps_m s) L BL LS INV) as LB0.
  unfold ORPH in RB. cbn [x_orph x0] in RB.
  pose proof (R63N_eq X BL HP) as R63E. rewrite <- R63E in RB.
  exists L, LS, BL. split; [exact INV|]. split; [exact HP|].
  destruct (malloc_ftq MQ (ps_m s) L BL LS P n (BM (map snd X) n) INV SI HAQ Hn (ROOMN_eq X BL P n HP HR) ltac:(unfold BM; rewrite R63E; lia) HBQ) as [FT BD].
  split; [exact FT|]. split; [exact BD|].
  pose proof (gm_nonneg L (ps_brk s) mo HK). pose proof (BB_ge_brkreg L (ps_brk s) mo HK) as [_ ?]. pose proof PINB_nonneg. pose proof (bigb_nonneg n).
  unfold BM, PINB, PGSZ in *.
  split; [| split; lia].
  split; [exact HK|]. split; [exact HLI|]. split; [exact HGs|]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma commit_sim {A B} (stG stC : mstate) (pG : A) (pC : B) (RM : @rel PS PS) (Q : A -> B -> @rel PS PS) :
  (forall sG moG sC moC, RM sG moG sC moC -> Q pG pC (set_m stG sG) moG (set_m stC sC) moC) ->
  fsimw (npeek segs) RM (mbind (mupd (set_m stG)) (fun _ => mret pG)) (mbind (mupd (set_m stC)) (fun _ => mret pC)) Q.
Proof.
  intros H. eapply fsimw_bind with (Q1 := fun _ _ sG moG sC moC => exists s1 s0, sG = set_m stG s1 /\ sC = set_m stC s0 /\ RM s1 moG s0 moC).
  { apply fsimw_upd. intros sG moG sC moC HR. exists sG, sC. auto. }
  intros [] []. apply fsimw_ret. intros ? ? ? ? (s1 & s0 & -> & -> & HR). apply H. exact HR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma FQ_commit_malloc {CE : CEIL} X G (s : PS) st' L' BL LS' p c off n mo :
  hframe_ok G ->
  INVL x0 st' L' (((c, off), n) :: BL) LS' -> SINV x0 st' (((c, off), n) :: BL) -> AQ st' (((c, off), n) :: BL) P ->
  KL L' (ps_brk s) mo -> LI L' mo -> G s mo -> Permutation X (map blk_ptr BL) -> p = aadd c (UNIT * off) ->
  FQ ((p, n) :: X) P G (set_m st' s) mo.
Proof.
  intros HG INV SI HAQ HK HL HGs HP ->. split; [| apply (HG s _ mo mo); [apply vm_only_refl| exact HGs]].
  exists L', LS', (((c, off), n) :: BL). cbn [ps_m ps_brk fheap_AllocSt set_m ps_heap set_heap fh_m fh_brk map].
  split; [exact INV|]. split; [exact SI|]. split; [exact HAQ|]. split; [destruct s; exact HK|]. split; [exact HL|].
  apply perm_skip. exact HP.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rest_heap_eq (s s0 : PS) : ps_rest s = ps_rest s0 -> forall st, set_m st s = set_heap (mkFH st (fh_brk (ps_heap s)) (fh_next (ps_heap s0)) (fh_blk (ps_heap s0))) s0.
Proof.
  intros Hr st. destruct s as [h l o t], s0 as [h0 l0 o0 t0]. cbn in Hr. unfold set_heap in Hr. cbn in Hr. injection Hr. intros -> -> -> E1 E2.
  cbn. unfold set_heap. cbn. rewrite E1, E2. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="HGG HGC FGG FGC"] Lemma raw_mallocF_sim_pt n XG XC sG0 moG0 sC0 moC0 :
  0 <= n -> size_overflows n = false -> bigb n <= QMAX ->
  FQ (CE:=CEG) XG P GG sG0 moG0 -> FQ (CE:=CEC) XC P GC sC0 moC0 -> Permutation (map snd XG) (map snd XC) ->
  ROOMN (map snd XG) P n -> PHI P + R63N (map snd XG) + bigb n <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (raw_mallocF (CE:=CEG) peekG n) (raw_mallocF (CE:=CEC) peekG n)
        (fun rG rC sG moG sC moC => exists pG pC, rG = Some pG /\ rC = Some pC
            /\ FQ (CE:=CEG) ((pG, n) :: XG) P GG sG moG /\ FQ (CE:=CEC) ((pC, n) :: XC) P GC sC moC
            /\ ps_rest sG = ps_rest sG0 /\ ps_rest sC = ps_rest sC0 /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros Hn Hov HBQ FQG FQC HPX HR HB.
  assert (HRC : ROOMN (map snd XC) P n).
  { destruct HR as [R1 R2]. split; intros Hc; [rewrite <- (LRN_perm _ _ _ HPX); exact (R1 Hc)| rewrite <- (n63N_perm _ _ HPX); exact (R2 Hc)]. }
  assert (HBC : PHI P + R63N (map snd XC) + bigb n <= BLIVE) by (rewrite <- (R63N_perm _ _ HPX); exact HB).
  assert (EBM : BM (map snd XC) n = BM (map snd XG) n) by (unfold BM; rewrite (R63N_perm _ _ HPX); reflexivity).
  destruct (malloc_setup XG GG sG0 moG0 n FGG FQG Hn HBQ HR HB) as (LG & LSG & BLG & INVG & HPG & FTG & BDG & DG & B0 & B1).
  destruct (malloc_setup XC GC sC0 moC0 n FGC FQC Hn HBQ HRC HBC) as (LC & LSC & BLC & INVC & HPC & FTC & BDC & DC & _ & _).
  rewrite EBM in BDC, DC.
  unfold raw_mallocF. eapply fsimw_bind; [apply fsimw_get|].
  intros a b sG moG sC moC (-> & -> & -> & -> & -> & ->).
  refine (fsimw_bind _ _ _ _ _ _ _ _ (membedF_fsimw segs _ _ LG LC _ _ GG GC sG0 sC0 moG0 moC0 _ FGG FGC FTG BDG FTC BDC (conj B0 B1) DG DC) _
            sG0 moG0 sC0 moC0 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  intros [stG pG] [stC pC].
  apply commit_sim.
  intros sG moG sC moC (GPG & GPC & (LG' & FPG & PQG & DG') & (LC' & FPC & PQC & DC') & HmG & HxG & HvoG & HmC & HxC & HvoC).
  pose proof (gleaf_gpath _ (malloc_progress (ps_m sG0) n Hov) GPG) as RG. unfold res_ok in RG. cbn [snd] in RG.
  pose proof (gleaf_gpath _ (malloc_progress (ps_m sC0) n Hov) GPC) as RC. unfold res_ok in RC. cbn [snd] in RC.
  destruct pG as [pG|]; [| exfalso; apply RG; reflexivity]. destruct pC as [pC|]; [| exfalso; apply RC; reflexivity].
  exists pG, pC. split; [reflexivity|]. split; [reflexivity|].
  unfold malloc_postQ in PQG, PQC. cbn [fst snd] in PQG, PQC.
  destruct PQG as (_ & _ & cG & offG & LSG' & EpG & _ & INVG' & _ & SIG' & AQG'). destruct PQC as (_ & _ & cC & offC & LSC' & EpC & _ & INVC' & _ & SIC' & AQC').
  destruct DG' as (KG' & LIG' & GG' & _). destruct DC' as (KC' & LIC' & GC' & _).
  split; [eapply FQ_commit_malloc; eauto|]. split; [eapply FQ_commit_malloc; eauto|].
  autorewrite with alloc_lens. split; [exact HxG|]. split; [exact HxC|]. split; assumption.
Qed.
(* [comment removed for export] *)
Definition hins (p : aptr) (n : Z) (h : fheap) : fheap :=
  mkFH (fh_m h) (fh_brk h) (N.succ (fh_next h)) (<[fh_next h := (p, n)]> (fh_blk h)).

#[using="Type"] Lemma tok_fresh_sim (pG pC : aptr) n (RM : @rel PS PS) (Q : option hptr -> option hptr -> @rel PS PS) :
  (forall sG moG sC moC, RM sG moG sC moC ->
     Q (Some (fh_next (ps_heap sG))) (Some (fh_next (ps_heap sC))) (set_heap (hins pG n (ps_heap sG)) sG) moG (set_heap (hins pC n (ps_heap sC)) sC) moC) ->
  fsimw (npeek segs) RM (k <- tok_fresh pG n ;; mret (Some k)) (k <- tok_fresh pC n ;; mret (Some k)) Q.
Proof.
  intros H.
  eapply fsimw_bind with (Q1 := fun kG kC sG' moG sC' moC => exists sG sC, RM sG moG sC moC /\ kG = fh_next (ps_heap sG) /\ kC = fh_next (ps_heap sC)
                                   /\ sG' = set_heap (hins pG n (ps_heap sG)) sG /\ sC' = set_heap (hins pC n (ps_heap sC)) sC).
  { unfold tok_fresh. eapply fsimw_bind with (Q1 := fun a b sG moG sC moC => a = sG /\ b = sC /\ RM sG moG sC moC); [apply fsimw_get|].
    intros a b. eapply fsimw_bind with (Q1 := fun _ _ sG' moG sC' moC => RM a moG b moC /\ sG' = set_heap (hins pG n (ps_heap a)) a /\ sC' = set_heap (hins pC n (ps_heap b)) b).
    { apply fsimw_upd. intros sG moG sC moC (-> & -> & HR). split; [exact HR|]. split; reflexivity. }
    intros [] []. apply fsimw_ret. intros sG' moG sC' moC (HR & -> & ->). exists a, b. repeat split; auto. }
  intros kG kC. apply fsimw_ret. intros ? moG ? moC (sG & sC & HR & -> & -> & -> & ->). apply H. exact HR.
Qed.

#[using="Type"] Lemma rest_eq_heap (s s0 : PS) : ps_rest s = ps_rest s0 ->
  fh_next (ps_heap s) = fh_next (ps_heap s0) /\ fh_blk (ps_heap s) = fh_blk (ps_heap s0) /\ forall h, set_heap h s = set_heap h s0.
Proof.
  intros Hr. destruct s as [hs l o t], s0 as [h0 l0 o0 t0]. cbn in Hr. unfold set_heap in Hr. cbn in Hr. injection Hr. intros -> -> -> -> ->.
  repeat split; reflexivity.
Qed.

#[using="Type"] Lemma HQ_fresh {CE : CEIL} G (s : PS) p n mo :
  hframe_ok G -> FQ ((p, n) :: tok_blocks (ps_heap s)) P G s mo -> toks_below (ps_heap s) ->
  HQ P G (set_heap (hins p n (ps_heap s)) s) mo.
Proof.
  intros HG HF HB. split.
  - eapply FQ_perm; [symmetry; apply (tok_blocks_insert (ps_heap s) p n HB)|].
    eapply FQ_other; [exact HF| destruct s; reflexivity| destruct s; reflexivity| apply (HG s _ mo mo); [apply vm_only_refl| exact (FQ_G _ _ _ _ _ HF)]].
  - cbn. apply toks_below_insert. exact HB.
Qed.

(* [comment removed for export] *)
#[using="HGG HGC FGG FGC"] Theorem hf_malloc_sim_pt n sG0 moG0 sC0 moC0 :
  0 <= n -> size_overflows n = false -> bigb n <= QMAX ->
  HR P GG GC sG0 moG0 sC0 moC0 ->
  ROOMN (tok_sizes (ps_heap sG0)) P n -> PHI P + R63N (tok_sizes (ps_heap sG0)) + bigb n <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (hf_malloc (CE:=CEG) n) (hf_malloc (CE:=CEC) n)
        (fun a b sG moG sC moC =>
           a = Some (fh_next (ps_heap sG0)) /\ b = a /\ HR P GG GC sG moG sC moC
           /\ tok_szmap (ps_heap sG) = <[fh_next (ps_heap sG0) := n]> (tok_szmap (ps_heap sG0))
           /\ fh_next (ps_heap sG) = N.succ (fh_next (ps_heap sG0))
           /\ (forall h, set_heap h sG = set_heap h sG0) /\ (forall h, set_heap h sC = set_heap h sC0)
           /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros Hn Hov HBQ (HQG & HQC & HT) HR HB. destruct HQG as [FQG TBG]. destruct HQC as [FQC TBC].
  unfold hf_malloc. eapply fsimw_bind.
  { apply (raw_mallocF_sim_pt n (tok_blocks (ps_heap sG0)) (tok_blocks (ps_heap sC0)) sG0 moG0 sC0 moC0 Hn Hov HBQ FQG FQC);
      [exact (toks_agree_sizes _ _ HT)| exact HR| exact HB]. }
  intros rG rC sG moG sC moC (pG & pC & -> & -> & FQG' & FQC' & HxG & HxC & HvoG & HvoC). cbn iota.
  apply (tok_fresh_sim pG pC n (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC));
    [| repeat split; reflexivity].
  intros ? ? ? ? (-> & -> & -> & ->).
  destruct (rest_eq_heap sG sG0 HxG) as (NG & BG & SG). destruct (rest_eq_heap sC sC0 HxC) as (NC & BC & SC).
  destruct HT as [HTn HTs].
  assert (EBG : tok_blocks (ps_heap sG) = tok_blocks (ps_heap sG0)) by (unfold tok_blocks; rewrite BG; reflexivity).
  assert (EBC : tok_blocks (ps_heap sC) = tok_blocks (ps_heap sC0)) by (unfold tok_blocks; rewrite BC; reflexivity).
  split; [rewrite NG; reflexivity|]. split; [rewrite NG, NC, HTn; reflexivity|].
  split.
  { split; [apply HQ_fresh; [exact HGG| rewrite EBG; exact FQG'| unfold toks_below; rewrite NG, BG; exact TBG]|].
    split; [apply HQ_fresh; [exact HGC| rewrite EBC; exact FQC'| unfold toks_below; rewrite NC, BC; exact TBC]|].
    split; [cbn; rewrite NG, NC, HTn; reflexivity|].
    unfold tok_szmap. cbn. rewrite !fmap_insert. cbn. unfold tok_szmap in HTs. rewrite NG, NC, BG, BC, HTs, HTn. reflexivity. }
  split; [unfold tok_szmap; cbn; rewrite fmap_insert, NG, BG; reflexivity|].
  split; [cbn; rewrite NG; reflexivity|].
  split; [intros h; rewrite set_heap_set_heap; apply SG|]. split; [intros h; rewrite set_heap_set_heap; apply SC|].
  split; assumption.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma calloc_setup {CE : CEIL} X G s mo m n :
  frame_ok G -> FQ X P G s mo -> 0 <= m -> 0 <= n -> bigb (m * n) <= QMAX -> ROOMN (map snd X) P (m * n) -> PHI P + R63N (map snd X) + bigb (m * n) <= BLIVE ->
  exists L LS BL, INVL x0 (ps_m s) L BL LS /\ Permutation X (map blk_ptr BL)
    /\ ftree L (calloc (ps_m s) m n) (malloc_postQ (ps_m s) L BL P (m * n))
    /\ fbnd8 (BM (map snd X) (m * n)) L (calloc (ps_m s) m n)
    /\ DCTX (BM (map snd X) (m * n)) L G s mo
    /\ 0 <= BM (map snd X) (m * n) /\ BM (map snd X) (m * n) + PINB <= BLIVE.
Proof.
  intros HG HF Hm Hn HBQ HR HB.
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HLI & HP) HGs].
  pose proof (regions_bound x0 (ps_m s) L BL LS P INV SI HAQ eq_refl) as RB. pose proof (ledger_bound x0 (ps_m s) L BL LS INV) as LB0.
  unfold ORPH in RB. cbn [x_orph x0] in RB.
  pose proof (R63N_eq X BL HP) as R63E. rewrite <- R63E in RB.
  exists L, LS, BL. split; [exact INV|]. split; [exact HP|].
  destruct (calloc_ftq MQ (ps_m s) L BL LS P m n (BM (map snd X) (m * n)) INV SI HAQ Hm Hn (ROOMN_eq X BL P (m * n) HP HR) ltac:(unfold BM; rewrite R63E; lia) HBQ) as [FT BD].
  split; [exact FT|]. split; [exact BD|].
  pose proof (gm_nonneg L (ps_brk s) mo HK). pose proof (BB_ge_brkreg L (ps_brk s) mo HK) as [_ ?]. pose proof PINB_nonneg. pose proof (bigb_nonneg (m * n)).
  unfold BM, PINB, PGSZ in *.
  split; [| split; lia].
  split; [exact HK|]. split; [exact HLI|]. split; [exact HGs|]. lia.
Qed.

#[using="HGG HGC FGG FGC"] Lemma raw_callocF_sim_pt m n XG XC sG0 moG0 sC0 moC0 :
  0 <= m -> 0 <= n -> (negb (n =? 0) && (SIZE_MAX / n <? m)) = false -> size_overflows (m * n) = false -> bigb (m * n) <= QMAX ->
  FQ (CE:=CEG) XG P GG sG0 moG0 -> FQ (CE:=CEC) XC P GC sC0 moC0 -> Permutation (map snd XG) (map snd XC) ->
  ROOMN (map snd XG) P (m * n) -> PHI P + R63N (map snd XG) + bigb (m * n) <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (raw_callocF (CE:=CEG) peekG m n) (raw_callocF (CE:=CEC) peekG m n)
        (fun rG rC sG moG sC moC => exists pG pC, rG = Some pG /\ rC = Some pC
            /\ FQ (CE:=CEG) ((pG, m * n) :: XG) P GG sG moG /\ FQ (CE:=CEC) ((pC, m * n) :: XC) P GC sC moC
            /\ ps_rest sG = ps_rest sG0 /\ ps_rest sC = ps_rest sC0 /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros Hm Hn Hov1 Hov2 HBQ FQG FQC HPX HR HB.
  assert (HRC : ROOMN (map snd XC) P (m * n)).
  { destruct HR as [R1 R2]. split; intros Hc; [rewrite <- (LRN_perm _ _ _ HPX); exact (R1 Hc)| rewrite <- (n63N_perm _ _ HPX); exact (R2 Hc)]. }
  assert (HBC : PHI P + R63N (map snd XC) + bigb (m * n) <= BLIVE) by (rewrite <- (R63N_perm _ _ HPX); exact HB).
  assert (EBM : BM (map snd XC) (m * n) = BM (map snd XG) (m * n)) by (unfold BM; rewrite (R63N_perm _ _ HPX); reflexivity).
  destruct (calloc_setup XG GG sG0 moG0 m n FGG FQG Hm Hn HBQ HR HB) as (LG & LSG & BLG & INVG & HPG & FTG & BDG & DG & B0 & B1).
  destruct (calloc_setup XC GC sC0 moC0 m n FGC FQC Hm Hn HBQ HRC HBC) as (LC & LSC & BLC & INVC & HPC & FTC & BDC & DC & _ & _).
  rewrite EBM in BDC, DC.
  unfold raw_callocF. eapply fsimw_bind; [apply fsimw_get|].
  intros a b sG moG sC moC (-> & -> & -> & -> & -> & ->).
  refine (fsimw_bind _ _ _ _ _ _ _ _ (membedF_fsimw segs _ _ LG LC _ _ GG GC sG0 sC0 moG0 moC0 _ FGG FGC FTG BDG FTC BDC (conj B0 B1) DG DC) _
            sG0 moG0 sC0 moC0 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  intros [stG pG] [stC pC].
  apply commit_sim.
  intros sG moG sC moC (GPG & GPC & (LG' & FPG & PQG & DG') & (LC' & FPC & PQC & DC') & HmG & HxG & HvoG & HmC & HxC & HvoC).
  pose proof (gleaf_gpath _ (calloc_progress (ps_m sG0) m n Hov1 Hov2) GPG) as RG. unfold res_ok in RG. cbn [snd] in RG.
  pose proof (gleaf_gpath _ (calloc_progress (ps_m sC0) m n Hov1 Hov2) GPC) as RC. unfold res_ok in RC. cbn [snd] in RC.
  destruct pG as [pG|]; [| exfalso; apply RG; reflexivity]. destruct pC as [pC|]; [| exfalso; apply RC; reflexivity].
  exists pG, pC. split; [reflexivity|]. split; [reflexivity|].
  unfold malloc_postQ in PQG, PQC. cbn [fst snd] in PQG, PQC.
  destruct PQG as (_ & _ & cG & offG & LSG' & EpG & _ & INVG' & _ & SIG' & AQG'). destruct PQC as (_ & _ & cC & offC & LSC' & EpC & _ & INVC' & _ & SIC' & AQC').
  destruct DG' as (KG' & LIG' & GG' & _). destruct DC' as (KC' & LIC' & GC' & _).
  split; [eapply FQ_commit_malloc; eauto|]. split; [eapply FQ_commit_malloc; eauto|].
  autorewrite with alloc_lens. split; [exact HxG|]. split; [exact HxC|]. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="HGG HGC FGG FGC"] Theorem hf_calloc_sim_pt m n sG0 moG0 sC0 moC0 :
  0 <= m -> 0 <= n -> (negb (n =? 0) && (SIZE_MAX / n <? m)) = false -> size_overflows (m * n) = false -> bigb (m * n) <= QMAX ->
  HR P GG GC sG0 moG0 sC0 moC0 ->
  ROOMN (tok_sizes (ps_heap sG0)) P (m * n) -> PHI P + R63N (tok_sizes (ps_heap sG0)) + bigb (m * n) <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (hf_calloc (CE:=CEG) m n) (hf_calloc (CE:=CEC) m n)
        (fun a b sG moG sC moC =>
           a = Some (fh_next (ps_heap sG0)) /\ b = a /\ HR P GG GC sG moG sC moC
           /\ tok_szmap (ps_heap sG) = <[fh_next (ps_heap sG0) := m * n]> (tok_szmap (ps_heap sG0))
           /\ fh_next (ps_heap sG) = N.succ (fh_next (ps_heap sG0))
           /\ (forall h, set_heap h sG = set_heap h sG0) /\ (forall h, set_heap h sC = set_heap h sC0)
           /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros Hm Hn Hov1 Hov2 HBQ (HQG & HQC & HT) HR HB. destruct HQG as [FQG TBG]. destruct HQC as [FQC TBC].
  unfold hf_calloc. eapply fsimw_bind.
  { apply (raw_callocF_sim_pt m n (tok_blocks (ps_heap sG0)) (tok_blocks (ps_heap sC0)) sG0 moG0 sC0 moC0 Hm Hn Hov1 Hov2 HBQ FQG FQC);
      [exact (toks_agree_sizes _ _ HT)| exact HR| exact HB]. }
  intros rG rC sG moG sC moC (pG & pC & -> & -> & FQG' & FQC' & HxG & HxC & HvoG & HvoC). cbn iota.
  apply (tok_fresh_sim pG pC (m * n) (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC));
    [| repeat split; reflexivity].
  intros ? ? ? ? (-> & -> & -> & ->).
  destruct (rest_eq_heap sG sG0 HxG) as (NG & BG & SG). destruct (rest_eq_heap sC sC0 HxC) as (NC & BC & SC).
  destruct HT as [HTn HTs].
  assert (EBG : tok_blocks (ps_heap sG) = tok_blocks (ps_heap sG0)) by (unfold tok_blocks; rewrite BG; reflexivity).
  assert (EBC : tok_blocks (ps_heap sC) = tok_blocks (ps_heap sC0)) by (unfold tok_blocks; rewrite BC; reflexivity).
  split; [rewrite NG; reflexivity|]. split; [rewrite NG, NC, HTn; reflexivity|].
  split.
  { split; [apply HQ_fresh; [exact HGG| rewrite EBG; exact FQG'| unfold toks_below; rewrite NG, BG; exact TBG]|].
    split; [apply HQ_fresh; [exact HGC| rewrite EBC; exact FQC'| unfold toks_below; rewrite NC, BC; exact TBC]|].
    split; [cbn; rewrite NG, NC, HTn; reflexivity|].
    unfold tok_szmap. cbn. rewrite !fmap_insert. cbn. unfold tok_szmap in HTs. rewrite NG, NC, BG, BC, HTs, HTn. reflexivity. }
  split; [unfold tok_szmap; cbn; rewrite fmap_insert, NG, BG; reflexivity|].
  split; [cbn; rewrite NG; reflexivity|].
  split; [intros h; rewrite set_heap_set_heap; apply SG|]. split; [intros h; rewrite set_heap_set_heap; apply SC|].
  split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BF (ns : list Z) : Z := PHI P + R63N ns - 3 * PGSZ.

Definition free_post {CE : CEIL} (st : mstate) (BL : list blk) (c : cptr) (L' : mled) (st' : mstate) : Prop :=
  exists LS', INVL x0 st' L' (bl_remove c BL) LS' /\ SINV x0 st' (bl_remove c BL) /\ AQ st' (bl_remove c BL) P.

#[using="Type"] Lemma free_setup {CE : CEIL} X X' G s mo p n :
  frame_ok G -> FQ X P G s mo -> Permutation X ((p, n) :: X') -> PHI P + R63N (map snd X) <= BLIVE ->
  exists L LS BL c off, INVL x0 (ps_m s) L BL LS /\ In ((c, off), n) BL /\ p = aadd c (UNIT * off)
    /\ Permutation X' (map blk_ptr (bl_remove c BL))
    /\ ftree L (free (ps_m s) (Some p)) (free_post (ps_m s) BL c)
    /\ fbnd8 (BF (map snd X)) L (free (ps_m s) (Some p))
    /\ DCTX (BF (map snd X)) L G s mo
    /\ 0 <= BF (map snd X) /\ BF (map snd X) + PINB <= BLIVE.
Proof.
  intros HG HF HPX HB.
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HLI & HP) HGs].
  pose proof (regions_bound x0 (ps_m s) L BL LS P INV SI HAQ eq_refl) as RB. pose proof (ledger_bound x0 (ps_m s) L BL LS INV) as LB0.
  unfold ORPH in RB. cbn [x_orph x0] in RB.
  pose proof (R63N_eq X BL HP) as R63E. rewrite <- R63E in RB.
  assert (Hin : In (p, n) (map blk_ptr BL)) by (eapply Permutation_in; [exact HP|]; eapply Permutation_in; [symmetry; exact HPX| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n'] & Ebp & Hk). unfold blk_ptr in Ebp. cbn [bslot boff bsize fst snd] in Ebp.
  assert (En : n' = n) by congruence. subst n'. assert (Ep : p = aadd c (UNIT * off)) by congruence.
  exists L, LS, BL, c, off. split; [exact INV|]. split; [exact Hk|]. split; [exact Ep|].
  split.
  { pose proof (blk_ptr_remove_perm c off n BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP.
    apply (Permutation_cons_inv (a := (p, n))). etransitivity; [symmetry; exact HPX|]. etransitivity; [exact HP|]. rewrite Ep.
    change (blk_ptr (c, off, n)) with (aadd c (UNIT * off), n) in BP. exact BP. }
  pose proof (free_fq (ps_m s) L BL LS P c off n (BF (map snd X)) INV SI HAQ Hk ltac:(unfold BF; rewrite R63E; lia)) as FQT. rewrite <- Ep in FQT.
  split; [exact (fqtree_ftree _ _ _ _ FQT)|]. split; [exact (fqtree_fbnd8 _ _ _ _ FQT)|].
  pose proof (gm_nonneg L (ps_brk s) mo HK). pose proof (BB_ge_brkreg L (ps_brk s) mo HK) as [_ ?]. pose proof PINB_nonneg.
  unfold BF, PINB, PGSZ in *.
  split; [| split; lia].
  split; [exact HK|]. split; [exact HLI|]. split; [exact HGs|]. lia.
Qed.

#[using="Type"] Lemma FQ_commit_free {CE : CEIL} X' G (s : PS) st' L' BL LS' c mo :
  hframe_ok G ->
  INVL x0 st' L' (bl_remove c BL) LS' -> SINV x0 st' (bl_remove c BL) -> AQ st' (bl_remove c BL) P ->
  KL L' (ps_brk s) mo -> LI L' mo -> G s mo -> Permutation X' (map blk_ptr (bl_remove c BL)) ->
  FQ X' P G (set_m st' s) mo.
Proof.
  intros HG INV SI HAQ HK HL HGs HP. split; [| apply (HG s _ mo mo); [apply vm_only_refl| exact HGs]].
  exists L', LS', (bl_remove c BL). cbn [ps_m ps_brk fheap_AllocSt set_m ps_heap set_heap fh_m fh_brk map].
  split; [exact INV|]. split; [exact SI|]. split; [exact HAQ|]. split; [destruct s; exact HK|]. split; [exact HL| exact HP].
Qed.

#[using="HGG HGC FGG FGC"] Lemma raw_freeF_sim_pt pG pC n XG XG' XC XC' sG0 moG0 sC0 moC0 :
  FQ (CE:=CEG) XG P GG sG0 moG0 -> FQ (CE:=CEC) XC P GC sC0 moC0 ->
  Permutation XG ((pG, n) :: XG') -> Permutation XC ((pC, n) :: XC') -> Permutation (map snd XG') (map snd XC') ->
  PHI P + R63N (map snd XG) <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (raw_freeF (CE:=CEG) peekG pG) (raw_freeF (CE:=CEC) peekG pC)
        (fun _ _ sG moG sC moC => FQ (CE:=CEG) XG' P GG sG moG /\ FQ (CE:=CEC) XC' P GC sC moC
            /\ ps_rest sG = ps_rest sG0 /\ ps_rest sC = ps_rest sC0 /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros FQG FQC HPG HPC HPX HB.
  assert (HPXX : Permutation (map snd XG) (map snd XC)).
  { etransitivity; [apply Permutation_map; exact HPG|]. etransitivity; [| apply Permutation_map; symmetry; exact HPC]. cbn [map snd]. apply perm_skip. exact HPX. }
  assert (HBC : PHI P + R63N (map snd XC) <= BLIVE) by (rewrite <- (R63N_perm _ _ HPXX); exact HB).
  assert (EBF : BF (map snd XC) = BF (map snd XG)) by (unfold BF; rewrite (R63N_perm _ _ HPXX); reflexivity).
  destruct (free_setup XG XG' GG sG0 moG0 pG n FGG FQG HPG HB) as (LG & LSG & BLG & cG & offG & INVG & HkG & EpG & HPG' & FTG & BDG & DG & B0 & B1).
  destruct (free_setup XC XC' GC sC0 moC0 pC n FGC FQC HPC HBC) as (LC & LSC & BLC & cC & offC & INVC & HkC & EpC & HPC' & FTC & BDC & DC & _ & _).
  rewrite EBF in BDC, DC.
  unfold raw_freeF. eapply fsimw_bind; [apply fsimw_get|].
  intros a b sG moG sC moC (-> & -> & -> & -> & -> & ->).
  refine (fsimw_bind _ _ _ _ _ _ _ _ (membedF_fsimw segs _ _ LG LC _ _ GG GC sG0 sC0 moG0 moC0 _ FGG FGC FTG BDG FTC BDC (conj B0 B1) DG DC) _
            sG0 moG0 sC0 moC0 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  intros stG stC. apply fsimw_upd.
  intros sG moG sC moC (GPG & GPC & (LG' & FPG & PQG & DG') & (LC' & FPC & PQC & DC') & HmG & HxG & HvoG & HmC & HxC & HvoC).
  destruct PQG as (LSG' & INVG' & SIG' & AQG'). destruct PQC as (LSC' & INVC' & SIC' & AQC').
  destruct DG' as (KG' & LIG' & GG' & _). destruct DC' as (KC' & LIC' & GC' & _).
  split; [eapply FQ_commit_free; eauto|]. split; [eapply FQ_commit_free; eauto|].
  autorewrite with alloc_lens. split; [exact HxG|]. split; [exact HxC|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition hdel (k : hptr) (h : fheap) : fheap := mkFH (fh_m h) (fh_brk h) (fh_next h) (delete k (fh_blk h)).

#[using="Type"] Lemma HQ_drop {CE : CEIL} G (s : PS) k p n mo :
  hframe_ok G -> fh_blk (ps_heap s) !! k = Some (p, n) ->
  (forall X', Permutation (tok_blocks (ps_heap s)) ((p, n) :: X') -> FQ X' P G s mo) -> toks_below (ps_heap s) ->
  HQ P G (set_heap (hdel k (ps_heap s)) s) mo.
Proof.
  intros HG Hk HF HB. split.
  - eapply FQ_other; [apply HF; apply (tok_blocks_delete (ps_heap s) k p n Hk)| destruct s; reflexivity| destruct s; reflexivity|].
    apply (HG s _ mo mo); [apply vm_only_refl|]. exact (FQ_G _ _ _ _ _ (HF _ (tok_blocks_delete (ps_heap s) k p n Hk))).
  - cbn. apply toks_below_delete. exact HB.
Qed.

(* [comment removed for export] *)
#[using="HGG HGC FGG FGC"] Theorem hf_free_sim_pt k n sG0 moG0 sC0 moC0 :
  HR P GG GC sG0 moG0 sC0 moC0 ->
  tok_szmap (ps_heap sG0) !! k = Some n ->
  PHI P + R63N (tok_sizes (ps_heap sG0)) <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (hf_free (CE:=CEG) k) (hf_free (CE:=CEC) k)
        (fun _ _ sG moG sC moC =>
           HR P GG GC sG moG sC moC
           /\ tok_szmap (ps_heap sG) = delete k (tok_szmap (ps_heap sG0))
           /\ fh_next (ps_heap sG) = fh_next (ps_heap sG0)
           /\ (forall h, set_heap h sG = set_heap h sG0) /\ (forall h, set_heap h sC = set_heap h sC0)
           /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros (HQG & HQC & HT) Hk HB. destruct HQG as [FQG TBG]. destruct HQC as [FQC TBC].
  pose proof (toks_agree_lookup _ _ k HT) as HkC. destruct HT as [HTn HTs].
  assert (HkG : exists pG, fh_blk (ps_heap sG0) !! k = Some (pG, n)).
  { unfold tok_szmap in Hk. rewrite lookup_fmap in Hk. destruct (fh_blk (ps_heap sG0) !! k) as [[pG n']|]; cbn in Hk; [| discriminate]. injection Hk as ->. exists pG. reflexivity. }
  destruct HkG as [pG HkG]. rewrite HkG in HkC. cbn in HkC.
  destruct (fh_blk (ps_heap sC0) !! k) as [[pC nC]|] eqn:HkC'; rewrite HkC' in HkC; cbn in HkC; [| discriminate]. injection HkC as EnC. subst nC.
  unfold hf_free, tok_lookup.
  eapply fsimw_bind with (Q1 := fun bG bC sG moG sC moC => bG = Some (pG, n) /\ bC = Some (pC, n) /\ sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0).
  { eapply fsimw_bind; [apply fsimw_get|]. intros a b. apply fsimw_ret. intros sG moG sC moC (-> & -> & -> & -> & -> & ->). rewrite HkG, HkC'. repeat split; reflexivity. }
  intros bG bC sG moG sC moC (-> & -> & -> & -> & -> & ->). cbn iota.
  pose proof (tok_blocks_delete (ps_heap sG0) k pG n HkG) as PDG. pose proof (tok_blocks_delete (ps_heap sC0) k pC n HkC') as PDC.
  refine (fsimw_bind _ _ _ _ _ _ _ _
            (raw_freeF_sim_pt pG pC n (tok_blocks (ps_heap sG0)) (tok_blocks (hdel k (ps_heap sG0))) (tok_blocks (ps_heap sC0)) (tok_blocks (hdel k (ps_heap sC0)))
               sG0 moG0 sC0 moC0 FQG FQC PDG PDC _ HB) _
            sG0 moG0 sC0 moC0 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  { (* [comment removed for export] *)
    change (Permutation (tok_sizes (hdel k (ps_heap sG0))) (tok_sizes (hdel k (ps_heap sC0)))). rewrite !tok_sizes_eq.
    unfold tok_szmap, hdel. cbn [fh_blk]. rewrite !fmap_delete. unfold tok_szmap in HTs. rewrite HTs. apply Permutation_refl. }
  intros [] []. unfold tok_drop. apply fsimw_upd.
  intros sG moG sC moC (FQG' & FQC' & HxG & HxC & HvoG & HvoC).
  destruct (rest_eq_heap sG sG0 HxG) as (NG & BG & SG). destruct (rest_eq_heap sC sC0 HxC) as (NC & BC & SC).
  assert (EBG : tok_blocks (hdel k (ps_heap sG)) = tok_blocks (hdel k (ps_heap sG0))) by (unfold tok_blocks, hdel; cbn; rewrite BG; reflexivity).
  assert (EBC : tok_blocks (hdel k (ps_heap sC)) = tok_blocks (hdel k (ps_heap sC0))) by (unfold tok_blocks, hdel; cbn; rewrite BC; reflexivity).
  split.
  { split.
    { change (HQ (CE:=CEG) P GG (set_heap (hdel k (ps_heap sG)) sG) moG). apply (HQ_drop GG sG k pG n moG HGG); [rewrite BG; exact HkG| | unfold toks_below; rewrite NG, BG; exact TBG].
      intros X' HPX'. eapply FQ_perm; [| rewrite <- EBG in FQG'; exact FQG'].
      apply (Permutation_cons_inv (a := (pG, n))). etransitivity; [| exact HPX']. symmetry. rewrite EBG. unfold tok_blocks. rewrite BG. exact PDG. }
    split.
    { change (HQ (CE:=CEC) P GC (set_heap (hdel k (ps_heap sC)) sC) moC). apply (HQ_drop GC sC k pC n moC HGC); [rewrite BC; exact HkC'| | unfold toks_below; rewrite NC, BC; exact TBC].
      intros X' HPX'. eapply FQ_perm; [| rewrite <- EBC in FQC'; exact FQC'].
      apply (Permutation_cons_inv (a := (pC, n))). etransitivity; [| exact HPX']. symmetry. rewrite EBC. unfold tok_blocks. rewrite BC. exact PDC. }
    split; [cbn; rewrite NG, NC, HTn; reflexivity|].
    unfold tok_szmap. cbn. rewrite !fmap_delete. unfold tok_szmap in HTs. rewrite BG, BC, HTs. reflexivity. }
  split; [unfold tok_szmap; cbn; rewrite fmap_delete, BG; reflexivity|].
  split; [cbn; rewrite NG; reflexivity|].
  split; [intros h; rewrite set_heap_set_heap; apply SG|]. split; [intros h; rewrite set_heap_set_heap; apply SC|].
  split; assumption.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma realloc_setup {CE : CEIL} X X' G s mo p n n' :
  frame_ok G -> FQ X P G s mo -> Permutation X ((p, n) :: X') ->
  0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  ROOMN (map snd X) P n' -> PHI P + R63N (map snd X) + bigb n' <= BLIVE ->
  exists L LS BL c off, INVL x0 (ps_m s) L BL LS /\ In ((c, off), n) BL /\ p = aadd c (UNIT * off)
    /\ Permutation X' (map blk_ptr (bl_remove c BL))
    /\ ftree L (realloc (ps_m s) (Some p) n') (realloc_postQ (ps_m s) BL P c n')
    /\ fbnd8 (BM (map snd X) n') L (realloc (ps_m s) (Some p) n')
    /\ DCTX (BM (map snd X) n') L G s mo
    /\ 0 <= BM (map snd X) n' /\ BM (map snd X) n' + PINB <= BLIVE.
Proof.
  intros HG HF HPX Hn' Hov Hnx HBQ HR HB.
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HLI & HP) HGs].
  pose proof (regions_bound x0 (ps_m s) L BL LS P INV SI HAQ eq_refl) as RB. pose proof (ledger_bound x0 (ps_m s) L BL LS INV) as LB0.
  unfold ORPH in RB. cbn [x_orph x0] in RB.
  pose proof (R63N_eq X BL HP) as R63E. rewrite <- R63E in RB.
  assert (Hin : In (p, n) (map blk_ptr BL)) by (eapply Permutation_in; [exact HP|]; eapply Permutation_in; [symmetry; exact HPX| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n_] & Ebp & Hk). unfold blk_ptr in Ebp. cbn [bslot boff bsize fst snd] in Ebp.
  assert (En : n_ = n) by congruence. subst n_. assert (Ep : p = aadd c (UNIT * off)) by congruence.
  exists L, LS, BL, c, off. split; [exact INV|]. split; [exact Hk|]. split; [exact Ep|].
  split.
  { pose proof (blk_ptr_remove_perm c off n BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP.
    apply (Permutation_cons_inv (a := (p, n))). etransitivity; [symmetry; exact HPX|]. etransitivity; [exact HP|]. rewrite Ep.
    change (blk_ptr (c, off, n)) with (aadd c (UNIT * off), n) in BP. exact BP. }
  destruct (realloc_ftq MQ P (BM (map snd X) n') (ps_m s) L BL LS c off n n' INV SI HAQ Hk Hn' Hov Hnx (ROOMN_eq X BL P n' HP HR)
              ltac:(unfold BM; rewrite R63E; lia) HBQ) as [FT BD]. rewrite <- Ep in FT, BD.
  split; [exact FT|]. split; [exact BD|].
  pose proof (gm_nonneg L (ps_brk s) mo HK). pose proof (BB_ge_brkreg L (ps_brk s) mo HK) as [_ ?]. pose proof PINB_nonneg. pose proof (bigb_nonneg n').
  unfold BM, PINB, PGSZ in *.
  split; [| split; lia].
  split; [exact HK|]. split; [exact HLI|]. split; [exact HGs|]. lia.
Qed.

#[using="HGG HGC FGG FGC"] Lemma raw_reallocF_sim_pt pG pC n n' XG XG' XC XC' sG0 moG0 sC0 moC0 :
  0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  FQ (CE:=CEG) XG P GG sG0 moG0 -> FQ (CE:=CEC) XC P GC sC0 moC0 ->
  Permutation XG ((pG, n) :: XG') -> Permutation XC ((pC, n) :: XC') -> Permutation (map snd XG') (map snd XC') ->
  ROOMN (map snd XG) P n' -> PHI P + R63N (map snd XG) + bigb n' <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (raw_reallocF (CE:=CEG) peekG (Some pG) n') (raw_reallocF (CE:=CEC) peekG (Some pC) n')
        (fun rG rC sG moG sC moC => exists qG qC, rG = Some qG /\ rC = Some qC
            /\ FQ (CE:=CEG) ((qG, n') :: XG') P GG sG moG /\ FQ (CE:=CEC) ((qC, n') :: XC') P GC sC moC
            /\ ps_rest sG = ps_rest sG0 /\ ps_rest sC = ps_rest sC0 /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros Hn' Hov Hnx HBQ FQG FQC HPG HPC HPX HR HB.
  assert (HPXX : Permutation (map snd XG) (map snd XC)).
  { etransitivity; [apply Permutation_map; exact HPG|]. etransitivity; [| apply Permutation_map; symmetry; exact HPC]. cbn [map snd]. apply perm_skip. exact HPX. }
  assert (HRC : ROOMN (map snd XC) P n').
  { destruct HR as [R1 R2]. split; intros Hc; [rewrite <- (LRN_perm _ _ _ HPXX); exact (R1 Hc)| rewrite <- (n63N_perm _ _ HPXX); exact (R2 Hc)]. }
  assert (HBC : PHI P + R63N (map snd XC) + bigb n' <= BLIVE) by (rewrite <- (R63N_perm _ _ HPXX); exact HB).
  assert (EBM : BM (map snd XC) n' = BM (map snd XG) n') by (unfold BM; rewrite (R63N_perm _ _ HPXX); reflexivity).
  destruct (realloc_setup XG XG' GG sG0 moG0 pG n n' FGG FQG HPG Hn' Hov Hnx HBQ HR HB) as (LG & LSG & BLG & cG & offG & INVG & HkG & EpG & HPG' & FTG & BDG & DG & B0 & B1).
  destruct (realloc_setup XC XC' GC sC0 moC0 pC n n' FGC FQC HPC Hn' Hov Hnx HBQ HRC HBC) as (LC & LSC & BLC & cC & offC & INVC & HkC & EpC & HPC' & FTC & BDC & DC & _ & _).
  rewrite EBM in BDC, DC.
  unfold raw_reallocF. eapply fsimw_bind; [apply fsimw_get|].
  intros a b sG moG sC moC (-> & -> & -> & -> & -> & ->).
  refine (fsimw_bind _ _ _ _ _ _ _ _ (membedF_fsimw segs _ _ LG LC _ _ GG GC sG0 sC0 moG0 moC0 _ FGG FGC FTG BDG FTC BDC (conj B0 B1) DG DC) _
            sG0 moG0 sC0 moC0 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  intros [stG qG] [stC qC].
  apply commit_sim.
  intros sG moG sC moC (GPG & GPC & (LG' & FPG & PQG & DG') & (LC' & FPC & PQC & DC') & HmG & HxG & HvoG & HmC & HxC & HvoC).
  pose proof (gleaf_gpath _ (realloc_progress (ps_m sG0) (Some pG) n' Hov) GPG) as RG. unfold res_ok in RG. cbn [snd] in RG.
  pose proof (gleaf_gpath _ (realloc_progress (ps_m sC0) (Some pC) n' Hov) GPC) as RC. unfold res_ok in RC. cbn [snd] in RC.
  destruct qG as [qG|]; [| exfalso; apply RG; reflexivity]. destruct qC as [qC|]; [| exfalso; apply RC; reflexivity].
  exists qG, qC. split; [reflexivity|]. split; [reflexivity|].
  unfold realloc_postQ in PQG, PQC. cbn [fst snd] in PQG, PQC.
  destruct PQG as [(cG' & offG' & LSG' & EqG & _ & INVG' & _ & SIG' & AQG') _]. destruct PQC as [(cC' & offC' & LSC' & EqC & _ & INVC' & _ & SIC' & AQC') _].
  destruct DG' as (KG' & LIG' & GG' & _). destruct DC' as (KC' & LIC' & GC' & _).
  split; [eapply FQ_commit_malloc; eauto|]. split; [eapply FQ_commit_malloc; eauto|].
  autorewrite with alloc_lens. split; [exact HxG|]. split; [exact HxC|]. split; assumption.
Qed.

#[using="Type"] Lemma ps_heap_set_heap (h : fheap) (s : PS) : ps_heap (set_heap h s) = h.
Proof. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
#[using="HGG HGC FGG FGC"] Theorem hf_realloc_sim_pt k n n' sG0 moG0 sC0 moC0 :
  0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  HR P GG GC sG0 moG0 sC0 moC0 ->
  tok_szmap (ps_heap sG0) !! k = Some n ->
  ROOMN (tok_sizes (ps_heap sG0)) P n' -> PHI P + R63N (tok_sizes (ps_heap sG0)) + bigb n' <= BLIVE ->
  fsimw (npeek segs) (fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0)
        (hf_realloc (CE:=CEG) k n') (hf_realloc (CE:=CEC) k n')
        (fun a b sG moG sC moC =>
           a = Some (fh_next (ps_heap sG0)) /\ b = a /\ HR P GG GC sG moG sC moC
           /\ tok_szmap (ps_heap sG) = <[fh_next (ps_heap sG0) := n']> (delete k (tok_szmap (ps_heap sG0)))
           /\ fh_next (ps_heap sG) = N.succ (fh_next (ps_heap sG0))
           /\ (forall h, set_heap h sG = set_heap h sG0) /\ (forall h, set_heap h sC = set_heap h sC0)
           /\ vm_only moG0 moG /\ vm_only moC0 moC).
Proof.
  intros Hn' Hov Hnx HBQ (HQG & HQC & HT) Hk HR HB. destruct HQG as [FQG TBG]. destruct HQC as [FQC TBC].
  pose proof (toks_agree_lookup _ _ k HT) as HkC. destruct HT as [HTn HTs].
  assert (HkG : exists pG, fh_blk (ps_heap sG0) !! k = Some (pG, n)).
  { unfold tok_szmap in Hk. rewrite lookup_fmap in Hk. destruct (fh_blk (ps_heap sG0) !! k) as [[pG n_]|]; cbn in Hk; [| discriminate]. injection Hk as ->. exists pG. reflexivity. }
  destruct HkG as [pG HkG]. rewrite HkG in HkC. cbn in HkC.
  destruct (fh_blk (ps_heap sC0) !! k) as [[pC nC]|] eqn:HkC'; rewrite HkC' in HkC; cbn in HkC; [| discriminate]. injection HkC as EnC. subst nC.
  unfold hf_realloc, tok_lookup.
  eapply fsimw_bind with (Q1 := fun bG bC sG moG sC moC => bG = Some (pG, n) /\ bC = Some (pC, n) /\ sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0).
  { eapply fsimw_bind; [apply fsimw_get|]. intros a b. apply fsimw_ret. intros sG moG sC moC (-> & -> & -> & -> & -> & ->). rewrite HkG, HkC'. repeat split; reflexivity. }
  intros bG bC sG moG sC moC (-> & -> & -> & -> & -> & ->). cbn iota.
  pose proof (tok_blocks_delete (ps_heap sG0) k pG n HkG) as PDG. pose proof (tok_blocks_delete (ps_heap sC0) k pC n HkC') as PDC.
  refine (fsimw_bind _ _ _ _ _ _ _ _
            (raw_reallocF_sim_pt pG pC n n' (tok_blocks (ps_heap sG0)) (tok_blocks (hdel k (ps_heap sG0))) (tok_blocks (ps_heap sC0)) (tok_blocks (hdel k (ps_heap sC0)))
               sG0 moG0 sC0 moC0 Hn' Hov Hnx HBQ FQG FQC PDG PDC _ HR HB) _
            sG0 moG0 sC0 moC0 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  { (* [comment removed for export] *)
    change (Permutation (tok_sizes (hdel k (ps_heap sG0))) (tok_sizes (hdel k (ps_heap sC0)))). rewrite !tok_sizes_eq.
    unfold tok_szmap, hdel. cbn [fh_blk]. rewrite !fmap_delete. unfold tok_szmap in HTs. rewrite HTs. apply Permutation_refl. }
  intros rG rC sG moG sC moC (qG & qC & -> & -> & FQG' & FQC' & HxG & HxC & HvoG & HvoC). cbn iota.
  destruct (rest_eq_heap sG sG0 HxG) as (NG & BG & SG). destruct (rest_eq_heap sC sC0 HxC) as (NC & BC & SC).
  (* [comment removed for export] *)
  unfold tok_drop.
  eapply (fsimw_bind (npeek segs) (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) _ _
            (fun _ _ sG' moG' sC' moC' => sG' = set_heap (hdel k (ps_heap sG)) sG /\ moG' = moG /\ sC' = set_heap (hdel k (ps_heap sC)) sC /\ moC' = moC));
    [apply fsimw_upd; intros ? ? ? ? (-> & -> & -> & ->); repeat split; reflexivity| | repeat split; reflexivity].
  intros [] [].
  (* [comment removed for export] *)
  apply (tok_fresh_sim qG qC n' (fun sG' moG' sC' moC' => sG' = set_heap (hdel k (ps_heap sG)) sG /\ moG' = moG /\ sC' = set_heap (hdel k (ps_heap sC)) sC /\ moC' = moC)).
  intros ? ? ? ? (-> & -> & -> & ->). rewrite !ps_heap_set_heap, !set_heap_set_heap.
  assert (EBG : tok_blocks (hdel k (ps_heap sG)) = tok_blocks (hdel k (ps_heap sG0))) by (unfold tok_blocks, hdel; cbn; rewrite BG; reflexivity).
  assert (EBC : tok_blocks (hdel k (ps_heap sC)) = tok_blocks (hdel k (ps_heap sC0))) by (unfold tok_blocks, hdel; cbn; rewrite BC; reflexivity).
  assert (HQG1 : HQ (CE:=CEG) P GG (set_heap (hins qG n' (hdel k (ps_heap sG))) sG) moG).
  { pose proof (HQ_fresh (CE:=CEG) GG (set_heap (hdel k (ps_heap sG)) sG) qG n' moG HGG) as H1. rewrite ps_heap_set_heap, set_heap_set_heap in H1. apply H1.
    - rewrite EBG. eapply FQ_other; [exact FQG'| destruct sG; reflexivity| destruct sG; reflexivity| apply hframe_set_heap; [exact HGG| exact (FQ_G _ _ _ _ _ FQG')]].
    - unfold hdel. apply toks_below_delete. unfold toks_below. rewrite NG, BG. exact TBG. }
  assert (HQC1 : HQ (CE:=CEC) P GC (set_heap (hins qC n' (hdel k (ps_heap sC))) sC) moC).
  { pose proof (HQ_fresh (CE:=CEC) GC (set_heap (hdel k (ps_heap sC)) sC) qC n' moC HGC) as H1. rewrite ps_heap_set_heap, set_heap_set_heap in H1. apply H1.
    - rewrite EBC. eapply FQ_other; [exact FQC'| destruct sC; reflexivity| destruct sC; reflexivity| apply hframe_set_heap; [exact HGC| exact (FQ_G _ _ _ _ _ FQC')]].
    - unfold hdel. apply toks_below_delete. unfold toks_below. rewrite NC, BC. exact TBC. }
  cbn [fh_next hdel]. split; [rewrite NG; reflexivity|]. split; [rewrite NG, NC, HTn; reflexivity|].
  split.
  { split; [exact HQG1|]. split; [exact HQC1|].
    split; [cbn; rewrite NG, NC, HTn; reflexivity|].
    unfold tok_szmap. cbn. rewrite !fmap_insert, !fmap_delete. cbn. unfold tok_szmap in HTs. rewrite NG, NC, BG, BC, HTs, HTn. reflexivity. }
  split; [unfold tok_szmap; cbn; rewrite fmap_insert, fmap_delete, NG, BG; reflexivity|].
  split; [cbn; rewrite NG; reflexivity|].
  split; [intros h; apply SG|]. split; [intros h; apply SC|].
  split; assumption.
Qed.
End Sim.
