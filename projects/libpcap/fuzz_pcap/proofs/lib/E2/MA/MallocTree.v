(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition mem := word -> option byte.

Definition pans_mem (o : mem) (q : aptr) (caddr hint : Z) : Z :=
  match o (wa caddr) with Some b => bv_unsigned b | None => 0 end.
Definition pupd_mem (o : mem) (e : ev) (z : Z) : mem := o.

#[using="Type"] Lemma pans_mem_range : forall o q c h, 0 <= pans_mem o q c h < 256.
Proof.
  intros. unfold pans_mem. destruct (o (wa c)) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.

Definition pans_l (l : list Z) (q : aptr) (caddr hint : Z) : Z :=
  match l with v :: _ => Z.min 255 (Z.max 0 v) | [] => 0 end.
Definition pupd_l (l : list Z) (e : ev) (z : Z) : list Z :=
  match e with EPeek _ _ _ => tl l | _ => l end.

#[using="Type"] Lemma pans_l_range : forall l q c h, 0 <= pans_l l q c h < 256.
Proof. intros [|v l] q c h; cbn; lia. Qed.

Definition lrun {R} (l : list Z) (t : Malloc.M R) : Malloc.M (list Z * R) := prun pans_l pupd_l l t.

#[using="Type"] Lemma lrun_ret {R} l (r : R) : lrun l (SRet r) = SRet (l, r).
Proof. reflexivity. Qed.
#[using="Type"] Lemma lrun_peek {R} l p c h (k : Z -> Malloc.M R) : lrun l (SVis (EPeek p c h) k) = lrun (tl l) (k (pans_l l p c h)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma lrun_peek_cons {R} v l p c h (k : Z -> Malloc.M R) : 0 <= v < 256 -> lrun (v :: l) (SVis (EPeek p c h) k) = lrun l (k v).
Proof. intros Hv. unfold lrun, prun. cbn [eruns psel pupd_l pans_l tl]. rewrite Z.max_r, Z.min_r by lia. reflexivity. Qed.
#[using="Type"] Lemma lrun_vis {R} l e (k : Z -> Malloc.M R) :
  match e with EPeek _ _ _ => False | _ => True end ->
  lrun l (SVis e k) = SVis e (fun z => lrun l (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.

(* [comment removed for export] *)

Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
  exists l ans l', follow (lrun l t) ans = Some (l', r).

#[using="Type"] Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. exists [], [], []. reflexivity. Qed.

#[using="Type"] Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
  intros He (l & ans & l' & H). exists l, (z :: ans), l'. unfold lrun, prun. cbn [eruns].
  destruct e; cbn [psel pupd_l]; try exact H; destruct He.
Qed.

#[using="Type"] Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) v r :
  0 <= v < 256 -> leaf_of o (k v) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. intros Hv (l & ans & l' & H). exists (v :: l), ans, l'. rewrite lrun_peek_cons by exact Hv. exact H. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. intros (l & ans & l' & H). rewrite lrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.

#[using="Type"] Lemma leaf_of_vis_inv {R} o e (k : Z -> Malloc.M R) r :
  leaf_of o (SVis e k) r ->
  match e with
  | EUndef _ => False
  | EPeek p c h => exists v, 0 <= v < 256 /\ leaf_of o (k v) r
  | _ => exists z, leaf_of o (k z) r
  end.
Proof.
  intros (l & ans & l' & H).
  destruct e; try (rewrite lrun_vis in H by exact I; cbn [follow] in H; destruct ans as [|a ans]; [discriminate|]; exists a; exists l, ans, l'; exact H).
  - rewrite lrun_peek in H. exists (pans_l l p caddr hint). split; [apply pans_l_range|]. exists (tl l), ans, l'. exact H.
  - rewrite lrun_vis in H by exact I. cbn [follow] in H. destruct ans; discriminate.
Qed.

#[using="Type"] Lemma leaf_of_bad {R} o (bail : Malloc.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 -> forall ans r1, follow t1 ans = Some r1 -> exists r2, follow t2 ans = Some r2 /\ RR r1 r2.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros ans x H.
  - cbn in H |- *. inversion H; subst. exists r2. split; [reflexivity| exact Hr].
  - destruct e; cbn [follow] in H |- *; try (destruct ans as [|a ans]; [discriminate| exact (IH a ans x H)]). discriminate.
Qed.

#[using="Type"] Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.

Section GenDefs.
Context {St : Type} {AS : AllocSt St}.

Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
  match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.

Definition ptr_rel (p : optr) (r : option bptr) : Prop :=
  match p, r with
  | None, None => True
  | Some pf, Some b => fst pf = fst (fst b) /\ exists off, snd pf = snd (fst b) + UNIT * off
  | _, _ => False
  end.

(* [comment removed for export] *)
Definition auxv_list (x3 x4 x5 x16 x6 x11 x12 x23 rnd : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

#[using="Type"] Lemma Forall_disjoint_from : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

Definition brk_link_ps (st : mstate) (s : St) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => ps_brk s = conc st (rid, off)
  | _ => True
  end.

(* [comment removed for export] *)
Definition optr_in (P : N -> Prop) (p : optr) : Prop :=
  match p with Some q => P (fst q) | None => True end.

Definition ptrs_in (P : N -> Prop) (st : mstate) : Prop :=
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid _ => P rid | _ => True end
  /\ (forall g, optr_in P (m_prev (get_meta_rec st g)) /\ optr_in P (m_next (get_meta_rec st g))
             /\ optr_in P (m_mem (get_meta_rec st g)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> P (fst b) /\ optr_in P (g_meta gh)).

#[using="Type"] Lemma ptrs_in_mono (P P' : N -> Prop) st : (forall r, P r -> P' r) -> ptrs_in P st -> ptrs_in P' st.
Proof.
  intros HP (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
  split; [intros g; destruct (H8 g) as (X1 & X2 & X3); auto|].
  split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
  intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.

(* [comment removed for export] *)
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
  amr_active : forall sc, active st1 sc = active st sc;
  amr_usage : forall sc, usage st1 sc = usage st sc;
  amr_bounces : forall i, bounces st1 i = bounces st i;
  amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
  amr_seq : c_seq (ctx st1) = c_seq (ctx st);
  amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
  amr_groups : s_groups st1 = s_groups st;
  amr_slots : s_slots st1 = s_slots st;
  amr_shadow : s_shadow st1 = s_shadow st;
  amr_tick : s_tick st1 = s_tick st;
  amr_reserved : s_reserved st1 = s_reserved st;
  (* [comment removed for export] *)
  amr_metas : forall g, Some g <> mo ->
      (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
      get_meta_rec st1 g = get_meta_rec st g;
  (* [comment removed for export] *)
  amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
  (* [comment removed for export] *)
  amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  (* [comment removed for export] *)
  amr_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
      ptrs_in P st -> ptrs_in P st1;
  (* [comment removed for export] *)
  amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.

Definition AM_STACK : Z := 128.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_addr (st : mstate) (a : Z) : Prop :=
  a < alloc_ceiling /\ ranges_free (live_ranges st) a 1 = true.

#[using="Type"] Lemma ranges_free_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.

#[using="Type"] Lemma ranges_free_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.

#[using="Type"] Lemma ranges_free_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof.
  intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.

#[using="Type"] Lemma In_live_ranges st rid r : (s_regions st) !! rid = Some r ->
  In (region_live_range r) (live_ranges st).
Proof.
  intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fresh_live_region st a rid r : fresh_addr st a -> (s_regions st) !! rid = Some r ->
  a + 1 <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= a.
Proof.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fresh_addr_anti st st' a :
  s_reserved st' = s_reserved st ->
  (forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  fresh_addr st' a -> fresh_addr st a.
Proof.
  intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. destruct HI as ([rid r] & E & HI). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    destruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.


End GenDefs.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tree.
Variable segs : list Segment.
Context {St : Type} {AS : AllocSt St}.

Definition implT {R} (o : mem) (t : Malloc.M R) (s : St)
           (Q : R -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM segs (membedF peekG t) s Q ms.

#[using="Type"] Lemma implT_ret {R} o (r : R) s Q ms : evt segs (Q r s) ms -> implT o (SRet r) s Q ms.
Proof. intros H. unfold implT. cbn [membedF]. apply implM_ret. exact H. Qed.

#[using="Type"] Lemma implT_undef {R} o w (k : Z -> Malloc.M R) s Q ms : implT o (SVis (EUndef w) k) s Q ms.
Proof.
  unfold implT. cbn [membedF ev_stepF ev_step].
  eapply (implM_bind segs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implT_vis {R} o e (k : Z -> Malloc.M R) s Q1 Q ms :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  implM segs (ev_step e) s Q1 ms ->
  (forall z s' ms', Q1 z s' ms' -> implT o (k z) s' Q ms') ->
  implT o (SVis e k) s Q ms.
Proof.
  intros He H K. unfold implT. cbn [membedF].
  eapply implM_bind; [|intros z s' ms' H1; apply (K z s' ms' H1)].
  destruct e; cbn [ev_stepF]; try exact H; destruct He.
Qed.

#[using="Type"] Lemma implT_mono {R} o (t : Malloc.M R) s Q Q' ms :
  implT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> implT o t s Q' ms.
Proof. intros H HQ. unfold implT in *. eapply implM_mono; [exact H|]. intros r s' ms'; cbn; auto. Qed.

#[using="Type"] Lemma implT_evt {R} o (t : Malloc.M R) s Q P ms :
  evt segs P ms -> (forall ms', P ms' -> implT o t s Q ms') -> implT o t s Q ms.
Proof. intros H K. unfold implT in *. eapply implM_evt; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implT_peek_now {R} o p c h (k : Z -> Malloc.M R) s Q ms :
  implT o (k (peek_byte segs ms c)) s Q ms -> implT o (SVis (EPeek p c h) k) s Q ms.
Proof.
  intros H. unfold implT, implM in *. cbn [membedF ev_stepF]. unfold mbind, peekG, msys, ebind, enode. cbn [ITree.bind].
  apply (impl_peek_now _ segs (at_node segs) (npeek segs) (NPeek c) (fun ms0 => peek_rsp (peek_byte segs ms0 c))); [reflexivity|].
  cbn [ITree.bind fst snd]. rewrite (dec_peek_rsp _ (peek_byte_range segs ms c)). exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implT_peek {R} o p c h (k : Z -> Malloc.M R) s Q ms :
  evt segs (fun ms1 => implT o (k (peek_byte segs ms1 c)) s Q ms1) ms -> implT o (SVis (EPeek p c h) k) s Q ms.
Proof. intros H. eapply implT_evt; [exact H|]. intros ms' H'. apply implT_peek_now. exact H'. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
  impl segs (at_node segs) (npeek segs) (ITree.bind _ t f1) Q1 ms ->
  (forall r ms', impl segs (at_node segs) (npeek segs) (f1 r) Q1 ms' -> impl segs (at_node segs) (npeek segs) (f2 r) Q2 ms') ->
  impl segs (at_node segs) (npeek segs) (ITree.bind _ t f2) Q2 ms.
Proof.
  revert ms. induction t as [r|n k IH]; intros ms H K; cbn [ITree.bind] in *.
  - apply K. exact H.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
    + left. split; [exact Hat|]. intros rsp. eapply IH; eauto.
    + right. exists g. split; [exact Hg|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implM_membedF_sbind {R S} (T : Malloc.M R) (F : R -> Malloc.M S) s Q1 Q ms :
  implM segs (membedF peekG T) s Q1 ms ->
  (forall x s' ms', Q1 x s' ms' -> implM segs (membedF peekG (F x)) s' Q ms') ->
  implM segs (membedF peekG (sbind T F)) s Q ms.
Proof.
  revert s ms. induction T as [x|e k IH]; intros s ms H K.
  - cbn [sbind membedF] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [exact H|]. intros ms' H1. exact (K x s ms' H1).
  - cbn [sbind membedF] in *. unfold implM, mbind, ebind in *.
    eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1|exact K].
Qed.

#[using="Type"] Lemma implT_bind {R S} o (t : Malloc.M R) (f : R -> Malloc.M S) s Q1 Q ms :
  implT o t s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implT o (f r) s' Q ms') ->
  implT o (sbind t f) s Q ms.
Proof. intros H K. unfold implT in *. eapply implM_membedF_sbind; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> implT o t1 s Q ms -> implT o t2 s Q ms.
Proof.
  intros Hs. revert s ms. induction Hs as [r | e k1 k2 Hk IH]; intros s ms H.
  - exact H.
  - unfold implT in *. cbn [membedF] in *. unfold implM, mbind, ebind in *.
    eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *; [exact H1|]. apply IH. exact H1.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implT_from_evt {R} o (t : Malloc.M R) s Q ms :
  evt segs (fun ms' => implT o t s Q ms') ms -> implT o t s Q ms.
Proof. intros H. eapply implT_evt; [exact H|]. intros ms' H'; exact H'. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma impl_vis_unfold {X} n (k : resp -> itree node X) Q ms :
  impl segs (at_node segs) (npeek segs) (Vis n k) Q ms =
  evt segs (fun ms1 => (at_node segs n ms1 /\ forall rsp, impl segs (at_node segs) (npeek segs) (k rsp) Q (nret ms1 rsp))
                       \/ (exists f, npeek segs n = Some f /\ impl segs (at_node segs) (npeek segs) (k (f ms1)) Q ms1)) ms.
Proof. reflexivity. Qed.

#[using="Type"] Lemma implM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
      (s : St) (Q : B -> St -> machine_state -> Prop) ms :
  impl segs (at_node segs) (npeek segs) (enode n dec) (epost P) ms ->
  (forall a ms', P a ms' -> evt segs (Q (f a) s) ms') ->
  implM segs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof.
  intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
  cbn [ITree.bind]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
  - left. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec rsp) as [a|]; cbn in *.
    + eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
    + exact Hk.
  - right. exists g. split; [exact Hg|]. destruct (dec (g ms1)) as [a|]; cbn in *.
    + eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
    + exact Hk.
Qed.

#[using="Type"] Lemma implT_mmap_rw {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl segs (at_node segs) (npeek segs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (mmap_val a)) s Q ms') ->
  implT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma implT_mmap_none {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl segs (at_node segs) (npeek segs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (mmap_val a)) s Q ms') ->
  implT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma implT_mmap_fixed {R} o addr len (k : Z -> Malloc.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
  impl segs (at_node segs) (npeek segs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (fixed_val addr a)) s Q ms') ->
  implT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma implT_munmap {R} o addr len (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl segs (at_node segs) (npeek segs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (range_val a)) s Q ms') ->
  implT o (SVis (EMunmap addr len) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma implT_mprotect {R} o addr len prot (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl segs (at_node segs) (npeek segs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (range_val a)) s Q ms') ->
  implT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implT_brk0 {R} o (k : Z -> Malloc.M R) s (P : Z -> machine_state -> Prop) Q ms :
  impl segs (at_node segs) (npeek segs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
  (forall r ms', P r ms' -> implT o (k r) (set_brk_ps r s) Q ms') ->
  implT o (SVis (EBrk 0) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
  - cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
    cbn [ITree.bind]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)]; [left|right].
    + split; [exact Hat|]. intros rsp. specialize (Hk rsp).
      destruct (dec_brk0 rsp) as [a|]; cbn in *; [|exact Hk].
      eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
    + exists g. split; [exact Hg|]. destruct (dec_brk0 (g ms1)) as [a|]; cbn in *; [|exact Hk].
      eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
  - intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implT_brk {R} o req (k : Z -> Malloc.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
  req <> 0 ->
  impl segs (at_node segs) (npeek segs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
  (forall a ms', P a ms' ->
     implT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
             (match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
  implT o (SVis (EBrk req) k) s Q ms.
Proof.
  intros Hr H K.
  eapply (implT_vis o _ k s (fun z s' ms' => exists a, P a ms' /\
            z = match a with BrkGrown => req | BrkSame => ps_brk s end /\
            s' = match a with BrkGrown => set_brk_ps req s | BrkSame => s end)); [exact I| |].
  - cbn [ev_step]. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
    unfold implM, mbind, msys, mget, mupd, mret, ebind, enode in *.
    cbn [ITree.bind fst snd]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)]; [left|right].
    + split; [exact Hat|]. intros rsp. specialize (Hk rsp).
      destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|exact Hk].
      destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
    + exists g. split; [exact Hg|]. destruct (dec_brk (ps_brk s) req (g ms1)) as [a|]; cbn in *; [|exact Hk].
      destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
  - intros z s' ms' (a & HP & -> & ->). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma implT_reach {R} o (t : Malloc.M R) : forall s Q ms,
  implT o t s Q ms -> implT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof.
  induction t as [r|e k IH]; intros s Q ms H.
  - unfold implT, implM in *. cbn [membedF] in *. unfold mret in *. cbn in *.
    eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| apply leaf_of_ret].
  - destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w|oa ol nl].
    5:{ unfold implT, implM in H |- *. cbn [membedF ev_stepF] in H |- *. unfold mbind, peekG, msys, ebind, enode in H |- *.
        cbn [ITree.bind] in H |- *.
        apply (impl_peek_inv _ segs (at_node segs) (npeek segs) (NPeek c) (fun ms0 => peek_rsp (peek_byte segs ms0 c))) in H;
          [| intros ms1 _ Hat; exact Hat | reflexivity].
        apply (impl_peek _ segs (at_node segs) (npeek segs) (NPeek c) (fun ms0 => peek_rsp (peek_byte segs ms0 c))); [reflexivity|].
        eapply evt_mono; [exact H|]. intros ms1 H1. cbn [ITree.bind fst snd] in H1 |- *.
        rewrite (dec_peek_rsp _ (peek_byte_range segs ms1 c)) in H1 |- *.
        pose proof (IH (peek_byte segs ms1 c) s Q ms1) as IH1. unfold implT, implM in IH1.
        eapply impl_epost_mono; [apply IH1; exact H1|].
        intros [r s2] ms2; cbn; intros [HQ HL]; split; [exact HQ|]. eapply leaf_of_peek; [apply peek_byte_range| exact HL]. }
    5:{ apply implT_undef. }
    all: unfold implT in H |- *; cbn [membedF] in H |- *;
         unfold implM, mbind, ebind in H |- *;
         eapply impl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         pose proof (IH z s' Q ms') as IH1; unfold implT, implM in IH1;
         eapply impl_epost_mono; [apply IH1; exact H1|];
         intros [r s2] ms2; cbn; intros [HQ HL]; split; [exact HQ| apply (leaf_of_vis o _ k z); [exact I| exact HL]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma raw_malloc_bridge : forall s n (o : mem) Q1 Q ms,
  implT o (malloc (ps_m s) n) s Q1 ms ->
  (forall st' (p : optr) s' ms', Q1 (st', p) s' ms' -> Q p (set_m st' s') ms') ->
  implM segs (raw_mallocF peekG n) s Q ms.
Proof.
  intros s n o Q1 Q ms H HQ. unfold raw_mallocF.
  eapply (implM_bind segs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind segs _ _ _ Q1); [exact H|].
  intros [st' p] s' ms' H1. cbv beta iota.
  eapply (implM_bind segs _ _ _ (fun _ s2 ms2 => s2 = set_m st' s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done. eapply HQ. exact H1.
Qed.

#[using="Type"] Lemma raw_free_bridge : forall s (pf : aptr) (o : mem) Q1 Q ms,
  implT o (free (ps_m s) (Some pf)) s Q1 ms ->
  (forall st' s' ms', Q1 st' s' ms' -> Q tt (set_m st' s') ms') ->
  implM segs (raw_freeF peekG pf) s Q ms.
Proof.
  intros s pf o Q1 Q ms H HQ. unfold raw_freeF.
  eapply (implM_bind segs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind segs _ _ _ Q1); [exact H|].
  intros st' s' ms' H1. cbv beta. apply implM_upd. apply evt_done. eapply HQ. exact H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable auxv_cell : Z.

Definition auxv_ok (m : mem) (B : Z) : Prop :=
  exists av x3 x4 x5 x16 x6 x11 x12 x23 rnd,
    rw_cells segs m auxv_cell [C8 (wz av)]
    /\ bytes_at segs m av (u64s (auxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd))
    /\ bytes_at segs m (rnd + 8) (le8 (wz msecret))      (* [comment removed for export] *)
    /\ alloc_ceiling <= B /\ B <= av /\ av + 160 <= 2^64 /\ B <= rnd + 8 /\ rnd + 16 <= 2^64
    /\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= x16 < 2^64 /\ 0 <= x6 < 2^64
    /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64.

#[using="Type"] Lemma auxv_ok_weaken : forall m B B', auxv_ok m B -> alloc_ceiling <= B' <= B -> auxv_ok m B'.
Proof.
  intros m B B' (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & H) HB.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. repeat (split; [tauto|]). lia.
Qed.

#[using="Type"] Lemma auxv_ok_frame : forall m m' B W,
  auxv_ok m B -> munch W m m' -> wmono segs m m' ->
  Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= auxv_cell \/ auxv_cell + 8 <= fst iv)) W ->
  auxv_ok m' B.
Proof.
  intros m m' B W (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H) MU WM FW.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rw_cells_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [_ ?]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pres_except (C : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> ~ C a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma pres_except_refl C m : pres_except C m m.
Proof. intros a _ _; auto. Qed.
#[using="Type"] Lemma pres_except_trans C m1 m2 m3 : pres_except C m1 m2 -> pres_except C m2 m3 -> pres_except C m1 m3.
Proof. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
#[using="Type"] Lemma pres_except_mono (C C' : Z -> Prop) m m' : pres_except C m m' -> (forall a, C a -> C' a) -> pres_except C' m m'.
Proof. intros H HC a Ha Hc. apply H; [exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.

#[using="Type"] Lemma pres_except_of_munch C W m m' :
  munch W m m' -> wmono segs m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> pres_except C m m'.
Proof.
  intros MU WM HW a Ha Hc. split.
  - apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
  - apply WM.
Qed.

#[using="Type"] Lemma pres_except_bytes_at C m m' A bs :
  pres_except C m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) ->
  bytes_at segs m' A bs.
Proof.
  intros HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma pres_except_wr_at C m m' A n :
  pres_except C m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> ~ C a) -> wr_at segs m' A n.
Proof.
  intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

#[using="Type"] Lemma pres_except_rw_cells C m m' A cs :
  pres_except C m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) ->
  rw_cells segs m' A cs.
Proof.
  intros HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply pres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply pres_except_wr_at; eauto.
Qed.

#[using="Type"] Lemma pres_except_stk C m m' lo hi :
  pres_except C m m' -> stk segs m lo hi -> (forall a, lo <= a < hi -> ~ C a) -> stk segs m' lo hi.
Proof.
  intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

End Tree.
End WithCeil.


Ltac iprefixT := apply implT_from_evt.
