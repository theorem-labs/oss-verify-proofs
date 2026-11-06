(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Export MallocTree.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Export RMallocRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)


Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition rimplT {R} (o : mem) (t : Malloc.M R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM rsegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

Lemma rimplT_ret {R} o (r : R) s Q ms : evt rsegs (Q r s) ms -> rimplT o (SRet r) s Q ms.
Proof. try hcb. try hsb. intros H. unfold rimplT. rewrite mrun_ret. cbn [membed]. apply implM_ret. exact H. Qed.

Lemma rimplT_peek {R} o p c h (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (pans_mem o p c h)) s Q ms -> rimplT o (SVis (EPeek p c h) k) s Q ms.
Proof. try hcb. try hsb. intros H. unfold rimplT. rewrite mrun_peek. exact H. Qed.

Lemma rimplT_undef {R} o w (k : Z -> Malloc.M R) s Q ms : rimplT o (SVis (EUndef w) k) s Q ms.
Proof. try hcb. try hsb.
  unfold rimplT. rewrite mrun_vis by exact I. cbn [membed ev_step].
  eapply (implM_bind rsegs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

(* [comment removed for export] *)
Lemma rimplT_vis {R} o e (k : Z -> Malloc.M R) s Q1 Q ms :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  implM rsegs (ev_step e) s Q1 ms ->
  (forall z s' ms', Q1 z s' ms' -> rimplT o (k z) s' Q ms') ->
  rimplT o (SVis e k) s Q ms.
Proof. try hcb. try hsb.
  intros He H K. unfold rimplT. rewrite mrun_vis by (destruct e; auto). cbn [membed].
  eapply implM_bind; [exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.

Lemma rimplT_mono {R} o (t : Malloc.M R) s Q Q' ms :
  rimplT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> rimplT o t s Q' ms.
Proof. try hcb. try hsb. intros H HQ. unfold rimplT in *. eapply implM_mono; [exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.

Lemma rimplT_evt {R} o (t : Malloc.M R) s Q P ms :
  evt rsegs P ms -> (forall ms', P ms' -> rimplT o t s Q ms') -> rimplT o t s Q ms.
Proof. try hcb. try hsb. intros H K. unfold rimplT in *. eapply implM_evt; eauto. Qed.

(* [comment removed for export] *)
Lemma rimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
  impl rsegs (at_node rsegs) (Vis n k) Q ms = evt rsegs (fun ms1 => at_node rsegs n ms1 /\ forall rsp, impl rsegs (at_node rsegs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. try hcb. try hsb. reflexivity. Qed.

Lemma rimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
  impl rsegs (at_node rsegs) (ITree.bind _ t f1) Q1 ms ->
  (forall r ms', impl rsegs (at_node rsegs) (f1 r) Q1 ms' -> impl rsegs (at_node rsegs) (f2 r) Q2 ms') ->
  impl rsegs (at_node rsegs) (ITree.bind _ t f2) Q2 ms.
Proof. try hcb. try hsb.
  revert ms. induction t as [r|n k IH]; intros ms H K; cbn [ITree.bind] in *.
  - apply K. exact H.
  - rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [exact H|].
    intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma rmembed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
  implM rsegs (membed t1) s Q1 ms ->
  (forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof. try hcb. try hsb.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1. eapply HQ; eauto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1| exact HQ].
Qed.

Lemma rimplT_strel {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : Malloc.M R1) (t2 : Malloc.M R2) s Q1 Q2 ms :
  strel RR (mrun o t1) t2 ->
  rimplT o t1 s Q1 ms ->
  (forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof. try hcb. try hsb.
  intros Hs H HQ. unfold rimplT in H. eapply (rmembed_strel _ _ _ Hs); [exact H|]. intros [o1 r1] r2 s' ms'; cbn; eauto.
Qed.

(* [comment removed for export] *)
Lemma rimplM_membed_steq {R} (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> implM rsegs (membed t1) s Q ms -> implM rsegs (membed t2) s Q ms.
Proof. try hcb. try hsb.
  intros Hs H. apply strel_eq_steq in Hs. eapply (rmembed_strel eq t1 t2 Hs); [exact H|]. intros; subst; auto.
Qed.


Lemma rimplM_membed_sbind {R S} (T : Malloc.M R) (F : R -> Malloc.M S) s Q1 Q ms :
  implM rsegs (membed T) s Q1 ms ->
  (forall x s' ms', Q1 x s' ms' -> implM rsegs (membed (F x)) s' Q ms') ->
  implM rsegs (membed (sbind T F)) s Q ms.
Proof. try hcb. try hsb.
  revert s ms. induction T as [x|e k IH]; intros s ms H K.
  - cbn [sbind membed] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [exact H|]. intros ms' H1. exact (K x s ms' H1).
  - cbn [sbind membed] in *. unfold implM, mbind, ebind in *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
Lemma rimplT_bind {R S} o (t : Malloc.M R) (f : R -> Malloc.M S) s Q1 Q ms :
  rimplT o t s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> rimplT o (f r) s' Q ms') ->
  rimplT o (sbind t f) s Q ms.
Proof. try hcb. try hsb.
  unfold rimplT, mrun, prun. revert s ms. induction t as [r|e k IH]; intros s ms H K.
  - cbn [sbind]. cbn [eruns membed] in H. unfold implM, mret in H. cbn in H.
    eapply implM_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
  - cbn [sbind eruns]. cbn [eruns] in H. unfold pupd_mem in *. destruct (psel pans_mem o e) as [a|].
    + eapply IH; [exact H|exact K].
    + cbn [membed]. cbn [membed] in H. unfold implM, mbind, ebind in H |- *.
      eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
      * exact H1.
      * eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
Lemma rimplT_from_evt {R} o (t : Malloc.M R) s Q ms :
  evt rsegs (fun ms' => rimplT o t s Q ms') ms -> rimplT o t s Q ms.
Proof. try hcb. try hsb. intros H. eapply rimplT_evt; [exact H|]. intros ms' H'; exact H'. Qed.

End HCW.

Ltac riprefixT := apply rimplT_from_evt.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rimplM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
      (s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
  (forall a ms', P a ms' -> evt rsegs (Q (f a) s) ms') ->
  implM rsegs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof. try hcb. try hsb.
  intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
  cbn [ITree.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec rsp) as [a|]; cbn in *.
  - eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
  - exact Hk.
Qed.


Lemma rimplT_mmap_rw {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
  rimplT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

Lemma rimplT_mmap_none {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
  rimplT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

Lemma rimplT_mmap_fixed {R} o addr len (k : Z -> Malloc.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (fixed_val addr a)) s Q ms') ->
  rimplT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

Lemma rimplT_munmap {R} o addr len (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
  rimplT o (SVis (EMunmap addr len) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
Lemma rimplT_mprotect {R} o addr len prot (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
  rimplT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
Lemma rimplT_brk0 {R} o (k : Z -> Malloc.M R) s (P : Z -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
  (forall r ms', P r ms' -> rimplT o (k r) (set_brk_ps r s) Q ms') ->
  rimplT o (SVis (EBrk 0) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
  - cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
    cbn [ITree.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk0 rsp) as [a|]; cbn in *; [|exact Hk].
    eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
  - intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.

(* [comment removed for export] *)
Lemma rimplT_brk {R} o req (k : Z -> Malloc.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
  req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
  (forall a ms', P a ms' ->
     rimplT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
             (match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
  rimplT o (SVis (EBrk req) k) s Q ms.
Proof. try hcb. try hsb.
  intros Hr H K.
  eapply (rimplT_vis o _ k s (fun z s' ms' => exists a, P a ms' /\
            z = match a with BrkGrown => req | BrkSame => ps_brk s end /\
            s' = match a with BrkGrown => set_brk_ps req s | BrkSame => s end)); [exact I| |].
  - cbn [ev_step]. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
    unfold implM, mbind, msys, mget, mupd, mret, ebind, enode in *.
    cbn [ITree.bind fst snd]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|exact Hk].
    destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
  - intros z s' ms' (a & HP & -> & ->). exact (K a ms' HP).
Qed.


Lemma rimplT_reach {R} o (t : Malloc.M R) : forall s Q ms,
  rimplT o t s Q ms -> rimplT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof. try hcb. try hsb.
  induction t as [r|e k IH]; intros s Q ms H.
  - unfold rimplT, implM in *. rewrite mrun_ret in *. cbn [membed] in *. unfold mret in *. cbn in *.
    eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| apply leaf_of_ret].
  - destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ apply rimplT_peek. eapply rimplT_mono; [apply IH; unfold rimplT in H |- *; rewrite mrun_peek in H; exact H|].
        cbn. intros r s' ms' [HQ HL]. split; [exact HQ|]. apply leaf_of_peek. exact HL. }
    5:{ apply rimplT_undef. }
    all: unfold rimplT in H |- *; rewrite mrun_vis in H |- * by exact I; cbn [membed] in H |- *;
         unfold implM, mbind, ebind in H |- *;
         eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         pose proof (IH z s' Q ms') as IH1; unfold rimplT, implM in IH1;
         eapply impl_epost_mono; [apply IH1; exact H1|];
         intros [[o1 r] s2] ms2; cbn; intros [HQ HL]; split; [exact HQ| apply (leaf_of_vis o _ k z); [exact I| exact HL]].
Qed.

Lemma rraw_malloc_bridge : forall st s n (o : mem) Q1 Q ms,
  strip st = ps_m s ->
  rimplT o (malloc st n) s Q1 ms ->
  (forall st' (p : optr) s' ms' (r : option bptr),
     Q1 (st', p) s' ms' -> ptr_rel p r ->
     (forall b, r = Some b -> snd b = fresh_off (strip st') (fst b) n) ->
     Q r (set_m (strip st') s') ms') ->
  implM rsegs (raw_malloc n) s Q ms.
Proof. try hcb. try hsb.
  intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
  eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind rsegs _ _ _ (fun r s' ms' => exists st' p, Q1 (st', p) s' ms' /\ MREL (o, (st', p)) r)).
  { rewrite <- Hst. eapply (rimplT_strel MREL o (malloc st n) (cmalloc (strip st) n) s Q1).
    - unfold mrun. apply malloc_control. apply pans_mem_range.
    - exact H.
    - intros o1 [st' p] [cs c] s' ms' HR H1. exists st', p. split; [exact H1|].
      unfold MREL in *. cbn in *. exact HR. }
  intros [cs c] s' ms' (st' & p & H1 & HR). cbv beta iota.
  eapply (implM_bind rsegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
  unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
  eapply HQ; [exact H1| |].
  - destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
  - intros b Hb. destruct c as [c|]; [|discriminate]. inversion Hb; subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition rauxv_list (x3 x4 x5 x16 x6 x11 x12 x23 rnd : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Definition rauxv_ok (m : mem) (B : Z) : Prop :=
  exists av x3 x4 x5 x16 x6 x11 x12 x23 rnd,
    rw_cells rsegs m RAUXV_CELL [C8 (wz av)]
    /\ bytes_at rsegs m av (u64s (rauxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd))
    /\ bytes_at rsegs m (rnd + 8) (le8 (wz hsecret))
    /\ hceil <= B /\ B <= av /\ av + 160 <= 2^64 /\ B <= rnd + 8 /\ rnd + 16 <= 2^64
    /\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= x16 < 2^64 /\ 0 <= x6 < 2^64
    /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64.
Scheme kc__1 := Elimination for Corelib.Init.Logic.ex Sort Prop.

Lemma rauxv_ok_weaken : forall m B B', rauxv_ok m B -> hceil <= B' <= B -> rauxv_ok m B'.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocTree.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocTree.HCW2.rauxv_ok); constr:(@kc__1); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.RAUXV_CELL); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocRep.wz); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocTree.HCW2.rauxv_list); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le8); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.and_ind); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z))|] [|@rnd; @x23; @x12; @x11; @x6; @x16; @x5; @x4; @x3; @av; @H33; @H15; @H32; @H29; @H31; @H30; @H27; @H28; @H25; @H26; @H23; @H24; @H21; @H22; @H19; @H20; @H17; @H18; @H16; @H14; @H13; @H12; @H11; @H10; @H7; @H9; @H8; @H; @H6; @H5; @H4; @H3; @H2; @H1; @H0; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__x9; @__x10; @__x11; @__x12; @__p1; @__p2; @__p3; @__p4; @__p5; @__arith; @__sat25; @__sat24; @HB; @x; @B'; @B; @m; @HCANB; @HSECB; @HCEILB|] "#D,$,$l$A$F$j###$#%$:$G$I$k$i#&#1#S#'#5#9#U#3#=#A#E#I#M#Q#/#Y#W$r#2#7#;#C#G#K#O#,#)#4#?#0#(#-#6#[#*#8#]#:#+#>#R#.#<#B#T#_#@#F#L$q#D#J#V#P#a#c#e#H#g#i#k#m#X#o#q$,#N#s#u$x#w#y#Z#{#}$#$%#\$9$'$)$[$6#^$+$0$L#`$V$X$`$\$a$g${$|$/$7$8$;$=$>$?$Q#b$U$W$Z$Y$b$e$f$h$s$w$v$y$~$}%#$z$@$1$2$D$M$T$P$<$E$H$K$O$N$J$4$5$l$o$n$_$p$B$R$C$3$c$d$m$u$^$]$S$tC$L%$M%$N%$O'$P($Q%$R%$S'$T&$U$$V,$W$$X$$Y$$Z$$[*$\'$]*$^$$_%$`%$a'$b($c$$d'$e%$f)$g%$h%$i&$j'$k&US~Ss1Sp1#1#1#1#1#1#1#1#1#1#1#1#1#0#1#1#1#1#1#1#1#1#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#:#UT#Ss$$#1s#&1#1#1#1#1#1#1#1#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#:#$s#%##s#%#m#s#W#UT$SlUT%Sl$I#0Sp:#0$0#0#0#0#:#VT&)#)-##-#m#0#UT'SlUT(Sl$I#)$)#$#m#'#7HG,S7/#UStK+K$#*DS;J#-SDS@S8S<QNHGF.#&DS;S7#::(F#,AUT)#&DS;%#$s#KS,$S,S71s#$0#0#0#0#0#:#(S7#$#s#$$S,1:s#*(F#$#s#($ISD)SDs#*#$#$IS@)S@s#-#$#$IS8)S8s#0#$#$IS<)S<s#3#$#$IQ)Qs#6#$#$IN)Ns#9#$#$IH)Hs#<#$#$IG)Gs#?#$#$IF)Fs#B#$##&##*##.##2##6##:##>##B##s#&##s#*##s#,##s#6##s#8##s#:##s#@##s#D#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#j#-C#%C#$s$=H$HN#$#7S<Nk##$#j##(#*DOJs#`&DOS7s#^&DOs#\s#Z$s$FS;$S;S7$S;s#_##s#*#s#S##&##(##*##,##.#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#j#-C#U#F*DS0Js$%&DS0S7s$#&DS0s#}s#{$s$gO$OS7$Os$$##s#K#s#t##&##(##*##,##.#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#,S=/#+K#s$G*DS%J#&DS%S=s$E&DS%s$Cs$A$s%-S0$S0S=(S=s$:$#s$[$S0s$H##s#o#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#$s%KS8$S8S@#$#7S7S@k##$#j##(#,SG/#+K#s$q*DS9J#&DS9SGs$o&DS9s$ms$k$s%WS%$S%SG(SGs$d$#s%)$S%s$r##s$=#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#U#F,S,/#+K#s%9*DRJ#&DRS,s%7&DRs%5s%3$s%{S9$S9S,(S,s%,$#s%M$S9s%:##s$a#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#,S;/#+K#s%[*DS>J#-S7S@S8S<QNHGF.#&DS>S;#&DS>s%Ys%W$s&CR$RS;(S;s%P$#s%q$Rs%^$IS7)S7s%t#$###s%.#s%Q##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#$s&dS=$S=SG#$#7S;SGk##$#j##(#,O/#+K#s&.*DS1J#-S=S@S8S<QNHGF.#&DS1O#&DS1s&,s&*$s&rS>$S>O(Os&#$#s&D$S>s&1$IS=)S=s&G#$###s%]#s&$##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#U#F,S0/#+K#s&W*DSAJ#-SGS@S8S<QNHGF.#&DSAS0#&DSAs&Us&S$s'?S1$S1S0(S0s&L$#s&m$S1s&Z$ISG)SGs&p#$###s&*#s&M##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#,S%/#+K#s&~*DS#J#-S,SDS8S<QNHGF.#&DS#S%#&DS#s&|s&z$s'fSA$SAS%(S%s&s$#s'8$SAs'%$IS,)S,s';#$##s&ps&R#$##s&u##)##+##.##0##2##4##8#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#$OS0#s%~#7S9S0k##$#j##'#,S9/#+K#s'O*DSCJ#-S;S7S8S<QNHGF.#&DSCS9#&DSCs'Ms'K$s(7S#$S#S9(S9s'D$#s'e$S#s'R$IS;)S;s'h#$##s$Ss'##$##s'F##)##+##.##0##2##4##8#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#U#F,R/#+K#s'w*DS2J#-OS=S8S<QNHGF.#&DS2R#&DS2s'us's$s(_SC$SCR(Rs'l$#s(1$SCs'z$IO)Os(4#$##s$Ls'K#$##s'n##)##+##.##0##2##4##8#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#,S>/#+K#s(A*DSHJ#-S0SGS@S<QNHGF.#&DSHS>#&DSHs(?s(=$s))S2$S2S>(S>s(6$#s(W$S2s(D$IS0)S0s(Z#$##s(0s'r#s$J##%##s(9##*##,##/##1##3##5##9#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#$RS>#s%d#7SAS>k##$#j##'#,S1/#+K#s(m*DS&J#-S%S,SDS<QNHGF.#&DS&S1#&DS&s(ks(i$s)USH$SHS1(S1s(b$#s)'$SHs(p$IS%)S%s)*#$##s(_s(B#s$O##%##s(e##*##,##/##1##3##5##9#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#U#F,SA/#+K#s)8*DSEJ#-S9S;S7S<QNHGF.#&DSESA#&DSEs)6s)4$s)|S&$S&SA(SAs)-$#s)N$S&s);$IS9)S9s)Q#$##s&<s(i#s$I##%##s)0##*##,##/##1##3##5##9#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#,S#/#+K#s)]*DS:J#-ROS=S8QNHGF.#&DS:S##&DS:s)[s)Y$s*ESE$SES#(S#s)R$#s)s$SEs)`$IR)Rs)v#$##s)Is)3#s&3##s$G##&##s)V##+##-##0##2##4##6##:#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#$S#SC#s%/#7SHSCk##$#j##'#,SC/#+K#s*,*DSLJ#-S>S0SGS@QNHGF.#&DSLSC#&DSLs**s*($s*pS:$S:SC(SCs)}$#s*B$S:s*/$IS>)S>s*E#$##s)ws)^#s&5##s$L##&##s*%##+##-##0##2##4##6##:#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#U#F,S2/#+K#s*R*DS'J#-S1S%S,SDQNHGF.#&DS'S2#&DS's*Ps*N$s+:SL$SLS2(S2s*G$#s*h$SLs*U$IS1)S1s*k#$##s*Ds*(#s&4##s$F##&##s*K##+##-##0##2##4##6##:#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#,SH/#+K#s*v*DSIJ#-SAS9S;S7S<NHGF.#&DSISH#&DSIs*ts*r$s+^S'$S'SH(SHs*k$#s+0$S's*y$ISA)SAs+3#$##s*_s*M#s'{##s&,##s$D##'##s*p##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#$S&SE#s$^#7SLSEk##$#j##'#,S&/#+K#s+D*DS3J#-S#ROS=S8NHGF.#&DS3S&#&DS3s+Bs+@$s,,SI$SIS&(S&s+9$#s+Z$SIs+G$IS#)S#s+]#$##s+0s*w#s'v##s&.##s$I##'##s+>##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#U#F,SE/#+K#s+i*DSPJ#-SCS>S0SGS@NHGF.#&DSPSE#&DSPs+gs+e$s,QS3$S3SE(SEs+^$#s,#$S3s+l$ISC)SCs,&#$##s+Xs+@#s'r##s&-##s$C##'##s+c##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#,S:/#+K#s,0*DS(J#-S2S1S%S,SDQHGF.#&DS(S:#&DS(s,.s,,$s,tSP$SPS:(S:s,%$#s,F$SPs,3$IS2)S2s,I#$##s+rs+d#s,###s'o##s&%##s$A##(##s,+##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#j#&C#%C#$S'SI#s$5#7SPSIk##$#j##'#,SL/#+K#s,Y*DSMJ#-SHSAS9S;S7S<HGF.#&DSMSL#&DSMs,Ws,U$s-AS($S(SL(SLs,N$#s,o$S(s,\$ISH)SHs,r#$##s,Bs,1#s)^##s'k##s&'##s$F##(##s,T##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#j#&C#U#F,S'/#+K#s,}*DS4J#-S&S#ROS=S8HGF.#&DS4S'#&DS4s,{s,y$s-eSM$SMS'(S's,r$#s-7$SMs-$$IS&)S&s-:#$##s,is,U#s)S##s'g##s&&##s$@##(##s,x##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#,SI/#+K#s-C*DSWJ#-SESCS>S0SGS@NGF.#&DSWSI#&DSWs-As-?$s.+S4$S4SI(SIs-8$#s-Y$S4s-F$ISE)SEs-\#$##s-&s,x#s-3##s)M##s'd##s%z##s$>##)##s-?##.##0##3##5##7##9##=#j#$C#%C#j#%C#%C#$S(SM#s#d#7SWSMk##$#j##'#,S3/#+K#s-k*DS)J#-S:S2S1S%S,SDQGF.#&DS)S3#&DS)s-is-g$s.SSW$SWS3(S3s-`$#s.%$SWs-n$IS:)S:s.(#$##s-Qs-D#s-^##s)N##s'`##s%|##s$C##)##s-g##.##0##3##5##7##9##=#j#$C#%C#j#%C#U#F,SP/#+K#s.2*DSQJ#-SLSHSAS9S;S7S<GF.#&DSQSP#&DSQs.0s..$s.vS)$S)SP(SPs.'$#s.H$S)s.5$ISL)SLs.K#$##s-ws-g#s+7##s)D##s'\##s%{##s$=##)##s..##.##0##3##5##7##9##=#j#$C#%C#,S(/#+K#s.S*DS5J#-S'S&S#ROS=S8HF.#&DS5S(#&DS5s.Qs.O$s/;SQ$SQS((S(s.H$#s.i$SQs.V$IS')S's.l#$##s.3s.-#s.@##s+*##s)>##s'Y##s%s##s$;##*##s.P##/##1##4##6##8##:##>#j#$C#%C#$S)SQ#s#>#7SNSQk##$#j##'#,SM/#+K#s.z*DSNJ#-SISESCS>S0SGS@NF.#&DSNSM#&DSNs.xs.v$s/bS5$S5SM(SMs.o$#s/4$S5s.}$ISI)SIs/7#$##s.]s.T#s.j##s+(##s)?##s'U##s%u##s$@##*##s.w##/##1##4##6##8##:##>#j#$C#U#F,S4/#+K#s/@*DS*J#-S3S:S2S1S%S,SDQF.#&DS*S4#&DS*s/>s/<$s0(SN$SNS4(S4s/5$#s/V$SNs/C$IS3)S3s/Y#$##s/&s.v#s/3##s+###s)5##s'Q##s%t##s$:##*##s/=##/##1##4##6##8##:##>#$SNS*#;#*DS-Js/_&DS-S7s/]&DS-s/[s/Y$s0ES.$S.S7$S.s/^##s/)#s/R##&##(##*##,##.#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#j#-C#,SF/#+K#s0&*DS\J#&DS\SFs0$&DS\s/~s/|$s0hSR$SRSF(SFs/u$#s0:$SRs0'##s/N#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#,S+/#+K#s0I*DS.J#-S*S@S8S<QNHGF.#&DS.S+#&DS.s0Gs0E$s11S$$S$S+(S+s0>$#s0_$S$s0L$IS*)S*s0b#$###s/x#s0?##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#,SS/#+K#s0q*DSRJ#-SNSWS8S<QNHGF.#&DSRSS#&DSRs0os0m$s1YSJ$SJSS(SSs0f$#s1+$SJs0t$ISN)SNs1.#$#$ISW)SWs11#$###s0H#'##s0k##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#,S6/#+K#s1?*DS$J#-S5S4S3S<QNHGF.#&DS$S6#&DS$s1=s1;$s2'P$PS6(S6s14$#s1U$Ps1B$IS5)S5s1X#$#$IS4)S4s1[#$##s$as0s#$##(##s1:##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#,S`/#+K#s1h*DSJJ#-SQSMSISEQNHGF.#&DSJS`#&DSJs1fs1d$s2PSF$SFS`(S`s1]$#s1~$SFs1k$ISQ)SQs2%#$#$ISM)SMs2(#$##s'+s1A#s%Q##%##)##s1d##.##0##3##5##7##9##=#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#,S*/#+K#s24*DPJ#-S)S(S'S&S#NHGF.#&DPS*#&DPs22s20$s2xS+$S+S*(S*s2)$#s2J$S+s27$IS))S)s2M#$#$IS()S(s2P#$##s)Rs1j#s'v##s&E##&##*##s21##/##1##4##6##8##:##>#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#,SN/#+K#s2[*DSFJ#-SWSPSLSHSAS9HGF.#&DSFSN#&DSFs2Ys2W$s3CSS$SSSN(SNs2P$#s2q$SSs2^$ISP)SPs2t#$##s,&s23#s*E##s(c##s'/##'##s$K##s2V##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#j#&C#,S5/#+K#s2~*DS+J#-S4S3S:S2S1S%S,GF.#&DS+S5#&DS+s2|s2z$s3fS6$S6S5(S5s2s$#s38$S6s3%#s.\s2T#s,n##s+.##s)Q##s's##s&C##s$B##s2w##+##-##0##2##4##6##:#j#$C#%C#j#%C#,SQ/#+K#s3A*DSSJ#-SMSISESCS>S0SGS@F.#&DSSSQ#&DSSs3?s3=$s4)S`$S`SQ(SQs36$#s3W$S`s3D#s3-s2t#s/G##s-^##s+t##s*8##s(_##s')##s$9##s3;##,##.##1##3##5##7##;#j#$C#,S)/#+K#s3_*DS6J#-S(S'S&S#ROS=S8H.#&DS6S)#(Hs3^&DS6#s3\$s4HS*$S*S)(S)s3U$#s3v$S*((Hs3T$#s3y#s3Ks3?#s05##s.I##s,d##s*~##s)F##s'q##s$2##+##.##0##3##5##7##:#-S5S4S3S:S2S1S%S,SD.#&DS$S6#(SDs3y&DS$#s3w$SJS6$SJ%(SDs3l$#s45#s/Xs3i#s-j##s,*##s*M##s(o##s'?##s%>##s%B##+##.##s%I##1##s%x##4##7#-SNSWSPSLSHSAS9S;S7.#&DSRSS#(S7s45&DSR#s43$S$SS$S$%(S7s4($#s4M#s/Cs17#s-[##s+z##s*<##s(d##s$<##s&$##s&(##+##.##s&/##1##s&\##4##7#$S$SR$SRS.-S6S5S4S3S:S2S1S%S,.#&DS-P#(S,s4O&DS-#s4M$s59S\$S\P(Ps4F$#s4g$S\((S,s4E$#s4j$IS6)S6s4l#$##s.Es04#s,a##s+(##s)J##s'v##s%u##s%y##*##.##1##3##6##8##:#,P/#+K#s4q*DS-J#(S;s4m&DSf#s4k$s5WS-$S-SJ(SJs4d$#s5)$S-((S;s4c$#s5,$ISS)SSs5.#$##s.<s0%#s,[##s*y##s)E##s$y##s&a##s&e##*##.##1##3##6##8##:#(Os5+&DS?#s5)$s5qSf$SfS$(S$s4~$#s5C$Sf((Os4}$#s5F$IS+)S+s5H#$##s.1s/s#s,K##s*o##s)>##s%[##s%_##s'K##*##.##1##3##6##8#,S$/#+K#s5L*DS?J#$s60S?$S?SR(SRs5=$#s5^(S0s5L$S?#(S0s5=$#s5b$ISF)SFs5d#$#$IS`)S`s5g#$##s.%s/l#s,E##s*l##s)6##s&F##s&J##)##-##1##4##7##:##<#$s6KSk$SkS.(S.s5X$#s5y(S%s5g$Sk#(S%s5X$#s5}$IP)Ps6##$##s-ss/X#s,:##s*\##s),##s'+##s'/##s#x##*##.##1##4##7#,S./#+K#s6&*DSBJ#$SBS\(S\s5r$#s67(S9s6%$SB#(S9s5r$#s6;$ISJ)SJs6=#$##s-is/K#s,+##s*S##s&+##s'o##s's##s#t##*##.##1##4##7#$SqS-(S-s6,$#s6M(Rs6;$Sq#(Rs6,$#s6Q$IS$)S$s6S#$##s-Us/<#s+y##s*H##s&e##s&i##s(U##s#p##*##.##1##4#,S-/#+K#s6U*DSKJ#(Sfs6D$#s6e(S>s6S$SK#(S>s6D$#s6i$ISR)SRs6k#$##s-Hs/)#s+o##s*9##s'I##s'M##s#h##s#l##*##.##1##4#(S?s6X$#s6y(S1s6g$Su#(S1s6X$#s6}$IS.)S.s7##$##s-9s.s#s+[##s*+##s(*##s(.##s$w##s#e##*##.##1#,S?/#+K#s7$*DSTJ#(SAs6|$ST#(SAs6m$#s76$IS\)S\s78#$##s-%s.d#s+M##s'%##s(i##s(m##s$n##s#`##*##.##1#(S#s71$T*#(S#s6~$#s7G$IS-)S-s7I#$##s,ns.K#s+=##s'Z##s'^##s)J##s$e##s#[##*##.#,SB/#+K#s7I*DSUJ#(SCs74$#s7Y$ISf)Sfs7[#$##s,^s.8#s+(##s(8##s(<##s$W##s$[##s#U##*##.#(S2s7B$#s7g$IS?)S?s7i#$##s,Ds.##s*p##s(o##s(s##s%`##s$N##s#O##*#,SK/#+K#s7h*DSVJ#$ISk)Sks7x#$##s,0s-e#s'd##s)L##s)P##s%Q##s$C##s#I##*#$ISB)SBs8'#$##s+vs-L#s(7##s(;##s*'##s%B##s$8##s#C#,ST/#+K#s8%*DSXJ##s+Zs-5#s(j##s(n##s%-##s%1##s$+##s#<#$ISK)SKs8<,SU/#+K#s82*DSYJ#)Sus8A#s(Os,3#s(S##s*?##s%Z##s$P##s#[#,SV/#+K#s8=*DSZJ##s)%s+r#s))##s%D##s%H##s$B##s#S#,SX/#+K#s8G*DS[J##s(fs(c#s*R##s%m##s$c##s#n#,SY/#+K#s8P*DS]J##s);s)8#s%V##s%Z##s$T##s#e#,SZ/#+K#s8Y*DS^J##s*cs(x#s%~##s$t##s$##,S[/#+K#s8a*DSaJ##s%fs)L#s%j##s$d##s#u#,S]/#+K#s8i*DSbJ##s&1s*s#s%'##s$2#,S^/#+K#s8p*DSdJ##s%xs%u#s$r##s$'#,Sa/#+K#s8w*DSeJ##s%4s&?#s$?#,Sb/#+K#s8}*DSgJ##s$~s&)#s$3#,Sd/#+K#s9'*DShJ##s$Js%@,Se/#+K#s9,*DSiJ##s$=s%-,Sg/#+K#s91*DSjJ#,Sh/#+K#s95*DSmJ#,Si/#+K#s99*DSnJ#,Sj/#+K#s9=*DSrJ#)Sqs9Lj#.#SRj#/s$*#'s$+s$*&#Hj#0s#m#j#1s#t#'s#us#t-#Gj#2s$U#j#/s$.#'s$/s$i4#Hj#3s#s#j#4s#z#'s#{s#z;#Gj#1@#j#/s$4#'s$5s#'s###Hj#5s#y#j#6s$$#'s$%s$$s#+#Gj#4s#0#j#/s$:#'s$;s#8s#4#Hj#7s$##j#8s$*#'s$+s$*s#=#Gj#6s#B#j#/s$@#'s$As#Ks#G#Hj#9s$)#j#:s$0#'s$1s$0s#Q#Gj#8s#V#j#/s$F#'s$Gs#`s#\#Hj#;s$/#j#<s$6#'s$7s$6s#g#Gj#:s#l#j#/s$L#'s$Ms#ws#s#Hj#=s$5#j#>s$<#'s$=s$<s$##Gj#<s$(#j#/s$R#'s$Ss$4s$0#Hj#?s$;#j#@s$B#'s$Cs$Bs$>#Gj#>s$E#j#/s$X#'s$Ys$Rs$N#Fj#@s$]#j#As$x#'s$ys$ns$j#Fj#/s$|#j#Bs%A#'s%Bs%4s%0#Fj#As%E#j#Cs%l#'s%ms%\s%X#Fj#Bs%p#j#Ds&A#'s&Bs&.s&*#Fj#Cs&D#j#Es&u#'s&vs&`s&\#Fj#Ds&x#j#Fs'S#'s'Ts'=s'9#Fj#Es'W#j#Gs(4#'s(5s'ws's#Hj#Hs(9#j#Is,<#'s,=s(<s,B#SDj#Fs(>#j#Js+N#'s+Os(Xs+O#S@j#Ks:8#j#Ls::#'s:;s::s*]#SJj#Ms:A#j#Ns:L#'s:Ms:Cs)r#Pj#Os:S#j#Ps:v#'s:ws:Us)8#SF-S4S3S:S2S1S%S,SDQ.#&DS+S5#-S)S(S'S&S#ROS=S8.#&DPS*#-S*S)S(S'S&S#ROS=.#&DS.S+#-S+S*S)S(S'S&S#RO.#&DS?S$#-PS6S5S4S3S:S2S1S%.#&DSBS.#-S$S+S*S)S(S'S&S#R.#&DSKS-#-S.PS6S5S4S3S:S2S1.#&DSTS?#-S-S$S+S*S)S(S'S&S#.#&DSUSB#-S?S.PS6S5S4S3S:S2.#&DSVSK#-SBS-S$S+S*S)S(S'S&.#&DSXST#-SKS?S.PS6S5S4S3S:.#&DSYSU#-STSBS-S$S+S*S)S(S'.#&DSZSV#-SUSKS?S.PS6S5S4S3.#&DS[SX#-SVSTSBS-S$S+S*S)S(.#&DS]SY#-SXSUSKS?S.PS6S5S4.#&DS^SZ#-SYSVSTSBS-S$S+S*S).#&DSaS[#-SZSXSUSKS?S.PS6S5.#&DSbS]#-S[SYSVSTSBS-S$S+S*.#&DSdS^#-S]SZSXSUSKS?S.PS6.#&DSeSa#-S^S[SYSVSTSBS-S$S+.#&DSgSb#-SaS]SZSXSUSKS?S.P.#&DShSd#-SbS^S[SYSVSTSBS-S$.#&DSiSe#-SdSaS]SZSXSUSKS?S..#&DSjSg#-SeSbS^S[SYSVSTSBS-.#&DSmSh#-SgSdSaS]SZSXSUSKS?.#&DSnSi#-ShSeSbS^S[SYSVSTSB.#&DSrSj#j#.s$LSFj#/s%s#'s%ts%s%#Hj#0s%Z#j#1s%a#'s%bs%a+#Gj#2s&B#j#/s%w#'s%xs&V1#Hj#3s%`#j#4s%g#'s%hs%g7#Gj#1s$i#j#/s%}#'s%~s$p=#Hj#5s%f#j#6s%m#'s%ns%ms###Gj#4s$y#j#/s&'#'s&(s%%s#)#Hj#7s%l#j#8s%s#'s%ts%ss#/#Gj#6s%/#j#/s&-#'s&.s%8s#5#Hj#9s%r#j#:s%y#'s%zs%ys#;#Gj#8s%C#j#/s&3#'s&4s%Ms#A#Hj#;s%x#j#<s&##'s&$s&#s#G#Gj#:s%Y#j#/s&9#'s&:s%ds#M#Hj#=s%~#j#>s&)#'s&*s&)s#S#Gj#<s%q#j#/s&?#'s&@s%}s#Y#Hj#?s&(#j#@s&/#'s&0s&/s#_#Gj#>s&2#j#/s&E#'s&Fs&?s#e#Fj#@s&J#j#As&e#'s&fs&[s#k#Fj#/s&i#j#Bs'.#'s'/s&}s#q#Fj#As'2#j#Cs'Y#'s'Zs'Is#w#Fj#Bs']#j#Ds(.#'s(/s'ws#}#Fj#Cs(1#j#Es(b#'s(cs(Ms$'#Fj#Ds(e#j#Fs)@#'s)As)*s$-#Fj#Es)D#j#Gs)}#'s)~s)ds)~#Hj#Hs*&#j#Is.)#'s.*s*)s$6#SDj#Fs*+#j#Js-;#'s-<s*Es*Z#S@j#Ks<%#j#Ls<'#'s<(s<'s$?#SJj#Ms<.#j#Ns<9#'s<:s<0s$E#Pj#Os<@#j#Ps<c#'s<ds<Bs*~#SF(Qs;~&DS+#s;|(S8s<$&DP#s;~(S=s<&&DS.#s<$&DSBs({s<%&DSKs(Ls<&&DSTs'}s<'&DSUs'Xs<((S2s<,&DSV#s<*(S&s<.&DSX#s<,(S:s<0&DSY#s<.(S's<2&DSZ#s<0(S3s<4&DS[#s<2(S(s<6&DS]#s<4(S4s<8&DS^#s<6(S)s<:&DSa#s<8(S5s<<&DSb#s<:(S*s<>&DSd#s<<(S6s<@&DSe#s<>(S+s<B&DSg#s<@(Ps<D&DSh#s<B(S$s<F&DSi#s<D(S.s<H&DSj#s<F(S-s<J&DSm#s<H(S?s<L&DSn#s<J(SBs<N&DSr#s<Lj#.s%uSSj#/s'@#'s'As'@%#Hj#0s''#j#1s'.#'s'/s'.*#Gj#2s'k#j#/s'D#'s'Es(#/#Hj#3s'-#j#4s'4#'s'5s'44#Gj#1s&6#j#/s'J#'s'Ks&=9#Hj#5s'3#j#6s':#'s';s':>#Gj#4s&F#j#/s'P#'s'Qs&Ns###Hj#7s'9#j#8s'@#'s'As'@s#(#Gj#6s&X#j#/s'V#'s'Ws&as#-#Hj#9s'?#j#:s'F#'s'Gs'Fs#2#Gj#8s&l#j#/s'\#'s']s&vs#7#Hj#;s'E#j#<s'L#'s'Ms'Ls#<#Gj#:s'&#j#/s'b#'s'cs'1s#A#Hj#=s'K#j#>s'R#'s'Ss'Rs#F#Gj#<s'>#j#/s'h#'s'is'Js#K#Hj#?s'Q#j#@s'X#'s'Ys'Xs#P#Gj#>s'[#j#/s'n#'s'os'hs#U#Fj#@s's#j#As(2#'s(3s((s#Z#Fj#/s(6#j#Bs(W#'s(Xs(Js#_#Fj#As([#j#Cs)&#'s)'s(rs#c#Fj#Bs)*#j#Ds)W#'s)Xs)Ds#g#Fj#Cs)Z#j#Es*/#'s*0s)vs#k#Fj#Ds*2#j#Fs*i#'s*js*Ss*j#Fj#Es*m#j#Gs+J#'s+Ks+1s+I#Hj#Hs+O#j#Is/R#'s/Ss+Rs#u#SDj#Fs+T#j#Js.d#'s.es+ns,%#S@j#Ks=N#j#Ls=P#'s=Qs=Ps#}#SJj#Ms=W#j#Ns=b#'s=cs=Ys$&#Pj#Os=i#j#Ps>0#'s>1s=ks,I#SF$s>3SB$s>4SK$s>5ST$s>6SU$s>7SV$s>8SX$s>9SY$s>:SZ$s>;S[$s><S]$s>=S^$s>>Sa$s>?Sb$s>@Sd$s>ASe$s>BSg$s>CSh$s>DSi$s>ESj$s>FSm$s>GSnj#.s')SJj#/s(P#'s(Qs(P%#Hj#0s(7#j#1s(>#'s(?s(>)#Gj#2s({#j#/s(T#'s(Us)3-#Hj#3s(=#j#4s(D#'s(Es(D1#Gj#1s'F#j#/s(Z#'s([s'M5#Hj#5s(C#j#6s(J#'s(Ks(J9#Gj#4s'V#j#/s(`#'s(as'^=#Hj#7s(I#j#8s(P#'s(Qs(PA#Gj#6s'h#j#/s(f#'s(gs'qs#%#Hj#9s(O#j#:s(V#'s(Ws(Vs#)#Gj#8s'|#j#/s(l#'s(ms(*s#-#Hj#;s(U#j#<s(\#'s(]s(\s#1#Gj#:s(6#j#/s(r#'s(ss(As#5#Hj#=s([#j#>s(b#'s(cs(bs#9#Gj#<s(N#j#/s(x#'s(ys(Zs#=#Hj#?s(a#j#@s(h#'s(is(hs#A#Gj#>s(k#j#/s(~#'s)#s(xs#E#Fj#@s)'#j#As)B#'s)Cs)8s#I#Fj#/s)F#j#Bs)g#'s)hs)Zs#M#Fj#As)k#j#Cs*6#'s*7s*&s#Q#Fj#Bs*:#j#Ds*g#'s*hs*Ts#U#Fj#Cs*j#j#Es+?#'s+@s+*s+[#Fj#Ds+B#j#Fs+y#'s+zs+cs,7#Fj#Es+}#j#Gs,Z#'s,[s,As1L#Hj#Hs,_#j#Is0b#'s0cs,bs0c#SDj#Fs,d#j#Js/t#'s/us,~s/p#S@j#Ks>^#j#Ls>`#'s>as>`s.~#SJj#Ms>g#j#Ns>r#'s>ss>is.7#Pj#Os>y#j#Ps?@#'s?As>{s-X#SFVT+s>us>o)Is>v$Is>q)Is>qk##$#k##&#$Is>{WT,s>|s>vGj##Sv#j#Q%#$Is>xk##Sv#k#Q(#VT-Is?&VSwT.#m##0UG#5Sx5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#5#?C#?C%?CSx@C$#@C&#VSy#Sz?C,@C#'@C*#VSy#SzUStSo+So$#+So)#UT/So<CSDUT0C;C$Q#<CS=;C#S8%;C%H#<CS7;C#S<(<CSG<CS,;C$S@#;C&N#;C)G#UT1CUT2C=#MEELO6CSp6Cs@[3C$SO#4'MEEL#S/2(MEEL'#UT3E=*MEELS0=+MEELS%=,MEELS9=-MEELR6Cs?j3C,SO#40MEEL#S/>Cs?EBC&#>Cs?nUT4s?jWT5C$#3C&SO#47MEEL#S/6Cs@p>Cs?ZBC$#3C8SO#4<MEEL#S/>Cs?MBC(#3C#SO,4@MEEL#S/>CI6Cs?|3C$SO#4s#$MEEL#S/3C%Sc24s#&MEEL#S/2s#'MEEL%#6Cs?b3C*SO#4s#*MEEL#S/3C%Sc84s#,MEEL#S/2s#-MEEL%#0sA*6C#3C1SO#4s#1MEEL#S/3C%Sc?4s#3MEEL#S/2s#4MEEL%#6CsA03C7SO#4s#7MEEL#S/3C%Scs#%4s#9MEEL#S/2s#:MEEL%#6Cs@83C=SO#4s#=MEEL#S/3C%Scs#+4s#?MEEL#S/2s#@MEEL%#1s@?6C#3Cs#$SO#4s#DMEEL#S/3C%Scs#24s#FMEEL#S/2s#GMEEL%#6Cs@%3Cs#*SO#4s#JMEEL#S/3C%Scs#84s#LMEEL#S/2s#MMEEL%#1s@,6C#3Cs#1SO#4s#QMEEL#S/3C%Scs#?4s#SMEEL#S/2s#TMEEL%#3Cs#6SOs#?4s#VMEEL#S/3Cs#AScs#D4s#XMEEL#S/2s#YMEEL%#2s#ZMEEL(#2s#[MEEL0#2s#\MEEL7#2s#]MEEL?#2s#^MEELs#&#2s#_MEELs#-#2s#`MEELs#5#2s#aMEELs#<#2s#bMEELs#D#2s#cMEELs#I#2s#dMEELs#O#2s#eMEELs#W#2s#fMEELs#[#2s#gMEELs#]#2s#hMEELs#_#2s#iMEELs#a#3Cs#hSOs#^4s#kMEEL#S/3Cs#jSOs#T4s#mMEEL#S/2s#nMEEL#.2s#oMEELs#Z#2s#pMEEL'#\S{s#qMEEL*s#j#\S{s#rMEELs#ls#k#VT6s#sLVSwS|S}VT7FHWT8S|#S}m$%#WT9CIGXT:FH$#l#R*)#l#Ss#}s#|#l#Ts$0s$/#j#UC#j#VC#j#WC#j#XC#j#YC#j#ZC#j#[C#j#\C#j#]C#j#^C#j#_C#j#`C#j#aS_#j#bS_#j#cS_#j#dS_#j#eS_#$FSG#S,#$S,H(Hs@i$#sA.(Ns@x$S,#(Ns@i$#sA2#s<|s@W#s=J##s=z##s@i##s@g##s@e##s@c##s@a##+##.##1##4##S9##S%##S0##O#(NsA#$#sAD$Hs'n(Qs@~$#sAG#s<js@o#s=6##s=`##s>4##sA###s@}##s@{##s@y##+##.##0##s@H#k##4#k##s#,#k#UC#k#VC#k#WC#k#XC#k#YC#k#ZC#k#[C#k#\C#k#]C#k#^C#k#_C#k#`C#k#aS_#k#bS_#k#cS_#k#dS_#k#eS_#gFs2Js(1s)xs2's1~SFS=ORS#S&S'S(S)S8S*S+QS<l#fs#A$#l#gs%Is%U#l#hs%Qs%N#l#gs%[s%V#As0Ws0Es%]#As0Ys0Es&n#As0\s0Es(<#As0`s0Es**#8Cs0eH#8Cs1(S8#8Cs1HS=#8Cs1lO#8Cs28R#8Cs2aS##8Cs3/S&#8Cs3ZS'#8Cs4'S(#8Cs4KS)#j#is4l#j#Is4o#j#$C#V#GFj##s56#j#jC#9Cs5`s5Z#Fj#Ps6&#j#%C#V#GFj##s6J#j#jC#9Cs6us6o#Fj#Ps7<#j#&C#V#GFj##s7a#j#jC#9Cs81s8+#Fj#Ps8U#j#'C#V#GFj##s8{#j#jC#9Cs9Ls9F#Fj#Ps9q#j#(C#V#GFj##s:<#j#jC#9Cs:js:d#Fj#Ps;4#j#)C#V#GFj##s;\#j#jC#9Cs</s<)#Fj#Ps<V#j#*C#V#GFj##s=##j#jC#9Cs=Ss=M#Fj#Ps={#j#+C#V#GFj##s>I#j#jC#9Cs>{s>t#Fj#Ps?H#j#,C#V#GFj##s?m#j#jC#9Cs@>s@7#Fj#Ps@b#j#-C#V#GFj##sA(#j#jC#9CsARsAK#Fj#PsBQ#j#kC#j#lC#j#mT;#l#nsBVsBW#l#osB]sB^#l#psBmsBn##"). Qed.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma rauxv_ok_frame : forall m m' B W,
  rauxv_ok m B -> munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) W ->
  rauxv_ok m' B.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocTree.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocTree.HCW2.rauxv_ok); constr:(@kc__1); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.RAUXV_CELL); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocRep.wz); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64s); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocTree.HCW2.rauxv_list); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Datatypes.fst); constr:(@kc__2); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocTree.Forall_disjoint_from); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.bytes_at_transport); constr:(@Corelib.Init.Datatypes.length); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X)|] [|@rnd; @x23; @x12; @x11; @x6; @x16; @x5; @x4; @x3; @av; @iv; @x; @y; @m; @n; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @__sat25; @__sat24; @H0; @_H; @hi; @lo; @__p1; @__p2; @__p3; @__p4; @__p5; @FW; @WM; @MU; @H; @A2; @A1; @C; @W; @B; @m'; @HCANB; @HSECB; @HCEILB|] "#@D#h$w$$$+###$#v$,$]#%$.#&#)#(#'#,$^$\#1#3#-#7#/#5#^#4#6#8#9#;#=#>#2#:#<#?#A#0#@#C#E#G#*#B#D#[#+#F#H#I#K#h#.#L#M#Q#]#J#P#W#X#N#O#U#Z#_#S#Y#R#T#V#`#\#b#g#a$5#n#f#e#d#c$c$d$C#u#r$P$V#l#~#}$%$1$D$F$O$R$X$j$k$s$p#k#s#t#w#y#z#{$#$&$6$:$;$=$M$N$Q$S$U$T$Y$[$f$e$g$h$m$l$n$i$o$A$r$u$v#|#m$)$E$2#x#p$*$0$-$/$4$3#q$<$'$7$8$9$L$?$(#o$a$`$>$w$Z$x$J$b$_$K$I$H$W$G$B$q$t$@N$O%#n%$P%$Q$$R'#m%$S%$T$$U'$V$$W&$X$$Y,$Z$$[$$\%$]%$^&$_&$`&$a%$b'$c(#u$$d$$e'$f*$g($h*$i+$j)$k$$l%$m*$n5$o/$p)$q'$r'$s)$t%$u%$v'USxSj1Sg1#1#1#1#1#1#1#1#1#1#1#1#1#*#1#1#1#1#1#1#1#1#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#;#USySj$$#1s#&1#1#1#1#1#1#1#1#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#;#$s#%##s#%#m#s#W#USzSfUS{Sf$G#*Sg;#*$*#*#*#*#;#VS|)#)-##-#m#0#US}SfUS~Sf$G#)$)#$#m#'#USk.USl#USk3USl#UT##k##&#USmT$3LF,P.#USnK-K$#+DS#H#/S?S;MNOLJFE0#'DS#P#;A(E#,s#(UT%#'DS#%#$s#RS'$S'P1s#+*#*#*#*#*#;#(P#$#s#+$S'1;s#1(E#$#s#/$GS?)S?s#1#$#$GS;)S;s#4#$#$GM)Ms#7#$#$GN)Ns#:#$#$GO)Os#=#$#$GL)Ls#@#$#$GJ)Js#C#$#$GF)Fs#F#$#$GE)Es#I#$##&##*##.##2##6##:##>##B##s#&##s#*##s#,##s#6##s#8##s#:##s#@##s#D#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#j#-C#%C#4JNO5DMNVT&CCWT'CCE$#M$$H(Hs#[WT(CCE$$#2&##(#j#.+#6,#O3S;Mk##$#k##0#k##2#j##4#+DS1Hs#l'DS1Ps#j'DS1s#hs#f$s$YS6$S6P$S6s#k##s#6#s#_##&##(##*##,##.#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#j#-C#U#E+DS$Hs$1'DS$Ps$/'DS$s$-s$+$s$zS#$S#P$S#s$0##s#W#s$$##&##(##*##,##.#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#,S%.#-K#s$S+DS*H#'DS*S%s$Q'DS*s$Os$M$s%@S1$S1S%(S%s$F$#s$n$S1s$T##s#{#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#4MPS?5DS%P$s#wS%##s#rj#.s#z#6s#{#S?3SES%k##$#k##)#k##+#j##-#,SE.#-K#s%&+DS(H#'DS(SEs%$'DS(s$~s$|$s%oS$$S$SE(SEs$u$#s%A$S$s%'##s$N#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#U#E,S'.#-K#s%J+DS+H#'DS+S's%H'DS+s%Fs%D$s&7S*$S*S'(S's%=$#s%e$S*s%K##s$r#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#,S6.#-K#s%l+DS&H#/PS;MNOLJFE0#'DS&S6#'DS&s%js%h$s&[S($S(S6(S6s%a$#s&-$S(s%o$GP)Ps&0#$###s%?#s%b##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#4S%S6S'5DS#S6$s%9S###s%4j#.s%<#6s%=#S'3S1S#k##$#k##)#k##+#j##-#,S#.#-K#s&D+DS,H#/S%S;MNOLJFE0#'DS,S##'DS,s&Bs&@$s'3S+$S+S#(S#s&9$#s&a$S+s&G$GS%)S%s&d#$###s%s#s&:##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#U#E,S1.#-K#s&m+DS-H#/SES;MNOLJFE0#'DS-S1#'DS-s&ks&i$s'\S&$S&S1(S1s&b$#s'.$S&s&p$GSE)SEs'1#$###s&@#s&c##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#,S$.#-K#s'8+DS2H#/S'S?MNOLJFE0#'DS2S$#'DS2s'6s'4$s('S,$S,S$(S$s'-$#s'U$S,s';$GS')S's'X#$##s'*s&h#$##s'/##)##+##.##0##2##4##8#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#4S#S*S$5DS(S*$s&`S(##s&[j#.s&c#6s&d#S$3S+S(k##$#k##)#k##+#j##-#,S*.#-K#s'k+DS.H#/S6PMNOLJFE0#'DS.S*#'DS.s'is'g$s(ZS-$S-S*(S*s'`$#s(,$S-s'n$GS6)S6s(/#$##s$^s'?#$##s'b##)##+##.##0##2##4##8#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#U#E,S(.#-K#s(7+DS3H#/S#S%MNOLJFE0#'DS3S(#'DS3s(5s(3$s)&S2$S2S((S(s(,$#s(T$S2s(:$GS#)S#s(W#$##s$Rs'g#$##s(.##)##+##.##0##2##4##8#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#,S+.#-K#s(]+DS/H#/S1SES;NOLJFE0#'DS/S+#'DS/s([s(Y$s)LS.$S.S+(S+s(R$#s(z$S.s(`$GS1)S1s(}#$##s(Ls(2#s$P##%##s(U##*##,##/##1##3##5##9#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#4S(S,S&5DS-S,$s((S-##s(#j#.s(+#6s(,#S&3S2S-k##$#k##)#k##+#j##-#,S&.#-K#s)3+DS0H#/S$S'S?NOLJFE0#'DS0S&#'DS0s)1s)/$s)~S3$S3S&(S&s)($#s)P$S3s)6$GS$)S$s)S#$##s)%s(d#s$[##%##s)+##*##,##/##1##3##5##9#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#U#E,S,.#-K#s)Z+DS4H#/S*S6PNOLJFE0#'DS4S,#'DS4s)Xs)V$s*IS/$S/S,(S,s)O$#s)w$S/s)]$GS*)S*s)z#$##s&Ms)/#s$O##%##s)R##*##,##/##1##3##5##9#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#,S-.#-K#s*#+DS7H#/S(S#S%MOLJFE0#'DS7S-#'DS7s)}s){$s*nS0$S0S-(S-s)t$#s*@$S0s*&$GS()S(s*C#$##s)ks)U#s&?##s$M##&##s)x##+##-##0##2##4##6##:#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#4S-S3S.5DS/S3$s)IS/##s)Dj#.s)L#6s)M#S.3S0S/k##$#k##)#k##+#j##-#,S2.#-K#s*T+DS5H#/S+S1SES;OLJFE0#'DS5S2#'DS5s*Rs*P$s+CS4$S4S2(S2s*I$#s*q$S4s*W$GS+)S+s*t#$##s*Cs**#s&G##s$X##&##s*M##+##-##0##2##4##6##:#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#U#E,S..#-K#s*z+DS<H#/S&S$S'S?OLJFE0#'DS<S.#'DS<s*xs*v$s+iS7$S7S.(S.s*o$#s+;$S7s*}$GS&)S&s+>#$##s*ls*P#s&F##s$L##&##s*s##+##-##0##2##4##6##:#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#,S3.#-K#s+B+DS8H#/S,S*S6PNLJFE0#'DS8S3#'DS8s+@s+>$s,1S5$S5S3(S3s+7$#s+_$S5s+E$GS,)S,s+b#$##s++s*u#s(6##s&8##s$J##'##s+<##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#4S/S7S45DS5S7$s*gS5##s*bj#.s*j#6s*k#S43S<S5k##$#k##)#k##+#j##-#,S/.#-K#s+r+DS=H#/S-S(S#S%MLJFE0#'DS=S/#'DS=s+ps+n$s,aS<$S<S/(S/s+g$#s,3$S<s+u$GS-)S-s,6#$##s+^s+I#s(2##s&@##s$U##'##s+l##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#U#E,S0.#-K#s,;+DS9H#/S2S+S1SES;LJFE0#'DS9S0#'DS9s,9s,7$s-*S8$S8S0(S0s,0$#s,X$S8s,>$GS2)S2s,[#$##s,*s+n#s(.##s&?##s$I##'##s,5##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#,S4.#-K#s,^+DS@H#/S.S&S$S'S?OJFE0#'DS@S4#'DS@s,\s,Z$s-MS=$S=S4(S4s,S$#s,{$S=s,a$GS.)S.s,~#$##s,Ds,6#s,Q##s(+##s&1##s$G##(##s,Y##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#j#&C#%C#4S5S=S85DS9S=$s,&S9##s+}j#.s,)#6s,*#S83S@S9k##$#k##)#k##+#j##-#,S7.#-K#s-1+DS:H#/S3S,S*S6PNJFE0#'DS:S7#'DS:s-/s--$s-|S9$S9S7(S7s-&$#s-N$S9s-4$GS3)S3s-Q#$##s,vs,e#s*%##s('##s&9##s$R##(##s-,##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#j#&C#U#E,S5.#-K#s-U+DSAH#/S/S-S(S#S%MJFE0#'DSAS5#'DSAs-Ss-Q$s.DS@$S@S5(S5s-J$#s-r$S@s-X$GS/)S/s-u#$##s-As--#s)q##s(###s&8##s$F##(##s-P##-##/##2##4##6##8##<#j#$C#%C#j#%C#%C#,S<.#-K#s-w+DSBH#/S0S2S+S1SES;LFE0#'DSBS<#'DSBs-us-s$s.fS:$S:S<(S<s-l$#s.8$S:s-z$GS0)S0s.;#$##s-Zs-P#s-g##s)k##s'|##s&*##s$D##)##s-s##.##0##3##5##7##9##=#j#$C#%C#j#%C#%C#4S9SAS:5DSBSA$s->SB##s-9j#.s-A#6s-B#S:3SJSBk##$#k##)#k##+#j##-#,S8.#-K#s.I+DSJH#/S4S.S&S$S'S?OFE0#'DSJS8#'DSJs.Gs.E$s/8SA$SAS8(S8s.>$#s.f$SAs.L$GS4)S4s.i#$##s./s-~#s.<##s)r##s'x##s&2##s$O##)##s.E##.##0##3##5##7##9##=#j#$C#%C#j#%C#U#E,S=.#-K#s.l+DSCH#/S7S3S,S*S6PNFE0#'DSCS=#'DSCs.js.h$s/[SB$SBS=(S=s.a$#s/-$SBs.o$GS7)S7s/0#$##s.Us.E#s+`##s)b##s't##s&1##s$C##)##s.h##.##0##3##5##7##9##=#j#$C#%C#,S9.#-K#s/1+DSFH#/S5S/S-S(S#S%MJE0#'DSFS9#'DSFs//s/-$s/|SJ$SJS9(S9s/&$#s/N$SJs/4$GS5)S5s/Q#$##s.ms.g#s.z##s+N##s)\##s'q##s&###s$A##*##s/.##/##1##4##6##8##:##>#j#$C#%C#4SBSFSC5DSGSF$s.SSG##s.Nj#.s.V#6s.W#SC3SNSGk##$#k##)#k##+#j##-#,S@.#-K#s/^+DSGH#/S<S0S2S+S1SES;LE0#'DSGS@#'DSGs/\s/Z$s0MSC$SCS@(S@s/S$#s/{$SCs/a$GS<)S<s/~#$##s/As/8#s/N##s+R##s)c##s'm##s&+##s$L##*##s/[##/##1##4##6##8##:##>#j#$C#U#E,S:.#-K#s0$+DSNH#/S8S4S.S&S$S'S?OE0#'DSNS:#'DSNs/~s/|$s0oSF$SFS:(S:s/u$#s0A$SFs0'$GS8)S8s0D#$##s/fs/Z#s/s##s+M##s)S##s'i##s&*##s$@##*##s/}##/##1##4##6##8##:##>#,SA.#-K#s0D+DSOH#/S=S7S3S,S*S6PNF0#'DSOSA#(Fs0C'DSO#s0A$s14SG$SGSA(SAs0:$#s0b$SG((Fs09$#s0e$GS=)S=s0g#$##s00s0$#s-;##s+=##s)O##s'h##s%z##s$@##*##.##1##3##6##8##:##=##A#4SGSKSO5DSHSK$s/gSH##s/bj#.s/j#6s/k#SO3SUSHk##$#k##)#k##+#j##-#/S9S5S/S-S(S#S%MJ0#'DSKSB#(Js0m'DSK#s0k$s1^SN$SNSB(SBs0d$#s10$SN((Js0c$#s13$GS9)S9s15#$##s0]s0Q#s-1##s+?##s)T##s'b##s&$##s$I##*##.##1##3##6##8##:##=#,SJ.#-K#s14+DSHH#/S:S8S4S.S&S$S'S?O0#'DSUSC#(Os13'DSU#s11$s2$SK$SKSC(SCs1*$#s1R$SK((Os1)$#s1U$GS:)S:s1W#$##s1)s0y#s,_##s*e##s({##s'<##s%R##s#x##*##.##1##3##6##8##:##=#/SAS=S7S3S,S*S6PN0#'DSSSF#(Ns1Q'DSS#s1O$s2BSH$SHSF(SFs1H$#s1p$SH((Ns1G$#s1s$GSA)SAs1u#$##s.Hs1>#s,J##s*\##s(u##s'+##s%M##s#s##*##.##1##3##6##8##:##=#4SHSVSS5DSPSV$s0tSP##s0oj#.s0w#6s0x#SS3SWSPk##$#k##)#k##+#j##-#(Ms1w'DSV#s1u$s2hSU$SUSG(SGs1n$#s2:$SU((Ms1m$#s2=$GSB)SBs2?#$##s.:s1g#s,H##s*]##s(k##s'-##s%R##s#o##*##.##1##3##6##8##:#/SJS@S<S0S2S+S1SES;0#'DSPSN#(S?s28'DSW#s26$s3)SV$SVSO(SOs2/$#s2W$SV((S?s2.$#s2Z$GSC)SCs2\#$##s-cs2.#s+i##s*###s(@##s&V##s$|##s#j##*##.##1##3##6##8##:#(Ps2R'DSL#s2P$s3CSP$SPSK(SKs2I$#s2q$SP((Ps2H$#s2t$GSF)SFs2v#$##s-Js/I#s+\##s)u##s(+##s&M##s$s##s#f##*##.##1##3##6##8##:#4SPSMSL5DSTSM$s1tST##s1oj#.s1w#6s1x#SL3SQSTk##$#k##)#k##+#j##-#$s3fSW$SWSH(SHs2l$#s38(S%s2{$SW#(S%s2l$#s3<$GSG)SGs3>#$##s-Fs/9#s+[##s)i##s(+##s&P##s$m##s#d##*##.##1##4##7##9#(SEs33'DST#s31$s4$SM$SMSS(SSs3*$#s3R(S's39$SM#(S's3*$#s3V$GSO)SOs3X#$##s,ds._#s*z##s);##s'Q##s%w##s$e##s#a##*##.##1##4##7##9#4SMS>SQ5DSYS>$s2USY##s2Pj#.s2X#6s2Y#SQ+DS[Hs3X'DS[Ps3V'DS[s3Ts3R$s4ES_$S_P$S_s3W##s2~#s3K##&##(##*##,##.#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#%C#j#-C#,SX.#-K#s3{+DS_H#'DS_SXs3y'DS_s3ws3u$s4hS`$S`SX(SXs3n$#s4:$S`s3|##s3G#%##(##*##,##.##0#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#%C#j#,C#,SR.#-K#s4B+DS`H#/S>S;MNOLJFE0#'DS`SR#'DS`s4@s4>$s51Sa$SaSR(SRs47$#s4_$Sas4E$GS>)S>s4b#$###s3q#s48##(##*##-##/##1##3##7#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#%C#j#+C#,S).#-K#s4j+DSaH#/SQSWMNOLJFE0#'DSaS)#'DSas4hs4f$s5YSb$SbS)(S)s4_$#s5+$Sbs4m$GSQ)SQs5.#$#$GSW)SWs51#$###s4A#'##s4d##,##.##1##3##5##7##;#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#%C#j#*C#,SI.#-K#s58+DSbH#/STSPSHNOLJFE0#'DSbSI#'DSbs56s54$s6'SZ$SZSI(SIs5-$#s5U$SZs5;$GST)STs5X#$#$GSP)SPs5[#$#$GSH)SHs5^#$###s4o#'##+##s56##0##2##5##7##9##;##?#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#%C#j#)C#,SY.#-K#s5d+DSZH#/SMSVSKSFOLJFE0#'DSZSY#'DSZs5bs5`$s6SS\$S\SY(SYs5Y$#s6%$S\s5g$GSM)SMs6(#$#$GSV)SVs6+#$#$GSK)SKs6.#$##s%ss5@#$##(##,##s5c##1##3##6##8##:##<##@#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#%C#j#(C#,S>.#-K#s63+DS\H#/SLSSSOSCS:LJFE0#'DS\S>#'DS\s61s6/$s6~SX$SXS>(S>s6($#s6P$SXs66$GSL)SLs6S#$#$GSS)SSs6V#$##s'^s5i#s&Z##s%_##&##*##s60##/##1##4##6##8##:##>#j#$C#%C#j#%C#%C#j#&C#%C#j#'C#,SQ.#-K#s6Z+DSXH#/SWSUSNSJS@S<JFE0#'DSXSQ#'DSXs6Xs6V$s7ISR$SRSQ(SQs6O$#s6w$SRs6]$GSU)SUs6z#$#$GSN)SNs6}#$#$GSJ)SJs7$#$#$GS@)S@s7'#$##s)ds6;#$##(##,##0##s$Z##s6^##6##8##;##=##?##A##s#%#j#$C#%C#j#%C#%C#j#&C#,ST.#-K#s7*+DSRH#/SPSHSGSBS9S5S/FE0#'DSRST#'DSRs7(s7&$s7uS)$S)ST(STs6{$#s7G$S)s7-#s,1s6\#s*V##s(s##s'j##s&l##s$M##s$Q##s7###+##-##0##2##4##6##:#j#$C#%C#j#%C#,SM.#-K#s7I+DS)H#/SVSKSFSAS=S7S3S,E0#'DS)SM#'DS)s7Gs7E$s88SI$SISM(SMs7>$#s7f$SIs7L#s.cs6|#s,u##s+;##s)a##s(T##s'T##s$A##s$E##s7C##,##.##1##3##5##7##;#j#$C#,SL.#-K#s7g+DSIH#/SSSOSCS:S8S4S.S&S$0#'DSISL#(S$s7f'DSI#s7d$s8WSY$SYSL(SLs7]$#s8)$SY((S$s7\$#s8,#s/Ls17#s-i##s,###s*I##s)7##s(3##s'8##s$;##+##.##0##3##5##7##:#$s7(SI##s7#j#.s7+#USoB:#$ES)$EH$s7,F2$##&#$FSR$FH$s71J2$##&#&Sp&#&#&#&#&#&#&#:#(H#$#L$JH2$#j##0#$s7BL2&#$LS\$OH$s7FN2$#$-M$NH2$#$s7KM2#%j#/CE$FEB#j#0C#j#/C#(FEXT)CCT*#7C#j#1C#j#2C#7CH:E7C#j#/Sh#7Cs8X`SqShCCCSeSe11$s##s8Y#ECCCCCCS]222S])HH(s##s8Z#7CMFCCS^4S^0s#$s7_$MM#B9G;:8:$#VT+s9$s8z)Gs9%$Gs8|)Gs8|k##$#k##&#$Gs9*WT,s9+s9%Fj##Sr#j#3%#$Gs9'k##Sr#k#3(#VT-Gs917T.#m##0UF#USnSiUSmSiVSsCJVSsCLHC$F#UT/CUT0CCCs:9CCSg<C$Sc#=&RIIQ#SdVT1Cs8{WT2C&#CCs9C<C$Sc#=+RIIQ#SdD,RIIQ(#UT3ID.RIIQ%*@/RIIQ%$#VT40Q7StSuVT5EJWT6St#Sum$%#WT7CGFXT8EJ$#l#4*)#l#5:9#l#6?>#j#7C#j#8C#j#9C#$JE$s95F2$#$s+SJ$LF2$#k##&#k#7C#k#8C#k#9C#XEPS%HOl#:.$#l#;s#0s#<#l#<s#8s#5#l#;s#Bs#=#Is#[s#Ys#D#j#=s#_#j#>s#c#V#FEj##s#f#j##s#{#>s#|s#ys#j#Ej#=s#~#j#?C#j#@C#$s8TSR##s8Oj#.s8W#XT9CCFEU$#USos%]:#(H#$#J2#s$,k##(#k#?C#k#@C#m#0#Js$:S>Hs$8E#^T:DS>S)SIHs$ZS'JF#Ks9ks$X:#&s$*&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#:#(S>#$#L$JS>2$#j##s%s#(S)($#M$NS)2$#$s)<M2#%7CS)7Cs;@`SqShCCCSeSes%bs%bs%U1s;A#ECCCCCCS]s%cs%cs%cS]s%ZS)S)%1s;B#FCCS^s%dS^s%`,s)B#MMs%SB+G-,*,$#LCs&#LCs&%LCSpWSvC$#WSvC&#VT;#T<-Si#s%GUT=CHC#Js%FHC$F#CCs<z<Cs%ESc#=s%GRIIQ#SdAs%HRIIQN<C&Scs%G=s%JRIIQ#SdAs%KRIIQM?s%LRIIQ$#?s%MRIIQ'#As%NRIIQS;Ds%ORIIQ#s%K@s%PRIIQ%s%E#@s%QRIIQ,s%F#l#4#s%Ds%>l#51s%T#l#65s%Y#j#7C#j#8C#j#9C#j#ASD#j#BSD#j#CSD#$FJ#s%=N#O#$LJ2S;#k##%#k##(#k#7C#k#8C#k#9C#k#ASD#k#BSD#k#CSD#(SZs;s$#S%$$s<@(S0s<'$S[#(S0s;t$#s<D$GS))S)s<F#$##s/'s0j#s(###s('##s(+##s(/##s)y##s)}##*##.##1##4#$s=(S[\E7$#S[PSZNS#l#:s#':#l#;s&+s&7#l#<s&3s&0#l#;s&=s&8#Is#Ts#Rs#K#j#>s&Z#j#=s&^#V#FEj##s&a#j##s&v#>s&ws&ts#^#Ej#=s&y#j#?C#j#@C#/SWSUSNSJS@S<S0S2S+0#Ks<X#:#(SQ#$#J$FSQ2$#k##s%]#k#?C#k#@C#m#.#Js'3S>SLs%TE#]SwDS>S)SISLs'PS?J#Ks<ds<T:#(S&s<Y(#s'#$#L$J%2$#j##s'0#(S2s<_(#s')$#M$N%2$#('s<d$#M2#&7C*ECCCCCCS]s&|s&|s&|S]s&s++#s'1s<hs&mFCCS^s&}S^s&y+'#MMs&lB*G,+(+$#<Cs#mScs&N=s&URIIQ#SdAs&VRIIQS??s&WRIIQ$#?s&XRIIQs#h#?s&YRIIQs#l#?s&ZRIIQs#p#As&[RIIQP<Cs&[Scs&V=s&]RIIQ#SdDs&^RIIQ%#@s&_RIIQ's&T#@s&`RIIQs#ws&U#l#4#s&Ss&Ml#5s#|s&c#l#6s$$s&h#j#7C#j#8C#j#9C#j#ASD#j#BSD#j#CSD#j#DSD#j#ESD#$Ls/C##S;#M##N##O#$Ls.z2P#k##%#k##s#w#k#7C#k#8C#k#9C#k#ASD#k#BSD#k#CSD#k#DSD#k#ESD#(s#ps=9$#S%$S[SZ^E$s#ds#t#s#aS[PS0NS#l#:8'#l#;s'-s'9#l#<s'5s'2#l#;s'?s':#Is#<s#9s#4#j#>s'\#j#=s'`#V#FEj##s'c#j##s'x#>s'ys'vs#G#Ej#=s'{#j#?C#j#@C#(S+s=K(#s#R$#J$F%2$#k##s&\#k#?C#k#@C#m#+#Js(2S>s(Ls#ZE#]SwDS>S)SIs(Ms=ROJ#Ms(Ms(9#LMs(Ps(9s#_#Ms(Ts(9s&Y#8Cs(YS$#8Cs(xS&#8Cs)<S.#8Cs)iS4#8Cs*5S8#8Cs*aS:#8Cs+2SC#8Cs+]SO#8Cs,*SS#8Cs,NSL#j#Fs,o#j#Gs,t#j#Hs,v#j#Is,x#j#Js-5#V#FEj##s-9#j##s-u#>s-vs-_s-S#Ej#=s-y#j#Ks.8#V#FEj##s.=#j##s.~#>s/#s.es.Y#Ej#=s/'#j#Ls/F#V#FEj##s/L#j##s09#>s0:s/xs/l#Ej#=s0?#j#$C#V#FEj##s0b#j#/C#9Cs16s1*#Ej#=s1X#j#%C#V#FEj##s1|#j#/C#9Cs2Qs2E#Ej#=s2t#j#&C#V#FEj##s3=#j#/C#9Cs3os3c#Ej#=s47#j#'C#V#FEj##s4]#j#/C#9Cs54s5(#Ej#=s5Y#j#(C#V#FEj##s6$#j#/C#9Cs6Xs6L#Ej#=s6~#j#)C#V#FEj##s7J#j#/C#9Cs8#s7s#Ej#=s8J#j#*C#V#FEj##s8s#j#/C#9Cs9Ms9A#Ej#=s9u#j#+C#V#FEj##s:C#j#/C#9Cs:zs:n#Ej#=s;G#j#,C#V#FEj##s;l#j#/C#9Cs<Bs<6#Ej#=s<f#j#-C#V#FEj##s=,#j#/C#9Cs=bs=O#Ej#=s>a#j#Ms>c#j#NC#j#Os>f#j#1T>#l#Ps>ns>o#l#Qs>us>v#l#Rs?)s?*##"). Qed.

(* [comment removed for export] *)
Lemma rraw_free_bridge : forall st s (p : bptr) (pf : aptr) (o : mem) Q1 Q ms,
  strip st = ps_m s ->
  hdr_ok pans_mem pupd_mem st pf (fst p) ->
  rimplT o (free st (Some pf)) s Q1 ms ->
  (forall st' s' ms', Q1 st' s' ms' -> Q tt (set_m (strip st') s') ms') ->
  implM rsegs (raw_free p) s Q ms.
Proof. try hcb. try hsb.
  intros st s p pf o Q1 Q ms Hst Hh H HQ. unfold raw_free.
  eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind rsegs _ _ _ (fun cs s' ms' => exists st', Q1 st' s' ms' /\ strip st' = cs)).
  { rewrite <- Hst. eapply (rimplT_strel FREL o (free st (Some pf)) (cfree (strip st) (Some (fst p))) s Q1).
    - unfold mrun. apply free_control. exact Hh.
    - exact H.
    - intros o1 st' cs s' ms' HR H1. exists st'. split; [exact H1|]. unfold FREL in HR. exact HR. }
  intros cs s' ms' (st' & H1 & <-). cbv beta.
  apply implM_upd. apply evt_done. eapply HQ. exact H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rpres_except (C : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> ~ C a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma rpres_except_refl C m : rpres_except C m m.
Proof. try hcb. try hsb. intros a _ _; auto. Qed.
Lemma rpres_except_trans C m1 m2 m3 : rpres_except C m1 m2 -> rpres_except C m2 m3 -> rpres_except C m1 m3.
Proof. try hcb. try hsb. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma rpres_except_mono (C C' : Z -> Prop) m m' : rpres_except C m m' -> (forall a, C a -> C' a) -> rpres_except C' m m'.
Proof. try hcb. try hsb. intros H HC a Ha Hc. apply H; [exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.

(* [comment removed for export] *)
Lemma rpres_except_of_munch C W m m' :
  munch W m m' -> wmono rsegs m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. try hcb. try hsb.
  intros MU WM HW a Ha Hc. split.
  - apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
  - apply WM.
Qed.

Lemma rpres_except_bytes_at C m m' A bs :
  rpres_except C m m' -> bytes_at rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) ->
  bytes_at rsegs m' A bs.
Proof. try hcb. try hsb.
  intros HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma rpres_except_wr_at C m m' A n :
  rpres_except C m m' -> wr_at rsegs m A n -> (forall a, A <= a < A + n -> ~ C a) -> wr_at rsegs m' A n.
Proof. try hcb. try hsb.
  intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

Lemma rpres_except_rw_cells C m m' A cs :
  rpres_except C m m' -> rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) ->
  rw_cells rsegs m' A cs.
Proof. try hcb. try hsb.
  intros HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rpres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rpres_except_wr_at; eauto.
Qed.

Lemma rpres_except_stk C m m' lo hi :
  rpres_except C m m' -> stk rsegs m lo hi -> (forall a, lo <= a < hi -> ~ C a) -> stk rsegs m' lo hi.
Proof. try hcb. try hsb.
  intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Definition ralloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ errno_addr (Z_to_bv 64 0x92650) <= a < errno_addr (Z_to_bv 64 0x92650) + 4
  \/ RCTX <= a < RCTX + 928
  \/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
  (* [comment removed for export] *)

Definition RAM_STACK : Z := 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rfresh_image st a : fresh_addr st a -> s_reserved st = ref_reserved -> a < 0x10000 \/ 0xb4000 <= a.
Proof. try hcb. try hsb.
  intros [_ FR] RS. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; right; left; reflexivity)). lia.
Qed.

(* [comment removed for export] *)
Lemma rfresh_below st a : fresh_addr st a -> s_reserved st = ref_reserved -> a < hceil.
Proof. try hcb. try hsb.
  intros [C FR] RS. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)) as X.
  cbv delta [Decode.CEIL_BAND Malloc.alloc_ceiling Decode.alloc_ceiling] in X, C. hcb. lia.
Qed.

(* [comment removed for export] *)
Lemma rlive_below st b n : s_reserved st = ref_reserved -> ranges_free (live_ranges st) b n = true ->
  0 <= n -> b + n <= Malloc.alloc_ceiling -> b + n <= hceil.
Proof. try hcb. try hsb.
  intros RS FR Hn Hc. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)) as X.
  cbv delta [Malloc.alloc_ceiling CEIL_BAND] in X, Hc. hcb. lia.
Qed.

Definition ram_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (s : PState) (lo : Z) (m : mem)
    (st1 : mstate) (mo : optr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (pw st1 mo) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' (bv_unsigned sp)
    /\ rpres_except (fun a => ralloc_fp (fun k => k <> RKGroup) st1 lo (bv_unsigned sp) a \/ fresh_addr st a) m m'
    /\ rmrep st1 m' /\ ticks_ok st1
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ am_rel st st1 mo.

(* [comment removed for export] *)
Definition ralloc_meta_stmt (am_pre : mstate -> Prop) : Prop :=
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 0x92650 ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs)).

End HCW2.

