(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Export MallocTree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export UMallocRep UMallocTree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc Realloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Export MallocOracle MallocRealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma xmrun_ret {R} o (r : R) : xmrun o (SRet r : MX R) = SRet (o, r).
Proof. reflexivity. Qed.

Lemma xmrun_peek {R} o p c h (k : Z -> MX R) :
  xmrun o (SVis (XE (EPeek p c h)) k) = xmrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.

Lemma xmrun_vis {R} o (e : xev) (k : Z -> MX R) :
  match e with XE (EPeek _ _ _) => False | _ => True end ->
  xmrun o (SVis e k) = SVis e (fun z => xmrun o (k z)).
Proof.
  intros He. unfold xmrun. rewrite xprun_vis by exact He.
  f_equal. destruct e as [e|]; [destruct e|]; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rimplTX {R} (o : mem) (t : MX R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM usegs (xmembed (xmrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

Lemma rimplTX_ret {R} o (r : R) s Q ms : evt usegs (Q r s) ms -> rimplTX o (SRet r) s Q ms.
Proof. intros H. unfold rimplTX. rewrite xmrun_ret. cbn [xmembed]. apply implM_ret. exact H. Qed.

Lemma rimplTX_peek {R} o p c h (k : Z -> MX R) s Q ms :
  rimplTX o (k (pans_mem o p c h)) s Q ms -> rimplTX o (SVis (XE (EPeek p c h)) k) s Q ms.
Proof. intros H. unfold rimplTX. rewrite xmrun_peek. exact H. Qed.

Lemma rimplTX_undef {R} o w (k : Z -> MX R) s Q ms : rimplTX o (SVis (XE (EUndef w)) k) s Q ms.
Proof.
  unfold rimplTX. rewrite xmrun_vis by exact I. cbn [xmembed xev_step ev_step].
  eapply (implM_bind usegs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

Lemma rimplTX_xguard {R} o t (c : bool) (k bail : MX R) s Q ms :
  (c = true -> rimplTX o k s Q ms) -> rimplTX o (xguard t c k bail) s Q ms.
Proof. intros H. unfold xguard. destruct c; [apply H; reflexivity| apply rimplTX_undef]. Qed.

Lemma rimplTX_xbad {R} o (bail : MX R) s Q ms : rimplTX o (xbad_answer bail) s Q ms.
Proof. unfold xbad_answer. apply rimplTX_undef. Qed.

Lemma rimplTX_if {R} o (c : bool) (t1 t2 : MX R) s Q ms :
  (c = true -> rimplTX o t1 s Q ms) -> (c = false -> rimplTX o t2 s Q ms) -> rimplTX o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.

Lemma rimplTX_mono {R} o (t : MX R) s Q Q' ms :
  rimplTX o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> rimplTX o t s Q' ms.
Proof. intros H HQ. unfold rimplTX in *. eapply implM_mono; [exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.

Lemma rimplTX_evt {R} o (t : MX R) s Q P ms :
  evt usegs P ms -> (forall ms', P ms' -> rimplTX o t s Q ms') -> rimplTX o t s Q ms.
Proof. intros H K. unfold rimplTX in *. eapply implM_evt; eauto. Qed.

Lemma rimplTX_from_evt {R} o (t : MX R) s Q ms :
  evt usegs (fun ms' => rimplTX o t s Q ms') ms -> rimplTX o t s Q ms.
Proof. intros H. eapply rimplTX_evt; [exact H|]. intros ms' H'; exact H'. Qed.
End RC__1.
Ltac riprefixTX := apply rimplTX_from_evt.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rimplTX_vis {R} o e (k : Z -> MX R) s Q1 Q ms :
  match e with XE (EPeek _ _ _) => False | XE (EUndef _) => False | _ => True end ->
  implM usegs (xev_step e) s Q1 ms ->
  (forall z s' ms', Q1 z s' ms' -> rimplTX o (k z) s' Q ms') ->
  rimplTX o (SVis e k) s Q ms.
Proof.
  intros He H K. unfold rimplTX. rewrite xmrun_vis by (destruct e as [e'|]; [destruct e'|]; auto). cbn [xmembed].
  eapply implM_bind; [exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.

(* [comment removed for export] *)
Lemma rimplTX_bind {R S} o (t : MX R) (f : R -> MX S) s Q1 Q ms :
  rimplTX o t s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> rimplTX o (f r) s' Q ms') ->
  rimplTX o (sbind t f) s Q ms.
Proof.
  unfold rimplTX, xmrun, xprun. revert s ms. induction t as [r|e k IH]; intros s ms H K.
  - cbn [sbind]. cbn [eruns xmembed] in H. unfold implM, mret in H. cbn in H.
    eapply implM_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
  - cbn [sbind eruns]. cbn [eruns] in H. destruct (xpsel pans_mem o e) as [a|] eqn:E.
    + replace (xpupd pupd_mem o e a) with o in * by (destruct e as [e'|]; reflexivity). eapply IH; [exact H|exact K].
    + cbn [xmembed]. cbn [xmembed] in H. unfold implM, mbind, ebind in H |- *.
      eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
      * exact H1.
      * replace (xpupd pupd_mem o e z) with o in * by (destruct e as [e'|]; reflexivity). eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rimplTX_mremap {R} o addr ol nl fl (k : Z -> MX R) s (P : mremap_ans -> machine_state -> Prop) Q ms :
  impl usegs (at_node usegs) (enode (NMremap addr ol nl fl) (dec_mremap addr ol nl [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplTX o (k (mremap_val addr a)) s Q ms') ->
  rimplTX o (SVis (XMremap addr ol nl fl) k) s Q ms.
Proof.
  intros H K. eapply (rimplTX_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mremap_val addr a /\ P a ms')); [exact I| |].
  - cbn [xev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rimplM_xmembed_xlift {R} (u : Malloc.M (mem * R)) : forall s Q ms,
  implM usegs (membed u) s Q ms -> implM usegs (xmembed (xlift u)) s Q ms.
Proof.
  induction u as [r|e k IH]; intros s Q ms H.
  - cbn [xlift xmembed membed] in *. exact H.
  - cbn [xlift xmembed membed xev_step] in *. unfold implM, mbind, ebind in H |- *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *; [exact H1|].
    apply IH. exact H1.
Qed.

(* [comment removed for export] *)
Lemma rxmembed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : MX R1) (t2 : MX R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
  implM usegs (xmembed t1) s Q1 ms ->
  (forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM usegs (xmembed t2) s Q2 ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
  - cbn [xmembed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1. eapply HQ; eauto.
  - cbn [xmembed] in *. unfold implM, mbind in *. unfold ebind in *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1| exact HQ].
Qed.

Lemma rimplM_xmembed_steq {R} (t1 t2 : MX R) s Q ms :
  steq t1 t2 -> implM usegs (xmembed t1) s Q ms -> implM usegs (xmembed t2) s Q ms.
Proof.
  intros Hs H. apply strel_eq_steq in Hs. eapply (rxmembed_strel eq t1 t2 Hs); [exact H|]. intros; subst; auto.
Qed.

Lemma rimplTX_xlift {R} o (t : Malloc.M R) s Q ms :
  rimplT o t s Q ms -> rimplTX o (xlift t) s Q ms.
Proof.
  intros H. unfold rimplTX, rimplT in *.
  eapply rimplM_xmembed_steq; [apply steq_sym; apply xmrun_xlift|].
  apply rimplM_xmembed_xlift. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint nopeek {R} (t : Malloc.M R) : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) _ => False
  | SVis (EUndef _) _ => True
  | SVis _ k => forall z, nopeek (k z)
  end.

Lemma rimplT_oracle {R} (t : Malloc.M R) : forall o o' s Q ms,
  nopeek t -> rimplT o t s Q ms -> rimplT o' t s Q ms.
Proof.
  induction t as [r|e k IH]; intros o o' s Q ms NP H.
  - unfold rimplT in *. rewrite mrun_ret in *. cbn [membed] in *. unfold implM, mret in *. cbn in *. exact H.
  - destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ destruct NP. }
    5:{ apply rimplT_undef. }
    all: cbn [nopeek] in NP; unfold rimplT in H |- *; rewrite mrun_vis in H |- * by exact I; cbn [membed] in H |- *;
         unfold implM, mbind, ebind in H |- *;
         eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         pose proof (IH z o o' s' Q ms' (NP z)) as IH1; unfold rimplT, implM in IH1; apply IH1; exact H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma xleaf_of_ret {R} o (r : R) : xleaf_of o (SRet r : MX R) r.
Proof. exists [], o. reflexivity. Qed.

Lemma xleaf_of_vis {R} o (e : xev) (k : Z -> MX R) z r :
  match e with XE (EPeek _ _ _) => False | XE (EUndef _) => False | _ => True end ->
  xleaf_of o (k z) r -> xleaf_of o (SVis e k) r.
Proof.
  intros He (ans & o' & H). exists (z :: ans), o'. rewrite xmrun_vis by (destruct e as [e'|]; [destruct e'|]; auto).
  cbn [xfollow]. destruct e as [e'|]; [destruct e'|]; try exact H; destruct He.
Qed.

Lemma xleaf_of_peek {R} o p c h (k : Z -> MX R) r :
  xleaf_of o (k (pans_mem o p c h)) r -> xleaf_of o (SVis (XE (EPeek p c h)) k) r.
Proof. intros (ans & o' & H). exists ans, o'. rewrite xmrun_peek. exact H. Qed.

Lemma rimplTX_reach {R} o (t : MX R) : forall s Q ms,
  rimplTX o t s Q ms -> rimplTX o t s (fun r s' ms' => Q r s' ms' /\ xleaf_of o t r) ms.
Proof.
  induction t as [r|e k IH]; intros s Q ms H.
  - unfold rimplTX, implM in *. rewrite xmrun_ret in *. cbn [xmembed] in *. unfold mret in *. cbn in *.
    eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| apply xleaf_of_ret].
  - assert (CASE : e = match e with XE (EPeek p c h) => XE (EPeek p c h) | XE (EUndef w) => XE (EUndef w) | _ => e end)
      by (destruct e as [e'|]; [destruct e'|]; reflexivity).
    destruct e as [e'|addr ol nl fl]; [destruct e' as [addr|addr len prot flags|addr len|addr len prot|p c h|w]|]; clear CASE.
    5:{ apply rimplTX_peek. eapply rimplTX_mono; [apply IH; unfold rimplTX in H |- *; rewrite xmrun_peek in H; exact H|].
        cbn. intros r s' ms' [HQ HL]. split; [exact HQ|]. apply xleaf_of_peek. exact HL. }
    5:{ apply rimplTX_undef. }
    all: unfold rimplTX in H |- *; rewrite xmrun_vis in H |- * by exact I; cbn [xmembed] in H |- *;
         unfold implM, mbind, ebind in H |- *;
         eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         pose proof (IH z s' Q ms') as IH1; unfold rimplTX, implM in IH1;
         eapply impl_epost_mono; [apply IH1; exact H1|];
         intros [[o1 r] s2] ms2; cbn; intros [HQ HL]; split; [exact HQ| apply (xleaf_of_vis o _ k z); [exact I| exact HL]].
Qed.

(* [comment removed for export] *)
Lemma xleaf_of_xlift {R} o (t : Malloc.M R) r : xleaf_of o (xlift t) r -> leaf_of o t r.
Proof.
  intros (ans & o' & H). exists ans, o'.
  rewrite (xfollow_steq _ _ ans (xmrun_xlift o t)) in H. rewrite xfollow_xlift in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma rimplTX_silent {R} o (t : MX R) o' (x : R) s Q ms :
  xmrun o t = SRet (o', x) -> rimplTX o t s Q ms -> evt usegs (Q x s) ms.
Proof. intros E H. unfold rimplTX in H. rewrite E in H. cbn [xmembed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.
End RC__2.
