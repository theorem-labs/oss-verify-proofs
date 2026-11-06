(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall7vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Monad MProg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg.MallocRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Monad OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module PortMisc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg MRep MRepAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac unmask64 K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia);
  try rewrite !Z.mod_small in K by lia.

(* [comment removed for export] *)
Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.

End PortMisc.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem := word -> option byte.

Definition pans_mem (o : mem) (q : aptr) (caddr hint : Z) : Z :=
  match mrd rsegs o (wa caddr) with Some b => bv_unsigned b | None => 0 end.
Definition pupd_mem (o : mem) (e : ev) (z : Z) : mem := o.

Lemma pans_mem_range : forall o q c h, 0 <= pans_mem o q c h < 256.
Proof.
  intros. unfold pans_mem. destruct (mrd rsegs o (wa c)) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.

Lemma mrun_ret {R} o (r : R) : mrun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
Lemma mrun_peek {R} o p c h (k : Z -> Malloc.M R) : mrun o (SVis (EPeek p c h) k) = mrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.
Lemma mrun_vis {R} o e (k : Z -> Malloc.M R) :
  match e with EPeek _ _ _ => False | _ => True end ->
  mrun o (SVis e k) = SVis e (fun z => mrun o (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition implT {R} (o : mem) (t : Malloc.M R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM rsegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

Lemma implT_ret {R} o (r : R) s Q ms : evt rsegs (Q r s) ms -> implT o (SRet r) s Q ms.
Proof. intros H. unfold implT. rewrite mrun_ret. cbn [membed]. apply implM_ret. exact H. Qed.

Lemma implT_peek {R} o p c h (k : Z -> Malloc.M R) s Q ms :
  implT o (k (pans_mem o p c h)) s Q ms -> implT o (SVis (EPeek p c h) k) s Q ms.
Proof. intros H. unfold implT. rewrite mrun_peek. exact H. Qed.

Lemma implT_undef {R} o w (k : Z -> Malloc.M R) s Q ms : implT o (SVis (EUndef w) k) s Q ms.
Proof.
  unfold implT. rewrite mrun_vis by exact I. cbn [membed ev_step].
  eapply (implM_bind rsegs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

(* [comment removed for export] *)
Lemma implT_vis {R} o e (k : Z -> Malloc.M R) s Q1 Q ms :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  implM rsegs (ev_step e) s Q1 ms ->
  (forall z s' ms', Q1 z s' ms' -> implT o (k z) s' Q ms') ->
  implT o (SVis e k) s Q ms.
Proof.
  intros He H K. unfold implT. rewrite mrun_vis by (destruct e; auto). cbn [membed].
  eapply implM_bind; [exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.

Lemma implT_mono {R} o (t : Malloc.M R) s Q Q' ms :
  implT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> implT o t s Q' ms.
Proof. intros H HQ. unfold implT in *. eapply implM_mono; [exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.

Lemma implT_evt {R} o (t : Malloc.M R) s Q P ms :
  evt rsegs P ms -> (forall ms', P ms' -> implT o t s Q ms') -> implT o t s Q ms.
Proof. intros H K. unfold implT in *. eapply implM_evt; eauto. Qed.

(* [comment removed for export] *)
Lemma impl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
  impl rsegs (at_node rsegs) (Vis n k) Q ms = evt rsegs (fun ms1 => at_node rsegs n ms1 /\ forall rsp, impl rsegs (at_node rsegs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. reflexivity. Qed.

Lemma impl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
  impl rsegs (at_node rsegs) (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.bind _ t f1) Q1 ms ->
  (forall r ms', impl rsegs (at_node rsegs) (f1 r) Q1 ms' -> impl rsegs (at_node rsegs) (f2 r) Q2 ms') ->
  impl rsegs (at_node rsegs) (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.bind _ t f2) Q2 ms.
Proof.
  revert ms. induction t as [r|n k IH]; intros ms H K; cbn [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.bind] in *.
  - apply K. exact H.
  - rewrite impl_vis_unfold in H. rewrite impl_vis_unfold. eapply evt_mono; [exact H|].
    intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma membed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
  implM rsegs (membed t1) s Q1 ms ->
  (forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1. eapply HQ; eauto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1| exact HQ].
Qed.

Lemma implT_strel {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : Malloc.M R1) (t2 : Malloc.M R2) s Q1 Q2 ms :
  strel RR (mrun o t1) t2 ->
  implT o t1 s Q1 ms ->
  (forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof.
  intros Hs H HQ. unfold implT in H. eapply (membed_strel _ _ _ Hs); [exact H|]. intros [o1 r1] r2 s' ms'; cbn; eauto.
Qed.

(* [comment removed for export] *)
Lemma implM_membed_steq {R} (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> implM rsegs (membed t1) s Q ms -> implM rsegs (membed t2) s Q ms.
Proof.
  intros Hs H. apply strel_eq_steq in Hs. eapply (membed_strel eq t1 t2 Hs); [exact H|]. intros; subst; auto.
Qed.

Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.

Lemma implM_membed_sbind {R S} (T : Malloc.M R) (F : R -> Malloc.M S) s Q1 Q ms :
  implM rsegs (membed T) s Q1 ms ->
  (forall x s' ms', Q1 x s' ms' -> implM rsegs (membed (F x)) s' Q ms') ->
  implM rsegs (membed (sbind T F)) s Q ms.
Proof.
  revert s ms. induction T as [x|e k IH]; intros s ms H K.
  - cbn [sbind membed] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [exact H|]. intros ms' H1. exact (K x s ms' H1).
  - cbn [sbind membed] in *. unfold implM, mbind, ebind in *.
    eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
Lemma implT_bind {R S} o (t : Malloc.M R) (f : R -> Malloc.M S) s Q1 Q ms :
  implT o t s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implT o (f r) s' Q ms') ->
  implT o (sbind t f) s Q ms.
Proof.
  unfold implT, mrun, prun. revert s ms. induction t as [r|e k IH]; intros s ms H K.
  - cbn [sbind]. cbn [eruns membed] in H. unfold implM, mret in H. cbn in H.
    eapply implM_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
  - cbn [sbind eruns]. cbn [eruns] in H. unfold pupd_mem in *. destruct (psel pans_mem o e) as [a|].
    + eapply IH; [exact H|exact K].
    + cbn [membed]. cbn [membed] in H. unfold implM, mbind, ebind in H |- *.
      eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
      * exact H1.
      * eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
Lemma implT_from_evt {R} o (t : Malloc.M R) s Q ms :
  evt rsegs (fun ms' => implT o t s Q ms') ms -> implT o t s Q ms.
Proof. intros H. eapply implT_evt; [exact H|]. intros ms' H'; exact H'. Qed.

End CEIL.
Ltac iprefixT := apply implT_from_evt.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma implM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
      (s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
  (forall a ms', P a ms' -> evt rsegs (Q (f a) s) ms') ->
  implM rsegs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof.
  intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
  cbn [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.bind]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec rsp) as [a|]; cbn in *.
  - eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
  - exact Hk.
Qed.

Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
  match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.

Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma implT_mmap_rw {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (mmap_val a)) s Q ms') ->
  implT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms'; (first [ intro dR_2; dand4 dR_2 as -> a -> HP | intros (-> & a & -> & HP) ])). exact (K a ms' HP).
Qed.

Lemma implT_mmap_none {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (mmap_val a)) s Q ms') ->
  implT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms'; (first [ intro dR_3; dand4 dR_3 as -> a -> HP | intros (-> & a & -> & HP) ])). exact (K a ms' HP).
Qed.

Lemma implT_mmap_fixed {R} o addr len (k : Z -> Malloc.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (fixed_val addr a)) s Q ms') ->
  implT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms'; (first [ intro dR_4; dand4 dR_4 as -> a -> HP | intros (-> & a & -> & HP) ])). exact (K a ms' HP).
Qed.

Lemma implT_munmap {R} o addr len (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (range_val a)) s Q ms') ->
  implT o (SVis (EMunmap addr len) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms'; (first [ intro dR_5; dand4 dR_5 as -> a -> HP | intros (-> & a & -> & HP) ])). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
Lemma implT_mprotect {R} o addr len prot (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> implT o (k (range_val a)) s Q ms') ->
  implT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms'; (first [ intro dR_6; dand4 dR_6 as -> a -> HP | intros (-> & a & -> & HP) ])). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
Lemma implT_brk0 {R} o (k : Z -> Malloc.M R) s (P : Z -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
  (forall r ms', P r ms' -> implT o (k r) (set_brk_ps r s) Q ms') ->
  implT o (SVis (EBrk 0) k) s Q ms.
Proof.
  intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
  - cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
    cbn [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.bind]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk0 rsp) as [a|]; cbn in *; [|exact Hk].
    eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
  - intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.

(* [comment removed for export] *)
Lemma implT_brk {R} o req (k : Z -> Malloc.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
  req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
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
    cbn [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.bind fst snd]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|exact Hk].
    destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
  - (intros z s' ms'; (first [ intro dR_7; dex1 dR_7 as a; dand3 dR_7 as HP -> -> | intro dR_7; dand4 dR_7 as a HP -> -> | intros (a & HP & -> & ->) ])). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
  exists ans o', follow (mrun o t) ans = Some (o', r).

Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. exists [], o. reflexivity. Qed.

Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
  (intros He; (first [ intro dR_8; dex2 dR_8 as ans o'; rename dR_8 into H | intro dR_8; dand3 dR_8 as ans o' H | intros (ans & o' & H) ])). exists (z :: ans), o'. unfold mrun, prun. cbn [eruns].
  destruct e; cbn [psel]; try exact H; destruct He.
Qed.

Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) r :
  leaf_of o (k (pans_mem o p c h)) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. ((first [ intro dR_9; dex2 dR_9 as ans o'; rename dR_9 into H | intro dR_9; dand3 dR_9 as ans o' H | intros (ans & o' & H) ])). exists ans, o'. rewrite mrun_peek. exact H. Qed.

Lemma implT_reach {R} o (t : Malloc.M R) : forall s Q ms,
  implT o t s Q ms -> implT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof.
  induction t as [r|e k IH]; intros s Q ms H.
  - unfold implT, implM in *. rewrite mrun_ret in *. cbn [membed] in *. unfold mret in *. cbn in *.
    eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| apply leaf_of_ret].
  - destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ apply implT_peek. eapply implT_mono; [apply IH; unfold implT in H |- *; rewrite mrun_peek in H; exact H|].
        cbn. intros r s' ms' [HQ HL]. split; [exact HQ|]. apply leaf_of_peek. exact HL. }
    5:{ apply implT_undef. }
    all: unfold implT in H |- *; rewrite mrun_vis in H |- * by exact I; cbn [membed] in H |- *;
         unfold implM, mbind, ebind in H |- *;
         eapply impl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         pose proof (IH z s' Q ms') as IH1; unfold implT, implM in IH1;
         eapply impl_epost_mono; [apply IH1; exact H1|];
         intros [[o1 r] s2] ms2; cbn; intros [HQ HL]; split; [exact HQ| apply (leaf_of_vis o _ k z); [exact I| exact HL]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ptr_rel (p : optr) (r : option bptr) : Prop :=
  match p, r with
  | None, None => True
  | Some pf, Some b => fst pf = fst (fst b) /\ exists off, snd pf = snd (fst b) + UNIT * off
  | _, _ => False
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition auxv_list (x3 x4 x5 hw x6 x11 x12 x23 rnd : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 16; hw; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].
(* [comment removed for export] *)

Definition auxv_ok (m : mem) (B : Z) : Prop :=
  exists av x3 x4 x5 hw x6 x11 x12 x23 rnd,
    rw_cells rsegs m AUXV_CELL [C8 (wz av)]
    /\ bytes_at rsegs m av (u64s (auxv_list x3 x4 x5 hw x6 x11 x12 x23 rnd))
    /\ bytes_at rsegs m (rnd + 8) (le8 (wz run_secret))
    /\ alloc_ceiling <= B /\ B <= av /\ av + 160 <= 2^64 /\ B <= rnd + 8 /\ rnd + 16 <= 2^64
    /\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= hw < 2^64 /\ 0 <= x6 < 2^64
    /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64.

Lemma auxv_ok_weaken : forall m B B', auxv_ok m B -> alloc_ceiling <= B' <= B -> auxv_ok m B'.
Proof.
  (intros m B B'; (first [ intro dR_12; dex10 dR_12 as av x3 x4 x5 hw x6 x11 x12 x23 rnd; rename dR_12 into H | intro dR_12; dand11 dR_12 as av x3 x4 x5 hw x6 x11 x12 x23 rnd H | intros (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & H) ]); intros HB).
  exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. repeat (split; [tauto|]). lia.
Qed.

Lemma Forall_disjoint_from : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

Lemma auxv_ok_frame : forall m m' B W,
  auxv_ok m B -> munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= AUXV_CELL \/ AUXV_CELL + 8 <= fst iv)) W ->
  auxv_ok m' B.
Proof.
  (intros m m' B W; (first [ intro dR_13; dex10 dR_13 as av x3 x4 x5 hw x6 x11 x12 x23 rnd; dand4 dR_13 as C A1 A2 H | intro dR_13; dand14 dR_13 as av x3 x4 x5 hw x6 x11 x12 x23 rnd C A1 A2 H | intros (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H) ]); intros MU WM FW).
  exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rw_cells_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [_ ?]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
Qed.

(* [comment removed for export] *)
Lemma raw_free_bridge : forall st s (p : bptr) (pf : aptr) (o : mem) Q1 Q ms,
  strip st = ps_m s ->
  hdr_ok pans_mem pupd_mem st pf (fst p) ->
  implT o (free st (Some pf)) s Q1 ms ->
  (forall st' s' ms', Q1 st' s' ms' -> Q tt (set_m (strip st') s') ms') ->
  implM rsegs (raw_free p) s Q ms.
Proof.
  intros st s p pf o Q1 Q ms Hst Hh H HQ. unfold raw_free.
  eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. }
  (intros s0 s1 ms1; (first [ intro dR_14; dand3 dR_14 as -> -> -> | intros (-> & -> & ->) ])). cbv beta.
  eapply (implM_bind rsegs _ _ _ (fun cs s' ms' => exists st', Q1 st' s' ms' /\ strip st' = cs)).
  { rewrite <- Hst. eapply (implT_strel FREL o (free st (Some pf)) (cfree (strip st) (Some (fst p))) s Q1).
    - unfold mrun. apply free_control. exact Hh.
    - exact H.
    - intros o1 st' cs s' ms' HR H1. exists st'. split; [exact H1|]. unfold FREL in HR. exact HR. }
  (intros cs s' ms'; (first [ intro dR_15; dex1 dR_15 as st'; destruct dR_15 as [H1 <-] | intro dR_15; dand3 dR_15 as st' H1 <- | intros (st' & H1 & <-) ])). cbv beta.
  apply implM_upd. apply evt_done. eapply HQ. exact H1.
Qed.

(* [comment removed for export] *)
Definition auxv_okd (d : Z) (m : mem) (B : Z) : Prop := alloc_ceiling <= B /\ (d <> 0 \/ auxv_ok m B).

Lemma auxv_okd_of_ok d m B : auxv_ok m B -> auxv_okd d m B.
Proof. intros H. split; [| right; exact H]. (first [ dex10 H as av x3 x4 x5 hw x6 x11 x12 x23 rnd; dand5 H as _ _ _ HB _ | dand15 H as av x3 x4 x5 hw x6 x11 x12 x23 rnd _ _ _ HB _ | destruct H as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HB & _) ]). exact HB. Qed.

Lemma auxv_okd_done d m B : d <> 0 -> alloc_ceiling <= B -> auxv_okd d m B.
Proof. intros Hd HB. split; [exact HB| left; exact Hd]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma auxv_okd_weaken : forall d m B B', auxv_okd d m B -> alloc_ceiling <= B' <= B -> auxv_okd d m B'.
Proof.
  intros d m B B' [HB [Hd|H]] HB'; split; [lia| left; exact Hd| lia| right]. eapply auxv_ok_weaken; eauto.
Qed.

Lemma auxv_okd_frame : forall d m m' B W,
  auxv_okd d m B -> munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= AUXV_CELL \/ AUXV_CELL + 8 <= fst iv)) W ->
  auxv_okd d m' B.
Proof.
  intros d m m' B W [HB [Hd|H]] MU WM FW; split; [exact HB| left; exact Hd| exact HB| right]. eapply auxv_ok_frame; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition brk_link_ps (st : mstate) (s : PState) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => ps_brk s = conc st (rid, off)
  | _ => True
  end.

Definition am_post (d : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (s : PState) (lo : Z) (m : mem)
    (st1 : mstate) (mo : optr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (pw st1 mo) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ auxv_okd d m' (bv_unsigned sp)
    /\ pres_except (fun a => alloc_fp (fun k => k <> RKGroup) st1 lo (bv_unsigned sp) a \/ fresh_addr st a) m m'
    /\ mrep st1 m' /\ ticks_ok st1
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ am_rel st st1 mo.

(* [comment removed for export] *)
Definition alloc_meta_stmt (am_pre : mstate -> Prop) : Prop :=
  forall (d : Z) (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> mrep st m -> ticks_ok st -> brk_link_ps st s ->
  auxv_okd d m (bv_unsigned sp) -> (d <> 0 -> c_init_done (ctx st) <> 0) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AM_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 PTP ->
  (forall st1 mo s' ms',
     am_post d ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     implT o (k st1 mo) s' Q ms') ->
  implT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 alloc_meta_entry) fc None m (seg_rom rsegs)).

End CEIL2.

(* [comment removed for export] *)
(* [comment removed for export] *)
