(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Export X0qn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Export X1m2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition rimplT {RCEIL : RunCeiling} {R} (o : mem) (t : X1qu.M R) (s : PState)
(Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
implM rsegs (membed alloc_ceiling (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

Lemma rimplT_ret {RCEIL : RunCeiling} {R} o (r : R) s Q ms : evt rsegs (Q r s) ms -> rimplT o (SRet r) s Q ms.
Proof. intros H. unfold rimplT. rewrite mrun_ret. cbn [membed]. apply implM_ret. exact H. Qed.

Lemma rimplT_peek {RCEIL : RunCeiling} {R} o p c h (k : Z -> X1qu.M R) s Q ms :
rimplT o (k (pans_mem o p c h)) s Q ms -> rimplT o (SVis (EPeek p c h) k) s Q ms.
Proof. intros H. unfold rimplT. rewrite mrun_peek. exact H. Qed.

Lemma rimplT_undef {RCEIL : RunCeiling} {R} o w (k : Z -> X1qu.M R) s Q ms : rimplT o (SVis (EUndef w) k) s Q ms.
Proof.
unfold rimplT. rewrite mrun_vis by exact I. cbn [membed ev_step].
eapply (implM_bind rsegs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

Lemma rimplT_vis {RCEIL : RunCeiling} {R} o e (k : Z -> X1qu.M R) s Q1 Q ms :
match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
implM rsegs (ev_step alloc_ceiling e) s Q1 ms ->
(forall z s' ms', Q1 z s' ms' -> rimplT o (k z) s' Q ms') ->
rimplT o (SVis e k) s Q ms.
Proof.
intros He H K. unfold rimplT. rewrite mrun_vis by (destruct e; auto). cbn [membed].
eapply implM_bind; [exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.

Lemma rimplT_mono {RCEIL : RunCeiling} {R} o (t : X1qu.M R) s Q Q' ms :
rimplT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> rimplT o t s Q' ms.
Proof. intros H HQ. unfold rimplT in *. eapply implM_mono; [exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.

Lemma rimplT_evt {RCEIL : RunCeiling} {R} o (t : X1qu.M R) s Q P ms :
evt rsegs P ms -> (forall ms', P ms' -> rimplT o t s Q ms') -> rimplT o t s Q ms.
Proof. intros H K. unfold rimplT in *. eapply implM_evt; eauto. Qed.

Lemma rimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
impl rsegs (at_node rsegs) (Vis n k) Q ms = evt rsegs (fun ms1 => at_node rsegs n ms1 /\ forall rsp, impl rsegs (at_node rsegs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. reflexivity. Qed.

Lemma rimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
impl rsegs (at_node rsegs) (X1bs.bind _ t f1) Q1 ms ->
(forall r ms', impl rsegs (at_node rsegs) (f1 r) Q1 ms' -> impl rsegs (at_node rsegs) (f2 r) Q2 ms') ->
impl rsegs (at_node rsegs) (X1bs.bind _ t f2) Q2 ms.
Proof.
revert ms. induction t as [r|n k IH]; intros ms H K; cbn [X1bs.bind] in *.
- apply K. exact H.
- rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma rmembed_strel {RCEIL : RunCeiling} {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : X1qu.M R1) (t2 : X1qu.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
implM rsegs (membed alloc_ceiling t1) s Q1 ms ->
(forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM rsegs (membed alloc_ceiling t2) s Q2 ms.
Proof.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1. eapply HQ; eauto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ exact H1.
+ eapply IH; [exact H1| exact HQ].
Qed.

Lemma rimplT_strel {RCEIL : RunCeiling} {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : X1qu.M R1) (t2 : X1qu.M R2) s Q1 Q2 ms :
strel RR (mrun o t1) t2 ->
rimplT o t1 s Q1 ms ->
(forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM rsegs (membed alloc_ceiling t2) s Q2 ms.
Proof.
intros Hs H HQ. unfold rimplT in H. eapply (rmembed_strel _ _ _ Hs); [exact H|]. intros [o1 r1] r2 s' ms'; cbn; eauto.
Qed.

Lemma rimplM_membed_steq {RCEIL : RunCeiling} {R} (t1 t2 : X1qu.M R) s Q ms :
steq t1 t2 -> implM rsegs (membed alloc_ceiling t1) s Q ms -> implM rsegs (membed alloc_ceiling t2) s Q ms.
Proof.
intros Hs H. apply strel_eq_steq in Hs. eapply (rmembed_strel eq t1 t2 Hs); [exact H|]. intros; subst; auto.
Qed.

Lemma rimplM_membed_sbind {RCEIL : RunCeiling} {R S} (T : X1qu.M R) (F : R -> X1qu.M S) s Q1 Q ms :
implM rsegs (membed alloc_ceiling T) s Q1 ms ->
(forall x s' ms', Q1 x s' ms' -> implM rsegs (membed alloc_ceiling (F x)) s' Q ms') ->
implM rsegs (membed alloc_ceiling (sbind T F)) s Q ms.
Proof.
revert s ms. induction T as [x|e k IH]; intros s ms H K.
- cbn [sbind membed] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [exact H|]. intros ms' H1. exact (K x s ms' H1).
- cbn [sbind membed] in *. unfold implM, mbind, ebind in *.
eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ exact H1.
+ eapply IH; [exact H1|exact K].
Qed.

Lemma rimplT_bind {RCEIL : RunCeiling} {R S} o (t : X1qu.M R) (f : R -> X1qu.M S) s Q1 Q ms :
rimplT o t s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> rimplT o (f r) s' Q ms') ->
rimplT o (sbind t f) s Q ms.
Proof.
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

Lemma rimplT_from_evt {RCEIL : RunCeiling} {R} o (t : X1qu.M R) s Q ms :
evt rsegs (fun ms' => rimplT o t s Q ms') ms -> rimplT o t s Q ms.
Proof. intros H. eapply rimplT_evt; [exact H|]. intros ms' H'; exact H'. Qed.
Ltac riprefixT := apply rimplT_from_evt.

Lemma rimplM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
(s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
(forall a ms', P a ms' -> evt rsegs (Q (f a) s) ms') ->
implM rsegs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof.
intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
cbn [X1bs.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec rsp) as [a|]; cbn in *.
- eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
- exact Hk.
Qed.

Lemma rimplT_mmap_rw {RCEIL : RunCeiling} {R} o len (k : Z -> X1qu.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMmap 0 len 3 34) (dec_mmap alloc_ceiling len [])) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
rimplT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' sfH_; first [ sf_destruct 4%nat sfH_ as -> a -> HP | sf_fb; destruct sfH_ as (-> & a & -> & HP) ]. exact (K a ms' HP).
Qed.

Lemma rimplT_mmap_none {RCEIL : RunCeiling} {R} o len (k : Z -> X1qu.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMmap 0 len 0 34) (dec_mmap_none alloc_ceiling len [])) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
rimplT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' sfH_; first [ sf_destruct 4%nat sfH_ as -> a -> HP | sf_fb; destruct sfH_ as (-> & a & -> & HP) ]. exact (K a ms' HP).
Qed.

Lemma rimplT_mmap_fixed {RCEIL : RunCeiling} {R} o addr len (k : Z -> X1qu.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (fixed_val addr a)) s Q ms') ->
rimplT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' sfH_; first [ sf_destruct 4%nat sfH_ as -> a -> HP | sf_fb; destruct sfH_ as (-> & a & -> & HP) ]. exact (K a ms' HP).
Qed.

Lemma rimplT_munmap {RCEIL : RunCeiling} {R} o addr len (k : Z -> X1qu.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
rimplT o (SVis (EMunmap addr len) k) s Q ms.
Proof.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
- cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' sfH_; first [ sf_destruct 4%nat sfH_ as -> a -> HP | sf_fb; destruct sfH_ as (-> & a & -> & HP) ]. exact (K a ms' HP).
Qed.

Lemma rimplT_mprotect {RCEIL : RunCeiling} {R} o addr len prot (k : Z -> X1qu.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
rimplT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
- cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' sfH_; first [ sf_destruct 4%nat sfH_ as -> a -> HP | sf_fb; destruct sfH_ as (-> & a & -> & HP) ]. exact (K a ms' HP).
Qed.

Lemma rimplT_brk0 {RCEIL : RunCeiling} {R} o (k : Z -> X1qu.M R) s (P : Z -> machine_state -> Prop) Q ms :
impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
(forall r ms', P r ms' -> rimplT o (k r) (set_brk_ps r s) Q ms') ->
rimplT o (SVis (EBrk 0) k) s Q ms.
Proof.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
- cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
cbn [X1bs.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec_brk0 rsp) as [a|]; cbn in *; [|exact Hk].
eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
- intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.

Lemma rimplT_brk {RCEIL : RunCeiling} {R} o req (k : Z -> X1qu.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
req <> 0 ->
impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
(forall a ms', P a ms' ->
rimplT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
(match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
rimplT o (SVis (EBrk req) k) s Q ms.
Proof.
intros Hr H K.
eapply (rimplT_vis o _ k s (fun z s' ms' => exists a, P a ms' /\
z = match a with BrkGrown => req | BrkSame => ps_brk s end /\
s' = match a with BrkGrown => set_brk_ps req s | BrkSame => s end)); [exact I| |].
- cbn [ev_step]. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
unfold implM, mbind, msys, mget, mupd, mret, ebind, enode in *.
cbn [X1bs.bind fst snd]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|exact Hk].
destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
- intros z s' ms' sfH_; first [ sf_destruct 4%nat sfH_ as a HP -> -> | sf_fb; destruct sfH_ as (a & HP & -> & ->) ]. exact (K a ms' HP).
Qed.

Lemma rimplT_reach {RCEIL : RunCeiling} {R} o (t : X1qu.M R) : forall s Q ms,
rimplT o t s Q ms -> rimplT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof.
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

Definition rauxv_list (x3 x4 x5 x16 x6 x11 x12 x23 rnd : Z) : list word :=
map wz [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Lemma rauxv_list_length x3 x4 x5 x16 x6 x11 x12 x23 rnd :
length (u64s (rauxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd)) = 160%nat.
Proof. unfold rauxv_list. rewrite u64s_length, map_length. reflexivity. Qed.

Definition rauxv_ok {RCEIL : RunCeiling} (m : mem) (B : Z) : Prop :=
exists av x3 x4 x5 x16 x6 x11 x12 x23 rnd,
rw_cells rsegs m RAUXV_CELL [C8 (wz av)]
/\ bytes_at rsegs m av (u64s (rauxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd))
/\ bytes_at rsegs m (rnd + 8) (le8 run_secret)
/\ alloc_ceiling <= B /\ B <= av /\ av + 160 <= 2^64 /\ B <= rnd + 8 /\ rnd + 16 <= 2^64
/\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= x16 < 2^64 /\ 0 <= x6 < 2^64
/\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64.

Lemma rauxv_ok_weaken {RCEIL : RunCeiling} : forall m B B', rauxv_ok m B -> alloc_ceiling <= B' <= B -> rauxv_ok m B'.
Proof.
intros m B B' sfH_; first [ sf_destruct 11%nat sfH_ as av x3 x4 x5 x16 x6 x11 x12 x23 rnd H | sf_fb; destruct sfH_ as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & H) ]; intros HB.
first [ unshelve sf_eexists 10%nat; [ exact (av) | exact (x3) | exact (x4) | exact (x5) | exact (x16) | exact (x6) | exact (x11) | exact (x12) | exact (x23) | exact (rnd) | ] | sf_fb; exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd ]. repeat (split; [tauto|]). lia.
Qed.

Lemma rauxv_ok_frame {RCEIL : RunCeiling} : forall m m' B W,
rauxv_ok m B -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) W ->
rauxv_ok m' B.
Proof.
intros m m' B W sfH_; first [ sf_destruct 14%nat sfH_ as av x3 x4 x5 x16 x6 x11 x12 x23 rnd C A1 A2 H | sf_fb; destruct sfH_ as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H) ]; intros MU WM FW.
first [ unshelve sf_eexists 10%nat; [ exact (av) | exact (x3) | exact (x4) | exact (x5) | exact (x16) | exact (x6) | exact (x11) | exact (x12) | exact (x23) | exact (rnd) | ] | sf_fb; exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd ]. split; [|split; [|split; [|exact H]]].
- eapply rw_cells_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [_ ?]. lia.
- eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
- eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
Qed.

Lemma rraw_free_bridge {RCEIL : RunCeiling} : forall st s (p : bptr) (pf : aptr) (o : mem) Q1 Q ms,
strip st = ps_m s ->
s_ceil (ps_m s) = alloc_ceiling ->
hdr_ok pans_mem pupd_mem st pf (fst p) ->
rimplT o (free st (Some pf)) s Q1 ms ->
(forall st' s' ms', Q1 st' s' ms' -> Q tt (set_m (strip st') s') ms') ->
implM rsegs (raw_free p) s Q ms.
Proof.
intros st s p pf o Q1 Q ms Hst Hceil Hh H HQ. unfold raw_free.
eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta. rewrite Hceil.
eapply (implM_bind rsegs _ _ _ (fun cs s' ms' => exists st', Q1 st' s' ms' /\ strip st' = cs)).
{ rewrite <- Hst. eapply (rimplT_strel FREL o (free st (Some pf)) (cfree (strip st) (Some (fst p))) s Q1).
- unfold mrun. apply free_control. exact Hh.
- exact H.
- intros o1 st' cs s' ms' HR H1. exists st'. split; [exact H1|]. unfold FREL in HR. exact HR. }
intros cs s' ms' (st' & H1 & <-). cbv beta.
apply implM_upd. apply evt_done. eapply HQ. exact H1.
Qed.

Definition rpres_except (C : Z -> Prop) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> ~ C a ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma rpres_except_refl C m : rpres_except C m m.
Proof. intros a _ _; auto. Qed.
Lemma rpres_except_trans C m1 m2 m3 : rpres_except C m1 m2 -> rpres_except C m2 m3 -> rpres_except C m1 m3.
Proof. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma rpres_except_mono (C C' : Z -> Prop) m m' : rpres_except C m m' -> (forall a, C a -> C' a) -> rpres_except C' m m'.
Proof. intros H HC a Ha Hc. apply H; [exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.

Lemma rpres_except_of_munch C W m m' :
munch W m m' -> wmono rsegs m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
intros MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.

Lemma rpres_except_bytes_at C m m' A bs :
rpres_except C m m' -> bytes_at rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) ->
bytes_at rsegs m' A bs.
Proof.
intros HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma rpres_except_wr_at C m m' A n :
rpres_except C m m' -> wr_at rsegs m A n -> (forall a, A <= a < A + n -> ~ C a) -> wr_at rsegs m' A n.
Proof.
intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

Lemma rpres_except_rw_cells C m m' A cs :
rpres_except C m m' -> rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) ->
rw_cells rsegs m' A cs.
Proof.
intros HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply rpres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply rpres_except_wr_at; eauto.
Qed.

Lemma rpres_except_stk C m m' lo hi :
rpres_except C m m' -> stk rsegs m lo hi -> (forall a, lo <= a < hi -> ~ C a) -> stk rsegs m' lo hi.
Proof.
intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Definition ralloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ errno_addr (Z_to_bv 64 0x4d450) <= a < errno_addr (Z_to_bv 64 0x4d450) + 4
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Definition RAM_STACK : Z := 144.

Lemma rfresh_image {RCEIL : RunCeiling} st a : fresh_addr st a -> s_reserved st = ref_reserved -> a < 0x10000 \/ 0x6e000 <= a.
Proof.
intros [_ FR] RS. unfold live_ranges in FR. rewrite RS in FR.
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). lia.
Qed.

Definition ram_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
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

Definition ralloc_meta_stmt {RCEIL : RunCeiling} (am_pre : mstate -> Prop) : Prop :=
forall (R : Type) (k : mstate -> optr -> X1qu.M R) (bail : X1qu.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
am_pre st -> s_ceil st = alloc_ceiling   ->
rmrep st m -> ticks_ok st -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 0x4d450 ->
(forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms') ->
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs)).
