(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require String ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim USim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UStdio UFmt UDriver UPcapA.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Mem Exec RelSpecMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require HeapDrive.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require EntryCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module UPcapB.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UStdio UFmt UDriver UPcapA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.UNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).
#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition pcore (p : pcapT) :=
  (pc_self p, pc_rfile p, pc_swapped p, pc_version_major p, pc_version_minor p, pc_snapshot p, pc_linktype p, pc_linktype_ext p,
   pc_tstamp_precision p).
Definition pkeep (p p' : pcapT) : Prop := pcore p' = pcore p /\ pc_priv p' = pc_priv p.
(* [comment removed for export] *)
Definition isng (p : pcapT) : bool := match pc_priv p with PrivPcap _ => false | PrivNg _ _ => true end.
(* [comment removed for export] *)
Definition psim (p p' : pcapT) : Prop := pcore p' = pcore p /\ isng p' = isng p.
#[using="Type"] Lemma pkeep_psim p p' : pkeep p p' -> psim p p'.
Proof. intros [A B]. split; [exact A| unfold isng; rewrite B; reflexivity]. Qed.
#[using="Type"] Lemma psim_refl p : psim p p. Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_trans p1 p2 p3 : psim p1 p2 -> psim p2 p3 -> psim p1 p3.
Proof. intros [A1 A2] [B1 B2]. split; congruence. Qed.
#[using="Type"] Lemma psim_set_bufdata dd p : psim p (set_bufdata dd p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_errbuf m p : psim p (set_errbuf m p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_header h p : psim p (set_header h p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_break_loop v p : psim p (set_break_loop v p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_ng p s i s0 i0 : pc_priv p = PrivNg s0 i0 -> psim p (set_ng s i p).
Proof. intros HS. split; [reflexivity| unfold isng; cbn; rewrite HS; reflexivity]. Qed.
#[using="Type"] Lemma psim_ng p p' s i : psim p p' -> pc_priv p = PrivNg s i -> exists s' i', pc_priv p' = PrivNg s' i'.
Proof. intros [_ E] HS. unfold isng in E. rewrite HS in E. destruct (pc_priv p') as [|s' i']; [discriminate|]. exists s', i'; reflexivity. Qed.
#[using="Type"] Lemma psim_sf p p' s : psim p p' -> pc_priv p = PrivPcap s -> exists s', pc_priv p' = PrivPcap s'.
Proof. intros [_ E] HS. unfold isng in E. rewrite HS in E. destruct (pc_priv p') as [s'|]; [| discriminate]. exists s'; reflexivity. Qed.
#[using="Type"] Lemma psim_bufdata_r p q dd : psim p q -> psim p (set_bufdata dd q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_bufdata]. Qed.
#[using="Type"] Lemma psim_errbuf_r p q m : psim p q -> psim p (set_errbuf m q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_errbuf]. Qed.
#[using="Type"] Lemma psim_header_r p q h : psim p q -> psim p (set_header h q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_header]. Qed.
#[using="Type"] Lemma psim_break_r p q v : psim p q -> psim p (set_break_loop v q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_break_loop]. Qed.
(* [comment removed for export] *)
End WithCeil.

Ltac psim_tac :=
  repeat first [ apply psim_refl | assumption | (apply pkeep_psim; assumption)
               | apply psim_bufdata_r | apply psim_errbuf_r | apply psim_header_r | apply psim_break_r
               | match goal with H : psim ?a ?b |- psim ?a ?c => apply (psim_trans _ _ _ H); clear H end
               | match goal with H : pkeep ?a ?b |- psim ?a ?c => apply (psim_trans _ _ _ (pkeep_psim _ _ H)); clear H end ];
  match goal with |- psim _ _ => fail "psim_tac" | |- _ => idtac end.
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma pkeep_refl p : pkeep p p. Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_trans p1 p2 p3 : pkeep p1 p2 -> pkeep p2 p3 -> pkeep p1 p3.
Proof. intros [A1 A2] [B1 B2]. split; congruence. Qed.
#[using="Type"] Lemma pkeep_set_bufdata dd p : pkeep p (set_bufdata dd p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_set_errbuf m p : pkeep p (set_errbuf m p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_set_buffer b sz al dd p : pkeep p (set_buffer b sz al dd p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_set_header h p : pkeep p (set_header h p). Proof. split; reflexivity. Qed.
End WithCeil.

#[export] Hint Resolve pkeep_refl pkeep_set_bufdata pkeep_set_errbuf pkeep_set_buffer pkeep_set_header : pk.

Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
Section ReadingB.
Variable segs : list Segment.
Variables (stkG stkC : stack_site -> Z).
Hypothesis STK : stk_ok stkG.
#[local] Notation npk := (npeek segs).
#[local] Notation usimS := (usim npk).
#[local] Notation RX := (UBase.RX (CEG:=CEG) (CEC:=CEC)).     (* [comment removed for export] *)
#[local] Notation RUK tm nx K C g W := (RX tm nx (UK nx K C g W)).
#[local] Notation PR_G := (prims fopsG fo_nop stkG).
#[local] Notation PR_C := (prims fopsC fo_nop stkC).
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
#[local] Notation B := (rc_B rc).
#[local] Notation Kx := (rc_Kx rc).
#[local] Notation F0 := (rc_F0 rc).
#[local] Notation hs := (rc_hs rc).
#[local] Notation Cc := (rc_C rc).
#[local] Notation oh := (rc_oh rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation KR_ := (KR_ rc).
#[local] Notation FR_ := (FR_ rc).
#[local] Notation PI := (PI rc).

(* [comment removed for export] *)
Definition RPP nx (tm : gmap N Z) (off pos : Z) : @rel PS PS := RUK tm nx (KR_ off) Cc idl (WF oh hs (FR_ off pos)).
Definition PST {A} (Φ : A -> pcapT -> Z -> Prop) : A -> A -> @rel PS PS :=
  eqpost (fun r => fun sG moG sC moC => exists p' tm' nx' off' pos',
            Φ r p' pos' /\ PI p' pos' /\ TML tm' (toks p') /\ RPP nx' tm' off' pos' sG moG sC moC).

#[using="Type"] Lemma pp_ret {A} (Φ : A -> pcapT -> Z -> Prop) nx p tm off pos (r : A) :
  Φ r p pos -> PI p pos -> TML tm (toks p) -> usimS (RPP nx tm off pos) (mret r) (mret r) (PST Φ).
Proof. intros H1 H2 H3. apply ru_ret. intros sG moG sC moC HR. exists p, tm, nx, off, pos. auto. Qed.

#[using="Type"] Lemma pp_bind {A B'} (Φ : A -> pcapT -> Z -> Prop) nx tm off pos (m m' : Monad.M PS A) (k k' : A -> Monad.M PS B') Q :
  usimS (RPP nx tm off pos) m m' (PST Φ) ->
  (forall r p' tm' nx' off' pos', Φ r p' pos' -> PI p' pos' -> TML tm' (toks p') -> usimS (RPP nx' tm' off' pos') (k r) (k' r) Q) ->
  usimS (RPP nx tm off pos) (mbind m k) (mbind m' k') Q.
Proof.
  intros H1 H2. eapply ru_bind; [exact H1|]. intros r.
  apply usim_exI; intros p'. apply usim_exI; intros tm'. apply usim_exI; intros nx'. apply usim_exI; intros off'. apply usim_exI; intros pos'.
  eapply ru_pre; [| intros ? ? ? ? (X1 & X2 & X3 & X4); exact (conj X1 (conj X2 (conj X3 X4)))].
  apply usim_pure; intros X1. apply usim_pure; intros X2. apply usim_pure; intros X3. exact (H2 _ _ _ _ _ _ X1 X2 X3).
Qed.

#[using="Type"] Lemma pp_post {A} (Φ Φ' : A -> pcapT -> Z -> Prop) R (m m' : Monad.M PS A) :
  usimS R m m' (PST Φ) -> (forall r p pos, Φ r p pos -> PI p pos -> Φ' r p pos) -> usimS R m m' (PST Φ').
Proof.
  intros H HI. eapply ru_post; [exact H|]. intros r ? ? ? ? (p' & tm' & nx' & off' & pos' & X1 & X2 & X3 & X4). exists p', tm', nx', off', pos'. auto 6.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pp_keep {A} (Φ : A -> pcapT -> Z -> Prop) nx p tm off pos (m m' : Monad.M PS A) :
  usimS (RPP nx tm off pos) m m' (eqpost (fun r => fun sG moG sC moC => Φ r p pos /\ RPP nx tm off pos sG moG sC moC)) ->
  PI p pos -> TML tm (toks p) -> usimS (RPP nx tm off pos) m m' (PST Φ).
Proof.
  intros H H2 H3. eapply ru_post; [exact H|]. intros r ? ? ? ? [X HR]. exists p, tm, nx, off, pos. auto.
Qed.

#[using="Type"] Lemma toks_set_buffer_perm p b al sz dd :
  Permutation ((b, al) :: lrm (pc_buffer p) (toks p)) (toks (set_buffer b sz al dd p)).
Proof. unfold UPcapA.toks. rewrite lrm_head. cbn. unfold psize, ifas. cbn. reflexivity. Qed.

#[using="Type"] Lemma PI_set_buffer p pos b sz al dd : PI p pos -> 1 <= al <= BUFMAX -> 1 <= sz <= BUFMAX -> PI (set_buffer b sz al dd p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4] Hal Hsz. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_set_bufdata p pos dd : PI p pos -> PI (set_bufdata dd p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4]. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_set_errbuf p pos m : PI p pos -> PI (set_errbuf m p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4]. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_set_header p pos h : PI p pos -> PI (set_header h p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4]. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_pos_mono p pos pos' : PI p pos -> pos <= pos' <= Z.of_nat (length d) -> PI p pos'.
Proof.
  intros [P1 P2 P2' P3 P3' P4] Hp. constructor; auto; [lia|]. destruct (pc_priv p) as [|s i]; [exact P4|]. destruct P4 as (A1 & A2 & A3 & A4 & A5). split; [lia|]. split; [lia|]. exact (conj A3 (conj A4 A5)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_read_bytes (p : pcapT) (pos n : Z) (r : rb_status * list Z) (p' : pcapT) (pos' : Z) : Prop :=
  p' = p /\ zlength (snd r) <= n /\ pos' = pos + zlength (snd r) /\
  match fst r with RBS_Ok => zlength (snd r) = n | RBS_Eof => zlength (snd r) = 0 | RBS_Err m => mok m end /\
  snd r = dsl d pos (zlength (snd r)).

#[using="STK RCW"] Lemma pr_read_bytes nx p tm off pos dst n foe :
  PI p pos -> TML tm (toks p) -> rdest_ok p dst n -> 0 <= n < 2^40 ->
  usimS (RPP nx tm off pos) (read_bytes MOps PR_G fp dst n foe) (read_bytes MOps PR_C fp dst n foe) (PST (Q_read_bytes p pos n)).
Proof.
  intros HPI HT HD Hn. unfold read_bytes. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  eapply ru_bind.
  { eapply ru_post; [apply (pr_fread (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx p tm off pos dst n HPI HT HD Hn)|]. intros r ? ? ? ? X. exact X. }
  intros got. apply usim_exI; intros off'. apply usim_pure; intros (Q1 & Q2 & Q3 & Q4).
  assert (HPI' : PI p (pos + zlength got)).
  { apply (PI_pos_mono p pos); [exact HPI|]. pose proof (zlength_nonneg got). lia. }
  destruct (negb (zlength got =? n)) eqn:EN.
  - eapply ruk_bind with (K1 := fun _ => KR_ off') (C1 := fun _ => Cc) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs (FR_ off' (pos + zlength got))); [apply (pr_ferror (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx)|].
    intros e ->. cbn beta iota.
    destruct ((zlength got =? 0) && negb foe) eqn:EZ.
    + apply (pp_ret _ nx p tm off'); [| exact HPI'| exact HT]. unfold Q_read_bytes. cbn [fst snd]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
      apply andb_prop in EZ as [EZ _]. apply Z.eqb_eq in EZ. exact (conj EZ Q4).
    + apply (pp_ret _ nx p tm off'); [| exact HPI'| exact HT]. unfold Q_read_bytes. cbn [fst snd]. split; [reflexivity|]. split; [lia|]. split; [reflexivity| split; [mok_tac| exact Q4]].
  - apply negb_false_iff in EN. apply Z.eqb_eq in EN.
    apply (pp_ret _ nx p tm off'); [| exact HPI'| exact HT]. unfold Q_read_bytes. cbn [fst snd]. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact (conj EN Q4)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_grow (p : pcapT) (pos sz : Z) (r : bool * pcapT) (p' : pcapT) (pos' : Z) : Prop :=
  p' = snd r /\ pos' = pos /\ pkeep p p' /\ (fst r = true -> pc_bufsize p' = sz /\ pc_bufalloc p' = sz).

#[using="RCW"] Lemma pr_grow_buffer nx p tm off pos sz :
  PI p pos -> TML tm (toks p) -> 1 <= sz <= BUFMAX ->
  usimS (RPP nx tm off pos) (grow_buffer MOps PR_G p sz) (grow_buffer MOps PR_C p sz) (PST (Q_grow p pos sz)).
Proof.
  intros HPI HT Hsz. unfold grow_buffer. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims].
  destruct (RP_budget rc RCW p pos tm sz HPI HT ltac:(lia)) as (R1 & R2 & R3).
  eapply ru_bind.
  { apply (gr_realloc (CEG:=CEG) (CEC:=CEC) segs tm (toks p) nx _ _ _ (pc_buffer p) (pc_bufalloc p) sz HT (toks_buf rc p)); [| unfold BUFMAX in Hsz; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT)); exact R2].
    unfold UPcapA.toks. rewrite !zlen_cons, zlen_app, zlen_cons. pose proof (rw_B _ RCW) as (BL & _). destruct (ifas_R63N rc p pos HPI) as [_ IL]. lia. }
  intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
  eapply (pp_ret _ (N.succ nx) (set_buffer nx sz sz (zfirstn sz (pc_bufdata p)) p) _ off pos).
  - unfold Q_grow. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [apply pkeep_set_buffer|]. intros _; split; reflexivity.
  - apply PI_set_buffer; [exact HPI| exact Hsz| lia].
  - eapply TML_perm; [exact HT'| apply toks_set_buffer_perm].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_read_block (p : pcapT) (pos : Z) (rb : block_result) (p' : pcapT) (pos' : Z) : Prop :=
  pkeep p p' /\ pos <= pos' /\
  match rb with
  | RB_Ok c p'' => p'' = p' /\ exists tl, 12 <= tl /\ pos' = pos + tl /\ cur_off c = 8 /\ cur_remaining c = tl - 12
  | RB_Eof p'' => p'' = p'
  | RB_Err m p'' => p'' = p' /\ mok m
  end.

#[using="STK RCW"] Lemma pr_read_block nx p tm off pos a_bhdr :
  PI p pos -> TML tm (toks p) -> rdest_ok p a_bhdr 8 ->
  usimS (RPP nx tm off pos) (read_block MOps PR_G a_bhdr p) (read_block MOps PR_C a_bhdr p) (PST (Q_read_block p pos)).
Proof.
  intros HPI HT HD. unfold read_block. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. rewrite (pi_fp _ _ _ HPI).
  eapply pp_bind; [apply (pr_read_bytes nx p tm off pos a_bhdr 8 false HPI HT HD ltac:(lia))|].
  intros [st bh] p1 tm1 nx1 off1 pos1 (-> & LB & -> & ST & CT) HPI1 HT1. cbn [fst snd] in *. pose proof (zlength_nonneg bh) as NB.
  destruct st as [| |m].
  2:{ apply (pp_ret _ nx1 p tm1 off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| reflexivity]. }
  2:{ apply (pp_ret _ nx1 p tm1 off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| split; [reflexivity| exact ST]]. }
  cbn in ST. rewrite !ST in *. cbv zeta.
  set (bt := if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0).
  set (tl := if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4).
  destruct (tl <? 12) eqn:ETL. { apply (pp_ret _ nx1 p tm1 off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| split; [reflexivity| mok_tac]]. }
  apply Z.ltb_ge in ETL.
  destruct (negb (tl mod 4 =? 0)). { apply (pp_ret _ nx1 p tm1 off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| split; [reflexivity| mok_tac]]. }
  (* [comment removed for export] *)
  eapply (pp_bind (fun r p' pos' => pos' = pos + 8 /\ pkeep p p' /\ p' = snd r /\ (fst r = None -> tl <= BUFMAX) /\ (forall m, fst r = Some m -> mok m))).
  { destruct (pc_bufsize p <? tl) eqn:EBS.
    - destruct (ng_max_blocksize (ng_of p) <? tl) eqn:EM.
      + apply (pp_ret _ nx1 p tm1 off1); [| exact HPI1| exact HT1]. cbn [fst snd]. split; [lia|]. split; [apply pkeep_refl|]. split; [reflexivity|]. split; [intros; discriminate| intros m X; injection X as <-; mok_tac].
      + apply Z.ltb_ge in EM.
        assert (TLB : 1 <= tl <= BUFMAX).
        { destruct HPI1 as [_ _ _ _ _ NG]. unfold ng_of in EM. destruct (pc_priv p) as [|sng i]; cbn in EM; [unfold BUFMAX; lia|]. destruct NG as (_ & _ & _ & _ & MB). lia. }
        cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims].
        (* [comment removed for export] *)
        destruct (RP_budget rc RCW p (pos + 8) tm1 tl HPI1 HT1 ltac:(lia)) as (R1 & R2 & R3).
        eapply ru_bind.
        { apply (gr_realloc (CEG:=CEG) (CEC:=CEC) segs tm1 (toks p) nx1 _ _ _ (pc_buffer p) (pc_bufalloc p) tl HT1 (toks_buf rc p)); [| unfold BUFMAX in TLB; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT1)); exact R2].
          unfold UPcapA.toks. rewrite !zlen_cons, zlen_app, zlen_cons. pose proof (rw_B _ RCW) as (BL & _). destruct (ifas_R63N rc p _ HPI1) as [_ IL]. lia. }
        intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
        eapply (pp_ret _ (N.succ nx1) (set_buffer nx1 (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p) _ off1 (pos + 8)).
        * cbn [fst snd]. split; [lia|]. split; [apply pkeep_set_buffer|]. split; [reflexivity|]. split; [intros _; lia| intros; discriminate].
        * apply PI_set_buffer; [exact HPI1| exact TLB| exact (pi_bsz _ _ _ HPI1)].
        * eapply TML_perm; [exact HT'| apply toks_set_buffer_perm].
    - apply Z.ltb_ge in EBS. pose proof (pi_bsz _ _ _ HPI1) as BSZ.
      apply (pp_ret _ nx1 p tm1 off1); [| exact HPI1| exact HT1]. cbn [fst snd]. split; [lia|]. split; [apply pkeep_refl|]. split; [reflexivity|]. split; [intros _; lia| intros; discriminate]. }
  intros [gerr p2] p2' tm2 nx2 off2 pos2 (-> & PK2 & E2 & TLB & MOK) HPI2 HT2. cbn [fst snd] in *. subst p2'.
  destruct gerr as [m|].
  { apply (pp_ret _ nx2 p2 tm2 off2); [| exact HPI2| exact HT2]. split; [exact PK2|]. split; [lia| split; [reflexivity| exact (MOK m eq_refl)]]. }
  specialize (TLB eq_refl).
  cbv zeta.
  set (p3 := set_bufdata (le_bytes 4 bt ++ le_bytes 4 tl) p2).
  assert (HPI3 : PI p3 (pos + 8)) by (apply PI_set_bufdata; exact HPI2).
  assert (HT3 : TML tm2 (toks p3)) by exact HT2.
  rewrite <- (pi_fp _ _ _ HPI2).
  replace (pc_rfile p2) with (pc_rfile p3) by reflexivity.
  rewrite (pi_fp _ _ _ HPI3).
  eapply pp_bind; [apply (pr_read_bytes nx2 p3 tm2 off2 (pos + 8) (DHeap (pc_buffer p3) 8) (tl - 8) true HPI3 HT3); [cbn; split; [reflexivity| unfold BUFMAX in TLB; lia]| unfold BUFMAX in TLB; lia]|].
  intros [st2 data] p4 tm4 nx4 off4 pos4 (-> & LB2 & -> & ST2 & CT2) HPI4 HT4. cbn [fst snd] in *. pose proof (zlength_nonneg data) as ND2.
  set (p5 := set_bufdata (pc_bufdata p3 ++ data) p3).
  assert (HPI5 : PI p5 (pos + 8 + zlength data)) by (apply PI_set_bufdata; exact HPI4).
  assert (PK5 : pkeep p p5) by (eapply pkeep_trans; [exact PK2|]; split; reflexivity).
  destruct st2 as [| |m2].
  2:{ apply (pp_ret _ nx4 p5 tm4 off4); [| exact HPI5| exact HT4]. split; [exact PK5|]. split; [lia| split; [reflexivity| mok_tac]]. }
  2:{ apply (pp_ret _ nx4 p5 tm4 off4); [| exact HPI5| exact HT4]. split; [exact PK5|]. split; [lia| split; [reflexivity| cbn in ST2; exact ST2]]. }
  cbv zeta.
  set (p6 := if pc_swapped p5 then set_bufdata (swap_field 4 (tl - 4) (pc_bufdata p5)) p5 else p5).
  assert (HPI6 : PI p6 (pos + 8 + zlength data)) by (subst p6; destruct (pc_swapped p5); [apply PI_set_bufdata|]; exact HPI5).
  assert (HT6 : TML tm4 (toks p6)) by (subst p6; destruct (pc_swapped p5); exact HT4).
  assert (PK6 : pkeep p p6) by (subst p6; destruct (pc_swapped p5); [eapply pkeep_trans; [exact PK5| split; reflexivity]| exact PK5]).
  destruct (negb (tl =? get_le32 (pc_bufdata p6) (tl - 4))).
  - apply (pp_ret _ nx4 p6 tm4 off4); [| exact HPI6| exact HT6]. split; [exact PK6|]. split; [lia| split; [reflexivity| mok_tac]].
  - apply (pp_ret _ nx4 p6 tm4 off4); [| exact HPI6| exact HT6]. split; [exact PK6|]. split; [lia|]. split; [reflexivity|].
    exists tl. cbn. split; [lia|]. split; [lia|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma lor_lt_pow2 a b m : 0 <= a < 2 ^ m -> 0 <= b < 2 ^ m -> 0 <= m -> 0 <= Z.lor a b < 2 ^ m.
Proof.
  intros Ha Hb Hm. pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))) as NN. split; [exact NN|].
  destruct (Z.eq_dec a 0) as [->|NA]; [rewrite Z.lor_0_l; lia|]. destruct (Z.eq_dec b 0) as [->|NB]; [rewrite Z.lor_0_r; lia|].
  assert (L : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [| lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply Z.log2_lt_pow2; [exact L|]. rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma roundup_pow2_small v : 1 <= v <= 2^27 -> 1 <= roundup_pow2_u32 v <= 2^27.
Proof.
  intros Hv. unfold roundup_pow2_u32. cbv zeta.
  assert (U : forall x, 0 <= x < 2^32 -> Prelim.u32 x = x) by (intros x Hx; unfold Prelim.u32; apply Z.mod_small; lia).
  rewrite (U (v - 1)) by lia.
  assert (STEP : forall n k, 0 <= n < 2^27 -> 0 <= k -> 0 <= Z.lor n (Z.shiftr n k) < 2^27).
  { intros n k Hn Hk. apply lor_lt_pow2; [lia| | lia]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). nia. }
  pose proof (STEP (v - 1) 1 ltac:(lia) ltac:(lia)) as S1. set (n1 := Z.lor (v - 1) (Z.shiftr (v - 1) 1)) in *.
  pose proof (STEP n1 2 S1 ltac:(lia)) as S2. set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
  pose proof (STEP n2 4 S2 ltac:(lia)) as S3. set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
  pose proof (STEP n3 8 S3 ltac:(lia)) as S4. set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
  pose proof (STEP n4 16 S4 ltac:(lia)) as S5. set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
  rewrite (U (n5 + 1)); lia.
Qed.

(* [comment removed for export] *)
#[using="STK RCW"] Lemma pr_discard_loop nx p tm : forall fuel off pos caplen btd br,
  PI p pos -> TML tm (toks p) -> 0 <= btd ->
  usimS (RPP nx tm off pos) (discard_loop MOps PR_G fuel fp caplen btd br) (discard_loop MOps PR_C fuel fp caplen btd br)
        (PST (fun _ p' pos' => p' = p /\ pos <= pos')).
Proof.
  induction fuel as [|fuel IH]; intros off pos caplen btd br HPI HT Hb; cbn [discard_loop]; cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  - apply (pp_ret _ nx p tm off); [| exact HPI| exact HT]. split; [reflexivity| lia].
  - destruct (btd =? 0). { apply (pp_ret _ nx p tm off); [| exact HPI| exact HT]. split; [reflexivity| lia]. }
    set (btr := if 4096 <? btd then 4096 else btd).
    assert (Hbtr : 0 <= btr <= 4096 /\ btr <= btd) by (subst btr; destruct (4096 <? btd) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; lia).
    eapply ru_bind.
    { eapply ru_post; [apply (pr_fread (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx p tm off pos (DStack SiteDiscardBuf 0) btr HPI HT); [cbn; lia| lia]|]. intros r ? ? ? ? X; exact X. }
    intros got. apply usim_exI; intros off'. apply usim_pure; intros (Q1 & Q2 & Q3 & Q4). pose proof (zlength_nonneg got) as NG.
    assert (HPI' : PI p (pos + zlength got)) by (apply (PI_pos_mono p pos); [exact HPI| lia]).
    change (RUK tm nx (KR_ off') Cc idl (WF oh hs (FR_ off' (pos + zlength got)))) with (RPP nx tm off' (pos + zlength got)).
    destruct (negb (zlength got =? btr)).
    + eapply ru_bind; [apply (pr_read_fail_msg (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx); mok_tac|].
      intros m. apply usim_pure; intros Mm. cbn beta. apply (pp_ret _ nx p tm off'); [| exact HPI'| exact HT]. split; [reflexivity| lia].
    + eapply pp_post; [apply (IH off' (pos + zlength got)); [exact HPI'| exact HT| lia]|]. cbn. intros ? ? ? [-> LE] _. split; [reflexivity| lia].
Qed.

Definition Q_next (p : pcapT) (pos : Z) (r : Z * pkthdr * pcapT) (p' : pcapT) (pos' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ (0 < fst (fst r) -> pos < pos').

#[using="STK RCW"] Lemma pr_pcap_next_packet nx p tm off pos s :
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivPcap s ->
  usimS (RPP nx tm off pos) (pcap_next_packet MOps PR_G p) (pcap_next_packet MOps PR_C p) (PST (Q_next p pos)).
Proof.
  intros HPI HT HS. unfold pcap_next_packet. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. rewrite (pi_fp _ _ _ HPI).
  unfold sf_of. rewrite HS.
  assert (HH : sf_hdrsize s = 16 \/ sf_hdrsize s = 24) by (pose proof (pi_ng _ _ _ HPI) as NG; rewrite HS in NG; exact NG).
  assert (HH' : 1 <= sf_hdrsize s <= 24) by lia.
  pose proof (pi_snap _ _ _ HPI) as SNAP. rewrite HS in SNAP.
  eapply ru_bind.
  { eapply ru_post; [apply (pr_fread (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx p tm off pos (DStack SiteSfHdr 0) (sf_hdrsize s) HPI HT); [cbn; lia| lia]|]. intros r ? ? ? ? X; exact X. }
  intros hb. apply usim_exI; intros off1. apply usim_pure; intros (Q1 & Q2 & Q3 & Q4). pose proof (zlength_nonneg hb) as NHB.
  assert (HPI1 : PI p (pos + zlength hb)) by (apply (PI_pos_mono p pos); [exact HPI| lia]).
  change (RUK tm nx (KR_ off1) Cc idl (WF oh hs (FR_ off1 (pos + zlength hb)))) with (RPP nx tm off1 (pos + zlength hb)).
  cbv zeta.
  destruct (negb (zlength hb =? sf_hdrsize s)) eqn:EH.
  { (* [comment removed for export] *)
    eapply ruk_bind with (K1 := fun _ => KR_ off1) (C1 := fun _ => Cc) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs (FR_ off1 (pos + zlength hb))); [apply (pr_ferror (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx)|].
    intros e ->. cbn beta iota.
    destruct (negb (zlength hb =? 0)).
    - apply (pp_ret _ nx (set_errbuf (Msg.trunc_header (sf_hdrsize s) (zlength hb)) p) tm off1); [| apply PI_set_errbuf; exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_set_errbuf|]. split; lia.
    - apply (pp_ret _ nx p tm off1); [| exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_refl|]. split; lia. }
  apply negb_false_iff in EH. apply Z.eqb_eq in EH.
  assert (HBok : bytes_ok hb) by (rewrite Q4; apply dsl_bytes).
  assert (SWB : forall v, 0 <= v < 2^32 -> 0 <= (if pc_swapped p then bswap32 v else v) < 2^32) by (intros v Hv; destruct (pc_swapped p); [apply bswap32_range| exact Hv]).
  (* [comment removed for export] *)
  match goal with |- context [let '(caplen, len) := ?cl in _] => destruct cl as [caplen len] eqn:ECL end.
  assert (CL0 : 0 <= caplen < 2^32 /\ 0 <= len < 2^32).
  { pose proof (SWB _ (get_le32_range hb 8 HBok)) as B8. pose proof (SWB _ (get_le32_range hb 12 HBok)) as B12.
    destruct (sf_lengths_swapped s); try destruct (_ <=? _); injection ECL as E1 E2; lia. }
  cbv zeta.
  destruct (max_snaplen_for_dlt (pc_linktype p) <? caplen) eqn:EMX.
  { destruct (pc_snapshot p <? caplen).
    - apply (pp_ret _ nx (set_errbuf (Msg.invalid_caplen_snaplen caplen (pc_snapshot p)) p) tm off1); [| apply PI_set_errbuf; exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_set_errbuf|]. split; lia.
    - apply (pp_ret _ nx (set_errbuf (Msg.invalid_caplen_maximum caplen (max_snaplen_for_dlt (pc_linktype p))) p) tm off1); [| apply PI_set_errbuf; exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_set_errbuf|]. split; lia. }
  apply Z.ltb_ge in EMX.
  assert (CAPB : caplen <= 2^27) by (unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN in EMX; destruct (pc_linktype p =? DLT_DBUS); [lia|]; destruct (pc_linktype p =? DLT_EBHSCR); [lia|]; destruct (pc_linktype p =? DLT_USBPCAP); lia).
  destruct (pc_snapshot p <? caplen) eqn:ESC.
  - apply Z.ltb_lt in ESC.
    (* [comment removed for export] *)
    eapply (pp_bind (fun r p' pos' => pos' = pos + zlength hb /\ pkeep p p' /\ snd r = p')).
    { destruct (pc_bufsize p <? caplen).
      - eapply pp_post; [apply (pr_grow_buffer nx p tm off1 _ (pc_snapshot p) HPI1 HT); unfold BUFMAX; lia|]. unfold Q_grow. cbn. intros [ok p'] ? ? (-> & -> & PK & _) _. auto.
      - apply (pp_ret _ nx p tm off1); [| exact HPI1| exact HT]. cbn. auto using pkeep_refl. }
    intros [ok p1] p1' tm1 nx1 off2 pos1 (-> & PK1 & E1) HPI2 HT1. cbn [fst snd] in E1. subst p1'.
    destruct (negb ok). { apply (pp_ret _ nx1 p1 tm1 off2); [| exact HPI2| exact HT1]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; exact PK1|]. split; lia. }
    eapply ru_bind.
    { eapply ru_post; [apply (pr_fread (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx1 p1 tm1 off2 _ (DHeap (pc_buffer p1) 0) (pc_snapshot p) HPI2 HT1); [cbn; split; [reflexivity| lia]| lia]|]. intros r ? ? ? ? X; exact X. }
    intros got. apply usim_exI; intros off3. apply usim_pure; intros (G1 & G2 & G3 & G4). pose proof (zlength_nonneg got) as NGT.
    set (p2 := set_bufdata got p1).
    assert (HPI3 : PI p2 (pos + zlength hb + zlength got)) by (apply PI_set_bufdata; apply (PI_pos_mono p1 (pos + zlength hb)); [exact HPI2| lia]).
    assert (HT2 : TML tm1 (toks p2)) by exact HT1.
    assert (PK2 : pkeep p p2) by (eapply pkeep_trans; [exact PK1| apply pkeep_set_bufdata]).
    change (RUK tm1 nx1 (KR_ off3) Cc idl (WF oh hs (FR_ off3 (pos + zlength hb + zlength got)))) with (RPP nx1 tm1 off3 (pos + zlength hb + zlength got)).
    destruct (negb (zlength got =? pc_snapshot p)).
    { eapply ru_bind; [apply (pr_read_fail_msg (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx1); mok_tac|].
      intros m. apply usim_pure; intros Mm. cbn beta. apply (pp_ret _ nx1 (set_errbuf m p2) tm1 off3); [| apply PI_set_errbuf; exact HPI3| exact HT2]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]|]. split; lia. }
    eapply pp_bind; [apply (pr_discard_loop nx1 p2 tm1 _ off3 (pos + zlength hb + zlength got)); [exact HPI3| exact HT2| lia]|].
    intros r p3 tm3 nx3 off4 pos3 [-> LE3] HPI4 HT3.
    destruct r as [m|[]].
    + apply (pp_ret _ nx3 (set_errbuf m p2) tm3 off4); [| apply PI_set_errbuf; exact HPI4| exact HT3]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]|]. split; lia.
    + match goal with |- context [let '(hdr, dd) := ?x in _] => destruct x as [hdr dd] end.
      match goal with |- usim _ _ (mret (_, _, ?q)) _ _ => apply (pp_ret _ nx3 q tm3 off4) end; [| apply PI_set_bufdata; exact HPI4| exact HT3]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_bufdata]|]. split; lia.
  - apply Z.ltb_ge in ESC.
    eapply (pp_bind (fun r p' pos' => pos' = pos + zlength hb /\ pkeep p p' /\ snd r = p')).
    { destruct (pc_bufsize p <? caplen) eqn:EBC.
      - apply Z.ltb_lt in EBC. pose proof (pi_bsz _ _ _ HPI) as BSZ.
        pose proof (roundup_pow2_small caplen ltac:(lia)) as RU.
        eapply pp_post; [apply (pr_grow_buffer nx p tm off1 _ _ HPI1 HT)|].
        + destruct (pc_snapshot p <? roundup_pow2_u32 caplen) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; unfold BUFMAX; lia.
        + unfold Q_grow. cbn. intros [ok p'] ? ? (-> & -> & PK & _) _. auto.
      - apply (pp_ret _ nx p tm off1); [| exact HPI1| exact HT]. cbn. auto using pkeep_refl. }
    intros [ok p1] p1' tm1 nx1 off2 pos1 (-> & PK1 & E1) HPI2 HT1. cbn [fst snd] in E1. subst p1'.
    destruct (negb ok). { apply (pp_ret _ nx1 p1 tm1 off2); [| exact HPI2| exact HT1]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; exact PK1|]. split; lia. }
    eapply ru_bind.
    { eapply ru_post; [apply (pr_fread (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx1 p1 tm1 off2 _ (DHeap (pc_buffer p1) 0) caplen HPI2 HT1); [cbn; split; [reflexivity| lia]| lia]|]. intros r ? ? ? ? X; exact X. }
    intros got. apply usim_exI; intros off3. apply usim_pure; intros (G1 & G2 & G3 & G4). pose proof (zlength_nonneg got) as NGT.
    set (p2 := set_bufdata got p1).
    assert (HPI3 : PI p2 (pos + zlength hb + zlength got)) by (apply PI_set_bufdata; apply (PI_pos_mono p1 (pos + zlength hb)); [exact HPI2| lia]).
    assert (HT2 : TML tm1 (toks p2)) by exact HT1.
    assert (PK2 : pkeep p p2) by (eapply pkeep_trans; [exact PK1| apply pkeep_set_bufdata]).
    change (RUK tm1 nx1 (KR_ off3) Cc idl (WF oh hs (FR_ off3 (pos + zlength hb + zlength got)))) with (RPP nx1 tm1 off3 (pos + zlength hb + zlength got)).
    destruct (negb (zlength got =? caplen)).
    { eapply ru_bind; [apply (pr_read_fail_msg (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx1); mok_tac|].
      intros m. apply usim_pure; intros Mm. cbn beta. apply (pp_ret _ nx1 (set_errbuf m p2) tm1 off3); [| apply PI_set_errbuf; exact HPI3| exact HT2]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]|]. split; lia. }
    match goal with |- context [let '(hdr, dd) := ?x in _] => destruct x as [hdr dd] end.
    match goal with |- usim _ _ (mret (_, _, ?q)) _ _ => apply (pp_ret _ nx1 q tm1 off3) end; [| apply PI_set_bufdata; exact HPI3| exact HT2]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_bufdata]|]. split; lia.
Qed.

End ReadingB.

End WithCeil.
End UPcapB.

(* [comment removed for export] *)
Module UPcapC.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UStdio UFmt UDriver UPcapA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.UNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).
#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
Section ReadingC.
Variable segs : list Segment.
Variables (stkG stkC : stack_site -> Z).
Hypothesis STK : stk_ok stkG.
#[local] Notation npk := (npeek segs).
#[local] Notation usimS := (usim npk).
#[local] Notation RX := (UBase.RX (CEG:=CEG) (CEC:=CEC)).     (* [comment removed for export] *)
#[local] Notation RUK tm nx K C g W := (RX tm nx (UK nx K C g W)).
#[local] Notation PR_G := (prims fopsG fo_nop stkG).
#[local] Notation PR_C := (prims fopsC fo_nop stkC).
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
#[local] Notation B := (rc_B rc).
#[local] Notation Kx := (rc_Kx rc).
#[local] Notation F0 := (rc_F0 rc).
#[local] Notation hs := (rc_hs rc).
#[local] Notation Cc := (rc_C rc).
#[local] Notation oh := (rc_oh rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation KR_ := (KR_ rc).
#[local] Notation FR_ := (FR_ rc).
#[local] Notation PI := (PI rc).
#[local] Notation RPP := (RPP (CEG:=CEG) (CEC:=CEC) rc).
#[local] Notation PST := (PST (CEG:=CEG) (CEC:=CEC) rc).

(* [comment removed for export] *)
#[using="Type"] Lemma toks_ng p s i :
  pc_priv p = PrivNg s i ->
  toks p = (pc_buffer p, pc_bufalloc p) :: (pc_self p, PCAP_NG_SF_TOTAL)
           :: match i with Some q => [(q, ng_ifaces_size s * PCAP_NG_IF_SIZE)] | None => [] end ++ (fp, FILE_ALLOC) :: B.
Proof. intros HS. unfold UPcapA.toks, psize, ifas. rewrite HS. destruct i; reflexivity. Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma toks_len p : zlen (toks p) + 1 <= 9.
Proof.
  unfold UPcapA.toks, ifas. pose proof (rw_B _ RCW) as (BL & _). unfold zlen in *. cbn [length]. rewrite length_app. cbn [length].
  destruct (pc_priv p) as [|s [q|]]; cbn [length]; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pow2_double_small k pos :
  0 <= k -> 20 * 2 ^ k <= pos - 20 -> pos < MAX_INPUT -> 2 ^ k * 2 <= IFSMAX.
Proof.
  intros Hk Hle Hp. unfold MAX_INPUT, IFSMAX in *.
  assert (LT : 2 ^ k < 2 ^ 22) by lia.
  apply Z.pow_lt_mono_r_iff in LT; [| lia| lia]. change (2 ^ 22) with (2 ^ 21 * 2).
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma gfbd_mok c n m : get_from_block_data c n = inl m -> mok m.
Proof. unfold get_from_block_data. destruct (cur_remaining c <? n); [| discriminate]. intros X. injection X as <-. mok_tac. Qed.
#[using="Type"] Lemma process_idb_options_loop_mok : forall fuel sw st c buf buf' m,
  process_idb_options_loop fuel sw st c buf = (buf', inl m) -> mok m.
Proof.
  induction fuel as [|fuel IH]; intros sw st c buf buf' m H; cbn [process_idb_options_loop] in H; [discriminate|].
  destruct (cur_remaining c =? 0); [discriminate|].
  unfold get_opthdr_from_block_data in H. destruct (get_from_block_data c 4) as [m1|[off c1]] eqn:E1; [injection H as _ <-; exact (gfbd_mok _ _ _ E1)|].
  cbv zeta in H. cbn [fst snd] in H.
  match type of H with context [get_optvalue_from_block_data ?cc ?ol] => unfold get_optvalue_from_block_data in H; destruct (get_from_block_data cc (((ol + 3) / 4) * 4)) as [m2|[voff c2]] eqn:E2; [injection H as _ <-; exact (gfbd_mok _ _ _ E2)|] end.
  repeat match type of H with
    | (if ?c then _ else _) = _ => destruct c
    | process_idb_options_loop _ _ _ _ _ = _ => exact (IH _ _ _ _ _ _ H)
    | (_, inl _) = (_, inl _) => injection H as _ <-; mok_tac
    | (_, inr _) = (_, inl _) => discriminate
    end.
Qed.
#[using="Type"] Lemma process_idb_options_mok sw c buf buf' m : process_idb_options sw c buf = (buf', inl m) -> mok m.
Proof. unfold process_idb_options. apply process_idb_options_loop_mok. Qed.

Definition Q_addif (p : pcapT) (pos : Z) (r : bool * cursor * pcapT * list Z) (p' : pcapT) (pos' : Z) : Prop :=
  snd (fst r) = p' /\ pos' = pos /\ psim p p' /\ mok (snd r).

#[using="RCW"] Lemma pr_add_interface nx p tm off pos s i idb_off c :
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> 20 * (ng_ifcount s + 1) <= pos ->
  usimS (RPP nx tm off pos) (add_interface MOps PR_G p idb_off c) (add_interface MOps PR_C p idb_off c) (PST (Q_addif p pos)).
Proof.
  intros HPI HT HS Hc. pose proof HPI as [P1 P2 P3 P4 P5 P6]. rewrite HS in P6. destruct P6 as (N1 & N2 & N3 & N4 & N5).
  pose proof (rw_d _ RCW) as DL.
  assert (U1 : Prelim.u32 (ng_ifcount s + 1) = ng_ifcount s + 1) by (unfold Prelim.u32; apply Z.mod_small; unfold MAX_INPUT in DL; lia).
  unfold add_interface. unfold ng_of, ng_ifaces_ptr_of. rewrite HS. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_realloc prims]. rewrite U1. cbv zeta.
  (* [comment removed for export] *)
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc (fun r p' pos' => pos' = pos /\ fst r = None /\ exists sz q k, snd r = p' /\
            p' = set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) sz (ng_ifaces s)) (Some q) p /\ 0 <= k /\ sz = 2 ^ k /\ sz <= IFSMAX)).
  { destruct (ng_ifaces_size s <? ng_ifcount s + 1) eqn:ELT.
    - apply Z.ltb_lt in ELT. destruct (ng_ifaces_size s =? 0) eqn:EZ.
      + (* [comment removed for export] *)
        apply Z.eqb_eq in EZ.
        assert (Hi : i = None) by (destruct i as [q|]; [destruct N4 as (k & Hk & E); pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia| reflexivity]). subst i.
        destruct (RP_budget rc RCW p pos tm PCAP_NG_IF_SIZE HPI HT ltac:(unfold PCAP_NG_IF_SIZE, BUFMAX; lia)) as (R1 & R2 & R3).
        eapply ru_bind.
        { eapply (gr_malloc (CEG:=CEG) (CEC:=CEC) segs tm (toks p) nx _ _ _ PCAP_NG_IF_SIZE HT); [apply toks_len| unfold PCAP_NG_IF_SIZE; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT)); exact R2]. }
        intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
        apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ (N.succ nx) (set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) 1 (ng_ifaces s)) (Some nx) p) _ off pos).
        * cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. exists 1, nx, 0. split; [reflexivity|]. split; [reflexivity|]. unfold IFSMAX. lia.
        * constructor; cbn; auto. split; [lia|]. split; [lia|]. split; [unfold IFSMAX; lia|]. split; [exists 0; split; [lia| reflexivity]|]. exact N5.
        * eapply TML_perm; [exact HT'|]. unfold UPcapA.toks, psize, ifas. rewrite HS. cbn.
          etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_swap.
      + (* [comment removed for export] *)
        apply Z.eqb_neq in EZ.
        destruct i as [old|]; [| lia]. destruct N4 as (k & Hk & Esz).
        assert (SZ2 : ng_ifaces_size s * 2 <= IFSMAX) by (rewrite Esz; apply (pow2_double_small k pos Hk); [rewrite <- Esz; lia| lia]).
        assert (U2 : Prelim.u32 (ng_ifaces_size s * 2) = ng_ifaces_size s * 2) by (unfold Prelim.u32; apply Z.mod_small; unfold IFSMAX in SZ2; lia).
        rewrite U2. destruct (ng_ifaces_size s * 2 <? ng_ifaces_size s) eqn:EO; [apply Z.ltb_lt in EO; lia|].
        replace (ng_ifcount s <? 2 ^ 22) with true by (symmetry; apply Z.ltb_lt; unfold MAX_INPUT in DL; lia). cbn [negb].
        destruct (RP_budget_if rc RCW p pos tm (ng_ifaces_size s * 2 * PCAP_NG_IF_SIZE) HPI HT ltac:(unfold PCAP_NG_IF_SIZE; lia)) as (R1 & R2 & R3).
        { unfold ifas. rewrite HS. cbn [map snd]. rewrite R63N_cons, R63N_nil.
          pose proof (bigb_le (ng_ifaces_size s * PCAP_NG_IF_SIZE) ltac:(unfold PCAP_NG_IF_SIZE; lia)). unfold IFSMAX, PCAP_NG_IF_SIZE, PGSZ in *. cbn. lia. }
        eapply ru_bind.
        { eapply (gr_realloc (CEG:=CEG) (CEC:=CEC) segs tm (toks p) nx _ _ _ old (ng_ifaces_size s * PCAP_NG_IF_SIZE) (ng_ifaces_size s * 2 * PCAP_NG_IF_SIZE) HT);
            [| apply toks_len| unfold PCAP_NG_IF_SIZE, IFSMAX in *; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT)); exact R2].
          rewrite (toks_ng p s (Some old) HS). right; right. apply in_app_iff. left. left. reflexivity. }
        intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
        apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ (N.succ nx) (set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s * 2) (ng_ifaces s)) (Some nx) p) _ off pos).
        * cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. exists (ng_ifaces_size s * 2), nx, (k + 1). split; [reflexivity|]. split; [reflexivity|].
          split; [lia|]. split; [rewrite Esz, Z.pow_add_r by lia; reflexivity| exact SZ2].
        * constructor; cbn; auto. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists (k + 1); split; [lia| rewrite Esz, Z.pow_add_r by lia; reflexivity]|]. exact N5.
        * eapply TML_perm; [exact HT'|]. pose proof (TML_nodup _ _ HT) as ND. unfold UPcapA.toks, psize, ifas in ND |- *. rewrite HS in ND |- *. cbn in ND |- *.
          inversion ND as [|? ? NI1 ND1]; subst. inversion ND1 as [|? ? NI2 ND2]; subst.
          destruct (N.eqb_spec (pc_buffer p) old) as [E|_]; [exfalso; apply NI1; rewrite E; right; left; reflexivity|].
          destruct (N.eqb_spec (pc_self p) old) as [E|_]; [exfalso; apply NI2; rewrite E; left; reflexivity|].
          rewrite N.eqb_refl. etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_swap.
    - apply Z.ltb_ge in ELT. destruct i as [old|]; [| lia]. destruct N4 as (k & Hk & Esz).
      apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx (set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)) (Some old) p) tm off pos).
      + cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. exists (ng_ifaces_size s), old, k. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Esz| lia].
      + constructor; cbn; auto. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists k; auto|]. exact N5.
      + unfold UPcapA.toks, psize, ifas in HT |- *. rewrite HS in HT. cbn in HT |- *. exact HT. }
  (* [comment removed for export] *)
  intros [r p1] p1' tm1 nx1 off1 pos1 (-> & Hr & (sz & q & k & E1 & -> & Hk & Hsz & SZM)) HPI1 HT1. cbn [fst snd] in Hr, E1. subst r p1.
  cbn [ng_of ng_ifaces_ptr_of set_ng set_priv pc_priv pc_bufdata pc_swapped ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size ng_ifaces
       pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header].
  destruct (process_idb_options (pc_swapped p) c (pc_bufdata p)) as [buf [m|[opts c']]] eqn:EPO.
  - match goal with |- usim _ _ (mret (_, _, ?q, _)) _ _ => apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 q tm1 off1 pos) end.
    + cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [split; [reflexivity| unfold isng; cbn; rewrite HS; reflexivity]| exact (process_idb_options_mok _ _ _ _ _ EPO)].
    + pose proof HPI1 as [X1 X2 X3 X4 X5 X6]. constructor; cbn in *; auto.
    + exact HT1.
  - cbv zeta.
    match goal with |- context [let '(scale_type, scale_factor) := ?x in _] => destruct x as [st sf] end.
    match goal with |- usim _ _ (mret (_, _, ?q, _)) _ _ => apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 q tm1 off1 pos) end.
    + cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [split; [reflexivity| unfold isng; cbn; rewrite HS; reflexivity]| apply mok_nil].
    + pose proof HPI1 as [X1 X2 X3 X4 X5 X6]. constructor; cbn in *; auto.
    + exact HT1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Q_thr {A} (p : pcapT) (pos : Z) (r : (list Z + A) * pcapT) (p' : pcapT) (pos' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ match fst r with inl m => mok m | inr _ => True end.

(* [comment removed for export] *)
Ltac q_thr_ret nx q tm off pos :=
  apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx q tm off pos); [cbv beta iota zeta delta [Q_thr fst snd]; split; [reflexivity|]; split; [psim_tac|]; split; [lia| first [exact I| mok_tac]]| | ].

#[using="Type"] Lemma gfbd_ok c n off c' : get_from_block_data c n = inr (off, c') -> n <= cur_remaining c /\ off = cur_off c /\ c' = mkCursor (cur_off c + n) (cur_remaining c - n) (cur_block_type c).
Proof. unfold get_from_block_data. destruct (cur_remaining c <? n) eqn:E; [discriminate|]. apply Z.ltb_ge in E. intros X. injection X as <- <-. auto. Qed.

#[using="STK RCW"] Lemma pr_ng_find_idb : forall fuel nx p tm off pos s i,
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> Z.of_nat (length d) < pos + Z.of_nat fuel ->
  usimS (RPP nx tm off pos) (ng_find_idb MOps PR_G fuel p) (ng_find_idb MOps PR_C fuel p) (PST (Q_thr p pos)).
Proof.
  induction fuel as [|fuel IH]; intros nx p tm off pos s i HPI HT HS HF.
  { exfalso. pose proof (pi_pos _ _ _ HPI). cbn in HF. lia. }
  cbn [ng_find_idb]. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_read_block (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx p tm off pos (DStack SiteBhdrCheckHeader 0) HPI HT); cbn; lia|].
  intros rb p1 tm1 nx1 off1 pos1 (PK & LE & HRB) HPI1 HT1.
  destruct rb as [p1'|m p1'|c p1'].
  { subst p1'. q_thr_ret nx1 p1 tm1 off1 pos1; [exact HPI1| exact HT1]. }
  { destruct HRB as [-> Mm]. q_thr_ret nx1 p1 tm1 off1 pos1; [exact HPI1| exact HT1]. }
  destruct HRB as (-> & tl & TL & -> & CO & CR). cbv zeta. cbn beta iota.
  destruct (cur_block_type c =? BT_IDB).
  - destruct (get_from_block_data c 8) as [m|[off' c']] eqn:EG.
    + pose proof (gfbd_mok _ _ _ EG) as Mm. q_thr_ret nx1 p1 tm1 off1 (pos + tl); [exact HPI1| exact HT1].
    + apply gfbd_ok in EG as (G1 & -> & ->).
      set (p2 := if pc_swapped p1 then set_bufdata (swap_field 4 (cur_off c + 4) (swap_field 2 (cur_off c) (pc_bufdata p1))) p1 else p1).
      assert (HPI2 : PI p2 (pos + tl)) by (subst p2; destruct (pc_swapped p1); [apply PI_set_bufdata|]; exact HPI1).
      assert (HT2 : TML tm1 (toks p2)) by (subst p2; destruct (pc_swapped p1); exact HT1).
      assert (PK2 : pkeep p p2) by (subst p2; destruct (pc_swapped p1); [eapply pkeep_trans; [exact PK| apply pkeep_set_bufdata]| exact PK]).
      assert (HS2 : pc_priv p2 = PrivNg s i) by (destruct PK2 as [_ E]; rewrite E; exact HS).
      pose proof (pi_ng _ _ _ HPI) as NG. rewrite HS in NG. destruct NG as (N1 & N2 & _).
      eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_add_interface nx1 p2 tm1 off1 (pos + tl) s i (cur_off c) _ HPI2 HT2 HS2); lia|].
      intros [[[ok c2] p3] m] p3' tm3 nx3 off3 pos3 (E3 & -> & PS3 & Mm) HPI3 HT3. cbn [fst snd] in E3, Mm. subst p3'. cbn beta iota.
      destruct ok; (q_thr_ret nx3 p3 tm3 off3 (pos + tl); [exact HPI3| exact HT3]).
  - destruct ((cur_block_type c =? BT_EPB) || (cur_block_type c =? BT_SPB) || (cur_block_type c =? BT_PB)).
    + q_thr_ret nx1 p1 tm1 off1 (pos + tl); [exact HPI1| exact HT1].
    + destruct (psim_ng p p1 s i (pkeep_psim _ _ PK) HS) as (s1 & i1 & HS1).
      eapply (pp_post (CEG:=CEG) (CEC:=CEC) segs rc); [apply (IH nx1 p1 tm1 off1 (pos + tl) s1 i1 HPI1 HT1 HS1); rewrite Nat2Z.inj_succ in HF; lia|].
      intros r p' pos' (A1 & A2 & A3 & A4) _. split; [exact A1|]. split; [psim_tac|]. split; [lia| exact A4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_scan (p : pcapT) (pos : Z) (r : (Z + ng_found) * pcapT) (p' : pcapT) (pos' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ (match fst r with inr _ => pos < pos' | inl st => st <= 0 end).

Ltac q_scan_ret nx q tm off pos :=
  apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx q tm off pos); [cbv beta iota zeta delta [Q_scan fst snd]; split; [reflexivity|]; split; [psim_tac|]; split; [lia| lia]| | ].

#[using="STK RCW"] Lemma pr_ng_scan_blocks : forall fuel nx p tm off pos s i,
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> Z.of_nat (length d) < pos + Z.of_nat fuel ->
  usimS (RPP nx tm off pos) (ng_scan_blocks MOps PR_G fuel p) (ng_scan_blocks MOps PR_C fuel p) (PST (Q_scan p pos)).
Proof.
  induction fuel as [|fuel IH]; intros nx p tm off pos s i HPI HT HS HF.
  { exfalso. pose proof (pi_pos _ _ _ HPI). cbn in HF. lia. }
  cbn [ng_scan_blocks]. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_read_block (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx p tm off pos (DStack SiteBhdrNextPacket 0) HPI HT); cbn; lia|].
  intros rb p1 tm1 nx1 off1 pos1 (PK & LE & HRB) HPI1 HT1.
  destruct rb as [p1'|m p1'|c p1'].
  { subst p1'. q_scan_ret nx1 p1 tm1 off1 pos1; [exact HPI1| exact HT1]. }
  { destruct HRB as [-> _]. q_scan_ret nx1 (set_errbuf m p1) tm1 off1 pos1; [apply PI_set_errbuf; exact HPI1| exact HT1]. }
  destruct HRB as (-> & tl & TL & -> & CO & CR). cbv zeta. cbn beta iota.
  destruct (psim_ng p p1 s i (pkeep_psim _ _ PK) HS) as (s1 & i1 & HS1).
  assert (IHfuel : Z.of_nat (length d) < pos + tl + Z.of_nat fuel) by (rewrite Nat2Z.inj_succ in HF; lia).
  destruct (cur_block_type c =? BT_EPB).
  { destruct (get_from_block_data c 20) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI1| exact HT1].
    - q_scan_ret nx1 p1 tm1 off1 (pos + tl); [exact HPI1| exact HT1]. }
  destruct (cur_block_type c =? BT_SPB).
  { destruct (get_from_block_data c 4) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI1| exact HT1].
    - q_scan_ret nx1 p1 tm1 off1 (pos + tl); [exact HPI1| exact HT1]. }
  destruct (cur_block_type c =? BT_PB).
  { destruct (get_from_block_data c 20) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI1| exact HT1].
    - q_scan_ret nx1 p1 tm1 off1 (pos + tl); [exact HPI1| exact HT1]. }
  destruct (cur_block_type c =? BT_IDB).
  { destruct (get_from_block_data c 8) as [m|[off' c']] eqn:EG.
    - q_scan_ret nx1 (set_errbuf m p1) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI1| exact HT1].
    - apply gfbd_ok in EG as (G1 & -> & ->).
      set (p2 := if pc_swapped p1 then set_bufdata (swap_field 4 (cur_off c + 4) (swap_field 2 (cur_off c) (pc_bufdata p1))) p1 else p1).
      assert (HPI2 : PI p2 (pos + tl)) by (subst p2; destruct (pc_swapped p1); [apply PI_set_bufdata|]; exact HPI1).
      assert (HT2 : TML tm1 (toks p2)) by (subst p2; destruct (pc_swapped p1); exact HT1).
      assert (PK2 : pkeep p p2) by (subst p2; destruct (pc_swapped p1); [eapply pkeep_trans; [exact PK| apply pkeep_set_bufdata]| exact PK]).
      assert (HS2 : pc_priv p2 = PrivNg s i) by (destruct PK2 as [_ E]; rewrite E; exact HS).
      pose proof (pi_ng _ _ _ HPI) as NG. rewrite HS in NG. destruct NG as (N1 & N2 & _).
      destruct (negb (pc_linktype p2 =? _)).
      { q_scan_ret nx1 (set_errbuf (Msg.iface_type_differs (get_le16 (pc_bufdata p2) (cur_off c))) p2) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI2| exact HT2]. }
      destruct (negb (pc_snapshot p2 =? _)).
      { q_scan_ret nx1 (set_errbuf (Msg.iface_snaplen_differs (get_le32 (pc_bufdata p2) (cur_off c + 4))) p2) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI2| exact HT2]. }
      eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_add_interface nx1 p2 tm1 off1 (pos + tl) s i (cur_off c) _ HPI2 HT2 HS2); lia|].
      intros [[[ok c2] p3] m] p3' tm3 nx3 off3 pos3 (E3 & -> & PS3 & _) HPI3 HT3. cbn [fst snd] in E3. subst p3'. cbn beta iota.
      destruct ok.
      + destruct (psim_ng p p3 s i ltac:(psim_tac) HS) as (s3 & i3 & HS3).
        eapply (pp_post (CEG:=CEG) (CEC:=CEC) segs rc); [apply (IH nx3 p3 tm3 off3 (pos + tl) s3 i3 HPI3 HT3 HS3 IHfuel)|].
        intros [r q] p' pos' (A1 & A2 & A3 & A4) _. unfold Q_scan. cbn [fst snd] in *. split; [exact A1|]. split; [psim_tac|]. split; [lia| destruct r; lia].
      + q_scan_ret nx3 (set_errbuf m p3) tm3 off3 (pos + tl); [apply PI_set_errbuf; exact HPI3| exact HT3]. }
  destruct (cur_block_type c =? BT_SHB).
  { destruct (get_from_block_data c 16) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI1| exact HT1].
    - set (p2 := if pc_swapped p1 then set_bufdata (swap_field 2 (off' + 4) (swap_field 4 off' (pc_bufdata p1))) p1 else p1).
      assert (HPI2 : PI p2 (pos + tl)) by (subst p2; destruct (pc_swapped p1); [apply PI_set_bufdata|]; exact HPI1).
      assert (HT2 : TML tm1 (toks p2)) by (subst p2; destruct (pc_swapped p1); exact HT1).
      assert (PK2 : pkeep p p2) by (subst p2; destruct (pc_swapped p1); [eapply pkeep_trans; [exact PK| apply pkeep_set_bufdata]| exact PK]).
      assert (HS2 : pc_priv p2 = PrivNg s i) by (destruct PK2 as [_ E]; rewrite E; exact HS).
      destruct (get_le32 (pc_bufdata p2) off' =? BYTE_ORDER_MAGIC).
      + destruct (negb (get_le16 (pc_bufdata p2) (off' + 4) =? 1)).
        * q_scan_ret nx1 (set_errbuf (Msg.unknown_major (get_le16 (pc_bufdata p2) (off' + 4))) p2) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI2| exact HT2].
        * unfold ng_of, ng_ifaces_ptr_of. rewrite HS2.
          set (p3 := set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) 0 (ng_ifaces_size s) []) i p2).
          assert (HPI3 : PI p3 (pos + tl)).
          { pose proof HPI2 as [X1 X2 X3 X4 X5 X6]. rewrite HS2 in X6. destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5). constructor; cbn; auto. split; [lia|]. split; [lia|]. auto. }
          assert (HT3 : TML tm1 (toks p3)) by (unfold UPcapA.toks, psize, ifas in HT2 |- *; rewrite HS2 in HT2; cbn in HT2 |- *; exact HT2).
          eapply (pp_post (CEG:=CEG) (CEC:=CEC) segs rc); [apply (IH nx1 p3 tm1 off1 (pos + tl) _ i HPI3 HT3 eq_refl IHfuel)|].
          intros [r q] p' pos' (A1 & A2 & A3 & A4) _. unfold Q_scan. cbn [fst snd] in *. split; [exact A1|].
          split; [eapply psim_trans; [| exact A2]; eapply psim_trans; [apply pkeep_psim; exact PK2| apply (psim_set_ng _ _ _ _ _ HS2)]|].
          split; [lia| destruct r; lia].
      + destruct (get_le32 (pc_bufdata p2) off' =? BYTE_ORDER_MAGIC_SWAPPED).
        * q_scan_ret nx1 (set_errbuf Msg.sections_byte_order p2) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI2| exact HT2].
        * q_scan_ret nx1 (set_errbuf Msg.bad_byte_order_magic p2) tm1 off1 (pos + tl); [apply PI_set_errbuf; exact HPI2| exact HT2]. }
  eapply (pp_post (CEG:=CEG) (CEC:=CEC) segs rc); [apply (IH nx1 p1 tm1 off1 (pos + tl) s1 i1 HPI1 HT1 HS1 IHfuel)|].
  intros [r q] p' pos' (A1 & A2 & A3 & A4) _. unfold Q_scan. cbn [fst snd] in *. split; [exact A1|]. split; [psim_tac|]. split; [lia| destruct r; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="STK RCW"] Lemma pr_pcap_ng_next_packet fuel nx p tm off pos s i :
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> Z.of_nat (length d) < pos + Z.of_nat fuel ->
  usimS (RPP nx tm off pos) (pcap_ng_next_packet MOps PR_G fuel p) (pcap_ng_next_packet MOps PR_C fuel p) (PST (Q_next p pos)).
Proof.
  intros HPI HT HS HF. unfold pcap_ng_next_packet. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_ng_scan_blocks fuel nx p tm off pos s i HPI HT HS HF)|].
  intros [r p1] p1' tm1 nx1 off1 pos1 (E1 & PS1 & LE1 & PR1) HPI1 HT1. cbn [fst snd] in E1, PR1. subst p1'. cbn beta iota.
  assert (RET : forall st h q, psim p1 q -> PI q pos1 -> TML tm1 (toks q) -> (0 < st -> pos < pos1) ->
            usimS (RPP nx1 tm1 off1 pos1) (mret (st, h, q)) (mret (st, h, q)) (PST (Q_next p pos))).
  { intros st h q PSq HPIq HTq Hst. apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 q tm1 off1 pos1); [| exact HPIq| exact HTq].
    unfold Q_next. cbn [fst snd]. split; [reflexivity|]. split; [eapply psim_trans; [exact PS1| exact PSq]|]. split; [lia| exact Hst]. }
  destruct r as [status|f].
  { apply RET; [apply psim_refl| exact HPI1| exact HT1| intros; lia]. }
  cbv zeta.
  destruct (ng_ifcount (ng_of p1) <=? f_interface_id f).
  { apply RET; [apply psim_set_errbuf| apply PI_set_errbuf; exact HPI1| exact HT1| lia]. }
  destruct (pc_snapshot p1 <? f_caplen f).
  { apply RET; [apply psim_set_errbuf| apply PI_set_errbuf; exact HPI1| exact HT1| lia]. }
  destruct (get_from_block_data (f_cursor f) (f_caplen f)) as [m|[doff cx]].
  { apply RET; [apply psim_set_errbuf| apply PI_set_errbuf; exact HPI1| exact HT1| lia]. }
  match goal with |- context [let '(hdr, dd) := ?x in _] => destruct x as [hdr dd] end.
  apply RET; [apply psim_set_bufdata| apply PI_set_bufdata; exact HPI1| exact HT1| lia].
Qed.

#[using="STK RCW"] Lemma pr_next_packet_op fuel nx p tm off pos :
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel ->
  usimS (RPP nx tm off pos) (next_packet_op MOps PR_G fuel p) (next_packet_op MOps PR_C fuel p) (PST (Q_next p pos)).
Proof.
  intros HPI HT HF. unfold next_packet_op. destruct (pc_priv p) as [sf|s i] eqn:HS.
  - apply (pr_pcap_next_packet (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW nx p tm off pos sf HPI HT HS).
  - apply (pr_pcap_ng_next_packet fuel nx p tm off pos s i HPI HT HS HF).
Qed.

(* [comment removed for export] *)
Definition Q_rd (p : pcapT) (pos : Z) (r : Z * pcapT) (p' : pcapT) (pos' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ (0 < fst r -> pos < pos').

#[using="STK RCW"] Lemma pr_offline_read_1 fuel nx p tm off pos :
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel ->
  usimS (RPP nx tm off pos) (pcapint_offline_read_1 MOps PR_G fuel p) (pcapint_offline_read_1 MOps PR_C fuel p) (PST (Q_rd p pos)).
Proof.
  intros HPI HT HF. unfold pcapint_offline_read_1. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  destruct (negb (pc_break_loop p =? 0)).
  { apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx (set_break_loop 0 p) tm off pos); [| destruct HPI; constructor; cbn; auto| exact HT].
    unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [apply psim_set_break_loop|]. split; lia. }
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_next_packet_op fuel nx p tm off pos HPI HT HF)|].
  intros [[st h] p1] p1' tm1 nx1 off1 pos1 (E1 & PS1 & LE1 & PR1) HPI1 HT1. cbn [fst snd] in E1, PR1. subst p1'. cbn beta iota.
  destruct (st <? 0) eqn:E.
  { apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 p1 tm1 off1 pos1); [| exact HPI1| exact HT1]. unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [exact PS1|]. split; [lia| exact PR1]. }
  destruct (st =? 0) eqn:E0.
  { apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 p1 tm1 off1 pos1); [| exact HPI1| exact HT1]. unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [exact PS1|]. split; lia. }
  apply Z.ltb_ge in E. apply Z.eqb_neq in E0.
  apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 (set_header h p1) tm1 off1 pos1); [| apply PI_set_header; exact HPI1| exact HT1].
  unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [apply psim_header_r; exact PS1|]. split; [lia|]. intros _. apply PR1. lia.
Qed.

#[using="STK RCW"] Lemma pr_pcap_next_ex fuel nx p tm off pos :
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel ->
  usimS (RPP nx tm off pos) (pcap_next_ex MOps PR_G fuel p) (pcap_next_ex MOps PR_C fuel p) (PST (Q_rd p pos)).
Proof.
  intros HPI HT HF. unfold pcap_next_ex. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_offline_read_1 fuel nx p tm off pos HPI HT HF)|].
  intros [st p1] p1' tm1 nx1 off1 pos1 (E1 & PS1 & LE1 & PR1) HPI1 HT1. cbn [fst snd] in E1, PR1. subst p1'. cbn beta iota.
  apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 p1 tm1 off1 pos1); [| exact HPI1| exact HT1]. unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [exact PS1|]. split; [lia|].
  destruct (st =? 0) eqn:E0; [intros; lia| exact PR1].
Qed.

#[using="Type"] Lemma pr_pcap_stats nx p tm off pos :
  PI p pos -> TML tm (toks p) ->
  usimS (RPP nx tm off pos) (pcap_stats MOps p) (pcap_stats MOps p) (PST (Q_rd p pos)).
Proof.
  intros HPI HT. unfold pcap_stats. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx (set_errbuf Msg.stats_not_avail p) tm off pos); [| apply PI_set_errbuf; exact HPI| exact HT].
  unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [apply psim_set_errbuf|]. split; [lia| intros; lia].
Qed.

End ReadingC.

End WithCeil.
End UPcapC.

(* [comment removed for export] *)
Module UPcapD.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UStdio UFmt UDriver UPcapA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.UNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).
#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
Section ReadingD.
Variable segs : list Segment.
Variables (stkG stkC : stack_site -> Z).
Hypothesis STK : stk_ok stkG.
#[local] Notation npk := (npeek segs).
#[local] Notation usimS := (usim npk).
#[local] Notation RX := (UBase.RX (CEG:=CEG) (CEC:=CEC)).     (* [comment removed for export] *)
#[local] Notation RUK tm nx K C g W := (RX tm nx (UK nx K C g W)).
#[local] Notation PR_G := (prims fopsG fo_nop stkG).
#[local] Notation PR_C := (prims fopsC fo_nop stkC).
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
#[local] Notation B := (rc_B rc).
#[local] Notation Kx := (rc_Kx rc).
#[local] Notation F0 := (rc_F0 rc).
#[local] Notation hs := (rc_hs rc).
#[local] Notation Cc := (rc_C rc).
#[local] Notation oh := (rc_oh rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation KR_ := (KR_ rc).
#[local] Notation FR_ := (FR_ rc).
#[local] Notation PI := (PI rc).
#[local] Notation RPP := (RPP (CEG:=CEG) (CEC:=CEC) rc).
#[local] Notation PST := (PST (CEG:=CEG) (CEC:=CEC) rc).

(* [comment removed for export] *)
Ltac case_if E := lazymatch goal with |- usim _ _ (if ?c then _ else _) _ _ => destruct c eqn:E end.
Ltac case_ifb E := lazymatch goal with |- usim _ _ (mbind (if ?c then _ else _) _) _ _ => destruct c eqn:E end.

(* [comment removed for export] *)
Definition L0 : list (N * Z) := (fp, FILE_ALLOC) :: B.

#[using="RCW"] Lemma L0_len : zlen L0 <= 4.
Proof. unfold L0. rewrite zlen_cons. pose proof (rw_B _ RCW) as (BL & _). lia. Qed.
#[using="Type"] Lemma L0_R63N : R63N (map snd L0) = R63N (map snd B).
Proof. unfold L0. cbn [map snd]. rewrite R63N_cons, bigb_FILE. lia. Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma budget_pre tm L n :
  TML tm L -> zlen L + 1 <= 9 -> R63N (map snd L) <= R63N (map snd B) -> 0 <= n <= BUFMAX ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE /\ bigb n <= QMAX /\ PHI P9 + R63N (map snd L) + bigb n <= BLIVE.
Proof.
  intros HT HL HR Hn. pose proof (rw_B _ RCW) as [BL BR]. pose proof (bigb_le n ltac:(lia)) as BN.
  assert (X : PHI P9 + R63N (map snd L) + bigb n <= BLIVE).
  { rewrite PHI_P9. unfold BASEB, B26, BUFMAX, BLIVE, PGSZ in *. lia. }
  destruct (budget_of_TML tm L n HT HL ltac:(lia) X) as [R1 R2].
  split; [exact R1|]. split; [exact R2|]. split; [unfold QMAX, BUFMAX, PGSZ in *; lia| exact X].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="STK RCW"] Lemma pr_freadS nx L tm off pos site o n :
  TML tm L -> In (fp, FILE_ALLOC) L -> 0 <= pos <= Z.of_nat (length d) -> 0 <= o -> o + n <= 8192 -> 0 <= n < 2^40 ->
  usimS (RPP nx tm off pos) (e_fread PR_G fp (DStack site o) n) (e_fread PR_C fp (DStack site o) n)
        (eqpost (fun r => fun sG moG sC moC => exists off',
           (zlength r <= n /\ (zlength r < n -> pos + zlength r = Z.of_nat (length d)) /\ pos + zlength r <= Z.of_nat (length d) /\ r = dsl d pos (zlength r)) /\
           RPP nx tm off' (pos + zlength r) sG moG sC moC)).
Proof.
  intros HT HIn Hpos Ho Hon Hn. cbn [e_fread prims].
  eapply ru_bind2; [apply ru_get|]. intros a b. apply usim_pointwise. intros sG0 moG0 sC0 moC0 (-> & -> & EL & EO & HR0).
  destruct (STK site) as [S1 S2].
  eapply ru_pre; [| intros ? ? ? ? (-> & -> & -> & ->); exact HR0].
  unfold eval_rdest; cbn [fo_site fo_nop]. assert (D1 : 0 <= stkG site + o) by lia. assert (D2 : stkG site + o + n < 2^64) by lia.
  eapply ru_post; [apply (us_fread (CEG:=CEG) (CEC:=CEC) segs tm nx (KR_ off) Cc oh hs (FR_ off pos) fp (kat e0 off) d pos _ _ n (KR_in rc off) (own_kat rc RCW off) (rw_hs _ RCW) (FR_in rc off pos)
                          (TML_lookup _ _ _ _ HT HIn) ltac:(lia) D1 D2)|].
  intros r sG moG sC moC (off' & (Q1 & Q2 & Q3 & Q4 & Q5) & H). exists off'. rewrite (KR_kset rc RCW), (FR_fupd rc RCW) in H. split; [| exact H]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_open_common nx L tm off pos total :
  TML tm L -> zlen L + 2 <= 9 -> R63N (map snd L) <= R63N (map snd B) -> total = PCAP_SF_TOTAL \/ total = PCAP_NG_SF_TOTAL ->
  usimS (RPP nx tm off pos) (pcapint_open_offline_common MOps PR_G total) (pcapint_open_offline_common MOps PR_C total)
        (eqpost (fun r => fun sG moG sC moC => (r = inr nx /\ TML (<[nx := total]> tm) ((nx, total) :: L)) /\ RPP (N.succ nx) (<[nx := total]> tm) off pos sG moG sC moC)).
Proof.
  intros HT HL HR Htot. unfold pcapint_open_offline_common. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_calloc prims].
  assert (TT : 0 <= total < 2^20 /\ total * 1 < MMAP_THRESHOLD) by (unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL, MMAP_THRESHOLD in *; lia).
  destruct (budget_pre tm L 0 HT ltac:(lia) HR ltac:(unfold BUFMAX; lia)) as (_ & _ & _ & R4). rewrite bigb_small in R4 by (unfold MMAP_THRESHOLD; lia).
  eapply ru_bind.
  { eapply (gr_calloc (CEG:=CEG) (CEC:=CEC) segs tm L nx _ _ _ total 1 HT ltac:(lia) ltac:(lia) ltac:(lia) (proj2 TT)). lia. }
  intros r. apply usim_pure. intros [-> HT']. cbn beta iota. rewrite Z.mul_1_r in HT'.
  apply ru_ret. intros sG moG sC moC HR'. split; [split; [reflexivity| exact HT']|]. rewrite Z.mul_1_r in HR'. exact HR'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma max_snaplen_range lt : 1 <= max_snaplen_for_dlt lt <= 134217728.
Proof. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. destruct (lt =? DLT_DBUS); [lia|]. destruct (lt =? DLT_EBHSCR); [lia|]. destruct (lt =? DLT_USBPCAP); lia. Qed.
#[using="Type"] Lemma adjust_snapshot_range lt v : 0 <= v -> 1 <= pcapint_adjust_snapshot lt v <= INT_MAX.
Proof.
  intros Hv. unfold pcapint_adjust_snapshot. pose proof (max_snaplen_range lt).
  destruct ((v =? 0) || (INT_MAX <? v)) eqn:E.
  - unfold INT_MAX. lia.
  - apply orb_false_iff in E as [E1 E2]. apply Z.eqb_neq in E1. apply Z.ltb_ge in E2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Q_check (r : check_result) (tm' : gmap N Z) (pos' : Z) : Prop :=
  match r with
  | CH_Ok p => PI p pos' /\ TML tm' (toks p)
  | CH_Err m => (TML tm' L0 /\ 0 <= pos' <= Z.of_nat (length d)) /\ mok m
  | CH_NotMe => TML tm' L0 /\ 0 <= pos' <= Z.of_nat (length d)
  end.
Definition PSTc : check_result -> check_result -> @rel PS PS :=
  eqpost (fun r => fun sG moG sC moC => exists tm' nx' off' pos', Q_check r tm' pos' /\ RPP nx' tm' off' pos' sG moG sC moC).

#[using="Type"] Lemma pc_ret_notok nx tm off pos (r : check_result) :
  match r with CH_Ok _ => False | CH_Err m => mok m | CH_NotMe => True end -> TML tm L0 -> 0 <= pos <= Z.of_nat (length d) ->
  usimS (RPP nx tm off pos) (mret r) (mret r) PSTc.
Proof. intros Hr HT Hp. apply ru_ret. intros sG moG sC moC HR. exists tm, nx, off, pos. split; [| exact HR]. destruct r; [split; assumption| split; [split; assumption| exact Hr]| destruct Hr]. Qed.

#[using="STK RCW"] Lemma pr_pcap_check_header nx tm off pos magic precision :
  TML tm L0 -> 0 <= pos <= Z.of_nat (length d) ->
  usimS (RPP nx tm off pos) (pcap_check_header MOps PR_G magic fp precision) (pcap_check_header MOps PR_C magic fp precision) PSTc.
Proof.
  intros HT Hp. unfold pcap_check_header. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
  cbv zeta. lazymatch goal with |- usim _ _ (match ?x with _ => _ end) _ _ => destruct x as [[ok magic_int] swapped] end. cbv beta iota zeta.
  destruct (negb ok); [apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp]|].
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm off pos SitePcapHdrRest 0 20 HT ltac:(left; reflexivity) Hp); lia|]. intros r ? ? ? ? X; exact X. }
  intros rest. apply usim_exI; intros off1. apply usim_pure; intros (R1 & R2 & R3 & R4). pose proof (zlength_nonneg rest) as NR.
  assert (Hp1 : 0 <= pos + zlength rest <= Z.of_nat (length d)) by lia.
  destruct (negb (zlength rest =? 20)) eqn:E20.
  { eapply ru_bind; [apply (pr_read_fail_msg (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx); mok_tac|]. intros m. apply usim_pure; intros Mm. cbn beta. apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp1]. }
  apply negb_false_iff in E20. apply Z.eqb_eq in E20.
  assert (RB : bytes_ok rest) by (rewrite R4; apply dsl_bytes).
  cbv zeta.
  case_if EV; [apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp1]|].
  case_if ELT; [apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp1]|].
  eapply ru_bind.
  { eapply ru_post; [apply (pr_open_common nx L0 tm off1 (pos + zlength rest) PCAP_SF_TOTAL HT); [pose proof L0_len; lia| rewrite L0_R63N; lia| left; reflexivity]|].
    intros r ? ? ? ? X; exact X. }
  intros r. apply usim_pure. intros [-> HT1]. cbn beta iota. cbv zeta.
  match goal with |- context [match ?x with Some scale_type => _ | None => _ end] => destruct x as [scale_type|] end.
  2:{ (* [comment removed for export] *)
    destruct (budget_pre _ _ 0 HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (_ & _ & _ & X0).
    pose proof (bigb_nonneg 0) as B0.
    eapply ru_bind.
    { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ (N.succ nx) _ _ _ nx PCAP_SF_TOTAL HT1); [left; reflexivity| lia]. }
    intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2.
    apply pc_ret_notok; [first [exact I| mok_tac]| exact HT2| exact Hp1]. }
  match goal with |- context [let '(hdrsize, snapshot) := ?x in _] => destruct x as [hdrsize snapshot] eqn:EHS end. cbv zeta.
  (* [comment removed for export] *)
  assert (SNAP : 1 <= snapshot /\ (hdrsize = 16 \/ hdrsize = 24)).
  { assert (V : 0 <= (if swapped then bswap32 (get_le32 rest 12) else get_le32 rest 12)).
    { destruct swapped; [apply bswap32_range| apply get_le32_range; exact RB]. }
    pose proof (adjust_snapshot_range (linktype_to_dlt (Z.land (if swapped then bswap32 (get_le32 rest 16) else get_le32 rest 16) 65535)) _ V) as AR.
    destruct (magic_int =? KUZNETZOV_TCPDUMP_MAGIC).
    - injection EHS as E1 E2. subst hdrsize. split; [| right; reflexivity].
      destruct (_ =? DLT_EN10MB); [| subst snapshot; lia]. destruct (_ <=? INT_MAX - 14) eqn:E; subst snapshot; [lia| unfold INT_MAX; lia].
    - injection EHS as E1 E2. subst hdrsize snapshot. split; [lia| left; reflexivity]. }
  destruct SNAP as [SNAP HDR].
  set (bufsize := if 2048 <? snapshot then 2048 else snapshot).
  assert (BS : 1 <= bufsize <= 2048) by (subst bufsize; destruct (2048 <? snapshot) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; lia).
  destruct (budget_pre _ _ bufsize HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (Q1 & Q2 & Q3 & Q4).
  eapply ru_bind.
  { eapply (gr_malloc (CEG:=CEG) (CEC:=CEC) segs _ _ (N.succ nx) _ _ _ bufsize HT1); [pose proof L0_len; rewrite zlen_cons; lia| lia| exact Q3| exact Q4]. }
  intros r. apply usim_pure. intros [-> HT2]. cbn beta iota.
  apply ru_ret. intros sG moG sC moC HR. eexists _, _, _, (pos + zlength rest). split; [| exact HR]. cbn [Q_check]. split.
  - constructor; cbn; auto; [unfold BUFMAX; lia| unfold BUFMAX; lia].
  - unfold UPcapA.toks, psize, ifas, L0 in *. cbn. exact HT2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_ng_fail nx p tm off pos s i (m : list Z) :
  mok m -> PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i ->
  usimS (RPP nx tm off pos)
        (mbind (free_opt MOps PR_G (ng_ifaces_ptr_of p)) (fun _ => mbind (pfree fopsG (pc_buffer p)) (fun _ => mbind (pfree fopsG (pc_self p)) (fun _ => mret (CH_Err m)))))
        (mbind (free_opt MOps PR_C (ng_ifaces_ptr_of p)) (fun _ => mbind (pfree fopsC (pc_buffer p)) (fun _ => mbind (pfree fopsC (pc_self p)) (fun _ => mret (CH_Err m)))))
        PSTc.
Proof.
  intros Hm HPI HT HS. pose proof (TML_nodup _ _ HT) as ND. pose proof (pi_pos _ _ _ HPI) as Hp.
  assert (BUD : forall tm' L', TML tm' L' -> R63N (map snd L') <= R63N (map snd (toks p)) -> PHI P9 + R63N (map snd L') <= BLIVE).
  { intros tm' L' HT' HR'. destruct (RP_budget rc RCW p pos tm 0 HPI HT ltac:(unfold BUFMAX; lia)) as (_ & R2 & _).
    rewrite (R63N_perm _ _ (TML_sizes _ _ HT)) in R2. pose proof (bigb_nonneg 0). lia. }
  unfold ng_ifaces_ptr_of. rewrite HS. unfold UPcapA.toks, psize, ifas in HT, ND, BUD. rewrite HS in HT, ND, BUD. cbn [map fst app] in ND.
  (* [comment removed for export] *)
  assert (NE12 : pc_buffer p <> pc_self p) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; left; reflexivity).
  destruct i as [q|].
  - cbn [app] in *.
    assert (NE13 : pc_buffer p <> q) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; right; left; reflexivity).
    assert (NE23 : pc_self p <> q) by (inversion ND as [|? ? NI ND1]; subst; inversion ND1 as [|? ? NI2 ND2]; subst; intros E; apply NI2; rewrite E; left; reflexivity).
    unfold free_opt. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims].
    eapply ru_bind.
    { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ q _ HT); [right; right; left; reflexivity|]. apply (BUD _ _ HT). lia. }
    intros []. apply usim_pure. intros HT1. cbn [lrm] in HT1. rewrite (proj2 (N.eqb_neq _ _) NE13), (proj2 (N.eqb_neq _ _) NE23), N.eqb_refl in HT1.
    eapply ru_bind.
    { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ (pc_buffer p) _ HT1); [left; reflexivity|]. apply (BUD _ _ HT1). cbn [map snd]; rewrite !R63N_cons; pose proof (bigb_nonneg (ng_ifaces_size s * PCAP_NG_IF_SIZE)); lia. }
    intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2.
    eapply ru_bind.
    { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ (pc_self p) _ HT2); [left; reflexivity|]. apply (BUD _ _ HT2). cbn [map snd]; rewrite !R63N_cons; pose proof (bigb_nonneg (ng_ifaces_size s * PCAP_NG_IF_SIZE)); pose proof (bigb_nonneg (pc_bufalloc p)); lia. }
    intros []. apply usim_pure. intros HT3. rewrite lrm_head in HT3.
    apply pc_ret_notok; [first [exact I| mok_tac]| exact HT3| exact Hp].
  - cbn [app] in *. unfold free_opt. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims]. apply ru_bind_retl.
    eapply ru_bind.
    { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ (pc_buffer p) _ HT); [left; reflexivity|]. apply (BUD _ _ HT). lia. }
    intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2.
    eapply ru_bind.
    { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ (pc_self p) _ HT2); [left; reflexivity|]. apply (BUD _ _ HT2). cbn [map snd]; rewrite !R63N_cons; pose proof (bigb_nonneg (pc_bufalloc p)); lia. }
    intros []. apply usim_pure. intros HT3. rewrite lrm_head in HT3.
    apply pc_ret_notok; [first [exact I| mok_tac]| exact HT3| exact Hp].
Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_short_notme nx tm off pos :
  TML tm L0 -> 0 <= pos <= Z.of_nat (length d) ->
  usimS (RPP nx tm off pos)
        (mbind (e_ferror PR_G fp) (fun e : bool => if e then mbind (errmsg_for_errno MOps PR_G "error reading dump file" []) (fun m => mret (CH_Err m)) else mret CH_NotMe))
        (mbind (e_ferror PR_C fp) (fun e : bool => if e then mbind (errmsg_for_errno MOps PR_C "error reading dump file" []) (fun m => mret (CH_Err m)) else mret CH_NotMe))
        PSTc.
Proof.
  intros HT Hp. eapply ru_bind; [apply (pr_ferror (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx)|]. intros e. apply usim_pure. intros ->. apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp].
Qed.

#[using="Type"] Lemma MAX_BLOCKSIZE_range lt : 1 <= MAX_BLOCKSIZE_FOR_SNAPLEN (max_snaplen_for_dlt lt) <= BUFMAX.
Proof. unfold MAX_BLOCKSIZE_FOR_SNAPLEN, BUFMAX. pose proof (max_snaplen_range lt). lia. Qed.

#[using="STK RCW"] Lemma pr_pcap_ng_check_header fuel nx tm off pos magic precision :
  TML tm L0 -> 0 <= pos <= Z.of_nat (length d) -> Z.of_nat (length d) < Z.of_nat fuel ->
  usimS (RPP nx tm off pos) (pcap_ng_check_header MOps PR_G fuel magic fp precision) (pcap_ng_check_header MOps PR_C fuel magic fp precision) PSTc.
Proof.
  intros HT Hp HF. unfold pcap_ng_check_header. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims]. cbv zeta.
  case_if EM; [apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp]|].
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm off pos SiteNgTotalLength 0 4 HT ltac:(left; reflexivity) Hp); lia|]. intros r ? ? ? ? X; exact X. }
  intros tlb. apply usim_exI; intros off1. apply usim_pure; intros (T1 & T2 & T3 & T4). pose proof (zlength_nonneg tlb) as NT.
  assert (Hp1 : 0 <= pos + zlength tlb <= Z.of_nat (length d)) by lia.
  case_if ET4; [apply (pr_short_notme nx tm off1 _ HT Hp1)|]. apply Z.ltb_ge in ET4.
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm off1 _ SiteNgByteOrderMagic 0 4 HT ltac:(left; reflexivity) Hp1); lia|]. intros r ? ? ? ? X; exact X. }
  intros bomb. apply usim_exI; intros off2. apply usim_pure; intros (M1 & M2 & M3 & M4). pose proof (zlength_nonneg bomb) as NM.
  assert (Hp2 : 0 <= pos + zlength tlb + zlength bomb <= Z.of_nat (length d)) by lia.
  case_if EB4; [apply (pr_short_notme nx tm off2 _ HT Hp2)|]. apply Z.ltb_ge in EB4.
  cbv zeta. lazymatch goal with |- usim _ _ (match ?x with _ => _ end) _ _ => destruct x as [[ok swapped] TL] end. cbv beta iota zeta.
  case_if EOK; [apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp2]|].
  case_if ETL; [apply pc_ret_notok; [first [exact I| mok_tac]| exact HT| exact Hp2]|].
  apply orb_false_iff in ETL as [ETL1 ETL2]. apply Z.ltb_ge in ETL1. apply Z.ltb_ge in ETL2. unfold BT_SHB_INSANE_MAX in ETL2.
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (pr_open_common nx L0 tm off2 _ PCAP_NG_SF_TOTAL HT); [pose proof L0_len; lia| rewrite L0_R63N; lia| right; reflexivity]|]. intros r ? ? ? ? X; exact X. }
  intros r. apply usim_pure. intros [-> HT1]. cbn beta iota. cbv zeta.
  pose proof (budget_pre _ _ 0 HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (_ & _ & _ & X0).
  pose proof (bigb_nonneg 0) as B0.
  lazymatch goal with |- usim _ _ (match ?x with _ => _ end) _ _ => destruct x as [user|] end.
  2:{ eapply ru_bind.
      { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ (N.succ nx) _ _ _ nx PCAP_NG_SF_TOTAL HT1); [left; reflexivity| lia]. }
      intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2. apply pc_ret_notok; [first [exact I| mok_tac]| exact HT2| exact Hp2]. }
  cbv beta iota zeta.
  set (bufsize := if 2048 <? TL then TL else 2048).
  assert (BS : 2048 <= bufsize <= 1048576) by (subst bufsize; destruct (2048 <? TL) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; lia).
  destruct (budget_pre _ _ bufsize HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (Q1 & Q2 & Q3 & Q4).
  eapply ru_bind.
  { eapply (gr_malloc (CEG:=CEG) (CEC:=CEC) segs _ _ (N.succ nx) _ _ _ bufsize HT1); [pose proof L0_len; rewrite zlen_cons; lia| lia| exact Q3| exact Q4]. }
  intros r. apply usim_pure. intros [-> HT2]. cbn beta iota. cbv zeta.
  (* [comment removed for export] *)
  set (p0 := mkPcap nx fp bufsize bufsize (N.succ nx) (le_bytes 4 (le_of_bytes magic) ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC) swapped 0 0 0 0 0 precision 0 [] hdr0
               (PrivNg (mkNg user INITIAL_MAX_BLOCKSIZE 0 0 []) None) : pcapT).
  assert (HPI0 : PI p0 (pos + zlength tlb + zlength bomb)).
  { constructor; cbn; auto; try (unfold BUFMAX; lia). unfold IFSMAX, INITIAL_MAX_BLOCKSIZE, BUFMAX. repeat split; lia. }
  assert (HT0 : TML (<[N.succ nx:=bufsize]> (<[nx:=PCAP_NG_SF_TOTAL]> tm)) (toks p0)) by (unfold UPcapA.toks, psize, ifas, L0 in *; cbn; exact HT2).
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_read_bytes (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW _ p0 _ off2 _ (DHeap (N.succ nx) 12) (TL - 12) true HPI0 HT0); [cbn; lia| lia]|].
  intros [st data] p1 tm3 nx3 off3 pos3 (-> & LB & -> & ST & CT) HPI3 HT3. cbn [fst snd] in LB, ST, CT. cbn beta iota. cbv zeta.
  set (p0' := set_bufdata (pc_bufdata p0 ++ data) p0).
  assert (HPI0' : PI p0' (pos + zlength tlb + zlength bomb + zlength data)) by (apply PI_set_bufdata; exact HPI3).
  assert (HT0' : TML tm3 (toks p0')) by exact HT3.
  destruct st as [| |m].
  2:{ apply (pr_ng_fail nx3 p0' tm3 off3 _ _ None [] mok_nil HPI0' HT0' eq_refl). }
  2:{ apply (pr_ng_fail nx3 p0' tm3 off3 _ _ None m ST HPI0' HT0' eq_refl). }
  set (p0'' := if swapped then set_bufdata (swap_field 2 14 (swap_field 2 12 (pc_bufdata p0'))) p0' else p0').
  assert (HPI0'' : PI p0'' (pos + zlength tlb + zlength bomb + zlength data)) by (subst p0''; destruct swapped; [apply PI_set_bufdata|]; exact HPI0').
  assert (HT0'' : TML tm3 (toks p0'')) by (subst p0''; destruct swapped; exact HT0').
  assert (HS0'' : pc_priv p0'' = pc_priv p0) by (subst p0'' p0'; destruct swapped; reflexivity).
  case_if EVER; [eapply (pr_ng_fail nx3 p0'' tm3 off3 (pos + zlength tlb + zlength bomb + zlength data) _ None); [mok_tac| exact HPI0''| exact HT0''| exact HS0'']|].
  match goal with |- usim _ _ (mbind (ng_find_idb _ _ _ ?q) _) _ _ => set (p2 := q) end.
  assert (HS2 : pc_priv p2 = PrivNg (mkNg user INITIAL_MAX_BLOCKSIZE 0 0 []) None) by (subst p2 p0'' p0' p0; destruct swapped; reflexivity).
  assert (HPI2 : PI p2 (pos + zlength tlb + zlength bomb + zlength data)).
  { pose proof HPI0'' as [X1 X2 X3 X4 X5 X6]. subst p2 p0'' p0' p0. destruct swapped; cbn in X2, X3, X4, X6; constructor; cbn; auto. }
  assert (HT2' : TML tm3 (toks p2)) by exact HT0''.
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_ng_find_idb segs stkG stkC STK rc RCW fuel nx3 p2 tm3 off3 _ _ None HPI2 HT2' HS2); pose proof (zlength_nonneg data); lia|].
  intros [r p3] p3' tm4 nx4 off4 pos4 (E4 & PS4 & LE4 & MM4) HPI4 HT4. cbn [fst snd] in E4, MM4. subst p3'. cbn beta iota.
  destruct (psim_ng p2 p3 _ None PS4 HS2) as (s4 & i4 & HS4).
  destruct r as [m|idb_off].
  { apply (pr_ng_fail nx4 p3 tm4 off4 _ _ _ m MM4 HPI4 HT4 HS4). }
  cbv zeta. unfold ng_of, ng_ifaces_ptr_of. rewrite HS4.
  apply ru_ret. intros sG moG sC moC HR. eexists tm4, nx4, off4, pos4. split; [| exact HR]. cbn [Q_check].
  pose proof HPI4 as [X1 X2 X3 X4 X5 X6]. rewrite HS4 in X6. destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5).
  pose proof (MAX_BLOCKSIZE_range (linktype_to_dlt (get_le16 (pc_bufdata p3) idb_off))) as MB.
  split.
  - destruct (ng_max_blocksize s4 <? _); constructor; cbn; auto; repeat split; auto; lia.
  - unfold UPcapA.toks, psize, ifas in HT4 |- *. rewrite HS4 in HT4. cbn in HT4 |- *. destruct (ng_max_blocksize s4 <? _); exact HT4.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_open (r : list Z + pcapT) (tm' : gmap N Z) (pos' : Z) : Prop :=
  match r with
  | inr p => PI p pos' /\ TML tm' (toks p)
  | inl m => (TML tm' L0 /\ 0 <= pos' <= Z.of_nat (length d)) /\ mok m
  end.
Definition PSTo : (list Z + pcapT) -> (list Z + pcapT) -> @rel PS PS :=
  eqpost (fun r => fun sG moG sC moC => exists tm' nx' off' pos', Q_open r tm' pos' /\ RPP nx' tm' off' pos' sG moG sC moC).

#[using="STK RCW"] Lemma pr_fopen_offline fuel nx tm off precision :
  TML tm L0 -> Z.of_nat (length d) < Z.of_nat fuel ->
  usimS (RPP nx tm off 0) (pcap_fopen_offline_with_tstamp_precision MOps PR_G fuel fp precision)
        (pcap_fopen_offline_with_tstamp_precision MOps PR_C fuel fp precision) PSTo.
Proof.
  intros HT HF. unfold pcap_fopen_offline_with_tstamp_precision. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fileno prims].
  assert (Hp : 0 <= 0 <= Z.of_nat (length d)) by lia.
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm off 0 SiteMagic 0 4 HT ltac:(left; reflexivity) Hp); lia|]. intros r ? ? ? ? X; exact X. }
  intros magic. apply usim_exI; intros off1. apply usim_pure; intros (G1 & G2 & G3 & G4). pose proof (zlength_nonneg magic) as NM. rewrite Z.add_0_l in *.
  assert (Hp1 : 0 <= zlength magic <= Z.of_nat (length d)) by lia.
  case_if E4.
  { eapply ru_bind; [apply (pr_read_fail_msg (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx); mok_tac|]. intros m. apply usim_pure; intros Mm. cbn beta.
    apply ru_ret. intros sG moG sC moC HR. exists tm, nx, off1, (zlength magic). split; [| exact HR]. cbn. auto. }
  (* [comment removed for export] *)
  assert (FIN : forall (r : check_result) nx' tm' off' pos', Q_check r tm' pos' ->
            usimS (RPP nx' tm' off' pos')
                  (match r with CH_NotMe => mret (inl Msg.unknown_file_format) | CH_Err m => mret (inl m) | CH_Ok p => mbind (s_fileno fopsG fp) (fun _ => mret (inr p)) end)
                  (match r with CH_NotMe => mret (inl Msg.unknown_file_format) | CH_Err m => mret (inl m) | CH_Ok p => mbind (s_fileno fopsC fp) (fun _ => mret (inr p)) end)
                  PSTo).
  { intros [|m|p] nx' tm' off' pos' Q; cbn in Q.
    - apply ru_ret. intros sG moG sC moC HR. exists tm', nx', off', pos'. split; [| exact HR]. split; [exact Q| mok_tac].
    - apply ru_ret. intros sG moG sC moC HR. exists tm', nx', off', pos'. split; [exact Q| exact HR].
    - eapply ru_bind; [apply (pr_fileno (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx')|]. intros fd. apply usim_pure. intros _.
      apply ru_ret. intros sG moG sC moC HR. exists tm', nx', off', pos'. split; [exact Q| exact HR]. }
  eapply ru_bind; [apply (pr_pcap_check_header nx tm off1 (zlength magic) magic precision HT Hp1)|].
  intros r1. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros off2. apply usim_exI; intros pos1. apply usim_pure; intros Q1.
  destruct r1 as [|m|p]; [| apply (FIN (CH_Err m) _ _ _ _ Q1)| apply (FIN (CH_Ok p) _ _ _ _ Q1)].
  cbn in Q1. destruct Q1 as [HT1 Hp2].
  eapply ru_bind; [apply (pr_pcap_ng_check_header fuel nx1 tm1 off2 pos1 magic precision HT1 Hp2 HF)|].
  intros r2. apply usim_exI; intros tm2. apply usim_exI; intros nx2. apply usim_exI; intros off3. apply usim_exI; intros pos2. apply usim_pure; intros Q2.
  apply (FIN r2 _ _ _ _ Q2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RCL (tm : gmap N Z) (nx : N) : @rel PS PS :=
  RUK tm nx Kx ((k_path e0, d) :: Cc) idl (WF oh (hrem fp hs) F0).

#[using="RCW"] Lemma kdel_KR off : kdel (k_fd e0) (KR_ off) = Kx.
Proof.
  unfold UPcapA.KR_, kdel. rewrite filter_app. cbn [List.filter]. replace (k_fd (kat e0 off)) with (k_fd e0) by (destruct e0; reflexivity). rewrite Z.eqb_refl. cbn.
  rewrite app_nil_r. apply forallb_filter_id. rewrite forallb_forall. intros x Hx. destruct (Z.eqb_spec (k_fd x) (k_fd e0)) as [E|NE]; [exfalso; exact (rw_Kx _ RCW x Hx E)| reflexivity].
Qed.
#[using="RCW"] Lemma fdel_FR off pos : fdel fp (FR_ off pos) = F0.
Proof. unfold UPcapA.FR_, fdel. cbn [List.filter fst]. rewrite N.eqb_refl. cbn. apply (fdel_notin fp F0). exact (rw_F0 _ RCW). Qed.
#[using="Type"] Lemma kpath_kat off : k_path (kat e0 off) = k_path e0.
Proof. destruct e0; reflexivity. Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_fclose_buf nx tm off pos buf ba self ps :
  TML tm ((buf, ba) :: (self, ps) :: (fp, FILE_ALLOC) :: B) -> 0 <= pos <= Z.of_nat (length d) -> 0 <= ba <= BUFMAX -> 0 <= ps < MMAP_THRESHOLD ->
  usimS (RPP nx tm off pos) (mbind (s_fclose fopsG fp) (fun _ => pfree fopsG buf)) (mbind (s_fclose fopsC fp) (fun _ => pfree fopsC buf))
        (eqpost (fun _ => fun sG moG sC moC => TML (delete buf (delete fp tm)) ((self, ps) :: B) /\ RCL (delete buf (delete fp tm)) nx sG moG sC moC)).
Proof.
  intros HT Hp Hba Hps. pose proof (TML_nodup _ _ HT) as ND. cbn [map fst] in ND.
  assert (NE1 : buf <> fp) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; right; left; reflexivity).
  assert (NE2 : self <> fp) by (inversion ND as [|? ? NI ND1]; subst; inversion ND1 as [|? ? NI2 ND2]; subst; intros E; apply NI2; rewrite E; left; reflexivity).
  pose proof (rw_B _ RCW) as [BL BR]. pose proof (bigb_le ba ltac:(lia)) as BB.
  assert (BUD : PHI P9 + R63N (sizes tm) <= BLIVE).
  { rewrite (R63N_perm _ _ (TML_sizes _ _ HT)). cbn [map snd]. rewrite !R63N_cons, bigb_FILE, (bigb_small ps) by lia. rewrite PHI_P9. unfold BASEB, B26, BUFMAX, BLIVE, PGSZ in *. lia. }
  eapply ru_bind.
  { apply (us_fclose_r (CEG:=CEG) (CEC:=CEC) segs tm nx (KR_ off) Cc oh hs (FR_ off pos) fp (kat e0 off) d pos FILE_ALLOC (KR_in rc off) (own_kat rc RCW off) (rw_hs _ RCW) (FR_in rc off pos) (rw_oh _ RCW)
                               (TML_lookup _ _ _ _ HT ltac:(right; right; left; reflexivity)) BUD). }
  intros []. rewrite kdel_KR, fdel_FR, kpath_kat.
  pose proof (TML_delete _ _ _ _ HT ltac:(right; right; left; reflexivity)) as HT1. cbn [lrm] in HT1.
  rewrite (proj2 (N.eqb_neq _ _) NE1), (proj2 (N.eqb_neq _ _) NE2), N.eqb_refl in HT1.
  eapply ru_post; [eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ buf ba HT1); [left; reflexivity|]|].
  - rewrite (R63N_perm _ _ (TML_sizes _ _ HT)) in BUD. cbn [map snd] in BUD |- *. rewrite ?R63N_cons in BUD. rewrite ?R63N_cons in BUD. rewrite ?R63N_cons. rewrite bigb_FILE in BUD. lia.
  - intros [] ? ? ? ? [X Y]. rewrite lrm_head in X. exact (conj X Y).
Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_free_self nx tm self ps :
  TML tm ((self, ps) :: B) -> 0 <= ps < MMAP_THRESHOLD ->
  usimS (RCL tm nx) (pfree fopsG self) (pfree fopsC self)
        (eqpost (fun _ => fun sG moG sC moC => exists tm', TML tm' B /\ RCL tm' nx sG moG sC moC)).
Proof.
  intros HT Hps. pose proof (rw_B _ RCW) as [BL BR].
  eapply ru_post; [eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ self ps HT); [left; reflexivity|]|].
  - cbn [map snd]. rewrite R63N_cons, (bigb_small ps) by lia. rewrite PHI_P9. unfold BASEB, B26, BLIVE, PGSZ in *. lia.
  - intros [] ? ? ? ? [X Y]. rewrite lrm_head in X. exists (delete self tm). exact (conj X Y).
Qed.

#[using="RCW"] Lemma pr_pcap_close nx p tm off pos :
  PI p pos -> TML tm (toks p) ->
  usimS (RPP nx tm off pos) (pcap_close MOps PR_G p) (pcap_close MOps PR_C p)
        (eqpost (fun _ => fun sG moG sC moC => exists tm', TML tm' B /\ RCL tm' nx sG moG sC moC)).
Proof.
  intros HPI HT. pose proof HPI as [P1 P2 P3 P4 P5 P6].
  unfold pcap_close, pcap_ng_cleanup, pcapint_sf_cleanup. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free e_fclose prims]. rewrite P4.
  unfold UPcapA.toks, psize, ifas in HT. destruct (pc_priv p) as [sf|s [q|]] eqn:HS; cbn [app] in HT.
  - eapply ru_bind; [apply (pr_fclose_buf nx tm off pos _ _ _ _ HT P1 ltac:(lia)); unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia|].
    intros []. apply usim_pure. intros HT1. apply (pr_free_self nx _ _ _ HT1). unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia.
  - (* [comment removed for export] *)
    pose proof (TML_nodup _ _ HT) as ND. cbn [map fst] in ND.
    assert (NE13 : pc_buffer p <> q) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; right; left; reflexivity).
    assert (NE23 : pc_self p <> q) by (inversion ND as [|? ? NI ND1]; subst; inversion ND1 as [|? ? NI2 ND2]; subst; intros E; apply NI2; rewrite E; left; reflexivity).
    eapply ru_bind.
    + eapply ru_bind.
      * unfold free_opt, ng_ifaces_ptr_of. rewrite HS. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims].
        eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx _ _ _ q _ HT); [right; right; left; reflexivity|].
        destruct (RP_budget rc RCW p pos tm 0 HPI ltac:(unfold UPcapA.toks, psize, ifas; rewrite HS; exact HT) ltac:(unfold BUFMAX; lia)) as (_ & R2 & _).
        rewrite (R63N_perm _ _ (TML_sizes _ _ HT)) in R2. pose proof (bigb_nonneg 0). lia.
      * intros []. apply usim_pure. intros HT1. cbn [lrm] in HT1. rewrite (proj2 (N.eqb_neq _ _) NE13), (proj2 (N.eqb_neq _ _) NE23), N.eqb_refl in HT1.
        apply (pr_fclose_buf nx _ off pos _ _ _ _ HT1 P1 ltac:(lia)). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
    + intros []. apply usim_pure. intros HT2. apply (pr_free_self nx _ _ _ HT2). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
  - (* [comment removed for export] *)
    eapply ru_bind.
    + unfold free_opt, ng_ifaces_ptr_of. rewrite HS. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. apply ru_bind_retl.
      apply (pr_fclose_buf nx tm off pos _ _ _ _ HT P1 ltac:(lia)). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
    + intros []. apply usim_pure. intros HT2. apply (pr_free_self nx _ _ _ HT2). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
Qed.

End ReadingD.

End WithCeil.
End UPcapD.

(* [comment removed for export] *)
Module UMain.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes RelSpec RelSpecMm Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.KPin OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapDrive HeapSim NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UStdio UDriver. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.UNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UDriver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).
#[local] Notation idl := (fun l : libc_st hptr => l).

(* [comment removed for export] *)
Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
#[using="Type"] Lemma FI_main {CE : CEIL} segs lim en inp tb t mo nx :
  startup_mo segs lim en inp tb t mo -> FI nx [] [] libc_init mo.
Proof.
  intros (_ & EF & _). apply FI_init; rewrite EF; unfold mo0; rewrite m_fds_init_model.
  - cbn. assert (D : forall a b, Z_to_bv 64 a = Z_to_bv 64 b -> 0 <= a < 3 -> 0 <= b < 3 -> a = b).
    { intros a b E Ha Hb. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E. }
    constructor. { intros [H|[H|[]]]; [pose proof (D _ _ H ltac:(lia) ltac:(lia))| pose proof (D _ _ H ltac:(lia) ltac:(lia))]; lia. }
    constructor. { intros [H|[]]. pose proof (D _ _ H ltac:(lia) ltac:(lia)). lia. }
    constructor. { intros []. } constructor.
  - intros k en0 Hin. cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; eexists; (split; [reflexivity| rewrite unsigned_lit by lia; lia]).
Qed.

Section UMain.
Variables (segsG segsC : list Segment) (limG limC : Z) (enG enC : ExecEntry) (inp : ProcInput).
Variables (tbG tbC : Z) (stkG stkC : stack_site -> Z).
Hypothesis IOG : image_ok segsG limG.
Hypothesis IOC : image_ok segsC limC.
Hypothesis BRKG : valid_brk segsG (en_brk enG).
Hypothesis BRKC : valid_brk segsC (en_brk enC).
Hypothesis TLSG : tls_in_image segsG tbG.
Hypothesis TLSC : tls_in_image segsC tbC.
(* [comment removed for export] *)
Hypothesis VIN : valid_input inp.
Hypothesis CEQG : alloc_ceiling (CEIL:=CEG) = page_round_down_Z (alloc_top (m_vmmaps (mo0 segsG limG enG inp))).
Hypothesis CEQC : alloc_ceiling (CEIL:=CEC) = page_round_down_Z (alloc_top (m_vmmaps (mo0 segsC limC enC inp))).
Variables (secG secC : Z).
Hypothesis SECG : 0 <= secG < 2^64.
Hypothesis SECC : 0 <= secC < 2^64.

#[local] Notation npk := (npeek segsC).
#[local] Notation usimS := (usim npk).
#[local] Notation RX := (UBase.RX (CEG:=CEG) (CEC:=CEC)).     (* [comment removed for export] *)
#[local] Notation RUK tm nx K C g W := (RX tm nx (UK nx K C g W)).
#[local] Notation W0 := (WF None [] []).
#[local] Notation moG0 := (mo0 segsG limG enG inp).
#[local] Notation moC0 := (mo0 segsC limC enC inp).
#[local] Notation INIT := (INIT segsG segsC limG limC enG enC inp secG secC).

(* [comment removed for export] *)
Hypothesis us_run : forall tm nx config payload,
  zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> zlength payload < MAX_INPUT ->
  usimS (RUK tm nx [] [] idl W0) (Prog.run fopsG fo_nop stkG config payload) (Prog.run fopsC fo_nop stkC config payload)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx' K' C' oh' hs' F',
                   EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K' /\
                   RUK tm' nx' K' C' idl (WF oh' hs' F') sG moG sC moC)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="VIN"] Lemma startup_etwf (s : PS) :
  etwf (startup_model (set_tls_pin fopsG) tbG s) moG0 (fun _ _ => True).
Proof.
  unfold startup_model, mbind, msys, mupd, mret. apply etwf_ebind. apply etwf_ret. cbn [fst snd].
  apply etwf_ebind. apply etwf_enode; [exact I|].
  intros rsp2 mo2 evs2 Hst2.
  pose proof (mo0_minv segsG limG enG inp VIN) as MI0.
  destruct (nstep_dec_set_tid moG0 _ mo2 evs2 MI0 Hst2) as (_ & t' & Hd & _). rewrite Hd. eexists. split; [reflexivity|]. exact I.
Qed.

#[using="IOG IOC BRKG BRKC TLSG TLSC VIN CEQG CEQC SECG SECC"] Theorem us_startup :
  usimS INIT (startup_model (set_tls_pin fopsG) tbG) (startup_model (set_tls_pin fopsC) tbC) (fun _ _ => RUK ∅ 0%N [] [] idl W0).
Proof.
  apply usim_of_parts.
  - intros sG moG sC moC HI. destruct (cg_startup (CEG:=CEG) (CEC:=CEC) segsG segsC limG limC enG enC inp tbG tbC IOG IOC BRKG BRKC TLSG TLSC VIN CEQG CEQC secG secC SECG SECC sG moG sC moC HI) as [HP HE].
    split; [| exact HE]. intros trG a sG' moG' Hp. eapply wreach_mono; [exact (HP trG a sG' moG' Hp)|].
    intros tr r mo' (b & sC' & -> & -> & HR). exists b, sC'. split; [reflexivity|]. split; [reflexivity|].
    destruct HI as (-> & -> & -> & ->).
    destruct (startup_tpath (CE:=CEG) (set_tls_pin fopsG) segsG limG enG inp tbG TLSG VIN CEQG (sG0 segsG secG) trG _ moG' Hp)
      as (tbG' & t & E & _ & _ & _ & SMG).
    injection E as Es. subst sG'. split; [exact HR|]. split.
    + cbn [ps_libc set_tls_pin set_tls set_heap ps_init sG0]. exact (FI_main _ _ _ _ _ _ _ 0%N SMG).
    + split; [reflexivity|]. split; [constructor|]. split; [intros ? []| intros ? ? ? []].
  - intros sG moG sC moC (-> & -> & -> & ->). apply startup_etwf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="IOG IOC BRKG BRKC TLSG TLSC VIN CEQG CEQC SECG SECC us_run"] Theorem us_prog argv :
  Forall (fun a => zlength a <= ARGMAX) argv ->
  usimS INIT (prog fopsG tbG fo_nop stkG argv) (prog fopsC tbC fo_nop stkC argv) (fun _ _ => INIT).
Proof.
  intros Hargv. unfold prog.
  eapply usim_bind; [exact (npk_inh segsC)| apply us_startup|]. intros [] [].
  eapply usim_bind; [exact (npk_inh segsC)| apply (us_main_prog segsC stkG stkC us_run 0%N argv Hargv)|]. intros codeG codeC.
  apply usim_pure; intros <-.
  apply usim_exI; intros tm'. apply usim_exI; intros nx'. apply usim_exI; intros K'. apply usim_exI; intros C'.
  apply usim_exI; intros oh'. apply usim_exI; intros hs'. apply usim_exI; intros F'.
  apply usim_pure; intros XK. apply (us_exit_model segsC). exact XK.
Qed.

(* [comment removed for export] *)
#[using="CEC segsC limC enC tbC stkC IOG IOC BRKG BRKC TLSG TLSC VIN CEQG CEQC secC SECG SECC us_run"] Theorem prog_model_ok argv :
  Forall (fun a => zlength a <= ARGMAX) (argv_Z argv) ->
  leaves_unreachable_m nstep (prog_itree fopsG tbG (fheap_init secG (reservedZ segsG)) fo_nop stkG argv) moG0
  /\ tsafe nstep nsafe (prog_itree fopsG tbG (fheap_init secG (reservedZ segsG)) fo_nop stkG argv) moG0.
Proof.
  intros Hargv. unfold prog_itree. apply etwf_leaves. apply etwf_ebind.
  pose proof (usim_usafe _ _ _ _ _ (us_prog (argv_Z argv) Hargv) (sG0 segsG secG) moG0 (sC0 segsC secC) moC0 ltac:(repeat split; reflexivity)) as HS.
  eapply etwf_mono; [exact HS|]. intros [[] ?] mo1 _.
Qed.

End UMain.

End WithCeil.
End UMain.

(* [comment removed for export] *)
Module EquivMain.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull StdioCore Stdio StartupFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase UStdio UDriver. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UMain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).

(* [comment removed for export] *)
Lemma valid_input_argv inp : valid_input inp -> Forall (fun a => zlength a <= ARGMAX) (argv_Z (in_argv inp)).
Proof.
  intros (HA & _). destruct HA as (_ & _ & HL & _). unfold argv_Z. apply Forall_map. eapply Forall_impl; [| exact HL].
  cbn. intros a Ha. unfold zlength, ARGMAX. rewrite length_map. lia.
Qed.

Section Main.
Variables (segsS : list Segment) (pcS : N) (phS : PhdrInfo).
Variables (segsT : list Segment) (pcT : N) (phT : PhdrInfo).
Variables (tbS tbT : ExecEntry -> Z) (stkS stkT : ExecEntry -> stack_site -> Z).
(* [comment removed for export] *)
Variables (secS secT : ExecEntry -> Z).
Hypothesis SECS : forall en, 0 <= secS en < 2^64.
Hypothesis SECT : forall en, 0 <= secT en < 2^64.

#[local] Notation treeS := (treeS segsS tbS stkS secS).
#[local] Notation treeT := (treeT segsT tbT stkT secT).

(* [comment removed for export] *)
Variables (limS limT : Z).
Hypothesis IOS : image_ok segsS limS.
Hypothesis IOT : image_ok segsT limT.
Hypothesis TLSS : forall en inp, valid_entry (mkImage segsS pcS phS) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsS (tbS en).
Hypothesis TLST : forall en inp, valid_entry (mkImage segsT pcT phT) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsT (tbT en).

(* [comment removed for export] *)
Definition run_contract_u (segsC : list Segment) (stkG stkC : stack_site -> Z) : Prop :=
  forall (CEG CEC : CEIL) tm nx config payload,
    zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> zlength payload < MAX_INPUT ->
    usim (npeek segsC) (RX (CEG:=CEG) (CEC:=CEC) tm nx (UK nx [] [] idl (WF None [] [])))
         (Prog.run (full_ops (CE:=CEG)) fo_nop stkG config payload) (Prog.run (full_ops (CE:=CEC)) fo_nop stkC config payload)
         (eqpost (fun _ => fun sG moG sC moC => exists tm' nx' K' C' oh' hs' F',
                    EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K' /\
                    RX (CEG:=CEG) (CEC:=CEC) tm' nx' (UK nx' K' C' idl (WF oh' hs' F')) sG moG sC moC)).
(* [comment removed for export] *)
Definition stk_ok (stk : stack_site -> Z) : Prop := forall site, 0 <= stk site /\ stk site + 8192 < 2^64.
Hypothesis STKS : forall en, stk_ok (stkS en).
Hypothesis STKT : forall en, stk_ok (stkT en).
(* [comment removed for export] *)
Hypothesis RUN : forall segsC stkG stkC, stk_ok stkG -> run_contract_u segsC stkG stkC.

(* [comment removed for export] *)
Hypothesis IMPL_S : exists QS, forall en inp, valid_entry (mkImage segsS pcS phS) en inp -> valid_input inp ->
  impl segsS (at_node segsS) (npeek segsS) (treeS inp en) QS (ms0 segsS pcS phS en inp).
Hypothesis IMPL_T : exists QT, forall en inp, valid_entry (mkImage segsT pcT phT) en inp -> valid_input inp ->
  impl segsT (at_node segsT) (npeek segsT) (treeT inp en) QT (ms0 segsT pcT phT en inp).

(* [comment removed for export] *)

#[using="SECS SECT IOS IOT TLSS TLST STKS STKT RUN"] Theorem route_abs_trees_equiv_u : trees_equiv_lim limS limT segsS pcS phS segsT pcT phT treeS treeT.
Proof.
  apply trees_equiv_lim_of_wexit. intros enS enT inp HvS HvT Hvi. split; intros full Hx.
  - eapply (prog_texit_wexit (CEG:=ceil_of_sp (en_sp enS)) (CEC:=ceil_of_sp (en_sp enT)) segsT
              (INIT segsS segsT limS limT enS enT inp (secS enS) (secT enT))).
    + exact (usim_fsimw _ _ _ _ _
               (us_prog (CEG:=ceil_of_sp (en_sp enS)) (CEC:=ceil_of_sp (en_sp enT))
                  segsS segsT limS limT enS enT inp (tbS enS) (tbT enT) (stkS enS) (stkT enT)
                  IOS IOT (valid_entry_brk _ _ _ _ _ HvS) (valid_entry_brk _ _ _ _ _ HvT) (TLSS _ _ HvS) (TLST _ _ HvT)
                  Hvi (mo0_ceil_valid _ _ _ _ _ _ Hvi HvS) (mo0_ceil_valid _ _ _ _ _ _ Hvi HvT)
                  (secS enS) (secT enT) (SECS enS) (SECT enT) (RUN _ _ _ (STKS enS) _ _) (argv_Z (in_argv inp)) (valid_input_argv _ Hvi))).
    + repeat split; reflexivity.
    + exact Hx.
  - eapply (prog_texit_wexit (CEG:=ceil_of_sp (en_sp enT)) (CEC:=ceil_of_sp (en_sp enS)) segsS
              (INIT segsT segsS limT limS enT enS inp (secT enT) (secS enS))).
    + exact (usim_fsimw _ _ _ _ _
               (us_prog (CEG:=ceil_of_sp (en_sp enT)) (CEC:=ceil_of_sp (en_sp enS))
                  segsT segsS limT limS enT enS inp (tbT enT) (tbS enS) (stkT enT) (stkS enS)
                  IOT IOS (valid_entry_brk _ _ _ _ _ HvT) (valid_entry_brk _ _ _ _ _ HvS) (TLST _ _ HvT) (TLSS _ _ HvS)
                  Hvi (mo0_ceil_valid _ _ _ _ _ _ Hvi HvT) (mo0_ceil_valid _ _ _ _ _ _ Hvi HvS)
                  (secT enT) (secS enS) (SECT enT) (SECS enS) (RUN _ _ _ (STKT enT) _ _) (argv_Z (in_argv inp)) (valid_input_argv _ Hvi))).
    + repeat split; reflexivity.
    + exact Hx.
Qed.

(* [comment removed for export] *)
#[using="SECS IOS TLSS STKS RUN IMPL_S"] Theorem tree_ok_S_u : exists QS, tree_ok segsS pcS phS limS treeS QS.
Proof.
  destruct IMPL_S as [QS HS]. exists QS. intros en inp Hv Hvi. split; [exact (HS en inp Hv Hvi)|].
  exact (prog_model_ok (CEG:=ceil_of_sp (en_sp en)) (CEC:=ceil_of_sp (en_sp en))
           segsS segsS limS limS en en inp (tbS en) (tbS en) (stkS en) (stkS en)
           IOS IOS (valid_entry_brk _ _ _ _ _ Hv) (valid_entry_brk _ _ _ _ _ Hv) (TLSS _ _ Hv) (TLSS _ _ Hv)
           Hvi (mo0_ceil_valid _ _ _ _ _ _ Hvi Hv) (mo0_ceil_valid _ _ _ _ _ _ Hvi Hv)
           (secS en) (secS en) (SECS en) (SECS en) (RUN _ _ _ (STKS en) _ _) (in_argv inp) (valid_input_argv _ Hvi)).
Qed.

#[using="SECT IOT TLST STKT RUN IMPL_T"] Theorem tree_ok_T_u : exists QT, tree_ok segsT pcT phT limT treeT QT.
Proof.
  destruct IMPL_T as [QT HT]. exists QT. intros en inp Hv Hvi. split; [exact (HT en inp Hv Hvi)|].
  exact (prog_model_ok (CEG:=ceil_of_sp (en_sp en)) (CEC:=ceil_of_sp (en_sp en))
           segsT segsT limT limT en en inp (tbT en) (tbT en) (stkT en) (stkT en)
           IOT IOT (valid_entry_brk _ _ _ _ _ Hv) (valid_entry_brk _ _ _ _ _ Hv) (TLST _ _ Hv) (TLST _ _ Hv)
           Hvi (mo0_ceil_valid _ _ _ _ _ _ Hvi Hv) (mo0_ceil_valid _ _ _ _ _ _ Hvi Hv)
           (secT en) (secT en) (SECT en) (SECT en) (RUN _ _ _ (STKT en) _ _) (in_argv inp) (valid_input_argv _ Hvi)).
Qed.

(* [comment removed for export] *)
#[using="tbS tbT stkS stkT secS secT SECS SECT IOS IOT TLSS TLST STKS STKT RUN IMPL_S IMPL_T"] Theorem route_abs_main_u :
  strong_universal_error_free_T_scfg_budgets CFG limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  destruct tree_ok_S_u as [QS HS]. destruct tree_ok_T_u as [QT HT].
  exact (strong_universal_error_free_scfg_budgets_from_trees_gen limS limT
           segsS pcS phS segsT pcT phT treeS treeT QS QT HS HT route_abs_trees_equiv_u).
Qed.
End Main.
End EquivMain.

(* [comment removed for export] *)
Module UPcapE.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UStdio UFmt UDriver UPcapA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.UNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).
#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition EO (out : hptr) (fdo : Z) : kfe := mkKfe fdo KNull (to_bytes DEVNULL) (Some out) None 0.
Definition KH (ho : option (hptr * Z)) : list kfe := match ho with Some (out, fdo) => [EO out fdo] | None => [] end.
Definition HSH (ho : option (hptr * Z)) : list hptr := match ho with Some (out, _) => [out] | None => [] end.
Definition FH (ho : option (hptr * Z)) : fpm := match ho with Some (out, fdo) => [(out, PW (EO out fdo) [])] | None => [] end.
Definition OH (ho : option (hptr * Z)) : option hptr := match ho with Some (out, _) => Some out | None => None end.
(* [comment removed for export] *)
Definition LH (ho : option (hptr * Z)) (LB : list (N * Z)) : list (N * Z) := match ho with Some (out, _) => (out, FILE_ALLOC) :: LB | None => LB end.
(* [comment removed for export] *)
Definition LBok (LB : list (N * Z)) : Prop := zlen LB <= 2 /\ R63N (map snd LB) <= BASEB.
End WithCeil.


Ltac case_if E := lazymatch goal with |- usim _ _ (if ?c then _ else _) _ _ => destruct c eqn:E end.

Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
Section Harness.
Variable segs : list Segment.
Variables (stkG stkC : stack_site -> Z).
Hypothesis STK : stk_ok stkG.
#[local] Notation npk := (npeek segs).
#[local] Notation usimS := (usim npk).
#[local] Notation RX := (UBase.RX (CEG:=CEG) (CEC:=CEC)).     (* [comment removed for export] *)
#[local] Notation RUK tm nx K C g W := (RX tm nx (UK nx K C g W)).
#[local] Notation PR_G := (prims fopsG fo_nop stkG).
#[local] Notation PR_C := (prims fopsC fo_nop stkC).

Definition RH (tm : gmap N Z) (nx : N) (ho : option (hptr * Z)) (C : list (list byte * list byte)) : @rel PS PS :=
  RUK tm nx (KH ho) C idl (WF (OH ho) (HSH ho) (FH ho)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma us_get_outfile tm nx K C oh hs F :
  usimS (RUK tm nx K C idl (WF oh hs F)) (mbind mget (fun s : PS => mret (ps_outfile s))) (mbind mget (fun s : PS => mret (ps_outfile s)))
        (eqpost (fun r => fun sG moG sC moC => r = oh /\ RUK tm nx K C idl (WF oh hs F) sG moG sC moC)).
Proof.
  eapply ru_bind2; [apply ru_get|]. intros a b. apply usim_pointwise. intros sG0 moG0 sC0 moC0 (-> & -> & EL & EO & HR0).
  eapply ru_pre; [| intros ? ? ? ? (-> & -> & -> & ->); exact HR0]. rewrite EO.
  apply ru_ret. intros sG moG sC moC HR. split; [| exact HR]. destruct HR0 as [_ [_ [HO _]]]. exact HO.
Qed.

#[using="Type"] Lemma us_set_outfile tm nx K C oh hs F o :
  usimS (RUK tm nx K C idl (WF oh hs F)) (mupd (set_outfile o)) (mupd (set_outfile o)) (eqpost (fun _ => RUK tm nx K C idl (WF o hs F))).
Proof.
  apply usim_upd. intros sG moG sC moC [HR [HF HW]]. split; [reflexivity|]. split; [apply RQ_outfile_upd; exact HR|].
  destruct sG; cbn in *. split; [exact HF|]. destruct HW as (_ & A & B & D). split; [reflexivity|]. exact (conj A (conj B D)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cstr_length l : (length (cstr l) <= length l)%nat.
Proof. induction l as [|c l IH]; cbn; [lia|]. destruct (c =? 0); cbn; lia. Qed.
#[using="Type"] Lemma small_packet_length a b : Forall (fun p => zlength p < 2^61) (pieces_packet_length a b).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_packet_length. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.
#[using="Type"] Lemma small_number_of_packets a : Forall (fun p => zlength p < 2^61) (pieces_number_of_packets a).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_number_of_packets. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.
#[using="Type"] Lemma small_couldnt_open m : mok m -> Forall (fun p => zlength p < 2^61) (pieces_couldnt_open (cstr m)).
Proof.
  intros Hm. apply (Forall_lt_of_le 512); [lia|]. unfold pieces_couldnt_open. apply pieces_small; [lia| items_small_tac|].
  apply args_small_cons_str; [| apply args_small_nil]. unfold mok, zlength in *. pose proof (cstr_length m). lia.
Qed.
#[using="Type"] Lemma small_failed_remove e : Forall (fun p => zlength p < 2^61) (pieces_failed_remove e).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_failed_remove. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.
#[using="Type"] Lemma small_failed_open e : Forall (fun p => zlength p < 2^61) (pieces_failed_open e).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_failed_open. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section InCtx.
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
Variables (out : hptr) (eo : kfe).
Hypothesis Hoh : rc_oh rc = Some out.
Hypothesis HF0 : rc_F0 rc = [(out, PW eo [])].
Hypothesis Heo : In eo (rc_Kx rc).
Hypothesis Heo_own : k_own eo = Some out.
Hypothesis Heo_kind : k_kind eo = KNull.
Hypothesis Heo_data : k_data eo = None.
Hypothesis Hhs : In out (rc_hs rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation PI := (PI rc).
#[local] Notation RPP := (RPP (CEG:=CEG) (CEC:=CEC) rc).
#[local] Notation PST := (PST (CEG:=CEG) (CEC:=CEC) rc).

(* [comment removed for export] *)
#[using="RCW out eo Hoh HF0 Heo Heo_own Heo_kind Heo_data Hhs"] Lemma pr_out_fprintf nx tm off pos ps :
  Forall (fun p => zlength p < 2^61) ps ->
  usimS (RPP nx tm off pos) (with_outfile MOps PR_G (fun o => e_fprintf PR_G o ps)) (with_outfile MOps PR_C (fun o => e_fprintf PR_C o ps))
        (eqpost (fun _ => RPP nx tm off pos)).
Proof.
  intros Hps. unfold with_outfile. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_get_outfile e_fprintf prims]. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.RPP.
  eapply ru_bind; [apply us_get_outfile|]. intros o. apply usim_pure. intros ->. rewrite Hoh.
  pose proof (rw_F0 _ RCW) as NF. rewrite HF0 in NF. cbn in NF.
  eapply ru_post.
  - apply (us_fprintf (CEG:=CEG) (CEC:=CEC) segs tm nx (UPcapA.KR_ rc off) (rc_C rc) (Some out) (rc_hs rc) (UPcapA.FR_ rc off pos) out eo [] ps).
    + unfold UPcapA.KR_. apply in_app_iff. left. exact Heo.
    + exact Heo_own.
    + right. exact Heo_kind.
    + exact Hhs.
    + unfold UPcapA.FR_. rewrite HF0. right. left. reflexivity.
    + exact Hps.
    + rewrite Heo_data. exact I.
  - intros [] ? ? ? ? (fl & H). rewrite (kapp_data_none eo fl Heo_data) in H.
    destruct H as [HR [HF HW]]. split; [exact HR|]. split.
    + rewrite kset_self in HF; [exact HF| unfold UPcapA.KR_; apply in_app_iff; left; exact Heo|].
      pose proof (proj1 (FI_KP _ _ _ _ _ HF)) as ND. rewrite (map_fd_kset eo (UPcapA.KR_ rc off) (or_intror I)) in ND. exact ND.
    + destruct HW as (W1 & W2 & W3 & W4). split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
      intros h P f HP Hf. assert (X : forall P', In (h, P') (fupd out (PW eo ([] ++ to_bytes (concat ps))) (UPcapA.FR_ rc off pos)) -> P' f) by (intros P' HP'; exact (W4 h P' f HP' Hf)).
      unfold UPcapA.FR_ in HP, X. rewrite HF0 in HP, X. unfold fupd in X. cbn [List.filter fst] in X.
      destruct (N.eqb_spec fp out) as [E|NE]; [exfalso; apply NF; left; symmetry; exact E|]. rewrite N.eqb_refl in X. cbn in X.
      destruct HP as [HP|[HP|[]]].
      * injection HP as <- <-. apply X. right. left. reflexivity.
      * injection HP as <- <-. pose proof (X _ ltac:(left; reflexivity)) as Y. unfold PW in Y |- *. rewrite Heo_data in Y |- *. exact Y.
Qed.

(* [comment removed for export] *)
#[using="STK RCW out eo Hoh HF0 Heo Heo_own Heo_kind Heo_data Hhs"] Lemma pr_packet_loop ngfuel : forall fuel nx p tm off pos,
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel -> Z.of_nat (length d) < Z.of_nat ngfuel ->
  usimS (RPP nx tm off pos) (packet_loop MOps PR_G fuel ngfuel p) (packet_loop MOps PR_C fuel ngfuel p)
        (PST (fun (r : pcapT) p' pos' => r = p')).
Proof.
  induction fuel as [|fuel IH]; intros nx p tm off pos HPI HT HF HNF.
  { exfalso. pose proof (pi_pos _ _ _ HPI). cbn in HF. lia. }
  cbn [packet_loop]. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
  eapply (pp_bind (CEG:=CEG) (CEC:=CEC) segs rc); [apply (pr_pcap_next_ex (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW ngfuel nx p tm off pos HPI HT); pose proof (pi_pos _ _ _ HPI); lia|].
  intros [r p1] p1' tm1 nx1 off1 pos1 (E1 & PS1 & LE1 & PR1) HPI1 HT1. cbn [fst snd] in E1, PR1. subst p1'. cbn beta iota.
  destruct (0 <? r) eqn:E.
  - apply Z.ltb_lt in E. specialize (PR1 E).
    eapply ru_bind; [apply (pr_out_fprintf nx1 tm1 off1 pos1 _ (small_packet_length _ _))|]. intros [].
    apply (IH nx1 p1 tm1 off1 pos1 HPI1 HT1); [rewrite Nat2Z.inj_succ in HF; lia| exact HNF].
  - apply (pp_ret (CEG:=CEG) (CEC:=CEC) segs rc _ nx1 p1 tm1 off1 pos1); [reflexivity| exact HPI1| exact HT1].
Qed.

End InCtx.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkrc (ho : option (hptr * Z)) (LB : list (N * Z)) (C : list (list byte * list byte)) (fp : hptr) (fd : Z) (dd : list byte) : rctx :=
  mkRC (LH ho LB) (KH ho) (FH ho) (fp :: HSH ho) (cdel (to_bytes TMPNAME) C) (OH ho) fp (mkKfe fd KR (to_bytes TMPNAME) (Some fp) (Some dd) 0) dd.

#[using="Type"] Lemma to_bytes_length l : length (to_bytes l) = length l.
Proof. unfold to_bytes. apply length_map. Qed.
#[using="Type"] Lemma neq_by_length {A} (a b : list A) : length a <> length b -> a <> b.
Proof. intros H E. apply H. rewrite E. reflexivity. Qed.
#[using="Type"] Lemma DEVNULL_ne_TMPNAME : to_bytes DEVNULL <> to_bytes TMPNAME.
Proof. apply neq_by_length. rewrite !to_bytes_length. vm_compute. discriminate. Qed.
#[using="Type"] Lemma TMPNAME_ne_dot : to_bytes TMPNAME <> dot_path.
Proof. apply neq_by_length. rewrite to_bytes_length. vm_compute. discriminate. Qed.
#[using="Type"] Lemma K_clear_KH ho : K_clear (KH ho) (to_bytes TMPNAME).
Proof. intros e He _. destruct ho as [[out fdo]|]; [| destruct He]. destruct He as [<-|[]]. cbn. exact DEVNULL_ne_TMPNAME. Qed.

#[using="Type"] Lemma LH_len ho LB : LBok LB -> zlen (LH ho LB) <= 3.
Proof. intros (A & _). destruct ho as [[o f]|]; cbn [LH]; rewrite ?zlen_cons; lia. Qed.
#[using="Type"] Lemma LH_R63N ho LB : R63N (map snd (LH ho LB)) = R63N (map snd LB).
Proof. destruct ho as [[o f]|]; cbn [LH map snd]; rewrite ?R63N_cons, ?bigb_FILE; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma LH_budget tm ho LB n : TML tm (LH ho LB) -> LBok LB -> 0 <= n < MMAP_THRESHOLD ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE /\ PHI P9 + R63N (map snd (LH ho LB)) <= BLIVE.
Proof.
  intros HT HL Hn. pose proof HL as [A B]. rewrite (bigb_small n) by lia.
  assert (X : PHI P9 + R63N (map snd (LH ho LB)) + bigb n <= BLIVE).
  { rewrite LH_R63N, (bigb_small n) by lia. rewrite PHI_P9. unfold BASEB, B26, BLIVE, PGSZ in *. lia. }
  destruct (budget_of_TML tm (LH ho LB) n HT ltac:(pose proof (LH_len ho LB HL); lia) ltac:(lia) X) as [R1 R2].
  rewrite (bigb_small n) in R2, X by lia. split; [exact R1|]. split; [lia| lia].
Qed.

#[using="STK"] Lemma pr_pcap_open_offline fuel tm nx out fdo LB C dd :
  TML tm (LH (Some (out, fdo)) LB) -> LBok LB -> clookup C (to_bytes TMPNAME) = Some dd -> Z.of_nat (length dd) < MAX_INPUT -> Z.of_nat (length dd) < Z.of_nat fuel ->
  usimS (RH tm nx (Some (out, fdo)) C) (pcap_open_offline MOps PR_G fuel TMPNAME) (pcap_open_offline MOps PR_C fuel TMPNAME)
        (eqpost (fun r => fun sG moG sC moC =>
           match r with
           | inl m => mok m /\ exists tm' nx' C', TML tm' (LH (Some (out, fdo)) LB) /\ RH tm' nx' (Some (out, fdo)) C' sG moG sC moC
           | inr p => exists fd tm' nx' off' pos', let rc := mkrc (Some (out, fdo)) LB C nx fd dd in
                      rcwf rc /\ PI rc p pos' /\ TML tm' (toks rc p) /\ RPP (CEG:=CEG) (CEC:=CEC) rc nx' tm' off' pos' sG moG sC moC
           end)).
Proof.
  intros HT HL HC HD HF. set (ho := Some (out, fdo)) in *.
  unfold pcap_open_offline, pcap_open_offline_with_tstamp_precision. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fopen_r e_fclose prims]. unfold RH.
  apply ru_use. intros sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
  destruct HR0 as [_ [HF0 _]]. pose proof (FI_owner _ _ _ _ _ HF0 (EO out fdo) out ltac:(left; reflexivity) eq_refl) as LT. clear HF0.
  destruct (LH_budget tm ho LB FILE_ALLOC HT HL ltac:(unfold FILE_ALLOC, MMAP_THRESHOLD; lia)) as (R1 & R2 & R3).
  eapply ru_bind.
  { apply (us_fopen_r (CEG:=CEG) (CEC:=CEC) segs tm nx (KH ho) C (OH ho) (HSH ho) (FH ho) TMPNAME dd (K_clear_KH ho) HC TMPNAME_ne_dot R1 R2). }
  intros [fp|].
  2:{ (* [comment removed for export] *)
    eapply ru_bind; [apply (pr_errmsg (CEG:=CEG) (CEC:=CEC) segs stkG stkC)|]. intros m. apply usim_pure. intros Mm.
    apply ru_ret. intros sG moG sC moC HR. split; [exact Mm|]. exists tm, nx, C. split; [exact HT| exact HR]. }
  apply usim_pure. intros ->. apply usim_exI. intros fd. apply usim_pure. intros Hfd. cbv zeta.
  set (rc := mkrc ho LB C nx fd dd).
  assert (HT1 : TML (<[nx:=FILE_ALLOC]> tm) (L0 rc)) by (apply TML_insert; [exact HT| exact FR]).
  (* [comment removed for export] *)
  apply ru_use. intros sG1 moG1 sC1 moC1 [_ [HF1 _]]. pose proof (proj1 (FI_KP _ _ _ _ _ HF1)) as ND1. clear HF1. cbn [map app k_fd KH EO] in ND1.
  assert (NEfd : fdo <> fd) by (inversion ND1 as [|? ? NI _]; subst; intros E; apply NI; left; symmetry; exact E).
  assert (RCW : rcwf rc).
  { pose proof HL as [A1 A2]. subst rc ho. constructor; cbn [rc_B rc_Kx rc_F0 rc_hs rc_C rc_oh rc_fp rc_e0 rc_d mkrc LH KH FH HSH OH k_own k_kind k_data k_fd].
    - split; [rewrite zlen_cons; lia|]. cbn [map snd]; rewrite R63N_cons, bigb_FILE; lia.
    - exact FR.
    - intros x [<-|[]]. cbn. exact NEfd.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - left; reflexivity.
    - cbn. intros [E|[]]. apply (N.lt_irrefl nx). rewrite <- E at 1. exact LT.
    - cbn. intros E. injection E as E. apply (N.lt_irrefl nx). rewrite <- E at 1. exact LT.
    - exact HD. }
  eapply ru_pre with (R' := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.RPP (CEG:=CEG) (CEC:=CEC) rc (N.succ nx) (<[nx:=FILE_ALLOC]> tm) 0 0).
  2:{ intros ? ? ? ? HR. subst rc ho. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.RPP, UPcapA.KR_, UPcapA.FR_. cbn [rc_Kx rc_C rc_oh rc_hs rc_F0 rc_fp rc_e0 rc_d rc_B mkrc KH FH HSH OH LH].
      unfold fupd in HR. cbn [List.filter fst KH FH HSH OH] in HR. destruct (N.eqb_spec out nx) as [E|_]; [exfalso; apply (N.lt_irrefl nx); rewrite <- E at 1; exact LT|]. cbn [negb] in HR. exact HR. }
  eapply ru_bind; [apply (pr_fopen_offline (CEG:=CEG) (CEC:=CEC) segs stkG stkC STK rc RCW fuel (N.succ nx) _ 0 PCAP_TSTAMP_PRECISION_MICRO HT1 HF)|].
  intros r. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros off1. apply usim_exI; intros pos1. apply usim_pure; intros Q.
  destruct r as [m|p]; cbn [Q_open] in Q.
  - destruct Q as [[HT2 Hp2] Mm].
    assert (BUD : PHI P9 + R63N (sizes tm1) <= BLIVE).
    { rewrite (R63N_perm _ _ (TML_sizes _ _ HT2)). unfold L0. cbn [map snd rc_B rc mkrc]. rewrite R63N_cons, bigb_FILE. pose proof (LH_budget tm ho LB 0 HT HL ltac:(unfold MMAP_THRESHOLD; lia)) as (_ & _ & X). lia. }
    eapply ru_bind.
    { unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.RPP. apply (us_fclose_r (CEG:=CEG) (CEC:=CEC) segs tm1 nx1 (UPcapA.KR_ rc off1) (rc_C rc) (rc_oh rc) (rc_hs rc) (UPcapA.FR_ rc off1 pos1) nx (kat (rc_e0 rc) off1) dd pos1 FILE_ALLOC
               (KR_in rc off1) (own_kat rc RCW off1) (rw_hs _ RCW) (FR_in rc off1 pos1) (rw_oh _ RCW) (TML_lookup _ _ _ _ HT2 ltac:(left; reflexivity)) BUD). }
    intros []. rewrite (kdel_KR rc RCW), (fdel_FR rc RCW), (kpath_kat rc).
    apply ru_ret. intros sG moG sC moC HR. split; [exact Mm|]. exists (delete nx tm1), nx1, ((k_path (rc_e0 rc), dd) :: rc_C rc). split.
    + pose proof (TML_delete _ _ _ _ HT2 ltac:(left; reflexivity)) as X. unfold L0 in X. rewrite lrm_head in X. exact X.
    + subst rc ho. cbn [rc_Kx rc_oh rc_hs rc_F0 mkrc hrem List.filter HSH] in HR |- *. rewrite N.eqb_refl in HR. cbn [negb] in HR.
      destruct (N.eqb_spec out nx) as [E|_]; [exfalso; apply (N.lt_irrefl nx); rewrite <- E at 1; exact LT|]. cbn [negb] in HR. exact HR.
  - destruct Q as [HPI2 HT2]. apply ru_ret. intros sG moG sC moC HR. exists fd, tm1, nx1, off1, pos1. cbv zeta. split; [exact RCW|]. split; [exact HPI2|]. split; [exact HT2| exact HR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation NDT := (ND (to_bytes TMPNAME)).
#[local] Notation frm := (framed NDT).

#[using="Type"] Lemma nd_lift {A} (R : @rel PS PS) (m m' : Monad.M PS A) (R1 : A -> @rel PS PS) :
  usimS R m m' (eqpost R1) -> usimS (frm R) m m' (eqpost (fun a => frm (R1 a))).
Proof.
  intros H. eapply usim_post; [apply (usim_ND (to_bytes TMPNAME) npk); exact H|].
  intros a b ? ? ? ? [[-> HR] HN]. split; [reflexivity| exact (conj HR HN)].
Qed.

#[using="Type"] Lemma fr_exI {A B X} (R : X -> @rel PS PS) (m : Monad.M PS A) (m' : Monad.M PS B) Q :
  (forall x, usimS (frm (R x)) m m' Q) -> usimS (frm (fun sG moG sC moC => exists x, R x sG moG sC moC)) m m' Q.
Proof. apply framed_exI. Qed.

#[using="Type"] Lemma fr_pure {A B} (R : @rel PS PS) (phi : Prop) (m : Monad.M PS A) (m' : Monad.M PS B) Q :
  (phi -> usimS (frm R) m m' Q) -> usimS (frm (fun sG moG sC moC => phi /\ R sG moG sC moC)) m m' Q.
Proof. apply framed_pure. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fr_use {A B} (R : @rel PS PS) (m : Monad.M PS A) (m' : Monad.M PS B) Q :
  (forall sG moG sC moC, R sG moG sC moC -> usimS (frm R) m m' Q) -> usimS (frm R) m m' Q.
Proof. intros H. apply framed_use. intros sG moG sC moC HR _. exact (H _ _ _ _ HR). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_bind_nd {A B} tm nx K C g W (phi : A -> Prop) (K1 : A -> list kfe) (C1 : A -> list (list byte * list byte)) (g1 : A -> libc_st hptr -> libc_st hptr)
      (W1 : A -> libc_st hptr -> option hptr -> Prop) (m m' : Monad.M PS A) (k k' : A -> Monad.M PS B) Q :
  usimS (RUK tm nx K C g W) m m' (eqpost (fun a => fun sG moG sC moC => phi a /\ RUK tm nx (K1 a) (C1 a) (g1 a) (W1 a) sG moG sC moC)) ->
  (forall a, phi a -> usimS (frm (RUK tm nx (K1 a) (C1 a) (g1 a) (W1 a))) (k a) (k' a) Q) ->
  usimS (frm (RUK tm nx K C g W)) (mbind m k) (mbind m' k') Q.
Proof. intros H1 H2. eapply ru_bind; [apply nd_lift; exact H1|]. intros a. apply fr_pure. exact (H2 a). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pp_bind_nd rc {A B'} (Φ : A -> pcapT -> Z -> Prop) nx tm off pos (m m' : Monad.M PS A) (k k' : A -> Monad.M PS B') Q :
  usimS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.RPP (CEG:=CEG) (CEC:=CEC) rc nx tm off pos) m m' (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.PST (CEG:=CEG) (CEC:=CEC) rc Φ) ->
  (forall r p' tm' nx' off' pos', Φ r p' pos' -> UPcapA.PI rc p' pos' -> TML tm' (UPcapA.toks rc p') ->
     usimS (frm (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.RPP (CEG:=CEG) (CEC:=CEC) rc nx' tm' off' pos')) (k r) (k' r) Q) ->
  usimS (frm (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapB.RPP (CEG:=CEG) (CEC:=CEC) rc nx tm off pos)) (mbind m k) (mbind m' k') Q.
Proof.
  intros H1 H2. eapply ru_bind; [apply nd_lift; exact H1|]. intros r.
  apply fr_exI; intros p'. apply fr_exI; intros tm'. apply fr_exI; intros nx'. apply fr_exI; intros off'. apply fr_exI; intros pos'.
  eapply framed_pre; [| intros ? ? ? ? (X1 & X2 & X3 & X4); exact (conj X1 (conj X2 (conj X3 X4)))].
  apply fr_pure; intros X1. apply fr_pure; intros X2. apply fr_pure; intros X3. exact (H2 _ _ _ _ _ _ X1 X2 X3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma DEVNULL_bytes : to_bytes DEVNULL = devnull_path.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma TMPNAME_not_devnull : to_bytes TMPNAME <> devnull_path.
Proof. intros E. apply (f_equal (@length _)) in E. vm_compute in E. discriminate. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma us_fopen_tmp tm nx K C oh hs F :
  K_clear K (to_bytes TMPNAME) ->
  ROOMN (sizes tm) P9 FILE_ALLOC -> PHI P9 + R63N (sizes tm) + bigb FILE_ALLOC <= BLIVE ->
  usimS (RUK tm nx K C idl (WF oh hs F)) (s_fopen fopsG TMPNAME true) (s_fopen fopsC TMPNAME true)
        (eqpost (fun r => fun sG moG sC moC =>
           match r with
           | None => RUK tm nx K C idl (WF oh hs F) sG moG sC moC
           | Some p => p = nx /\ exists fd, 3 <= fd <= 4096 /\
               let e := mkKfe fd KW (to_bytes TMPNAME) (Some nx) (Some []) 0 in
               RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (UK (N.succ nx) (K ++ [e]) (cdel (to_bytes TMPNAME) C) idl (WF oh (nx :: hs) (fupd nx (PW e []) F))) sG moG sC moC
           end)).
Proof.
  intros HC R1 R2.
  eapply ru_post; [apply (us_fopen_w (CEG:=CEG) (CEC:=CEC) segs tm nx K C oh hs F TMPNAME true HC ltac:(vm_compute; reflexivity) R1 R2)|].
  intros [p|] sG moG sC moC H; [| exact H]. destruct H as [-> (fd & Hfd & HR)]. split; [reflexivity|]. exists fd. split; [exact Hfd|].
  cbv zeta in HR |- *. rewrite (wkind_other _ TMPNAME_not_devnull) in HR. exact HR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma us_fopen_devnull tm nx K C oh hs F :
  K_clear K (to_bytes DEVNULL) ->
  ROOMN (sizes tm) P9 FILE_ALLOC -> PHI P9 + R63N (sizes tm) + bigb FILE_ALLOC <= BLIVE ->
  usimS (RUK tm nx K C idl (WF oh hs F)) (s_fopen fopsG DEVNULL true) (s_fopen fopsC DEVNULL true)
        (eqpost (fun r => fun sG moG sC moC =>
           match r with
           | None => RUK tm nx K C idl (WF oh hs F) sG moG sC moC
           | Some p => p = nx /\ exists fd, 3 <= fd <= 4096 /\
               let e := mkKfe fd KNull (to_bytes DEVNULL) (Some nx) None 0 in
               RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (UK (N.succ nx) (K ++ [e]) (cdel (to_bytes DEVNULL) C) idl (WF oh (nx :: hs) (fupd nx (PW e []) F))) sG moG sC moC
           end)).
Proof.
  intros HC R1 R2.
  eapply ru_post; [apply (us_fopen_w (CEG:=CEG) (CEC:=CEC) segs tm nx K C oh hs F DEVNULL false HC ltac:(vm_compute; reflexivity) R1 R2)|].
  intros [p|] sG moG sC moC H; [| exact H]. destruct H as [-> (fd & Hfd & HR)]. split; [reflexivity|]. exists fd. split; [exact Hfd|].
  cbv zeta in HR |- *. rewrite DEVNULL_bytes, wkind_devnull in HR. rewrite DEVNULL_bytes. exact HR.
Qed.

#[using="Type"] Lemma filter_idem {A} (f : A -> bool) l : List.filter f (List.filter f l) = List.filter f l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (f x) eqn:E; cbn; [rewrite E, IH; reflexivity| exact IH]. Qed.
#[using="Type"] Lemma fdel_fupd h P F : fdel h (fupd h P F) = fdel h F.
Proof. unfold fdel, fupd. cbn. rewrite N.eqb_refl. cbn. apply filter_idem. Qed.
#[using="Type"] Lemma hrem_hd h l : hrem h (h :: l) = hrem h l.
Proof. unfold hrem. cbn. rewrite N.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma hrem_notin h l : ~ In h l -> hrem h l = l.
Proof.
  induction l as [|x l IH]; intros NI; [reflexivity|]. unfold hrem in *. cbn. destruct (N.eqb_spec x h) as [->|NE]; [exfalso; apply NI; left; reflexivity|].
  cbn. rewrite IH; [reflexivity|]. intros X; apply NI; right; exact X.
Qed.

#[using="Type"] Lemma kdel_snoc_EO out fdo e : k_fd e <> fdo -> kdel (k_fd e) ([EO out fdo] ++ [e]) = [EO out fdo].
Proof. intros NE. unfold kdel. cbn. rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym NE)), Z.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma pr_bufferToFile tm nx out fdo LB C data :
  TML tm (LH (Some (out, fdo)) LB) -> LBok LB -> zlength data < MAX_INPUT ->
  usimS (frm (RH tm nx (Some (out, fdo)) C)) (bufferToFile MOps PR_G TMPNAME data) (bufferToFile MOps PR_C TMPNAME data)
        (eqpost (fun r => fun sG moG sC moC => exists tm' nx' C',
           TML tm' (LH (Some (out, fdo)) LB) /\ (0 <= r -> clookup C' (to_bytes TMPNAME) = Some (to_bytes data)) /\ frm (RH tm' nx' (Some (out, fdo)) C') sG moG sC moC)).
Proof.
  intros HT HL HD. set (ho := Some (out, fdo)) in *. pose proof (zlength_nonneg data) as ND0.
  unfold bufferToFile. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_remove e_last_errno e_printf e_fopen_w e_fwrite e_fclose prims]. unfold RH.
  apply fr_use. intros sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
  destruct HR0 as [_ [HF0 _]]. pose proof (FI_owner _ _ _ _ _ HF0 (EO out fdo) out ltac:(left; reflexivity) eq_refl) as LT. clear HF0.
  assert (NEo : out <> nx) by (intros E; apply (N.lt_irrefl nx); rewrite <- E at 1; exact LT).
  (* [comment removed for export] *)
  eapply ru_bind; [apply (us_remove (CEG:=CEG) (CEC:=CEC) segs tm nx (KH ho) C (OH ho) (HSH ho) (FH ho) TMPNAME (K_clear_KH ho))|].
  intros r0. apply usim_pure. intros Hr0. set (C1 := if r0 =? 0 then cdel (to_bytes TMPNAME) C else C).   (* [comment removed for export] *)
  assert (RET : forall (z : Z) tm' nx' C', z < 0 -> TML tm' (LH ho LB) ->
            usimS (frm (RUK tm' nx' (KH ho) C' idl (WF (OH ho) (HSH ho) (FH ho)))) (mret z) (mret z)
                  (eqpost (fun r => fun sG moG sC moC => exists tm'' nx'' C'', TML tm'' (LH ho LB) /\ (0 <= r -> clookup C'' (to_bytes TMPNAME) = Some (to_bytes data)) /\
                                                        frm (RUK tm'' nx'' (KH ho) C'' idl (WF (OH ho) (HSH ho) (FH ho))) sG moG sC moC))).
  { intros z tm' nx' C' Hz HT'. apply ru_ret. intros sG moG sC moC HR. exists tm', nx', C'. split; [exact HT'|]. split; [intros; lia| exact HR]. }
  eapply (ruk_bind_nd tm nx (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
  { destruct (negb (r0 =? 0)).
    - eapply (ruk_bind (CEG:=CEG) (CEC:=CEC) segs tm nx (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
      { eapply ru_post; [apply us_get_errno|]. intros ? ? ? ? ? H; exact (conj I H). }
      intros e _. case_if EE.
      + eapply (ruk_bind (CEG:=CEG) (CEC:=CEC) segs tm nx (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
        { eapply ru_post; [apply us_printf; apply small_failed_remove|]. intros ? ? ? ? ? H; exact (conj I H). }
        intros [] _. apply ruk_ret. exact I.
      + apply ruk_ret. exact I.
    - apply ruk_ret. exact I. }
  intros k _. destruct (negb k); [apply (RET (-1) tm nx C1 ltac:(lia) HT)|].
  (* [comment removed for export] *)
  destruct (LH_budget tm ho LB FILE_ALLOC HT HL ltac:(unfold FILE_ALLOC, MMAP_THRESHOLD; lia)) as (R1 & R2 & R3).
  eapply ru_bind; [apply nd_lift; apply (us_fopen_tmp tm nx (KH ho) C1 (OH ho) (HSH ho) (FH ho) (K_clear_KH ho) R1 R2)|].
  intros [fd1|].
  2:{ eapply (ruk_bind_nd tm nx (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
      { eapply ru_post; [apply us_get_errno|]. intros ? ? ? ? ? H; exact (conj I H). }
      intros e _. eapply (ruk_bind_nd tm nx (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
      { eapply ru_post; [apply us_printf; apply small_failed_open|]. intros ? ? ? ? ? H; exact (conj I H). }
      intros [] _. apply (RET (-2) tm nx C1 ltac:(lia) HT). }
  apply fr_pure. intros ->. apply fr_exI. intros fd. apply fr_pure. intros Hfd. cbv zeta.
  set (e1 := mkKfe fd KW (to_bytes TMPNAME) (Some nx) (Some []) 0).
  assert (HT1 : TML (<[nx:=FILE_ALLOC]> tm) ((nx, FILE_ALLOC) :: LH ho LB)) by (apply TML_insert; [exact HT| exact FR]).
  (* [comment removed for export] *)
  apply fr_use. intros sG1 moG1 sC1 moC1 [_ [HF1 _]]. pose proof (proj1 (FI_KP _ _ _ _ _ HF1)) as ND1. clear HF1. subst ho. cbn [map app k_fd KH EO] in ND1.
  assert (NEfd : k_fd e1 <> fdo) by (cbn; inversion ND1 as [|? ? NI _]; subst; intros E; apply NI; left; exact E).
  (* [comment removed for export] *)
  eapply ru_bind.
  { apply nd_lift. apply (us_fwrite (CEG:=CEG) (CEC:=CEC) segs _ (N.succ nx) (KH (Some (out, fdo)) ++ [e1]) (cdel (to_bytes TMPNAME) C1) (OH (Some (out, fdo))) (nx :: HSH (Some (out, fdo))) (fupd nx (PW e1 []) (FH (Some (out, fdo)))) nx e1 [] data).
    - apply in_app_iff. right. left. reflexivity.
    - reflexivity.
    - left. split; [reflexivity| discriminate].       (* [comment removed for export] *)
    - left. reflexivity.
    - left. reflexivity.
    - unfold MAX_INPUT in HD. lia.
    - cbn. unfold FLEN, MAX_INPUT in *. lia. }
  intros n. apply fr_exI. intros fl. apply fr_pure. intros ->.
  (* [comment removed for export] *)
  assert (BUD : PHI P9 + R63N (sizes (<[nx:=FILE_ALLOC]> tm)) <= BLIVE).
  { rewrite (R63N_perm _ _ (TML_sizes _ _ HT1)). cbn [map snd]. rewrite R63N_cons, bigb_FILE. lia. }
  eapply ru_bind.
  { apply nd_lift. apply (us_fclose_w (CEG:=CEG) (CEC:=CEC) segs _ (N.succ nx) _ _ _ _ _ nx (kapp e1 fl) ([] ++ to_bytes data) FILE_ALLOC).
    - apply (In_kset_new _ _ e1); [apply in_app_iff; right; left; reflexivity| reflexivity].
    - reflexivity.
    - reflexivity.
    - left. reflexivity.
    - left. reflexivity.
    - cbn. intros E. injection E as E. exact (NEo E).
    - apply (TML_lookup _ _ _ _ HT1). left. reflexivity.
    - exact BUD.
    - cbn. rewrite to_bytes_length. unfold FLEN, MAX_INPUT, zlength in *. lia. }
  intros []. rewrite kdel_kset. replace (k_fd (kapp e1 fl)) with (k_fd e1) by reflexivity. change (KH (Some (out, fdo))) with [EO out fdo] at 1.
  rewrite (kdel_snoc_EO out fdo e1 NEfd). subst e1. cbn [k_data kapp kmove k_fd k_path k_off].
  rewrite Z.eqb_refl. cbn [negb].
  eapply ru_pre with (R' := frm (RUK (delete nx (<[nx:=FILE_ALLOC]> tm)) (N.succ nx) (KH (Some (out, fdo))) ((to_bytes TMPNAME, [] ++ to_bytes data) :: cdel (to_bytes TMPNAME) C1) idl
                               (WF (OH (Some (out, fdo))) (HSH (Some (out, fdo))) (FH (Some (out, fdo)))))).
  2:{ intros ? ? ? ? [HR HN]. split; [| exact HN]. rewrite !fdel_fupd, hrem_hd in HR. cbn [HSH FH] in HR. rewrite (hrem_notin nx [out]) in HR by (intros [E|[]]; exact (NEo E)).
      rewrite (fdel_notin nx) in HR by (intros [E|[]]; exact (NEo E)). exact HR. }
  apply ru_ret. intros sG moG sC moC HR. exists (delete nx (<[nx:=FILE_ALLOC]> tm)), (N.succ nx), ((to_bytes TMPNAME, [] ++ to_bytes data) :: cdel (to_bytes TMPNAME) C1).
  split; [pose proof (TML_delete _ _ _ _ HT1 ltac:(left; reflexivity)) as X; rewrite lrm_head in X; exact X|].
  split; [intros _; cbn [clookup app]; rewrite path_eqb_refl; reflexivity| exact HR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma seal_TEMPLATE : seal_name TEMPLATE = Some TMPNAME.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pr_h_fprintf tm nx out fdo C ps :
  Forall (fun p => zlength p < 2^61) ps ->
  usimS (RH tm nx (Some (out, fdo)) C) (with_outfile MOps PR_G (fun o => e_fprintf PR_G o ps)) (with_outfile MOps PR_C (fun o => e_fprintf PR_C o ps))
        (eqpost (fun _ => RH tm nx (Some (out, fdo)) C)).
Proof.
  intros Hps. unfold with_outfile, RH. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_get_outfile e_fprintf prims KH OH HSH FH].
  eapply ru_bind; [apply us_get_outfile|]. intros o. apply usim_pure. intros ->.
  eapply ru_post.
  - apply (us_fprintf (CEG:=CEG) (CEC:=CEC) segs tm nx [EO out fdo] C (Some out) [out] [(out, PW (EO out fdo) [])] out (EO out fdo) [] ps); [left; reflexivity| reflexivity| right; reflexivity| left; reflexivity| left; reflexivity| exact Hps| exact I].
  - intros [] ? ? ? ? (fl & H). rewrite (kapp_data_none (EO out fdo) fl eq_refl) in H. destruct H as [HR [HF HW]]. split; [exact HR|]. split.
    + unfold kset in HF. cbn [map k_fd EO] in HF. rewrite Z.eqb_refl in HF. exact HF.
    + destruct HW as (W1 & W2 & W3 & W4). split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
      intros h P f [HP|[]] Hf. injection HP as <- <-. pose proof (W4 out _ f ltac:(left; reflexivity) Hf) as Y. unfold PW in Y |- *. cbn [k_data EO] in Y |- *. exact Y.
Qed.

#[using="STK"] Lemma pr_fuzz_one tm nx ho C LB data :
  TML tm (LH ho LB) -> LBok LB -> zlength data < MAX_INPUT ->
  usimS (RH tm nx ho C) (LLVMFuzzerTestOneInput MOps PR_G data) (LLVMFuzzerTestOneInput MOps PR_C data)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx' ho' C', TML tm' (LH ho' LB) /\ RH tm' nx' ho' C' sG moG sC moC)).
Proof.
  intros HT HL HD. pose proof (zlength_nonneg data) as ND0.
  unfold LLVMFuzzerTestOneInput. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_get_outfile e_set_outfile e_fopen_w e_mkstemp e_close_fd e_unlink prims].
  unfold RH. eapply ru_bind; [apply us_get_outfile|]. intros o0. apply usim_pure. intros ->.
  (* [comment removed for export] *)
  eapply (ru_bind segs _ _ _ _ (fun o => fun sG moG sC moC => exists tm1 nx1 ho1 C1, (TML tm1 (LH ho1 LB) /\ o = OH ho1) /\ RUK tm1 nx1 (KH ho1) C1 idl (WF (OH ho1) (HSH ho1) (FH ho1)) sG moG sC moC)).
  { destruct ho as [[out fdo]|]; cbn [OH].
    - apply ru_ret. intros sG moG sC moC HR. exists tm, nx, (Some (out, fdo)), C. split; [split; [exact HT| reflexivity]| exact HR].
    - cbn [KH HSH FH].
      apply ru_use. intros sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh _ _ _ _ _ _ _ _ _ _ HT HR0) as FR. clear HR0.
      destruct (LH_budget tm None LB FILE_ALLOC HT HL ltac:(unfold FILE_ALLOC, MMAP_THRESHOLD; lia)) as (R1 & R2 & R3).
      eapply ru_bind; [apply (us_fopen_devnull tm nx [] C None [] [] ltac:(intros e [])); [exact R1| exact R2]|].
      intros [fp|].
      + apply usim_pure. intros ->. apply usim_exI. intros fd. apply usim_pure. intros Hfd. cbv zeta. cbn [app fupd List.filter].
        eapply ru_bind; [apply us_set_outfile|]. intros [].
        apply ru_ret. intros sG moG sC moC HR. exists (<[nx:=FILE_ALLOC]> tm), (N.succ nx), (Some (nx, fd)), (cdel (to_bytes DEVNULL) C).
        split; [split; [cbn [LH]; apply TML_insert; [exact HT| exact FR]| reflexivity]| exact HR].
      + eapply ru_bind; [apply us_set_outfile|]. intros [].
        apply ru_ret. intros sG moG sC moC HR. exists tm, nx, None, C. split; [split; [exact HT| reflexivity]| exact HR]. }
  intros o. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros ho1. apply usim_exI; intros C1. apply usim_pure. intros [HT1 ->].
  destruct ho1 as [[out fdo]|]; cbn [OH].
  2:{ apply ru_ret. intros sG moG sC moC HR. exists tm1, nx1, None, C1. exact (conj HT1 HR). }
  clear tm nx ho C HT. set (ho := Some (out, fdo)).
  (* [comment removed for export] *)
  eapply ru_bind; [apply (us_mkstemp (CEG:=CEG) (CEC:=CEC) segs tm1 nx1 (KH ho) C1 (OH ho) (HSH ho) (FH ho) TEMPLATE TMPNAME false seal_TEMPLATE (K_clear_KH ho) TMPNAME_not_devnull)|].
  intros [filename fd]. apply usim_pure. intros Hname. apply usim_pure. intros Hfd. cbn [fst snd] in Hname, Hfd. subst filename. cbn beta iota.
  case_if Efd.
  { apply ru_ret. intros sG moG sC moC [HR _]. apply Z.ltb_lt in Efd. assert (E : fd = -1) by lia. rewrite E in HR. cbn in HR.
    exists tm1, nx1, ho, C1. exact (conj HT1 HR). }
  apply Z.ltb_ge in Efd. assert (NE1 : fd <> -1) by lia. rewrite (proj2 (Z.eqb_neq _ _) NE1).
  set (et := mkKfe fd KW (to_bytes TMPNAME) None None 0).
  (* [comment removed for export] *)
  eapply ru_pre with (R' := frm (RUK tm1 nx1 (KH ho ++ [et]) (cdel (to_bytes TMPNAME) C1) idl (WF (OH ho) (HSH ho) (FH ho))));
    [| intros ? ? ? ? [HR HN]; exact (conj HR (HN NE1))].
  apply fr_use. intros sG1 moG1 sC1 moC1 [_ [HF1 _]]. pose proof (proj1 (FI_KP _ _ _ _ _ HF1)) as ND1.
  pose proof (FI_owner _ _ _ _ _ HF1 (EO out fdo) out ltac:(apply in_app_iff; left; left; reflexivity) eq_refl) as LT. clear HF1. subst ho. cbn [map app k_fd KH EO] in ND1.
  assert (NEfd : k_fd et <> fdo) by (cbn; inversion ND1 as [|? ? NI _]; subst; intros E; apply NI; left; exact E).
  assert (NEo : out <> nx1) by (intros E; apply (N.lt_irrefl nx1); rewrite <- E at 1; exact LT).
  (* [comment removed for export] *)
  eapply ru_bind; [apply nd_lift; apply (us_close (CEG:=CEG) (CEC:=CEC) segs tm1 nx1 (KH (Some (out, fdo)) ++ [et]) (cdel (to_bytes TMPNAME) C1) _ _ _ et ltac:(apply in_app_iff; right; left; reflexivity) eq_refl)|].
  intros r0. apply fr_pure. intros _. change (KH (Some (out, fdo))) with [EO out fdo] at 1. rewrite (kdel_snoc_EO out fdo et NEfd). cbn [cclose k_data k_kind et].
  (* [comment removed for export] *)
  eapply ru_bind; [apply (pr_bufferToFile tm1 nx1 out fdo LB _ data HT1 HL HD)|].
  intros r. apply usim_exI; intros tm2. apply usim_exI; intros nx2. apply usim_exI; intros C2. apply usim_pure; intros HT2. apply usim_pure; intros HC2.
  case_if Er.
  { eapply ru_bind; [apply (us_unlink (CEG:=CEG) (CEC:=CEC) segs tm2 nx2 _ C2 _ _ _ TMPNAME (K_clear_KH (Some (out, fdo))))|].
    intros r1. apply usim_pure. intros _. apply ru_ret. intros sG moG sC moC HR. eexists tm2, nx2, (Some (out, fdo)), _. exact (conj HT2 (proj1 HR)). }
  apply Z.ltb_ge in Er. specialize (HC2 Er).
  (* [comment removed for export] *)
  eapply ru_bind; [apply nd_lift; apply (pr_pcap_open_offline (S (length data)) tm2 nx2 out fdo LB C2 (to_bytes data) HT2 HL HC2); rewrite to_bytes_length; unfold zlength in HD; lia|].
  intros [m|p].
  - apply fr_pure. intros Mm. apply fr_exI; intros tm3. apply fr_exI; intros nx3. apply fr_exI; intros C3. apply fr_pure. intros HT3.
    eapply ru_bind; [apply nd_lift; apply (pr_h_fprintf tm3 nx3 out fdo C3 _ (small_couldnt_open m Mm))|]. intros [].
    eapply ru_bind; [apply (us_unlink (CEG:=CEG) (CEC:=CEC) segs tm3 nx3 _ C3 _ _ _ TMPNAME (K_clear_KH (Some (out, fdo))))|].
    intros r1. apply usim_pure. intros _. apply ru_ret. intros sG moG sC moC HR. eexists tm3, nx3, (Some (out, fdo)), _. exact (conj HT3 (proj1 HR)).
  - apply fr_exI; intros fd2. apply fr_exI; intros tm3. apply fr_exI; intros nx3. apply fr_exI; intros off3. apply fr_exI; intros pos3.
    cbv zeta. apply fr_pure; intros RCW. apply fr_pure; intros HPI3. apply fr_pure; intros HT3.
    set (rc := mkrc (Some (out, fdo)) LB C2 nx2 fd2 (to_bytes data)) in *.
    pose proof (pi_pos _ _ _ HPI3) as Hp3. cbn [rc_d rc mkrc] in Hp3. rewrite to_bytes_length in Hp3.
    eapply (pp_bind_nd rc).
    { apply (pr_packet_loop rc RCW out (EO out fdo) eq_refl eq_refl ltac:(left; reflexivity) eq_refl eq_refl eq_refl ltac:(right; left; reflexivity) (S (length data)) (S (length data)) nx3 p tm3 off3 pos3 HPI3 HT3);
        cbn [rc_d rc mkrc]; rewrite to_bytes_length; lia. }
    intros p1 p1' tm4 nx4 off4 pos4 E4 HPI4 HT4. cbn beta in E4. subst p1.
    eapply (pp_bind_nd rc); [apply (pr_pcap_stats (CEG:=CEG) (CEC:=CEC) segs rc nx4 _ tm4 off4 pos4 HPI4 HT4)|].
    intros [sr p2] p2' tm5 nx5 off5 pos5 (E5 & PS5 & LE5 & PR5) HPI5 HT5. cbn [fst snd] in E5. subst p2'. cbn beta iota.
    eapply ru_bind.
    { apply nd_lift. destruct (sr =? 0); [apply (pr_out_fprintf rc RCW out (EO out fdo) eq_refl eq_refl ltac:(left; reflexivity) eq_refl eq_refl eq_refl ltac:(right; left; reflexivity)); apply small_number_of_packets|].
      apply ru_ret. intros ? ? ? ? HR. exact HR. }
    intros []. eapply ru_bind; [apply nd_lift; apply (pr_pcap_close (CEG:=CEG) (CEC:=CEC) segs stkG stkC rc RCW nx5 p2 tm5 off5 pos5 HPI5 HT5)|].
    intros []. apply fr_exI; intros tm6. apply fr_pure; intros HT6.
    unfold RCL. cbn [rc_Kx rc_e0 rc_d rc_C rc_oh rc_hs rc_fp rc_F0 rc_B rc mkrc k_path] in HT6 |- *. rewrite hrem_hd. cbn [HSH]. rewrite (hrem_notin nx2 [out]) by (intros [E|[]]; pose proof (rw_oh _ RCW) as X; cbn in X; apply X; rewrite E; reflexivity).
    eapply ru_bind; [apply (us_unlink (CEG:=CEG) (CEC:=CEC) segs tm6 nx5 _ _ _ _ _ TMPNAME (K_clear_KH (Some (out, fdo))))|].
    intros r1. apply usim_pure. intros _. apply ru_ret. intros sG moG sC moC HR. eexists tm6, nx5, (Some (out, fdo)), _. exact (conj HT6 (proj1 HR)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation emit_dG := (@emit_d PS hptr ps_libc set_libc).

#[using="STK"] Lemma pr_call_loop LB data : forall n tm nx ho C rc0,
  TML tm (LH ho LB) -> LBok LB -> zlength data < MAX_INPUT ->
  usimS (RH tm nx ho C) (call_loop emit_dG (harness_call fopsG fo_nop stkG) n data rc0) (call_loop emit_dG (harness_call fopsC fo_nop stkC) n data rc0)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx' ho' C', TML tm' (LH ho' LB) /\ RH tm' nx' ho' C' sG moG sC moC)).
Proof.
  induction n as [|n IH]; intros tm nx ho C rc0 HT HL HD; cbn [call_loop].
  - apply ru_ret. intros sG moG sC moC HR. exists tm, nx, ho, C. exact (conj HT HR).
  - unfold harness_call at 1 2. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
    eapply (ru_bind segs _ _ _ _ (fun _ => fun sG moG sC moC => exists tm' nx' ho' C', TML tm' (LH ho' LB) /\ RH tm' nx' ho' C' sG moG sC moC)).
    { eapply ru_bind; [apply (pr_fuzz_one tm nx ho C LB data HT HL HD)|]. intros []. apply ru_ret. intros ? ? ? ? HR. exact HR. }
    intros rc. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros ho1. apply usim_exI; intros C1. apply usim_pure; intros HT1.
    unfold RH. eapply ru_bind; [apply us_emit_d|]. intros []. apply (IH tm1 nx1 ho1 C1 _ HT1 HL HD).
Qed.

#[using="Type"] Lemma EXT_of_TML tm tm' L L' : TML tm L -> TML tm' L' -> (forall x, In x L -> In x L') -> EXT tm tm'.
Proof.
  intros HT HT' HI k n Hk. apply (TML_lookup _ _ _ _ HT'). apply HI.
  apply elem_of_map_to_list in Hk. unfold TML in HT. rewrite HT in Hk. apply list_elem_of_In in Hk. exact Hk.
Qed.
#[using="Type"] Lemma exit_ok_KH ho : exit_ok (KH ho).
Proof. intros e h He Ho. destruct ho as [[o f]|]; [| destruct He]. destruct He as [<-|[]]. split; reflexivity. Qed.
#[using="Type"] Lemma In_LH x ho LB : In x LB -> In x (LH ho LB).
Proof. intros H. destruct ho as [[o f]|]; cbn [LH]; [right|]; exact H. Qed.

(* [comment removed for export] *)
#[using="STK"] Theorem us_run tm nx config payload :
  zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> zlength payload < MAX_INPUT ->
  usimS (RUK tm nx [] [] idl (WF None [] [])) (Prog.run fopsG fo_nop stkG config payload) (Prog.run fopsC fo_nop stkC config payload)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx' K' C' oh' hs' F',
                   EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K' /\
                   RUK tm' nx' K' C' idl (WF oh' hs' F') sG moG sC moC)).
Proof.
  intros HL1 HL2 HD. set (LB := map_to_list tm).
  assert (HT : TML tm LB) by (unfold TML; reflexivity).
  assert (EL : zlen LB = zlen (sizes tm)) by (unfold sizes, zlen; rewrite length_map; reflexivity).
  assert (ER : R63N (map snd LB) = R63N (sizes tm)) by reflexivity.
  assert (B26p : 0 <= B26) by (unfold B26, PGSZ; lia).
  assert (HLB : LBok LB) by (split; [lia| unfold BASEB; lia]).
  pose proof (zlength_nonneg payload) as NP.
  (* [comment removed for export] *)
  assert (FIN : forall tm' nx' ho' C' (z : Z), TML tm' (LH ho' LB) ->
            usimS (RH tm' nx' ho' C') (mret z) (mret z)
                  (eqpost (fun _ => fun sG moG sC moC => exists tm'' nx'' K' C'' oh' hs' F',
                     EXT tm tm'' /\ PHI P9 + R63N (sizes tm'') <= BLIVE /\ exit_ok K' /\ RUK tm'' nx'' K' C'' idl (WF oh' hs' F') sG moG sC moC))).
  { intros tm' nx' ho' C' z HT'. apply ru_ret. intros sG moG sC moC HR. exists tm', nx', (KH ho'), C', (OH ho'), (HSH ho'), (FH ho').
    split; [exact (EXT_of_TML _ _ _ _ HT HT' (fun x Hx => In_LH x ho' LB Hx))|].
    split; [destruct (LH_budget tm' ho' LB 0 HT' HLB ltac:(unfold MMAP_THRESHOLD; lia)) as (_ & X & _); pose proof (bigb_nonneg 0); lia|].
    split; [apply exit_ok_KH| exact HR]. }
  unfold Prog.run, target_run. cbv zeta. change (RUK tm nx [] [] idl (WF None [] [])) with (RH tm nx None []).
  destruct (length payload =? 0)%nat eqn:EP.
  - apply ru_bind_retl. eapply ru_bind; [apply (pr_call_loop LB payload _ tm nx None [] false HT HLB HD)|].
    intros rc. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros ho1. apply usim_exI; intros C1. apply usim_pure; intros HT1.
    apply ru_bind_retl. apply (FIN _ _ _ _ _ HT1).
  - apply Nat.eqb_neq in EP.
    unfold RH. apply ru_use. intros sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh _ _ _ _ _ _ _ _ _ _ HT HR0) as FR. clear HR0.
    pose proof (bigb_le (zlength payload) NP) as BP.
    eapply (ru_bind segs _ _ _ _ (fun owned => fun sG moG sC moC => (owned = Some (Some nx) /\ TML (<[nx:=zlength payload]> tm) ((nx, zlength payload) :: LB)) /\
                                    RUK (<[nx := zlength payload]> tm) (N.succ nx) [] [] idl (WF None [] []) sG moG sC moC)).
    { eapply ru_bind.
      { eapply (gr_malloc (CEG:=CEG) (CEC:=CEC) segs tm LB nx [] [] _ (zlength payload) HT); [lia| unfold MAX_INPUT in HD; lia| unfold QMAX, MAX_INPUT, PGSZ in *; lia|].
        rewrite ER, PHI_P9. unfold B26, MAX_INPUT, BLIVE, PGSZ in *. lia. }
      intros q. apply usim_pure. intros [-> HT1]. apply ru_ret. intros sG moG sC moC HR. split; [split; [reflexivity| exact HT1]| exact HR]. }
    intros owned. apply usim_pure. intros [-> HT1].
    assert (HLB1 : LBok ((nx, zlength payload) :: LB)).
    { split; [rewrite zlen_cons; lia|]. cbn [map snd]. rewrite R63N_cons. unfold BASEB, B26, MAX_INPUT in *. lia. }
    change (RUK (<[nx:=zlength payload]> tm) (N.succ nx) [] [] idl (WF None [] [])) with (RH (<[nx:=zlength payload]> tm) (N.succ nx) None []).
    eapply ru_bind; [apply (pr_call_loop _ payload _ _ (N.succ nx) None [] false HT1 HLB1 HD)|].
    intros rc. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros ho1. apply usim_exI; intros C1. apply usim_pure; intros HT2.
    unfold RH. pose proof (TML_nodup _ _ HT2) as ND2.
    eapply ru_bind.
    { eapply (gr_free (CEG:=CEG) (CEC:=CEC) segs _ _ nx1 _ _ _ nx (zlength payload) HT2); [apply In_LH; left; reflexivity|].
      destruct (LH_budget tm1 ho1 _ 0 HT2 HLB1 ltac:(unfold MMAP_THRESHOLD; lia)) as (_ & _ & X). exact X. }
    intros []. apply usim_pure. intros HT3.
    assert (HT4 : TML (delete nx tm1) (LH ho1 LB)).
    { destruct ho1 as [[o f]|]; cbn [LH lrm] in HT3 |- *.
      - cbn [LH map fst] in ND2. inversion ND2 as [|? ? NI _]; subst.
        destruct (N.eqb_spec o nx) as [E|NE]; [exfalso; apply NI; left; symmetry; exact E|]. rewrite N.eqb_refl in HT3. exact HT3.
      - rewrite N.eqb_refl in HT3. exact HT3. }
    change (RUK (delete nx tm1) nx1 (KH ho1) C1 idl (WF (OH ho1) (HSH ho1) (FH ho1))) with (RH (delete nx tm1) nx1 ho1 C1).
    apply (FIN _ _ _ _ _ HT4).
Qed.

End Harness.

End WithCeil.

(* [comment removed for export] *)
Theorem run_contract_holds segsC stkG stkC : stk_ok stkG -> run_contract_u segsC stkG stkC.
Proof. intros STK CEG CEC tm nx config payload H1 H2 H3. exact (us_run (CEG:=CEG) (CEC:=CEC) segsC stkG stkC STK tm nx config payload H1 H2 H3). Qed.
End UPcapE.

(* [comment removed for export] *)
Module EquivFinal.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad HeapFull StdioCore Stdio StartupFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UBase UStdio UDriver. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UPcapE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Final.
Variables (segsS : list Segment) (pcS : N) (phS : PhdrInfo).
Variables (segsT : list Segment) (pcT : N) (phT : PhdrInfo).
Variables (tbS tbT : ExecEntry -> Z) (stkS stkT : ExecEntry -> stack_site -> Z).
Variables (secS secT : ExecEntry -> Z).
Hypothesis SECS : forall en, 0 <= secS en < 2^64.
Hypothesis SECT : forall en, 0 <= secT en < 2^64.
#[local] Notation treeS := (treeS segsS tbS stkS secS).
#[local] Notation treeT := (treeT segsT tbT stkT secT).
(* [comment removed for export] *)
Variables (limS limT : Z).
Hypothesis IOS : image_ok segsS limS.
Hypothesis IOT : image_ok segsT limT.
Hypothesis TLSS : forall en inp, valid_entry (mkImage segsS pcS phS) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsS (tbS en).
Hypothesis TLST : forall en inp, valid_entry (mkImage segsT pcT phT) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsT (tbT en).
Hypothesis STKS : forall en, stk_ok (stkS en).
Hypothesis STKT : forall en, stk_ok (stkT en).
Hypothesis IMPL_S : exists QS, forall en inp, valid_entry (mkImage segsS pcS phS) en inp -> valid_input inp ->
  impl segsS (at_node segsS) (npeek segsS) (treeS inp en) QS (ms0 segsS pcS phS en inp).
Hypothesis IMPL_T : exists QT, forall en inp, valid_entry (mkImage segsT pcT phT) en inp -> valid_input inp ->
  impl segsT (at_node segsT) (npeek segsT) (treeT inp en) QT (ms0 segsT pcT phT en inp).

#[using="SECS SECT IOS IOT TLSS TLST STKS STKT"] Theorem trees_equiv_final : trees_equiv_lim limS limT segsS pcS phS segsT pcT phT treeS treeT.
Proof. exact (route_abs_trees_equiv_u segsS pcS phS segsT pcT phT tbS tbT stkS stkT secS secT SECS SECT limS limT IOS IOT TLSS TLST STKS STKT run_contract_holds). Qed.

#[using="SECS IOS TLSS STKS IMPL_S"] Theorem tree_ok_S_final : exists QS, tree_ok segsS pcS phS limS treeS QS.
Proof. exact (tree_ok_S_u segsS pcS phS tbS stkS secS SECS limS IOS TLSS STKS run_contract_holds IMPL_S). Qed.

#[using="SECT IOT TLST STKT IMPL_T"] Theorem tree_ok_T_final : exists QT, tree_ok segsT pcT phT limT treeT QT.
Proof. exact (tree_ok_T_u segsT pcT phT tbT stkT secT SECT limT IOT TLST STKT run_contract_holds IMPL_T). Qed.

(* [comment removed for export] *)
#[using="tbS tbT stkS stkT secS secT SECS SECT IOS IOT TLSS TLST STKS STKT IMPL_S IMPL_T"] Theorem route_abs_main_final :
  strong_universal_error_free_T_scfg_budgets CFG limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof. exact (route_abs_main_u segsS pcS phS segsT pcT phT tbS tbT stkS stkT secS secT SECS SECT limS limT IOS IOT TLSS TLST STKS STKT run_contract_holds IMPL_S IMPL_T). Qed.
End Final.

(* [comment removed for export] *)
Theorem route_abs_main_final_scfg :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo) (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tbS tbT : ExecEntry -> Z) (stkS stkT : ExecEntry -> stack_site -> Z) (secS secT : ExecEntry -> Z),
  (forall en, 0 <= secS en < 2^64) -> (forall en, 0 <= secT en < 2^64) ->
  image_ok segsS source_alloc_limit -> image_ok segsT target_alloc_limit ->
  (forall en inp, valid_entry (mkImage segsS pcS phS) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsS (tbS en)) ->
  (forall en inp, valid_entry (mkImage segsT pcT phT) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsT (tbT en)) ->
  (forall en, stk_ok (stkS en)) -> (forall en, stk_ok (stkT en)) ->
  (exists QS, forall en inp, valid_entry (mkImage segsS pcS phS) en inp -> valid_input inp ->
     impl segsS (at_node segsS) (npeek segsS) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeS segsS tbS stkS secS inp en) QS (ms0 segsS pcS phS en inp)) ->
  (exists QT, forall en inp, valid_entry (mkImage segsT pcT phT) en inp -> valid_input inp ->
     impl segsT (at_node segsT) (npeek segsT) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.treeT segsT tbT stkT secT inp en) QT (ms0 segsT pcT phT en inp)) ->
  strong_universal_error_free_T_scfg CFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT tbS tbT stkS stkT secS secT SECS SECT IOS IOT TLSS TLST STKS STKT IMPL_S IMPL_T.
  destruct (tree_ok_S_final segsS pcS phS tbS stkS secS SECS source_alloc_limit IOS TLSS STKS IMPL_S) as [QS HS].
  destruct (tree_ok_T_final segsT pcT phT tbT stkT secT SECT target_alloc_limit IOT TLST STKT IMPL_T) as [QT HT].
  exact (strong_universal_error_free_scfg_from_trees_gen segsS pcS phS segsT pcT phT _ _ QS QT HS HT
           (trees_equiv_final segsS pcS phS segsT pcT phT tbS tbT stkS stkT secS secT SECS SECT
              source_alloc_limit target_alloc_limit IOS IOT TLSS TLST STKS STKT)).
Qed.
End EquivFinal.
