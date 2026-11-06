(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_ReallocQ HeapFull Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapDrive HeapSim NodeSim ProgSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA NodesAS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StdioCore Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module HeapI_S.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_ReallocQ HeapFull Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Addr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.MI_Calloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_ReallocQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapDrive HeapSim NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UBase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA NodesAS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unsafeS (n : node) (_ : unit) (mo : Model) : Prop := nsafe n mo.
Definition ugstepS (n : node) (_ : resp) (g : unit) : unit := g.
Lemma UK_safeS : forall n (g : unit) mo, xnode n -> nsafe n mo -> unsafeS n g mo.
Proof. intros n g mo _ H. exact H. Qed.
Lemma UK_stepS : forall n rsp (g : unit), xnode n -> ugstepS n rsp g = g.
Proof. intros. reflexivity. Qed.

Lemma twfX_unit {R} (t : itree node R) : forall mo (P : R -> Model -> Prop) (g : unit),
  twf t mo P -> twfX unsafeS ugstepS t g mo (fun r _ mo' => P r mo').
Proof.
  induction t as [r|n k IH]; intros mo P g H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. exact (Hk _ _ _ Hst).
Qed.

(* [comment removed for export] *)
Lemma okn_silent n mo rsp mo' evs : okn n -> nstep n mo rsp mo' evs -> evs = [].
Proof. intros Hn Hst. destruct n; cbn in Hn; try (exfalso; exact Hn); cbn [nstep] in Hst; try exact (proj1 Hst). exact (proj1 (proj2 Hst)). Qed.
Lemma oknodes_silent {R} (t : itree node R) : forall mo tr r mo', oknodes t mo -> tpath nstep t mo tr r mo' -> tr = [].
Proof.
  induction t as [r0|n k IH]; intros mo tr r mo' Hok Hp; cbn in Hp.
  - destruct Hp as (_ & _ & ->). reflexivity.
  - destruct Hok as [Hn Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    rewrite (okn_silent _ _ _ _ _ Hn Hst). cbn. eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

(* [comment removed for export] *)
Lemma lseek_result_vmS : forall mo fd mk base off eff mo', lseek_result mo fd mk base off eff mo' -> m_vm mo' = m_vm mo.
Proof.
  intros mo fd mk base off eff mo' H. unfold lseek_result in H. destruct base as [b|]; [| destruct H].
  destruct (lseek_dest b (Z_to_bv 64 off)); destruct H as [_ ->]; reflexivity.
Qed.
Lemma xnode_nstep_vmS : forall n mo eff mo' evs,
  xnode n -> nstep n mo eff mo' evs -> m_vm mo' = m_vm mo.
Proof.
  intros n mo eff mo' evs Hx H.
  destruct n; cbn [xnode] in Hx; try contradiction; try (eapply NodesAS.nstep_vm_same; [| exact H]; exact I); cbn [nstep] in H.
  all: try (destruct H as (-> & _); reflexivity); try (destruct H; fail).
  destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [_ ->]; reflexivity.
Qed.
Lemma xnode_static_ok n mo rsp mo' evs : xnode n -> nstep n mo rsp mo' evs -> node_static_ok n.
Proof. intros Hx Hst. destruct n; cbn in Hx |- *; try exact I; try (exfalso; exact Hx). exact (proj1 (proj2 Hst)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[local] Notation full_ops := (full_ops (CE:=CE)).

Definition ShiQ (tm : gmap N Z) (nx : N) (P : Z) (s : PS) (mo : Model) : Prop :=
  HQ P9 htrue s mo /\ tok_szmap (ps_heap s) = tm /\ fh_next (ps_heap s) = nx /\ pot_ok P.
Definition ShiG (tm : gmap N Z) (nx : N) (P : Z) (g : unit) (s : PS) (mo : Model) : Prop := ShiQ tm nx P s mo.

#[using="Type"] Lemma ShiQ_heap tm nx P (s s' : PS) mo : ps_heap s' = ps_heap s -> ShiQ tm nx P s mo -> ShiQ tm nx P s' mo.
Proof. intros E (HQs & ET & EN & PP). split; [exact (HQ_same_heap P9 s s' mo E HQs)|]. rewrite E. auto. Qed.

#[using="Type"] Lemma ShiQ_step tm nx P s mo n rsp mo' evs :
  xnode n -> nstep n mo rsp mo' evs -> m_halted mo' = None -> ShiQ tm nx P s mo -> ShiQ tm nx P s mo'.
Proof.
  intros Hx Hst HH (HQs & ET & EN & PP). split; [| auto].
  eapply (HQ_xstep P9); [exact (xnode_static_ok _ _ _ _ _ Hx Hst)| exact HQs| exact Hst|].
  pose proof (xnode_nstep_vmS _ _ _ _ _ Hx Hst) as VM. unfold m_vmmaps. rewrite VM. reflexivity.
Qed.

#[using="Type"] Lemma ShiQ_below tm nx P s mo k n : ShiQ tm nx P s mo -> tm !! k = Some n -> (k < nx)%N.
Proof.
  intros ([_ TB] & ET & EN & _) Hk. subst tm nx. apply TB. unfold tok_szmap in Hk. rewrite lookup_fmap in Hk.
  destruct (fh_blk (ps_heap s) !! k); [discriminate| cbn in Hk; discriminate].
Qed.
#[using="Type"] Lemma ShiQ_fresh tm nx P s mo : ShiQ tm nx P s mo -> tm !! nx = None.
Proof. intros HS. destruct (tm !! nx) as [n|] eqn:E; [| reflexivity]. pose proof (ShiQ_below _ _ _ _ _ _ _ HS E). lia. Qed.
#[using="Type"] Lemma ShiQ_pot tm nx P s mo : ShiQ tm nx P s mo -> pot_ok P.
Proof. intros (_ & _ & _ & PP). exact PP. Qed.

#[using="Type"] Lemma ShiQ_addr tm nx P s mo k n : ShiQ tm nx P s mo -> tm !! k = Some n ->
  0 < ho_addr full_ops (ps_heap s) k /\ ho_addr full_ops (ps_heap s) k + n <= alloc_ceiling /\ 0 <= n.
Proof.
  intros (HQs & ET & _) Hk. destruct HQs as [[(L & LS & BL & INV & _ & _ & _ & _ & HP) _] _].
  destruct (tok_live (ps_heap s) tm k n ET Hk) as [p Hp].
  assert (HIn : In (p, n) (map blk_ptr BL)).
  { eapply Permutation_in; [exact HP|]. unfold tok_blocks. apply in_map_iff. exists (k, (p, n)). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Hp. }
  apply in_map_iff in HIn as (b & Eb & Hb). unfold blk_ptr in Eb. injection Eb as Ep En. subst p n.
  cbn [ho_addr full_ops]. unfold hf_addr. rewrite Hp.
  pose proof (blk_addr_range x0 (ps_m s) L BL LS INV b Hb) as (A1 & A2 & A3). unfold bptr_of in *.
  cbn [ps_m fheap_AllocSt] in A1, A2. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ShiQ_sizes tm nx P s mo : ShiQ tm nx P s mo -> tok_sizes (ps_heap s) = sizes tm.
Proof. intros (_ & ET & _). rewrite tok_sizes_sizes, ET. reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma oknodes_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo :
  oknodes t mo -> (forall a mo' tr, tpath nstep t mo tr (Ok a) mo' -> oknodes (f a) mo') -> oknodes (ebind t f) mo.
Proof. intros Ht Hf. unfold ebind. apply oknodes_bind; [exact Ht|]. intros [|a] mo' tr Hp; [exact I| exact (Hf a mo' tr Hp)]. Qed.

Section S.
Let MQP : malloc_core_fq_stmt := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc.malloc_core_fq_proof.
#[local] Notation D0 := ([] : list Segment).   (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma diag_leaf {A} (m : Monad.M PS A) (Q : A -> A -> @rel PS PS) s mo tr a s' mo' :
  fsimw (npeek D0) (fun sG moG sC moC => sG = s /\ moG = mo /\ sC = s /\ moC = mo) m m Q ->
  tpath nstep (m s) mo tr (Ok (a, s')) mo' -> exists b sC' moC', Q a b s' mo' sC' moC'.
Proof.
  intros HF Hp. destruct (HF s mo s mo (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))) as [HP _].
  destruct (wreach_tpath _ _ _ _ _ _ (npk_inh D0) (HP tr a s' mo' Hp)) as (trC & rC & moC' & _ & b & sC' & -> & _ & HQ).
  exists b, sC', moC'. exact HQ.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma set_heap_rest (s s' : PS) : (forall h, set_heap h s' = set_heap h s) -> ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s.
Proof.
  intros SG. pose proof (SG (ps_heap s')) as E. rewrite set_heap_eta in E. rewrite E. destruct s; cbn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma HR_diag s mo : HQ P9 htrue s mo -> HR P9 htrue htrue s mo s mo.
Proof. intros H. split; [exact H|]. split; [exact H|]. split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="MQP"] Lemma S_malloc_facts tm nx P s mo n :
  ShiQ tm nx P s mo -> pre_malloc tm P n ->
  etwf (hf_malloc n s) mo (fun _ _ => True)
  /\ oknodes (hf_malloc n s) mo
  /\ (forall tr a s' mo', tpath nstep (hf_malloc n s) mo tr (Ok (a, s')) mo' ->
        a = Some nx /\ ShiQ (<[nx := n]> tm) (N.succ nx) (P + n1 n) s' mo'
        /\ ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s /\ vm_only mo mo').
Proof.
  intros HS (Hn & Hov & HBQ & HR & HB & AP). pose proof HS as (HQs & ET & EN & PP). pose proof HQs as [FQs TBs].
  pose proof (ShiQ_sizes _ _ _ _ _ HS) as ES.
  assert (HR' : ROOMN (map snd (tok_blocks (ps_heap s))) P9 n) by (change (map snd (tok_blocks (ps_heap s))) with (tok_sizes (ps_heap s)); rewrite ES; exact HR).
  assert (HB' : PHI P9 + R63N (map snd (tok_blocks (ps_heap s))) + bigb n <= BLIVE) by (change (map snd (tok_blocks (ps_heap s))) with (tok_sizes (ps_heap s)); rewrite ES; exact HB).
  split; [| split].
  - eapply (mspec_etwf (fun s' mo' => FQ (tok_blocks (ps_heap s)) P9 htrue s' mo' /\ ROOMN (map snd (tok_blocks (ps_heap s))) P9 n) _ (fun _ _ _ => True)); [| exact (conj FQs HR')].
    unfold hf_malloc. eapply mspec_bind; [apply (raw_mallocF_Q MQP); [exact (hframe_frame htrue hframe_htrue)| exact Hn| exact HBQ]|].
    intros [q|]; [eapply mspec_bind; [apply tok_fresh_mspec| intros; apply mspec_ret; intros; exact I]| apply mspec_ret; intros; exact I].
  - destruct (malloc_setup P9 (tok_blocks (ps_heap s)) htrue s mo n (hframe_frame htrue hframe_htrue) FQs Hn HBQ HR' HB') as (L & LS & BL & INV & HP & FT & BD & (HK & _) & _).
    unfold hf_malloc, raw_mallocF, mbind, mget. cbn [ebind bind fst snd].
    apply oknodes_ebind.
    + apply oknodes_ebind; [exact (membedF_oknodes _ _ _ _ _ _ (hframe_frame htrue hframe_htrue) FT HK I)|]. intros [[st p] s1] mo' tr _. cbn. exact I.
    + intros [[q|] s1] mo' tr _; cbn; [| exact I]. unfold tok_fresh, mbind, mget, mupd, mret. cbn. exact I.
  - intros tr a s' mo' Hp.
    destruct (diag_leaf _ _ s mo tr a s' mo' (hf_malloc_sim_pt D0 P9 htrue htrue hframe_htrue hframe_htrue n s mo s mo Hn Hov HBQ (HR_diag s mo HQs) ltac:(rewrite ES; exact HR) ltac:(rewrite ES; exact HB)) Hp)
      as (b & sC' & moC' & Ea & _ & (HQ' & _ & _) & ET' & EN' & SG & _ & VO & _).
    destruct (set_heap_rest s s' SG) as (E1 & E2 & E3).
    split; [rewrite Ea, EN; reflexivity|]. split; [| auto].
    split; [exact HQ'|]. split; [rewrite ET', ET, EN; reflexivity|]. split; [rewrite EN', EN; reflexivity|].
    destruct AP as (A1 & A2 & _). unfold pot_ok, n1 in *. lia.
Qed.

#[using="MQP"] Lemma S_mallocG tm nx P g s mo n :
  ShiG tm nx P g s mo -> pre_malloc tm P n ->
  gop unsafeS ugstepS (hf_malloc n) nx s g mo (gpost ShiG (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo).
Proof.
  intros HS PRE. destruct (S_malloc_facts tm nx P s mo n HS PRE) as (SAFE & OKN & LEAF). split; [| split].
  - unfold etwfX. apply twfX_of_tpathX.
    { eapply twfX_mono; [apply twfX_unit; exact SAFE| intros; exact I]. }
    intros tr [|[a s']] g' mo' Hp; cbn.
    + exact (twf_tpath _ _ _ _ _ _ SAFE (tpathX_tpath _ _ _ _ _ _ _ _ Hp)).
    + destruct (LEAF tr a s' mo' (tpathX_tpath _ _ _ _ _ _ _ _ Hp)) as (Ea & HS' & E1 & E2 & E3 & VO).
      split; [exact Ea|]. destruct g'. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
  - intros tr r mo' Hp. exact (oknodes_silent _ _ _ _ _ OKN Hp).
  - intros tr Hx. exact (oknodes_no_texit _ _ _ OKN Hx).
Qed.

#[using="MQP"] Lemma S_mallocC segs tm nx P s mo n :
  ShiQ tm nx P s mo -> pre_malloc tm P n ->
  cop (npeek segs) (hf_malloc n) nx s mo (cpost ShiQ (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo).
Proof.
  intros HS PRE. destruct (S_malloc_facts tm nx P s mo n HS PRE) as (SAFE & OKN & LEAF). unfold cop.
  eapply wreach_mono; [exact (twf_drive segs _ mo _ SAFE OKN)|].
  intros tr [|[a s']] mo' [Hp HP]; cbn in HP; [destruct HP|].
  split; [exact (oknodes_silent _ _ _ _ _ OKN Hp)|]. destruct (LEAF tr a s' mo' Hp) as (-> & HS' & E1 & E2 & E3 & VO).
  exists s'. split; [reflexivity|]. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="MQP"] Lemma S_calloc_facts tm nx P s mo m n :
  ShiQ tm nx P s mo -> pre_calloc tm P m n ->
  etwf (hf_calloc m n s) mo (fun _ _ => True)
  /\ oknodes (hf_calloc m n s) mo
  /\ (forall tr a s' mo', tpath nstep (hf_calloc m n s) mo tr (Ok (a, s')) mo' ->
        a = Some nx /\ ShiQ (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s' mo'
        /\ ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s /\ vm_only mo mo').
Proof.
  intros HS (Hm & Hn & Hov1 & Hov2 & HBQ & HR & HB & AP). pose proof HS as (HQs & ET & EN & PP). pose proof HQs as [FQs TBs].
  pose proof (ShiQ_sizes _ _ _ _ _ HS) as ES.
  assert (HR' : ROOMN (map snd (tok_blocks (ps_heap s))) P9 (m * n)) by (change (map snd (tok_blocks (ps_heap s))) with (tok_sizes (ps_heap s)); rewrite ES; exact HR).
  assert (HB' : PHI P9 + R63N (map snd (tok_blocks (ps_heap s))) + bigb (m * n) <= BLIVE) by (change (map snd (tok_blocks (ps_heap s))) with (tok_sizes (ps_heap s)); rewrite ES; exact HB).
  split; [| split].
  - eapply (mspec_etwf (fun s' mo' => FQ (tok_blocks (ps_heap s)) P9 htrue s' mo' /\ ROOMN (map snd (tok_blocks (ps_heap s))) P9 (m * n)) _ (fun _ _ _ => True)); [| exact (conj FQs HR')].
    unfold hf_calloc. eapply mspec_bind; [apply (raw_callocF_Q MQP); [exact (hframe_frame htrue hframe_htrue)| exact Hm| exact Hn| exact HBQ]|].
    intros [q|]; [eapply mspec_bind; [apply tok_fresh_mspec| intros; apply mspec_ret; intros; exact I]| apply mspec_ret; intros; exact I].
  - destruct (calloc_setup P9 (tok_blocks (ps_heap s)) htrue s mo m n (hframe_frame htrue hframe_htrue) FQs Hm Hn HBQ HR' HB') as (L & LS & BL & INV & HP & FT & BD & (HK & _) & _).
    unfold hf_calloc, raw_callocF, mbind, mget. cbn [ebind bind fst snd].
    apply oknodes_ebind.
    + apply oknodes_ebind; [exact (membedF_oknodes _ _ _ _ _ _ (hframe_frame htrue hframe_htrue) FT HK I)|]. intros [[st p] s1] mo' tr _. cbn. exact I.
    + intros [[q|] s1] mo' tr _; cbn; [| exact I]. unfold tok_fresh, mbind, mget, mupd, mret. cbn. exact I.
  - intros tr a s' mo' Hp.
    destruct (diag_leaf _ _ s mo tr a s' mo' (hf_calloc_sim_pt D0 P9 htrue htrue hframe_htrue hframe_htrue m n s mo s mo Hm Hn Hov1 Hov2 HBQ (HR_diag s mo HQs) ltac:(rewrite ES; exact HR) ltac:(rewrite ES; exact HB)) Hp)
      as (b & sC' & moC' & Ea & _ & (HQ' & _ & _) & ET' & EN' & SG & _ & VO & _).
    destruct (set_heap_rest s s' SG) as (E1 & E2 & E3).
    split; [rewrite Ea, EN; reflexivity|]. split; [| auto].
    split; [exact HQ'|]. split; [rewrite ET', ET, EN; reflexivity|]. split; [rewrite EN', EN; reflexivity|].
    destruct AP as (A1 & A2 & _). unfold pot_ok, n1 in *. lia.
Qed.

#[using="MQP"] Lemma S_callocG tm nx P g s mo m n :
  ShiG tm nx P g s mo -> pre_calloc tm P m n ->
  gop unsafeS ugstepS (hf_calloc m n) nx s g mo (gpost ShiG (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo).
Proof.
  intros HS PRE. destruct (S_calloc_facts tm nx P s mo m n HS PRE) as (SAFE & OKN & LEAF). split; [| split].
  - unfold etwfX. apply twfX_of_tpathX.
    { eapply twfX_mono; [apply twfX_unit; exact SAFE| intros; exact I]. }
    intros tr [|[a s']] g' mo' Hp; cbn.
    + exact (twf_tpath _ _ _ _ _ _ SAFE (tpathX_tpath _ _ _ _ _ _ _ _ Hp)).
    + destruct (LEAF tr a s' mo' (tpathX_tpath _ _ _ _ _ _ _ _ Hp)) as (Ea & HS' & E1 & E2 & E3 & VO).
      split; [exact Ea|]. destruct g'. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
  - intros tr r mo' Hp. exact (oknodes_silent _ _ _ _ _ OKN Hp).
  - intros tr Hx. exact (oknodes_no_texit _ _ _ OKN Hx).
Qed.

#[using="MQP"] Lemma S_callocC segs tm nx P s mo m n :
  ShiQ tm nx P s mo -> pre_calloc tm P m n ->
  cop (npeek segs) (hf_calloc m n) nx s mo (cpost ShiQ (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo).
Proof.
  intros HS PRE. destruct (S_calloc_facts tm nx P s mo m n HS PRE) as (SAFE & OKN & LEAF). unfold cop.
  eapply wreach_mono; [exact (twf_drive segs _ mo _ SAFE OKN)|].
  intros tr [|[a s']] mo' [Hp HP]; cbn in HP; [destruct HP|].
  split; [exact (oknodes_silent _ _ _ _ _ OKN Hp)|]. destruct (LEAF tr a s' mo' Hp) as (-> & HS' & E1 & E2 & E3 & VO).
  exists s'. split; [reflexivity|]. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma S_free_facts tm nx P s mo k n :
  ShiQ tm nx P s mo -> pre_free tm k n ->
  etwf (hf_free k s) mo (fun _ _ => True)
  /\ oknodes (hf_free k s) mo
  /\ (forall tr a s' mo', tpath nstep (hf_free k s) mo tr (Ok (a, s')) mo' ->
        ShiQ (delete k tm) nx P s' mo'
        /\ ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s /\ vm_only mo mo').
Proof.
  intros HS [Hk HB]. pose proof HS as (HQs & ET & EN & PP). pose proof HQs as [FQs TBs].
  pose proof (ShiQ_sizes _ _ _ _ _ HS) as ES.
  destruct (tok_live (ps_heap s) tm k n ET Hk) as [p Hp]. pose proof (tok_blocks_delete (ps_heap s) k p n Hp) as PD.
  assert (HB' : PHI P9 + R63N (map snd (tok_blocks (ps_heap s))) <= BLIVE) by (change (map snd (tok_blocks (ps_heap s))) with (tok_sizes (ps_heap s)); rewrite ES; exact HB).
  split; [| split].
  - eapply (mspec_etwf (fun s' mo' => s' = s /\ mo' = mo) _ (fun _ _ _ => True)); [| split; reflexivity].
    unfold hf_free, tok_lookup. eapply mspec_bind with (Q1 := fun b s' mo' => b = fh_blk (ps_heap s) !! k /\ s' = s /\ mo' = mo).
    { eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret. intros s1 mo1 [-> [-> ->]]. repeat split; reflexivity. }
    intros b. cbv beta. apply mspec_pointwise. intros ? ? (-> & -> & ->). rewrite Hp.
    eapply mspec_bind.
    { eapply mspec_conseq; [apply (raw_freeF_Q (tok_blocks (hdel k (ps_heap s))) P9 htrue p n (hframe_frame htrue hframe_htrue))| | intros; exact I].
      intros s1 mo1 [-> ->]. eapply FQ_perm; [exact PD| exact FQs]. }
    intros []. unfold tok_drop. apply mspec_upd' with (Q := fun _ _ _ => True). intros; exact I.
  - destruct (free_setup P9 (tok_blocks (ps_heap s)) (tok_blocks (hdel k (ps_heap s))) htrue s mo p n (hframe_frame htrue hframe_htrue) FQs PD HB') as (L & LS & BL & c & off & INV & HIn & Ep & HP & FT & BD & (HK & _) & _).
    unfold hf_free, tok_lookup, raw_freeF, tok_drop, mbind, mget, mupd, mret. cbn [ebind bind fst snd]. rewrite Hp. cbn [ebind bind fst snd].
    apply oknodes_ebind.
    + apply oknodes_ebind; [exact (membedF_oknodes _ _ _ _ _ _ (hframe_frame htrue hframe_htrue) FT HK I)|]. intros [st s1] mo' tr _. cbn. exact I.
    + intros [[] s1] mo' tr _. cbn. exact I.
  - intros tr a s' mo' Hpth.
    destruct (diag_leaf _ _ s mo tr a s' mo' (hf_free_sim_pt D0 P9 htrue htrue hframe_htrue hframe_htrue k n s mo s mo (HR_diag s mo HQs) ltac:(rewrite ET; exact Hk) ltac:(rewrite ES; exact HB)) Hpth)
      as (b & sC' & moC' & (HQ' & _ & _) & ET' & EN' & SG & _ & VO & _).
    destruct (set_heap_rest s s' SG) as (E1 & E2 & E3).
    split; [| auto]. split; [exact HQ'|]. split; [rewrite ET', ET; reflexivity|]. split; [rewrite EN', EN; reflexivity| exact PP].
Qed.

#[using="Type"] Lemma S_freeG tm nx P g s mo k n :
  ShiG tm nx P g s mo -> pre_free tm k n ->
  gopu unsafeS ugstepS (hf_free k) s g mo (gpost ShiG (delete k tm) nx P s mo).
Proof.
  intros HS PRE. destruct (S_free_facts tm nx P s mo k n HS PRE) as (SAFE & OKN & LEAF). split; [| split].
  - unfold etwfX. apply twfX_of_tpathX.
    { eapply twfX_mono; [apply twfX_unit; exact SAFE| intros; exact I]. }
    intros tr [|[a s']] g' mo' Hp; cbn.
    + exact (twf_tpath _ _ _ _ _ _ SAFE (tpathX_tpath _ _ _ _ _ _ _ _ Hp)).
    + destruct (LEAF tr a s' mo' (tpathX_tpath _ _ _ _ _ _ _ _ Hp)) as (HS' & E1 & E2 & E3 & VO).
      destruct g'. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
  - intros tr r mo' Hp. exact (oknodes_silent _ _ _ _ _ OKN Hp).
  - intros tr Hx. exact (oknodes_no_texit _ _ _ OKN Hx).
Qed.

#[using="Type"] Lemma S_freeC segs tm nx P s mo k n :
  ShiQ tm nx P s mo -> pre_free tm k n ->
  copu (npeek segs) (hf_free k) s mo (cpost ShiQ (delete k tm) nx P s mo).
Proof.
  intros HS PRE. destruct (S_free_facts tm nx P s mo k n HS PRE) as (SAFE & OKN & LEAF). unfold copu.
  eapply wreach_mono; [exact (twf_drive segs _ mo _ SAFE OKN)|].
  intros tr [|[[] s']] mo' [Hp HP]; cbn in HP; [destruct HP|].
  split; [exact (oknodes_silent _ _ _ _ _ OKN Hp)|]. destruct (LEAF tr tt s' mo' Hp) as (HS' & E1 & E2 & E3 & VO).
  exists s'. split; [reflexivity|]. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="MQP"] Lemma S_realloc_facts tm nx P s mo k n n' :
  ShiQ tm nx P s mo -> pre_realloc tm P k n n' ->
  etwf (hf_realloc k n' s) mo (fun _ _ => True)
  /\ oknodes (hf_realloc k n' s) mo
  /\ (forall tr a s' mo', tpath nstep (hf_realloc k n' s) mo tr (Ok (a, s')) mo' ->
        a = Some nx /\ ShiQ (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') s' mo'
        /\ ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s /\ vm_only mo mo').
Proof.
  intros HS (Hk & Hn1 & Hov & Hnx & HBQ & HR & HB & AP). pose proof HS as (HQs & ET & EN & PP). pose proof HQs as [FQs TBs].
  pose proof (ShiQ_sizes _ _ _ _ _ HS) as ES. assert (Hn : 0 <= n') by lia.
  destruct (tok_live (ps_heap s) tm k n ET Hk) as [p Hp]. pose proof (tok_blocks_delete (ps_heap s) k p n Hp) as PD.
  assert (HR' : ROOMN (map snd (tok_blocks (ps_heap s))) P9 n') by (change (map snd (tok_blocks (ps_heap s))) with (tok_sizes (ps_heap s)); rewrite ES; exact HR).
  assert (HB' : PHI P9 + R63N (map snd (tok_blocks (ps_heap s))) + bigb n' <= BLIVE) by (change (map snd (tok_blocks (ps_heap s))) with (tok_sizes (ps_heap s)); rewrite ES; exact HB).
  split; [| split].
  - eapply (mspec_etwf (fun s' mo' => s' = s /\ mo' = mo) _ (fun _ _ _ => True)); [| split; reflexivity].
    unfold hf_realloc, tok_lookup. eapply mspec_bind with (Q1 := fun b s' mo' => b = fh_blk (ps_heap s) !! k /\ s' = s /\ mo' = mo).
    { eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret. intros s1 mo1 [-> [-> ->]]. repeat split; reflexivity. }
    intros b. cbv beta. apply mspec_pointwise. intros ? ? (-> & -> & ->). rewrite Hp.
    eapply mspec_bind.
    { eapply mspec_conseq; [apply (raw_reallocF_Q MQP (tok_blocks (hdel k (ps_heap s))) P9 htrue p n n' (hframe_frame htrue hframe_htrue) Hn Hov Hnx HBQ)| | intros; exact I].
      intros s1 mo1 [-> ->]. split; [eapply FQ_perm; [exact PD| exact FQs]|].
      destruct HR' as [R1 R2]. rewrite (LRN_perm _ _ (size_to_class n') (Permutation_map snd PD)) in R1. rewrite (n63N_perm _ _ (Permutation_map snd PD)) in R2. exact (conj R1 R2). }
    intros [q|]; [| apply mspec_ret; intros; exact I].
    unfold tok_drop. eapply mspec_bind; [apply mspec_upd' with (Q := fun _ _ _ => True); intros; exact I|]. intros [].
    eapply mspec_bind; [apply tok_fresh_mspec| intros; apply mspec_ret; intros; exact I].
  - destruct (realloc_setup P9 (tok_blocks (ps_heap s)) (tok_blocks (hdel k (ps_heap s))) htrue s mo p n n' (hframe_frame htrue hframe_htrue) FQs PD Hn Hov Hnx HBQ HR' HB')
      as (L & LS & BL & c & off & INV & HIn & Ep & HP & FT & BD & (HK & _) & _).
    unfold hf_realloc, tok_lookup, raw_reallocF, tok_drop, tok_fresh, mbind, mget, mupd, mret. cbn [ebind bind fst snd]. rewrite Hp. cbn [ebind bind fst snd].
    apply oknodes_ebind.
    + apply oknodes_ebind; [exact (membedF_oknodes _ _ _ _ _ _ (hframe_frame htrue hframe_htrue) FT HK I)|]. intros [[st q] s1] mo' tr _. cbn. exact I.
    + intros [[q|] s1] mo' tr _; cbn; exact I.
  - intros tr a s' mo' Hpth.
    destruct (diag_leaf _ _ s mo tr a s' mo' (hf_realloc_sim_pt D0 P9 htrue htrue hframe_htrue hframe_htrue k n n' s mo s mo Hn Hov Hnx HBQ (HR_diag s mo HQs) ltac:(rewrite ET; exact Hk) ltac:(rewrite ES; exact HR) ltac:(rewrite ES; exact HB)) Hpth)
      as (b & sC' & moC' & Ea & _ & (HQ' & _ & _) & ET' & EN' & SG & _ & VO & _).
    destruct (set_heap_rest s s' SG) as (E1 & E2 & E3).
    split; [rewrite Ea, EN; reflexivity|]. split; [| auto].
    split; [exact HQ'|]. split; [rewrite ET', ET, EN; reflexivity|]. split; [rewrite EN', EN; reflexivity|].
    destruct AP as (A1 & A2 & _). unfold pot_ok in *. lia.
Qed.

#[using="MQP"] Lemma S_reallocG tm nx P g s mo k n n' :
  ShiG tm nx P g s mo -> pre_realloc tm P k n n' ->
  gop unsafeS ugstepS (hf_realloc k n') nx s g mo (gpost ShiG (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') s mo).
Proof.
  intros HS PRE. destruct (S_realloc_facts tm nx P s mo k n n' HS PRE) as (SAFE & OKN & LEAF). split; [| split].
  - unfold etwfX. apply twfX_of_tpathX.
    { eapply twfX_mono; [apply twfX_unit; exact SAFE| intros; exact I]. }
    intros tr [|[a s']] g' mo' Hp; cbn.
    + exact (twf_tpath _ _ _ _ _ _ SAFE (tpathX_tpath _ _ _ _ _ _ _ _ Hp)).
    + destruct (LEAF tr a s' mo' (tpathX_tpath _ _ _ _ _ _ _ _ Hp)) as (Ea & HS' & E1 & E2 & E3 & VO).
      split; [exact Ea|]. destruct g'. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
  - intros tr r mo' Hp. exact (oknodes_silent _ _ _ _ _ OKN Hp).
  - intros tr Hx. exact (oknodes_no_texit _ _ _ OKN Hx).
Qed.

#[using="MQP"] Lemma S_reallocC segs tm nx P s mo k n n' :
  ShiQ tm nx P s mo -> pre_realloc tm P k n n' ->
  cop (npeek segs) (hf_realloc k n') nx s mo (cpost ShiQ (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') s mo).
Proof.
  intros HS PRE. destruct (S_realloc_facts tm nx P s mo k n n' HS PRE) as (SAFE & OKN & LEAF). unfold cop.
  eapply wreach_mono; [exact (twf_drive segs _ mo _ SAFE OKN)|].
  intros tr [|[a s']] mo' [Hp HP]; cbn in HP; [destruct HP|].
  split; [exact (oknodes_silent _ _ _ _ _ OKN Hp)|]. destruct (LEAF tr a s' mo' Hp) as (-> & HS' & E1 & E2 & E3 & VO).
  exists s'. split; [reflexivity|]. exact (conj HS' (conj E1 (conj E2 (conj E3 VO)))).
Qed.
End S.
End WithCeil.
End HeapI_S.

(* [comment removed for export] *)
Module UNodesX.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio HeapFull Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fnode {A} (n : node) (dec : resp -> option A)
    (P : libc_st hptr -> Model -> Prop) (Q : A -> libc_st hptr -> Model -> Prop) : Prop :=
  forall l mo, P l mo -> minvX mo ->
    nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a l mo'.

Section Lift.
Context {HG : Type}.
#[local] Notation PS := (PState HG hptr).
(* [comment removed for export] *)
#[using="Type"] Lemma unode_lift {A} n dec (P : libc_st hptr -> Model -> Prop) (Q : A -> libc_st hptr -> Model -> Prop)
      (g : libc_st hptr -> libc_st hptr) (W : libc_st hptr -> option hptr -> Prop) :
  fnode n dec P Q ->
  unode n dec (fun (s : PS) mo => P (g (ps_libc s)) mo /\ W (ps_libc s) (ps_outfile s))
              (fun a (s : PS) mo => Q a (g (ps_libc s)) mo /\ W (ps_libc s) (ps_outfile s)).
Proof.
  intros H s mo [HP HW] MI. destruct (H _ _ HP MI) as [Hs Hk]. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk _ _ _ Hst) as (a & Ha & HQ). exists a. auto.
Qed.

End Lift.

Lemma fnode_post {A} n dec P (Q Q' : A -> libc_st hptr -> Model -> Prop) :
  fnode n dec P Q -> (forall a l mo, Q a l mo -> Q' a l mo) -> fnode n dec P Q'.
Proof.
  intros H HQ l mo HP MI. destruct (H l mo HP MI) as [Hs Hk]. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk _ _ _ Hst) as (a & Ha & X). exists a. split; [exact Ha| apply HQ; exact X].
Qed.

Lemma fnode_pre {A} n dec (P P' : libc_st hptr -> Model -> Prop) (Q : A -> libc_st hptr -> Model -> Prop) :
  fnode n dec P' Q -> (forall l mo, P l mo -> P' l mo) -> fnode n dec P Q.
Proof. intros H HP l mo X MI. exact (H l mo (HP _ _ X) MI). Qed.

(* [comment removed for export] *)
Lemma bv_add_lits a b : (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma unsigned_add_le (x : word) k : 0 <= k -> bv_unsigned (x + Z_to_bv 64 k)%bv <= bv_unsigned x + k.
Proof.
  intros Hk. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in *.
  etransitivity; [apply Z.mod_le; [| lia]| apply Z.add_le_mono_l; apply Z.mod_le; lia].
  pose proof (Z.mod_pos_bound k (2^64) ltac:(lia)). lia.
Qed.

Lemma length_file_read_le d off count :
  0 <= off -> 0 <= count < 2^64 -> off <= Z.of_nat (length d) -> Z.of_nat (length d) < 2^64 ->
  Z.of_nat (length (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count))) <= Z.of_nat (length d) - off.
Proof.
  intros Ho Hc Hle Hd. rewrite file_read_unguarded, length_firstn, length_skipn. unfold word_to_nat. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma kset_self K e : In e K -> List.NoDup (map k_fd K) -> kset e K = K.
Proof.
  intros He ND. unfold kset. rewrite <- (map_id K) at 2. apply map_ext_in. intros x Hx.
  destruct (Z.eqb_spec (k_fd x) (k_fd e)) as [E|NE]; [| reflexivity]. exact (K_fd_inj K e x ND He Hx (eq_sym E)).
Qed.

Section Nodes.
Variables (nx : N) (K : list kfe) (C : list (list byte * list byte)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fn_ioctl fd req :
  fnode (NIoctl fd req) dec_ioctl (FI nx K C) (fun r l mo => FI nx K C l mo /\ exists e, r = SErr e).
Proof.
  intros l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_ioctl _ _ _ _ _ _ Hst) as (e & Hd & -> & -> & _). exists (SErr e). split; [exact Hd|]. split; [exact H| exists e; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fn_writev fd bufs :
  Z.of_nat (length (concat bufs)) < 2^64 ->
  fnode (NWritev fd bufs) (dec_writev (Z.of_nat (length (concat bufs)))) (FI nx K C)
        (fun k l mo => FI nx K C l mo /\ ((length (concat bufs) = 0%nat /\ k = 0) \/ 1 <= k <= Z.of_nat (length (concat bufs)))).
Proof.
  intros Hl l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_writev _ _ _ _ _ _ Hl Hst) as (k & Hk & Hd & -> & _). exists k. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma fn_open path :
  K_clear K path ->
  fnode (NOpen path) dec_open (FI nx K C)
        (fun r l mo => match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal fd => 3 <= fd <= 4096 /\ exists kd, kd <> KW /\ FI nx (K ++ [mkKfe fd kd path None None 0]) (cdel path C) l mo
           end).
Proof.
  intros HC l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_openX _ _ _ _ _ MI Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [e|fd].
  { destruct X as [-> R]. auto. }
  - destruct X as (Efd & R & Fresh & ent & Hent & ->). split; [exact R|].
    assert (NF : path <> [] /\ (path_max <=? length path)%nat = false).
    { destruct Hst as [_ Y]. destruct (path_max <=? length path)%nat eqn:EL.
      - destruct Y as [E _]. exfalso.
        pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold ENAMETOOLONG; lia). discriminate.
      - split; [| reflexivity]. intros ->. destruct Y as [E _]. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold State.ENOENT; lia). discriminate. }
    destruct Hent as [-> | ->].
    + exists KDir. split; [discriminate|]. eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| intros X; exfalso; exact (not_kfile_KDir X)| intros _; reflexivity].
    + exists KR. split; [discriminate|].
      assert (EX : fs_lookup (m_fs mo) path <> None).
      { destruct Hst as [_ Y]. rewrite (proj2 NF) in Y. destruct path as [|c p']; [exfalso; exact (proj1 NF eq_refl)|].
        destruct (path_eqb (c :: p') dot_path) eqn:ED.
        - (* [comment removed for export] *)
          destruct Y as [(e & HIn & E & _)|(_ & E & E2)].
          + exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (apply openat_errnos_range; exact HIn). discriminate.
          + exfalso. apply (f_equal m_fds) in E2. rewrite !m_fds_with_fds in E2. rewrite <- Efd in E2.
            apply (f_equal (fun fds => fd_lookup fds (Z_to_bv 64 fd))) in E2. rewrite !fd_lookup_insert, bv_eqb_refl in E2. discriminate.
        - destruct (fs_lookup (m_fs mo) (c :: p')); [discriminate|]. destruct Y as [E _].
          exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold State.ENOENT; lia). discriminate. }
      eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| intros _; rewrite m_fs_with_fds; exact EX| intros _; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fn_open_known path d :
  K_clear K path -> clookup C path = Some d -> path <> dot_path ->
  fnode (NOpen path) dec_open (FI nx K C)
        (fun r l mo => match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal fd => 3 <= fd <= 4096 /\ FI nx (K ++ [mkKfe fd KR path None (Some d) 0]) (cdel path C) l mo
           end).
Proof.
  intros HC HCd ND l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  pose proof (FI_C _ _ _ _ _ H path d (clookup_In _ _ _ HCd)) as FS.
  pose proof (proj1 (proj2 (FI_CP _ _ _ _ _ H) path d (clookup_In _ _ _ HCd))) as FL.
  destruct (nstep_dec_openX _ _ _ _ _ MI Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [e|fd].
  { destruct X as [-> R]. auto. }
  - destruct X as (Efd & R & Fresh & ent & Hent & ->). split; [exact R|].
    assert (Hent' : ent = FdFile path (Z_to_bv 64 0)).
    { destruct Hst as [_ Y]. destruct (path_max <=? length path)%nat.
      { destruct Y as [E _]. exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold ENAMETOOLONG; lia). discriminate. }
      destruct path as [|c p']. { destruct Y as [E _]. exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold State.ENOENT; lia). discriminate. }
      destruct (path_eqb (c :: p') dot_path) eqn:ED. { apply path_eqb_eq in ED. exfalso. exact (ND ED). }
      rewrite FS in Y. destruct Y as [(e & HIn & E & _)|(_ & _ & E2)].
      + exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (apply openat_errnos_range; exact HIn). discriminate.
      + apply (f_equal m_fds) in E2. rewrite !m_fds_with_fds in E2. rewrite <- Efd in E2. apply (f_equal (fun fds => fd_lookup fds (Z_to_bv 64 fd))) in E2.
        rewrite !fd_lookup_insert, bv_eqb_refl in E2. injection E2 as E2. exact E2. }
    subst ent. eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| | intros X; exfalso; exact (X kfile_KR)].
    intros _. cbn. rewrite m_fs_with_fds. split; [exact FS|]. split; [exact FL| intros; discriminate].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fn_openw path mode (track : bool) :
  K_clear K path -> (path = devnull_path -> track = false) ->
  fnode (NOpenW path mode) dec_openw (FI nx K C)
        (fun r l mo => match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal fd => 3 <= fd <= 4096
               /\ FI nx (K ++ [mkKfe fd (wkind path) path None (if track then Some [] else None) 0]) (cdel path C) l mo
               /\ (path <> devnull_path -> fs_under (m_fs mo) path = false)
           end).
Proof.
  intros HC TRK l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_openwX _ _ _ _ _ _ MI Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [e|fd].
  { destruct X as [-> R]. auto. }
  destruct X as (_ & R & Fresh & _ & _ & [[-> ->]|(NDV & WD & _ & ->)]); (split; [exact R|]).
  - (* [comment removed for export] *)
    rewrite (TRK eq_refl), wkind_devnull. split; [| intros X; exfalso; exact (X eq_refl)].
    eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| intros X; exfalso; exact (not_kfile_KNull X)| intros _; reflexivity].
  - rewrite (wkind_other _ NDV). split.
    + eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| | | intros X; exfalso; exact (X kfile_KW)].
      * intros q NE. rewrite m_fs_with_fds, m_fs_with_fs. apply fs_lookup_set_other. exact NE.
      * intros _. rewrite m_fs_with_fds, m_fs_with_fs. destruct track.
        -- split; [apply fs_lookup_set_same|]. split; [unfold FLEN; cbn; lia| reflexivity].
        -- rewrite fs_lookup_set_same. discriminate.
    + intros _. rewrite (nstep_fs_under _ _ _ _ _ Hst path). unfold write_dirref in WD. apply orb_false_elim in WD. exact (proj2 WD).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fn_close e :
  In e K ->
  fnode (NClose (k_fd e)) dec_close (FI nx K C)
        (fun r l mo => r = SVal 0 /\ FI nx (kdel (k_fd e) K) (cclose e C) (lrem e l) mo).
Proof.
  intros He l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (FI_lookup _ _ _ _ _ H e He) as (off & L & _).
  destruct (nstep_dec_close _ _ _ _ _ Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [err|v].
  - destruct X as (_ & _ & N0). rewrite L in N0. discriminate.
  - destruct X as (-> & _ & ->). split; [reflexivity|]. eapply FI_close; [exact H| exact He| rewrite m_fds_with_fds; reflexivity| rewrite m_fs_with_fds; reflexivity].
Qed.

#[using="Type"] Lemma fn_close_ok e :
  In e K ->
  fnode (NClose (k_fd e)) dec_close_ok (FI nx K C)
        (fun _ l mo => FI nx (kdel (k_fd e) K) (cclose e C) (lrem e l) mo).
Proof.
  intros He l mo H MI. destruct (fn_close e He l mo H MI) as [Hs Hk]. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk _ _ _ Hst) as (a & Ha & -> & X). exists tt. unfold dec_close_ok. rewrite Ha. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_post (e : kfe) (count : Z) (a : read_ans) (l : libc_st hptr) (mo : Model) : Prop :=
  match a with
  | RdErr _ => k_kind e <> KR /\ FI nx K C l mo
  | RdData bs => k_kind e = KR /\ Z.of_nat (length bs) <= count /\
      match k_data e with
      | Some d => bs = file_read d (Z_to_bv 64 (k_off e)) (Z_to_bv 64 count) /\
                  k_off e + Z.of_nat (length bs) <= Z.of_nat (length d) /\
                  FI nx (kset (kmove (Some d) (k_off e + Z.of_nat (length bs)) e) K) C l mo
      | None => FI nx K C l mo
      end
  end.

#[using="Type"] Lemma read_core e count l mo mo' p off data bs :
  FI nx K C l mo -> In e K -> 0 <= count < 2^64 ->
  fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (FdFile p off) ->
  fs_lookup (m_fs mo) p = Some data ->
  bs = file_read data off (Z_to_bv 64 count) ->
  mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 (k_fd e)) (FdFile p (off + len_word bs)%bv)) mo ->
  read_post e count (RdData bs) l mo'.
Proof.
  intros H He Hc L FS Ebs ->.
  destruct (FI_lookup _ _ _ _ _ H e He) as (off0 & L0 & EX). rewrite L in L0.
  assert (KD : k_kind e = KR /\ p = k_path e /\ off = off0).
  { unfold mkent in L0. destruct (k_kind e); [injection L0 as -> ->; auto| discriminate| discriminate| discriminate]. }
  destruct KD as (KD & -> & ->). pose proof (FI_kwf _ _ _ _ _ H e He) as (R & O & W).
  destruct (FI_file_of _ _ _ _ _ H e He ltac:(kndtac)) as (off1 & d1 & L1 & FS1 & LE1 & EXA).
  rewrite L in L1. unfold mkent in L1. rewrite KD in L1. injection L1 as <-. rewrite FS in FS1. injection FS1 as <-.
  assert (LENB : Z.of_nat (length bs) <= count).
  { subst bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
  assert (LENF : Z.of_nat (length bs) <= Z.of_nat (length data) - bv_unsigned off0).
  { subst bs. rewrite file_read_unguarded, length_firstn, length_skipn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
  pose proof (bv_unsigned_in_range 64 off0) as RO. change (bv_modulus 64) with (2^64) in RO.
  split; [exact KD|]. split; [exact LENB|].
  assert (GO : forall e', e' = kmove (k_data e) (match k_data e with Some _ => k_off e + Z.of_nat (length bs) | None => k_off e end) e ->
               FI nx (kset e' K) C l (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 (k_fd e)) (FdFile (k_path e) (off0 + len_word bs)%bv)) mo)).
  { intros e' ->.
    eapply (FI_advance nx K C l l mo _ e _ (off0 + len_word bs)%bv);
      [exact H| exact He| kndtac| reflexivity| reflexivity| reflexivity| reflexivity| | | intros; rewrite m_fs_with_fds; reflexivity| | reflexivity| reflexivity| exact (FI_nodup_files _ _ _ _ _ H)|].
    - unfold kwf, kmove; cbn. split; [lia|]. destruct (k_data e) as [d|] eqn:ED; [| split; [lia| exact I]].
      destruct (EXA d eq_refl) as (-> & -> & U0). destruct W as (_ & LE & FL & _).
      split; [lia|]. split; [unfold knd; cbn; rewrite KD; exact kfile_KR|]. split; [lia|]. split; [exact FL|]. intros E. congruence.
    - rewrite m_fds_with_fds. unfold mkent. rewrite KD. reflexivity.
    - cbn. rewrite m_fs_with_fds. destruct (k_data e) as [d|] eqn:ED.
      + destruct (EXA d eq_refl) as (-> & -> & U0). split; [| exact FS].
        unfold len_word. rewrite bv_add_lits. reflexivity.
      + exists data. split; [exact FS|]. unfold len_word. pose proof (unsigned_add_le off0 (Z.of_nat (length bs)) ltac:(lia)). lia.
    - intros h f' Hin. exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [| intros; lia].
      intros Ho. cbn. destruct (FI_owner_file _ _ _ _ _ _ _ _ H He Ho Hin) as [_ LE']. destruct (k_data e); lia. }
  destruct (k_data e) as [d|] eqn:ED.
  - destruct (EXA d eq_refl) as (-> & E2 & U0). split; [rewrite <- E2; exact Ebs|]. split; [lia|]. apply GO. reflexivity.
  - pose proof (GO _ eq_refl) as G. rewrite kset_self in G; [exact G| | exact (proj1 (FI_KP _ _ _ _ _ H))].
    unfold kmove. destruct e; cbn in *. subst. exact He.
Qed.

#[using="Type"] Lemma read_err e l mo err :
  FI nx K C l mo -> In e K ->
  ((err = EBADF /\ (fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = None \/ (exists p off, fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (FdFileW p off))
                    \/ fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some FdNull))     (* [comment removed for export] *)
   \/ (err = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some FdDir)) ->
  k_kind e <> KR.
Proof.
  intros H He X KD. destruct (FI_lookup _ _ _ _ _ H e He) as (off0 & L0 & _). unfold mkent in L0. rewrite KD in L0.
  destruct X as [[_ [N0|[(p & off & L)|L]]]|[_ L]]; rewrite L0 in *; [discriminate| | |]; congruence.
Qed.

#[using="Type"] Lemma fn_read e buf count :
  In e K -> 0 <= count < 2^64 ->
  fnode (NRead (k_fd e) buf count) (dec_read buf count) (FI nx K C) (read_post e count).
Proof.
  intros He Hc l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_read _ _ _ _ _ _ _ Hc Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [err|bs].
  - destruct X as [-> X]. split; [exact (read_err e l mo err H He X)| exact H].
  - destruct X as (p & off & data & L & FS & Ebs & Emo). eapply read_core; eauto.
Qed.

#[using="Type"] Lemma fn_readv e dsts :
  In e K -> Forall (fun d => 0 <= fst d < 2^64 /\ 0 <= snd d < 2^64) dsts -> dsts_total dsts < 2^62 + 2^61 ->
  (k_kind e = KR -> k_data e <> None) ->     (* [comment removed for export] *)
  fnode (NReadv (k_fd e) dsts) (dec_readv dsts) (FI nx K C) (read_post e (dsts_total dsts)).
Proof.
  intros He HF HT2 TRK l mo H MI.
  assert (HT : dsts_total dsts <= 2^64 - 4096) by lia.
  split.
  { (* [comment removed for export] *)
    cbn. intros p off L. destruct (FI_lookup _ _ _ _ _ H e He) as (off0 & L0 & _). rewrite L in L0.
    assert (KD : k_kind e = KR) by (unfold mkent in L0; destruct (k_kind e); [reflexivity| discriminate| discriminate| discriminate]).
    destruct (k_data e) as [d|] eqn:ED; [| exfalso; exact (TRK KD eq_refl)].
    destruct (FI_file_of _ _ _ _ _ H e He ltac:(kndtac)) as (off1 & d1 & L1 & _ & _ & EXA). rewrite L in L1. unfold mkent in L1. rewrite KD in L1. injection L1 as _ <-.
    destruct (EXA d ED) as (_ & _ & U0). pose proof (FI_kwf _ _ _ _ _ H e He) as (_ & _ & W). rewrite ED in W. destruct W as (_ & LE & FL & _).
    unfold FLEN in FL. lia. }
  intros rsp mo' evs Hst.
  pose proof (dsts_total_nonneg dsts ltac:(apply Forall_impl with (2 := HF); intros [? ?] [_ ?]; cbn in *; lia)) as NN.
  destruct (nstep_dec_readv _ _ _ _ _ _ HF HT Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [err|bs].
  - destruct X as [-> X]. split; [exact (read_err e l mo err H He X)| exact H].
  - destruct X as (p & off & data & L & FS & Ebs & Emo). eapply read_core; eauto. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma file_write_app d bs : Z.of_nat (length d) < 2^64 -> file_write d (Z_to_bv 64 (Z.of_nat (length d))) bs = d ++ bs.
Proof.
  intros Hd. unfold file_write. destruct bs as [|b bs']; [rewrite app_nil_r; reflexivity|].
  unfold word_to_nat. rewrite unsigned_lit by lia. rewrite Nat2Z.id, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
  rewrite firstn_all2 by lia. rewrite skipn_all2 by (cbn; lia). rewrite app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma fn_writevf e bufs :
  In e K -> kwr e ->     (* [comment removed for export] *)
  match k_data e with Some d => Z.of_nat (length d) + Z.of_nat (length (concat bufs)) <= FLEN | None => Z.of_nat (length (concat bufs)) <= 2^64 - 4096 end ->
  fnode (NWritevF (k_fd e) bufs) (dec_writevf_ok (Z.of_nat (length (concat bufs)))) (FI nx K C)
        (fun r l mo => r = Z.of_nat (length (concat bufs)) /\
           match k_data e with
           | Some d => FI nx (kset (kmove (Some (d ++ concat bufs)) (k_off e + Z.of_nat (length (concat bufs))) e) K) C l mo
           | None => FI nx K C l mo
           end).
Proof.
  intros He KWR BUD l mo H MI. set (bs := concat bufs) in *.
  pose proof (FI_kwf _ _ _ _ _ H e He) as (R & O & W).
  assert (Hl : Z.of_nat (length bs) <= 2^64 - 4096) by (destruct (k_data e); unfold FLEN in BUD; lia).
  destruct KWR as [[KD TRK]|KN].
  2:{ (* [comment removed for export] *)
    destruct (FI_lookup _ _ _ _ _ H e He) as (off & L & _). unfold mkent in L. rewrite KN in L.
    assert (ED : k_data e = None).
    { destruct (k_data e) as [d|]; [| reflexivity]. exfalso. exact (knd_not_KNull e (proj1 W) KN). }
    split; [cbn; right; exact L|].
    intros rsp mo' evs Hst. destruct (nstep_dec_writevf _ _ _ _ _ _ Hl Hst) as (_ & Hd & [(p & off' & data & L' & _)|[_ ->]]); [rewrite L in L'; discriminate|].
    fold bs in Hd. exists (Z.of_nat (length bs)). split; [unfold dec_writevf_ok; rewrite Hd; reflexivity|]. split; [reflexivity|]. rewrite ED. exact H. }
  destruct (k_data e) as [d|] eqn:ED; [| exfalso; exact (TRK eq_refl)]. clear TRK.
  destruct (FI_file_of _ _ _ _ _ H e He ltac:(kndtac)) as (off & d0 & L & FS & LE & EXA). unfold mkent in L. rewrite KD in L.
  destruct (EXA d ED) as (-> & -> & U0). destruct W as (_ & LE' & FL & EQ). specialize (EQ KD).
  split.
  { cbn. left. exists (k_path e), (Z_to_bv 64 (k_off e)), d. split; [exact L|]. split; [exact FS|]. unfold rw_bytes_max. unfold FLEN in *. fold bs. lia. }
  intros rsp mo' evs Hst. destruct (nstep_dec_writevf _ _ _ _ _ _ Hl Hst) as (_ & Hd & [(p & off' & data & L' & FS' & ->)|[L' _]]); [| rewrite L in L'; discriminate].
  rewrite L in L'. injection L' as <- <-. rewrite FS in FS'. injection FS' as <-.
  fold bs in Hd. exists (Z.of_nat (length bs)). split; [unfold dec_writevf_ok; rewrite Hd; reflexivity|]. split; [reflexivity|].
  eapply (FI_advance nx K C l l mo _ e _ (Z_to_bv 64 (k_off e) + len_word bs)%bv);
    [exact H| exact He| kndtac| reflexivity| reflexivity| reflexivity| reflexivity| | | | | reflexivity| reflexivity| exact (FI_nodup_files _ _ _ _ _ H)|].
  - unfold kwf, kmove; cbn. split; [lia|]. rewrite length_app. split; [lia|]. split; [unfold knd; cbn; rewrite KD; exact kfile_KW|]. split; [lia|]. split; [rewrite Nat2Z.inj_add; exact BUD|]. intros _. lia.
  - rewrite m_fds_with_fds. unfold mkent. rewrite KD. reflexivity.
  - intros q NE. rewrite m_fs_with_fds, m_fs_with_fs. apply fs_lookup_set_other. exact NE.
  - cbn. rewrite m_fs_with_fds, m_fs_with_fs, fs_lookup_set_same. rewrite EQ.
    split; [unfold len_word; rewrite bv_add_lits; reflexivity|]. rewrite file_write_app by (unfold FLEN in FL; lia). reflexivity.
  - intros h f' Hin. exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [| intros; lia].
    intros Ho. cbn. destruct (FI_owner_file _ _ _ _ _ _ _ _ H He Ho Hin) as [Sh _]. destruct Sh as (_ & _ & _ & Sh). rewrite KD in Sh.
    destruct Sh as (_ & -> & _). unfold zlength. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fn_lseek e d n :
  In e K -> k_kind e = KR -> k_data e = Some d -> 0 <= n <= k_off e ->
  fnode (NLseek (k_fd e) (- n) SEEK_CUR) dec_lseek_ok (FI nx K C)
        (fun r l mo => r = k_off e - n /\ FI nx (kset (kmove (Some d) (k_off e - n) e) K) C (lrem e l) mo).
Proof.
  intros He KD ED Hn l mo H MI.
  pose proof (FI_kwf _ _ _ _ _ H e He) as (R & O & W). rewrite ED in W. destruct W as (_ & LE & FL & _).
  destruct (FI_lookup_exact _ _ _ _ _ H e d He ED) as [L FS]. specialize (FS ltac:(kndtac)). unfold kent, mkent in L. rewrite KD in L.
  split. { cbn. rewrite L. discriminate. }
  intros rsp mo' evs Hst. destruct Hst as [_ Y]. rewrite L, FS in Y. unfold lseek_result in Y.
  assert (HB : forall cur len, lseek_base (Z_to_bv 64 SEEK_CUR) cur len = Some cur) by (intros; vm_compute; reflexivity).
  rewrite HB in Y. unfold lseek_dest in Y. rewrite unsigned_lit in Y by (unfold FLEN in FL; lia).
  assert (SG : bv_signed (Z_to_bv 64 (- n)) = - n).
  { rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus. change (bv_modulus 64) with (2^64). unfold FLEN in FL. lia. }
  rewrite SG in Y.
  replace ((0 <=? k_off e + - n) && (k_off e + - n <? 2 ^ 63)) with true in Y by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold FLEN in FL; lia).
  destruct Y as [-> ->]. exists (k_off e - n). split.
  { unfold dec_lseek_ok, dec_lseek. rewrite dec_plain_val; [f_equal; f_equal; lia| unfold FLEN in FL; lia| reflexivity]. }
  split; [reflexivity|].
  replace (k_off e + - n) with (k_off e - n) by lia.
  eapply (FI_advance nx K C l (lrem e l) mo _ e _ (Z_to_bv 64 (k_off e - n)));
    [exact H| exact He| kndtac| reflexivity| reflexivity| reflexivity| reflexivity| | | intros; rewrite m_fs_with_fds; reflexivity| | | | |].
  - unfold kwf, kmove; cbn. split; [lia|]. split; [lia|]. split; [unfold knd; cbn; rewrite KD; exact kfile_KR|]. split; [lia|]. split; [exact FL|]. intros; congruence.
  - rewrite m_fds_with_fds. unfold mkent. rewrite KD. reflexivity.
  - cbn. rewrite m_fs_with_fds. auto.
  - unfold lrem. destruct (k_own e); reflexivity.
  - unfold lrem. destruct (k_own e); reflexivity.
  - unfold lrem. destruct (k_own e); [cbn; apply NoDup_files_remove|]; exact (FI_nodup_files _ _ _ _ _ H).
  - intros h f' Hin. unfold lrem in Hin. destruct (k_own e) as [h0|] eqn:EO.
    + cbn in Hin. apply (In_files_remove _ _ _ (FI_nodup_files _ _ _ _ _ H)) in Hin as [Hin NE]. cbn in NE.
      exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [intros E; exfalso; apply NE; congruence| intros; lia].
    + exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [intros; discriminate| intros; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma fn_unlink path rmdir :
  K_clear K path ->
  fnode (NUnlink path rmdir) dec_unlink (fun l mo => FI nx K C l mo /\ fs_under (m_fs mo) path = false)
        (fun r l mo => fs_under (m_fs mo) path = false /\
           match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal v => v = 0 /\ rmdir = false /\ FI nx K (cdel path C) l mo
           end).
Proof.
  intros HC l mo [H NDP] MI. split. { cbn. split; [exact NDP|]. intros _. exact (FI_names_path _ _ _ _ _ H path HC). }
  intros rsp mo' evs Hst. pose proof (nstep_fs_under _ _ _ _ _ Hst path) as FU.
  destruct (nstep_dec_unlink _ _ _ _ _ _ Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|].
  split; [rewrite FU; exact NDP|]. destruct a as [err|v].
  - destruct X as [-> X]. split; [exact H|].
    destruct X as [[_ ->]|[[_ [_ ->]]|[[_ [_ [_ ->]]]|[_ [_ [_ HIn]]]]]]; [destruct rmdir; unfold ENOTEMPTY, State.EISDIR; lia| unfold State.ENOENT; lia| unfold ENOTDIR; lia| apply unlinkat_errnos_range'; exact HIn].
  - destruct X as (-> & _ & _ & -> & _ & ->). split; [reflexivity|]. split; [reflexivity|].
    eapply FI_unlink; [exact H| exact HC| rewrite m_fds_with_fs; reflexivity| rewrite m_fs_with_fs; reflexivity].
Qed.

End Nodes.
End UNodesX.
