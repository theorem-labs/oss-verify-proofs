(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode RelSpec RelSpecMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA NodesAS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrlProps AsanInv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotalCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ProtoS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeAlloc. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.ATsafeEv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeAlloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.MSafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition gstepA (n : node) (rsp : resp) (A : alw) : alw :=
  match n with
  | NMmap addr len _ _ =>
      if addr =? 0 then let z := bv_unsigned (eff_ret rsp) in aunion A (range_pages z len ++ range_pages (shad z) (shlen len)) else A
  | _ => A
  end.

#[using="Type"] Lemma gstepA_xnode : forall n rsp A, xnode n -> gstepA n rsp A = A.
Proof. intros n rsp A H. destruct n; cbn in H |- *; try reflexivity; contradiction. Qed.

Section Kit.
Variable NMAX : nat.
Local Notation SHM := ASHM0.

Definition RNGof (A : alw) (mo : Model) : footprint := fp_ok (m_vm_lazy mo) A.

Definition nsafePA (n : node) (A : alw) (mo : Model) : Prop :=
  acct_ok NMAX (RNGof A mo) A mo /\ nsafeA NMAX SHM n mo /\
  forall rsp mo' evs, nstepA n mo rsp mo' evs ->
    fstepS n rsp (RNGof A mo) (RNGof (gstepA n rsp A) mo') /\ alw_le A (gstepA n rsp A).

(* [comment removed for export] *)
#[using="Type"] Lemma nsafePA_io : forall n A mo, vmfree_node n -> nsafe n mo -> acct_ok NMAX (RNGof A mo) A mo -> nsafePA n A mo.
Proof.
  intros n A mo Hio Hns HA. split; [exact HA|]. split.
  { split; [exact Hns|]. split; destruct Hio as [Hfs|(a & ->)]; try (destruct n; cbn in Hfs |- *; try contradiction; exact I); exact I. }
  intros rsp mo' evs Hst. unfold nstepA in Hst.
  assert (EG : gstepA n rsp A = A) by (destruct Hio as [Hfs|(a & ->)]; [destruct n; cbn in Hfs |- *; try contradiction; reflexivity| reflexivity]).
  rewrite EG. split; [| apply alw_le_refl].
  assert (EL : m_vm_lazy mo' = m_vm_lazy mo).
  { destruct Hio as [Hfs|(a & ->)]; [unfold m_vm_lazy; rewrite (nstep_vm_same _ _ _ _ _ Hfs Hst); reflexivity| cbn [nstep] in Hst; destruct Hst as (-> & _); reflexivity]. }
  unfold RNGof. rewrite EL. apply fstepS_id. destruct Hio as [Hfs|(a & ->)]; [destruct n; cbn in Hfs |- *; try contradiction; exact I| exact I].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twfX_TS : forall {R} (t : itree node R) A mo (P : R -> alw -> Model -> Prop) (Q : postT R),
  twfX nsafePA gstepA t A mo P ->
  (forall r A' mo', P r A' mo' -> acct_ok NMAX (RNGof A' mo') A' mo' /\ Q r (RNGof A' mo') A' mo') ->
  TS NMAX SHM (RNGof A mo) A t mo Q.
Proof.
  intros R t. induction t as [r|n k IH]; intros A mo P Q H HQ; cbn in H |- *.
  - destruct (HQ _ _ _ H) as [H1 H2]. split; assumption.
  - destruct H as [(HA & HS & HF) HK]. split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HF rsp mo' evs Hst) as [F1 F2].
    exists (RNGof (gstepA n rsp A) mo'), (gstepA n rsp A). split; [exact F1|]. split; [exact F2|].
    eapply IH; [exact (HK rsp mo' evs Hst)| exact HQ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twfX_event : forall {R} n (d : resp -> option Z) (f : Z -> itree node (exc R)) A mo (P : exc R -> alw -> Model -> Prop),
  acct_ok NMAX (RNGof A mo) A mo -> nsafeA NMAX SHM n mo ->
  (forall rsp mo' evs, nstepA n mo rsp mo' evs ->
     exists z, d rsp = Some z /\ fstepS n rsp (RNGof A mo) (RNGof (gstepA n rsp A) mo') /\ alw_le A (gstepA n rsp A)
               /\ twfX nsafePA gstepA (f z) (gstepA n rsp A) mo' P) ->
  twfX nsafePA gstepA (ebind (enode n d) f) A mo P.
Proof.
  intros R n d f A mo P HA HS HK. unfold ebind, enode. cbn [bind twfX]. split.
  - split; [exact HA|]. split; [exact HS|]. intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (z & _ & F1 & F2 & _). exact (conj F1 F2).
  - intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (z & Hd & _ & _ & HT). rewrite Hd. cbn [bind]. exact HT.
Qed.

Section Ops.
Variables SB PA : Z.
Variable Abase : alw.
Variable NLK : Z.
Let NMAXZ : Z := Z.of_nat NMAX.
Hypothesis HLIM : NLK + NMAXZ * 4096 <= LIMIT.
Hypothesis HNLK : 0 <= NLK.
Hypothesis ABASE_SH : forall z',
  (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation KI := (ATsafeAlloc.KI Abase NLK).

(* [comment removed for export] *)
Definition KPOSTX {R} (RP : list (Z * Z) -> R -> Prop) (Post : R -> Model -> Prop) (G : list (Z * Z)) (KCAP : Z)
  : exc R -> alw -> Model -> Prop :=
  fun r A' mo' => match r with Unr => False | Ok r =>
    exists G' b' k', RP G' r /\ Post r mo' /\ KI b' G' A' k' mo' /\ k' <= KCAP /\ incl G G' end.

#[using="Type"] Lemma KPOSTX_mono_G : forall {R} RP Post (G G1 : list (Z * Z)) KCAP (r : exc R) A mo,
  incl G G1 -> KPOSTX RP Post G1 KCAP r A mo -> KPOSTX (R:=R) RP Post G KCAP r A mo.
Proof.
  intros R RP Post G G1 KCAP [|r] A mo HI H; cbn in *; [exact H|].
  destruct H as (G' & b' & k' & H1 & H2 & H3 & H4 & H5). exists G', b', k'. repeat (split; [assumption|]). eapply incl_tran; eauto.
Qed.


#[using="HLIM ABASE_SH"] Theorem TWF_aembed : forall {R} (t : AM R) (RP : list (Z * Z) -> R -> Prop) Post ga G b A k KCAP mo,
  atotal (aok ATOP) (apost ATOP) t mo Post -> evq SB PA RP ga G b t -> KI b G A k mo ->
  Forall (fun l => 0 <= l) ga -> k + gcost ga <= KCAP -> KCAP <= NMAXZ ->
  twfX nsafePA gstepA (aembed ATOP t) A mo (KPOSTX RP Post G KCAP).
Proof.
  intros R t. induction t as [r | e k0 IH]; intros RP Post ga G b A k KCAP mo HT HE HK Hga Hk HKC.
  - rewrite aembed_ret. pose proof (gcost_nonneg NMAX ga Hga). cbn [twfX KPOSTX].
    cbn in HT, HE. exists G, b, k. split; [exact HE|]. split; [exact HT|]. split; [exact HK|]. split; [lia| apply incl_refl].
  - cbn [atotal] in HT. destruct HT as [Hok HT]. pose proof (gcost_nonneg NMAX ga Hga) as GC0.
    assert (HAT : atop_ok ATOP) by (unfold atop_ok, AsanInv.ACEIL, AsanInv.ATOP_MAX; atop_facts; lia).
    pose proof (asan_node_sound (CE:=ceil_of_rc) ATOP HAT eq_refl e mo Hok) as (n & d & En & Hans & _ & _).
    pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk0).
    destruct e as [t0|b0|a len prot flags|a len|a l p|w]; cbn [aok] in Hok; try contradiction.
    + (* [comment removed for export] *)
      destruct Hok as (-> & Hlen & Htop & Hc). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE. destruct HE as (_ & _ & Hlal & HE).
      rewrite aembed_vis. cbn [aev_tree].
      assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
      destruct HE as [(-> & -> & HE)|[(-> & HAP & Hlb & HE)|(-> & HCG & HE)]].
      * (* [comment removed for export] *)
        rewrite Z.eqb_refl in Hc. destruct Hc as (_ & Hbud & Hgap).
        destruct ga as [|l0 ga']; [destruct HE|]. destruct HE as (<- & Hlb & HE). cbn [gcost] in Hk. apply Forall_cons_iff in Hga as [_ Hga].
        pose proof (pcost_nonneg len ltac:(lia)). pose proof (gcost_nonneg NMAX ga' Hga).
        apply twfX_event.
        -- eapply (ATsafeAlloc.KI_acct_ok NMAX Abase NLK HLIM); [exact HK| subst NMAXZ; lia].
        -- eapply (ATsafeAlloc.nsafeA_grant NMAX Abase NLK HLIM); [exact HK| lia| exact Hlal| exact Hlb].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. rewrite Z.eqb_refl in Hpost. rewrite ML in Hpost.
           destruct Hpost as (Z1 & Z2 & Z3 & Z4 & ->).
           destruct (ATsafeAlloc.step_grant NMAX Abase NLK b G A k mo len z rsp HK ltac:(lia) Hlal Hlb Z1 Z2 Z3 Z4 Hd) as (HF & HL & HK').
           pose proof (ATsafeAlloc.adec_mmap_ret _ _ _ Hd) as RET.
           assert (EG : gstepA (NMmap 0 len PROT_RW F_ANON) rsp A = aunion A (range_pages z len ++ range_pages (shad z) (shlen len))).
           { unfold gstepA. rewrite Z.eqb_refl. cbv zeta. rewrite RET. reflexivity. }
           exists z. split; [exact Hd|]. rewrite EG. split; [exact HF|]. split; [exact HL|].
           eapply twfX_mono.
           ++ eapply (IH z RP Post ga' ((z, len) :: G) (b - len) _ (k + pcost len) KCAP).
              ** apply HT. exact Hpost'.
              ** specialize (HE z). rewrite is_err_small in HE by (unfold TWO64; atop_facts; lia). exact HE.
              ** exact HK'.
              ** exact Hga.
              ** lia.
              ** exact HKC.
           ++ intros x A'' mo'' HP. apply (KPOSTX_mono_G RP Post G ((z, len) :: G) KCAP x); [| exact HP]. intros g Hg. right; exact Hg.
      * (* [comment removed for export] *)
        destruct (Z.eqb_spec a 0) as [->|Hnz]. { destruct Hc as (Hc & _). exfalso. revert Hc. cbv. discriminate. }
        destruct Hc as (_ & Ha & Haal & Hce & Hrf & Hmc & _ & Hsh). rewrite ML in Hce, Hrf, Hmc, Hsh.
        apply twfX_event.
        -- eapply (ATsafeAlloc.KI_acct_ok NMAX Abase NLK HLIM); [exact HK| subst NMAXZ; lia].
        -- eapply (ATsafeAlloc.nsafeA_fixed NMAX Abase NLK HLIM); [exact HK| left; reflexivity| lia| exact Hlal| exact Ha| exact Haal| exact Hce| exact Hrf| exact Hmc| intros _; exact Hlb| apply sh_apart_apart_sh; exact Hsh].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. replace (a =? 0) with false in Hpost by (symmetry; apply Z.eqb_neq; exact Hnz).
           rewrite ML in Hpost. destruct Hpost as (-> & ->).
           destruct (ATsafeAlloc.step_commit NMAX SB PA Abase NLK ABASE_SH b G A k mo a len rsp HK ltac:(lia) Hlal Hlb Ha Haal ltac:(exact Hce) HAP Hmc Hd) as (HF & HK').
           assert (EG : gstepA (NMmap a len PROT_RW F_FIXED) rsp A = A) by (unfold gstepA; rewrite (proj2 (Z.eqb_neq a 0) Hnz); reflexivity).
           exists a. split; [exact Hd|]. rewrite EG. split; [exact HF|]. split; [apply alw_le_refl|].
           eapply (IH a RP Post ga G (b - len) A k KCAP).
           ++ apply HT. exact Hpost'.
           ++ specialize (HE a). rewrite is_err_small in HE by (unfold TWO64; atop_facts; lia). exact HE.
           ++ exact HK'.
           ++ exact Hga.
           ++ exact Hk.
           ++ exact HKC.
      * (* [comment removed for export] *)
        destruct (Z.eqb_spec a 0) as [->|Hnz]. { destruct Hc as (Hc & _). exfalso. revert Hc. cbv. discriminate. }
        destruct Hc as (_ & Ha & Haal & Hce & Hrf & Hmc & _ & Hsh). rewrite ML in Hce, Hrf, Hmc, Hsh.
        apply twfX_event.
        -- eapply (ATsafeAlloc.KI_acct_ok NMAX Abase NLK HLIM); [exact HK| subst NMAXZ; lia].
        -- eapply (ATsafeAlloc.nsafeA_fixed NMAX Abase NLK HLIM); [exact HK| right; reflexivity| lia| exact Hlal| exact Ha| exact Haal| exact Hce| exact Hrf| exact Hmc| intros X; discriminate| apply sh_apart_apart_sh; exact Hsh].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. replace (a =? 0) with false in Hpost by (symmetry; apply Z.eqb_neq; exact Hnz).
           rewrite ML in Hpost. destruct Hpost as (-> & ->).
           destruct (ATsafeAlloc.step_recommit NMAX Abase NLK b G A k mo a len rsp HK ltac:(lia) Hlal Ha Haal ltac:(exact Hce) HCG Hmc Hd) as (HF & HK').
           assert (EG : gstepA (NMmap a len PROT_RW F_FIXNORES) rsp A = A) by (unfold gstepA; rewrite (proj2 (Z.eqb_neq a 0) Hnz); reflexivity).
           exists a. split; [exact Hd|]. rewrite EG. split; [exact HF|]. split; [apply alw_le_refl|].
           eapply (IH a RP Post ga G b A k KCAP).
           ++ apply HT. exact Hpost'.
           ++ exact (HE a).
           ++ exact HK'.
           ++ exact Hga.
           ++ exact Hk.
           ++ exact HKC.
    + (* [comment removed for export] *)
      destruct Hok as (Hlen & Ha & Haal & Hce & Hmh & Hsh). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE.
      rewrite aembed_vis. cbn [aev_tree]. apply twfX_event.
      * eapply (ATsafeAlloc.KI_acct_ok NMAX Abase NLK HLIM); [exact HK| subst NMAXZ; lia].
      * eapply ATsafeAlloc.nsafeA_munmap; eauto. apply sh_apart_apart_sh; exact Hsh.
      * intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
        pose proof Hpost as Hpost'. cbn [apost] in Hpost. destruct Hpost as (-> & ->).
        destruct (ATsafeAlloc.step_munmap NMAX Abase NLK b G A k mo a len rsp HK Hlen Ha Hce Hmh) as (HF & HK').
        exists 0. split; [exact Hd|]. cbn [gstepA]. split; [exact HF|]. split; [apply alw_le_refl|].
        eapply (IH 0 RP Post ga G b A k KCAP).
        -- apply HT. exact Hpost'.
        -- exact (HE 0).
        -- exact HK'.
        -- exact Hga.
        -- exact Hk.
        -- exact HKC.
Qed.
End Ops.
End Kit.
End CANSEC1.
