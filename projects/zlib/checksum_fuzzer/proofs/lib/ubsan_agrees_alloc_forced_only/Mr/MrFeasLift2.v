(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require MmapSim.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. Import SM01.KStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM06. Import SM06. Import SM06.MI_Contracts.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge MrFeasSome1 MrKGrant MrFeasLift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Lift2.
Context {rc : runConstT}.

Definition grantable (B : Z) (mo : Model) : Prop :=
  forall len, 0 < len <= B -> exists a : word, MmapSim.grant_ok (Z_to_bv 64 0) mo a (page_round_up_Z len) = true.

Lemma ev_grant_path : forall L (G : PState -> Model -> Prop) s0 mo len,
  KL L (ps_brk s0) mo -> 0 < len < 2^63 ->
  (exists a : word, MmapSim.grant_ok (Z_to_bv 64 0) mo a (page_round_up_Z len) = true) ->
  exists z s' mo', tpath nstep (ev_step (ld_atop L) (EMmap 0 len PROT_RW MAPF) s0) mo [] (Ok (z, s')) mo' /\ is_err z = false.
Proof.
  intros L G s0 mo len HK Hlen [a Hg].
  destruct (nstep_mmap_grant len mo a Hlen Hg) as [mo' Hst].
  pose proof Hg as Hg'. unfold MmapSim.grant_ok in Hg'.
  (* port727 (): grant_ok now leads with Linux's placement (linux_place_is). *)
  apply andb_prop in Hg' as [Hg' _]. apply andb_prop in Hg' as [Hg' _]. apply andb_prop in Hg' as [Hg' Htop].
  apply andb_prop in Hg' as [Hg' Hpos]. apply andb_prop in Hg' as [_ Hal].
  apply Z.leb_le in Htop. apply Z.ltb_lt in Hpos.
  assert (Hn0 : 0 <= page_round_up_Z len) by (apply page_round_up_Z_nonneg; lia).
  pose proof (alloc_top_lt64 (m_vmmaps mo)) as Hcl.
  exists (bv_unsigned a), s0, mo'. split.
  - unfold ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. cbv iota.
    change (PROT_RW =? 0) with false. cbv iota.
    eapply (tpath_mbind_ok _ _ s0 mo (MmOk (bv_unsigned a)) s0 mo').
    + apply (tpath_msys_ok _ _ s0 mo _ mo' (MmOk (bv_unsigned a)) Hst).
      unfold dec_mmap. rewrite !bv_eqb_refl. cbn [andb].
      unfold mmap_addr_ok, mmap_len. rewrite Hal, (proj2 (Z.ltb_lt _ _) Hpos). cbn [andb].
      rewrite (kl_atop _ _ _ HK). rewrite (proj2 (Z.leb_le _ _) Htop). reflexivity.
    + cbv beta iota. apply tpath_ret_ok.
  - unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Lemma membed_grant_path : forall {R} (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop)
    (G : PState -> Model -> Prop) B al L s0 mo,
  frame_ok G -> ctree_ok L t Post -> KL L (ps_brk s0) mo -> G s0 mo -> gone B al P t ->
  (al = true -> grantable B mo) -> B < 2^63 ->
  exists r s' mo', tpath nstep (membed (ld_atop L) t s0) mo [] (Ok (r, s')) mo' /\ P r.
Proof.
  intros R t. induction t as [r|e k IH]; intros Post P G B al L s0 mo HG Hok HK HGs Hgo Hgr HB.
  - exists r, s0, mo. split; [apply tpath_ret_ok | exact Hgo].
  - cbn [ctree_ok] in Hok. destruct Hok as [Hpre Hk].
    destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [gone] in Hgo; try contradiction.
    destruct Hgo as (-> & -> & -> & -> & Hlen & Hkz).
    destruct (ev_grant_path L G s0 mo len HK ltac:(lia) (Hgr eq_refl len Hlen)) as (z & s1 & mo1 & Hp & Hz).
    pose proof (ev_step_spec L _ G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as Hspec.
    unfold etwf in Hspec. pose proof (twf_tpath _ _ _ _ _ _ Hspec Hp) as Hpost. cbn [fst snd] in Hpost.
    destruct Hpost as (Hans & HK1 & HG1 & _).
    destruct (IH z Post P G B false (event_post L _ z) s1 mo1 HG (Hk z Hans) HK1 HG1 (Hkz z Hz) ltac:(discriminate) HB)
      as (r & s' & mo' & Hp' & HP).
    rewrite event_post_atop in Hp'.
    exists r, s', mo'. split; [|exact HP].
    cbn [membed]. eapply tpath_mbind_ok; [exact Hp | exact Hp'].
Qed.

Definition metaok_ps (s : PState) : Prop := metaok (Z.of_nat FUEL) (ps_m s).

Theorem raw_malloc_some_feasible : forall X (G : PState -> Model -> Prop) B n s mo,
  frame_ok G -> OWN X G s mo -> metaok_ps s -> grantable B mo ->
  0 <= n -> n + 20 <= B -> 2^24 <= B -> B < 2^62 ->
  B.tfeas node nstep (raw_malloc n s) mo (fun r => is_null r = false).
Proof.
  intros X G B n s mo HG [(L & Hcr & HK & _) [_ HGs]] Hmeta Hgr Hn HnB HB HB2.
  pose proof (cmalloc_contract_proof _ _ n Hcr Hn) as Hok.
  assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; lia).
  destruct (membed_grant_path (cmalloc (ps_m s) n) _ (fun r => snd r <> None) G B true L s mo HG Hok HK HGs
              (cmalloc_gone B (ps_m s) n (Z.of_nat FUEL) Hmeta ltac:(lia) Hov Hn HnB HB) (fun _ => Hgr) ltac:(lia))
    as ([st' p] & s' & mo' & Hp & HP).
  cbn in HP. destruct p as [c|]; [|contradiction]. rewrite <- (creach_atop _ _ Hcr) in Hp.
  eapply (tfeas_of_tpath _ mo [] (Ok (Some (c, fresh_off st' c n), set_m st' s')) mo'); [|reflexivity].
  unfold raw_malloc.
  eapply tpath_mbind_ok; [cbn; repeat split|].
  eapply tpath_mbind_ok; [exact Hp|]. cbv beta iota.
  eapply tpath_mbind_ok; [cbn; repeat split|]. apply tpath_ret_ok.
Qed.

End Lift2.
