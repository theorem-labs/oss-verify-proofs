(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Ceiling VmGap.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct BackingAlgebra MainExport MainFactsBoth B0Img MainEntryBoth B0Handoff B0LZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout PEnv LJ ALinkPg ALinkVm ALink.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAI Require Import ALinkInit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require Import GlueKit GlueAllocKit GlueAllocLay.
Import ListNotations.
Open Scope Z_scope.

Section Base.
Context {HC : HasCeiling}.
Variables (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model).
Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
Hypothesis AM : bmodel V sp fs mo.
Hypothesis CEIL : alloc_ceiling = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608.

Definition Bs_of : vmbase := vb0 mo (al_space (AL_of V)).

#[using="sp fs HP AM"] Lemma ent_in : forall b n k, In (LMap b n k) both_ledger -> ent_ok V (zv V b) n -> 0 < n < 2^62 ->
  exists e, In e (vb_maps Bs_of) /\ vlo e = zv V b /\ vhi e = zv V b + n.
Proof.
  intros b n k Hin (E0 & _ & _ & E3) Hn. pose proof (bm_maps _ _ _ _ AM) as LD.
  destruct (sp_digits V HP) as (S0 & S6 & S10 & _).
  exists (wa (zv V b), wa n). split; [exact (ledger_den_In V both_ledger _ b n k LD Hin)|].
  unfold vhi, vlo, vsz. cbn [fst snd]. rewrite !wa_unsigned by lia. split; reflexivity.
Qed.

Ltac in_ledger := unfold both_ledger; repeat first [left; reflexivity | right].

#[using="sp fs HP AM"] Lemma reg_base : Forall (fun rg => exists e, In e (vb_maps Bs_of) /\ vlo e <= fst rg /\ fst rg + snd rg <= vhi e) (al_regions (AL_of V)).
Proof.
  destruct (space_facts V HP) as (SF1 & SF2 & _).
  unfold al_regions, AL_of. cbn [al_space al_parr al_thread al_fsb al_depot al_dtls at_ctx at_thr DN0 SS0].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 208)) 137439023104 AsanPlan.AP.KRW ltac:(in_ledger) (ent_208 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 226)) 8388608 AsanPlan.AP.KNONELAZY ltac:(in_ledger) (ent_226 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 228)) 65536 AsanPlan.AP.KRW ltac:(in_ledger) (ent_228 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 227)) 4096 AsanPlan.AP.KRW ltac:(in_ledger) (ent_227 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 377)) 11571200 AsanPlan.AP.KRW ltac:(in_ledger) (ent_377 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 453)) 1048576 AsanPlan.AP.KRW ltac:(in_ledger) (ent_453 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 454)) 8388608 AsanPlan.AP.KRWLAZY ltac:(in_ledger) (ent_454 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
  - destruct (ent_in (ZMul (ZLit 4096) (ZV 310)) 4096 AsanPlan.AP.KRW ltac:(in_ledger) (ent_310 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
    exists e. split; [exact I|]. rewrite L, H. split; lia.
Qed.

#[using="sp fs HP AM"] Lemma parr_base : exists e, In e (vb_maps Bs_of) /\ vlo e <= al_parr (AL_of V) /\ al_parr (AL_of V) + 2^23 <= vhi e.
Proof.
  destruct (ent_in (ZMul (ZLit 4096) (ZV 226)) 8388608 AsanPlan.AP.KNONELAZY ltac:(in_ledger) (ent_226 V HP) ltac:(lia)) as (e & I & L & H). cbn [zv] in L, H.
  exists e. split; [exact I|]. rewrite L, H. unfold AL_of. cbn [al_parr]. split; lia.
Qed.

Hypothesis CEILsp : alloc_ceiling = bv_unsigned sp - 8388608.
#[using="sp fs HP AM CEILsp"] Lemma base_ok_of : base_ok Bs_of.
Proof.
  destruct (space_facts V HP) as (SF1 & SF2 & _).
  apply (base_ok_init V sp fs mo AM CEILsp (al_space (AL_of V))); unfold vhi, vlo, vsz; cbn [fst snd zv].
  - destruct (ent_208 V HP) as (E0 & _ & _ & E3). destruct (sp_digits V HP) as (S0 & S6 & S10 & _). rewrite wa_unsigned by lia.
    unfold AL_of. cbn [al_space]. exact SF1.
  - destruct (ent_208 V HP) as (E0 & _ & _ & E3). destruct (sp_digits V HP) as (S0 & S6 & S10 & _). rewrite !wa_unsigned by lia.
    unfold AL_of. cbn [al_space]. lia.
Qed.
#[using="Type"] Lemma vb_consts : vb_space Bs_of = al_space (AL_of V) /\ vb_used Bs_of = 2477351424 /\ vb_gapB Bs_of = 137478443008 /\ vb_gapN Bs_of = 16.
Proof. repeat split; reflexivity. Qed.
End Base.
