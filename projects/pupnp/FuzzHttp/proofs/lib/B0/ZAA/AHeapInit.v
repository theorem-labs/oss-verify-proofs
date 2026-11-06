(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim LJ PEnv APrimSpec2 APrimLem APrimQ APrimCover ASec ASecD AQuar AQuarM AHeap AQuarR AQuarT F_quar_M
                        F_hooks F_ialloc F_free_icpt F_alloc_env ALedger AHeap2 AInitReps AFsEnv.
Import ListNotations.
Open Scope Z_scope.

Section INIT.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).

Definition bs0 (H0 : word -> bool) (P0 : list word) (hs0 : list Z) (tot0 : Z) : astB :=
  mkASB H0 P0 prim0 (mkSEC [] 0) (mkAQ [] []) hs0 tot0 0 [] hs0.

#[using="Type"] Lemma RHEAP_B_init : forall H0 P0 hs0 tot0 (m : mem),
  alayout_ok AL ->
  RPRIM AL prim0 m -> RSEC AL (mkSEC [] 0) m -> poison_env E m -> thread_env L m -> shvis H0 m ->
  rw_cells asegs m QUAR_GQ (qcells AL []) -> rw_cells asegs m TQ (qcells AL []) ->
  rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]] -> quar_env m ->
  RDEPOT D hs0 tot0 m -> List.NoDup hs0 -> 0 <= tot0 <= 31 * zlen hs0 -> (length hs0 <= 4)%nat ->
  thread_env2 AL m -> hooks_env m -> trace_env m -> alloc_env m -> (exists inited, ia_cells 262144 262728 inited m) ->
  fs_tls_env (at_thr (al_thread AL)) A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m ->
  RHEAP_B AL E (bs0 H0 P0 hs0 tot0) [] m /\ bs_ghost (bs0 H0 P0 hs0 tot0) = (H0, P0) /\ bs_nsec (bs0 H0 P0 hs0 tot0) = 0.
Proof.
  intros H0 P0 hs0 tot0 m AO RP RS PE TE SV GC TQC MTX QE RD ND0 TB0 LH0 TE2 HKE TRE AENV IA FTE.
  assert (DOK : depot_ok hs0 hs0 tot0) by (split; [exact ND0| split; [intros x Hx; apply in_or_app; left; exact Hx| split; [exact TB0| exact LH0]]]).
  split; [| split; reflexivity].
  unfold RHEAP_B, bs0. cbv zeta. unfold bs_X, bs_gl, live_chunks, heldB, allheld, bs_gl, heldB, live_chunks.
  cbn [bs_H bs_prim bs_sec bs_quar bs_depot bs_dtotal bs_live bs_depot0 q_glob q_loc map flat_map app].
  split; [apply Permutation_refl|]. split; [constructor|]. split; [exact AO|].
  split.
  { unfold dr_invB. cbn [fst snd map flat_map app]. split; [exact RP|].
    split; [intros _ c Hc; rewrite get_cls_prim0; reflexivity|]. split; [exact RS|]. split; [exact PE|]. split; [exact TE|]. split; [exact SV|].
    split; [constructor|]. split; [constructor|]. split; [constructor|]. split; [split; constructor|]. split; [constructor|]. split; constructor. }
  split; [exact I|]. split; [exact GC|]. split; [split; [exact TQC| exact I]|]. split; [exact MTX|]. split; [exact QE|].
  split; [split; [constructor| cbn; lia]|]. split; [exact RD|]. split; [exact DOK|].
  split; [constructor|]. split; [constructor|]. split; [constructor|]. split; [apply Permutation_refl|].
  split.
  { intros c v Hc V0 V1 _. exfalso. rewrite get_cls_prim0 in V1. cbn [p_au pclass0] in V1. pose proof (class_size_pos c Hc). lia. }
  split; [exact TE2|]. split; [exact HKE|]. split; [exact TRE|]. split; [exact AENV|]. split; [exact IA|].
  split; [constructor|]. split; [constructor|]. split; [constructor|]. split; [| exact FTE].
  unfold budget_ok, allheld, bs_gl, heldB, live_chunks. cbn [bs_prim bs_quar bs_live q_glob q_loc map flat_map app].
  split; [intros c Hc; rewrite get_cls_prim0; cbn [p_mu pclass0]; exact (proj1 (PM_fits c Hc))|].
  split; [intros c Hc; unfold cls_cnt; cbn [List.filter length Z.of_nat]; destruct (a0_caps_ok c ltac:(lia)) as [C0 C1]; lia|].
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  unfold sec_live_cnt, sec_live_bytes, live_chunks, A0_SEC_CNT, A0_SEC_BYTES, A0_NSEC_MAX. cbn [bs_live bs_nsec map flat_map length fold_right Z.of_nat]. lia.
Qed.

End INIT.
