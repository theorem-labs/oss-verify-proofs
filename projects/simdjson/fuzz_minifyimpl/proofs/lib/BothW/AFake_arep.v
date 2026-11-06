(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.lia3 ::= lia3_u.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
     FsKit AFake_iface F_tlsga F_m2s_b.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Definition AH : aholes := mkAHoles AQ ASEC (ADEPOT DI) AFAKE.
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Lemma HB_FAKE : forall L RNG st LB m p A n,
  AHEAP_P AH L RNG st LB m -> In (HB p A n) LB ->
  ablock_range A n /\ (A + n <= al_fake L \/ al_fake L + 11571200 <= A).
Proof. intros. split; [eapply AHEAP_P_hb_range; eauto| eapply AHEAP_P_hb_fake; eauto]. Qed.

Lemma AREP_frame_ext' : forall L st X m m' W,
  alayout_ok L -> AREP AH L st X m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
            (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
         \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
         \/ ATOP <= fst iv) W ->
  AREP AH L st X m'.
Proof.
  (* [comment removed for export] *)
  intros L st X m m' W AL AR MU WM HW. eapply (AREP_frame_ext AH HL); [exact AL| exact AR| exact MU| exact WM|].
  eapply List.Forall_impl; [| exact HW]. cbv beta. intros iv H Hlt.
  destruct (H Hlt) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; left; exact A].
Qed.


(* [comment removed for export] *)
Lemma AREP_cells : forall L st X m, AREP AH L st X m ->
  rt_got m /\ rt_shbase m
  /\ rw_cells bsegs m 0x17cce0 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0x17cce4 [C4 (Z_to_bv 64 0)]
  /\ rt_inited m /\ rt_layout m
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None).
Proof.
  intros L st X m H. pose proof (AREP_relro AH L st X m H) as RR. unfold AREP, arep_rt in H. decompose [and] H.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fake_flag_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP          (* [comment removed for export] *)
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Proof.
  intros L RNG st LB m cls F N AHP Hin. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L LB m cls F N HFK Hin) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  pose proof (afake_flag L LB m cls F N HFK Hin) as FL.
  destruct HFK as (G & _). destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, KHIGH, AIMG_HI in *.   (* [comment removed for export] *)
  destruct ARNG as (_ & _ & _ & _ & _ & _ & RF & _).
  split; [exact FL|]. split; [eapply rng_sub'; [exact RF| lia]|]. split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split.
  - intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    + pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [_ D]. lia.
    + pose proof (afake_lb L LB m c' A' n' (proj2 (proj2 (proj2 AHP))) Hb) as (_ & _ & _ & _ & X1 & X2 & _). lia.
  - intros (iv & Hiv & R). pose proof (CI_OK iv Hiv). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ablocks_tail : forall L st X b LB, ablocks L st X (b :: LB) -> ablocks L st X LB.
Proof.
  intros L st X b LB (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). right; exact Hin.
  - intros c A n Hin. apply (H2 c A n). right; exact Hin.
  - destruct b as [[p|c] A n]; cbn in H3; [inversion H3; assumption| exact H3].
  - inversion H4; assumption.
Qed.

Theorem fake_release_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP_P AH L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L _ m cls F N HFK ltac:(left; reflexivity)) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  assert (NI : ~ In (mkABlock (ABFake cls) F N) LB) by (destruct BL as (_ & _ & _ & ND); inversion ND; assumption).
  destruct HFK as (G & HFK'). pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI in *.   (* [comment removed for export] *)
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| eapply ablocks_tail; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AH ah_fake]. apply (afake_release L LB m cls F N); [exact (conj G HFK')| exact NI].
Qed.

(* [comment removed for export] *)
End S.
End CANSEC1.
(* [comment removed for export] *)
