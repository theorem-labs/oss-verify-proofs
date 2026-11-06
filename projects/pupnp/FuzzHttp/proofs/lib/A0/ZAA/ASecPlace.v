(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning ITree Nodes Decode Ceiling VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout PEnv ASec F_sec_A LJ ALinkPg ALinkVm ALink ALinkSec ALinkFreeIn.
Import ListNotations.
Open Scope Z_scope.

Section S.
Context {HC : HasCeiling}.
Variable Bs : vmbase.
Variable AL : alayout.

#[using="Type"] Lemma link_new_chunk_sep : forall p a n chs ns ax mo,
  LINK Bs (mkVA p ((a, n) :: chs) ns ax) mo ->
  chunk_sane (a, n)
  /\ Forall (fun c => a + n <= fst c \/ fst c + snd c <= a) chs
  /\ Forall (fun e => a + n <= vlo e \/ vhi e <= a) (vb_maps Bs).
Proof.
  intros p a n chs ns ax mo LK.
  pose proof (lk_sane Bs _ _ LK) as SANE. unfold chunks_sane in SANE. cbn [va_chunks] in SANE. apply Forall_cons_iff in SANE as [CS0 SANE].
  destruct (lk_wf Bs _ _ LK) as [_ SEPS]. pose proof (lk_maps Bs _ _ LK) as PM. cbn [va_chunks map app] in PM.
  pose proof (seps_perm _ _ PM SEPS) as SP. inversion SP as [|e0 l0 FD _]; subst. apply Forall_app in FD as [FD1 FD2].
  destruct (sc_ent_unsigned (a, n) CS0) as [E1 E2]. cbn [fst snd] in E1, E2.
  split; [exact CS0|]. split.
  - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) SANE c Hc) as CSc.
    pose proof (proj1 (Forall_forall _ _) FD1 (sc_ent c) (in_map sc_ent _ c Hc)) as D. destruct (sc_ent_unsigned c CSc) as [F1 F2].
    unfold iv_disjoint in D. rewrite E1, E2, F1, F2 in D. exact D.
  - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) FD2 e He) as D.
    unfold iv_disjoint in D. rewrite E1, E2 in D. unfold vhi, vlo, vsz. exact D.
Qed.

#[using="Type"] Lemma sec_wf_alloc_link : forall (S : asec) a size v mo,
  sec_wf AL S -> se_n S < K_MAX_CHUNKS -> 0 < size ->
  Permutation (va_chunks v) (map cpair (se_chunks S)) ->
  LINK Bs (va_sec_alloc v S a (sec_msize size)) mo -> a + sec_msize size <= alloc_ceiling ->
  Forall (fun rg => exists e, In e (vb_maps Bs) /\ vlo e <= fst rg /\ fst rg + snd rg <= vhi e) (al_regions AL) ->
  sec_wf AL (sec_alloc S a size).
Proof.
  intros S a size v mo (W0 & W1 & W2 & W3 & W4 & W5 & W6) WMAX SZ PMV LK CE REG.
  destruct (link_new_chunk_sep _ _ _ _ _ _ _ LK) as (CS & SEPC & SEPB).
  destruct CS as (C1 & C2 & C3 & C4 & C5 & C6). cbn [fst snd] in C1, C2, C3, C4, C5, C6.
  unfold sec_wf, sec_alloc, se_n in *. cbn [se_chunks se_nres]. rewrite length_app. cbn [length].
  assert (NR : 0 <= (if Z.of_nat (length (se_chunks S)) =? se_nres S then se_nres S + 16384 else se_nres S)
               /\ (if Z.of_nat (length (se_chunks S)) =? se_nres S then se_nres S + 16384 else se_nres S) mod 16384 = 0
               /\ 8 * (if Z.of_nat (length (se_chunks S)) =? se_nres S then se_nres S + 16384 else se_nres S) <= 2^23
               /\ Z.of_nat (length (se_chunks S) + 1) <= (if Z.of_nat (length (se_chunks S)) =? se_nres S then se_nres S + 16384 else se_nres S)
               /\ Z.of_nat (length (se_chunks S) + 1) <= K_MAX_CHUNKS).
  { change (2^23) with 8388608 in *. destruct (Z.eqb_spec (Z.of_nat (length (se_chunks S))) (se_nres S)) as [EQ|NE].
    - split; [lia|]. split; [rewrite <- Zplus_mod_idemp_l, W1; reflexivity|].
      pose proof (Z.div_mod (se_nres S) 16384 ltac:(lia)) as DM. rewrite W1 in DM. split; [lia|]. split; lia.
    - split; [lia|]. split; [exact W1|]. split; [lia|]. split; lia. }
  destruct NR as (N0 & N1 & N2 & N3 & N4).
  split; [exact N0|]. split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split.
  - apply Forall_app. split; [exact W5|]. constructor; [| constructor].
    unfold chunk_ok. cbn [sc_beg sc_msize sc_size].
    split; [exact C4|]. split; [exact C1|]. split; [exact SZ|]. split; [reflexivity|]. split; [destruct C6 as [C6|C6]; [left; split; lia| right; exact C6]|]. split; [exact CE|].
    apply Forall_forall. intros rg Hrg. destruct (proj1 (Forall_forall _ _) REG rg Hrg) as (e & He & R1 & R2).
    pose proof (proj1 (Forall_forall _ _) SEPB e He) as D. unfold apart. destruct D as [D|D]; [left| right]; lia.
  - apply chunks_sep_snoc; [exact W6|]. apply Forall_forall. intros c Hc.
    assert (IC : In (cpair c) (va_chunks v)) by (eapply Permutation_in; [apply Permutation_sym; exact PMV| apply in_map; exact Hc]).
    pose proof (proj1 (Forall_forall _ _) SEPC (cpair c) IC) as D. unfold cpair in D. cbn [fst snd] in D.
    unfold apart_chunks. cbn [sc_beg sc_msize]. destruct D as [D|D]; [right| left]; lia.
Qed.
End S.
