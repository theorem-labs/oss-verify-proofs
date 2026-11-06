(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep
     AsanWf1 AsanFrame AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf7 AsanWf8 AsanWf9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section WF.
Variable E : aenv.
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E [] []).

(* [comment removed for export] *)
Definition freed_only (s0 s' : astate) (cb0 : Z) : Prop :=
  forall cb cm i, cm_state cm = CAllocated i -> (as_chunks s' !! cb = Some cm <-> as_chunks s0 !! cb = Some cm /\ cb <> cb0).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma afree_core_spec : forall s0 key p cm aid,
  depot_ok E s0 key -> AWF s0 ->
  as_chunks s0 !! (p - kChunkHeaderSize) = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = p ->
  room s0 kBatchClass ->
  hoare (fun s => s = s0) (afree_core E key p)
    (fun s' _ => AWF s' /\ freed_only s0 s' (p - kChunkHeaderSize) /\ fgrow kBatchClass s0 s' /\ depot_n_ids E s' <= depot_n_ids E s0 + 1).
Proof.
  intros s0 key p cm aid HK WF Hcm ST UB ROOM. unfold afree_core. apply hoare_get_bind. intros s ->.
  rewrite Hcm, ST, UB, Z.eqb_refl. cbn [negb].
  set (cb := p - kChunkHeaderSize) in *.
  apply hoare_upd_bind. apply hoare_pre. intros s (sx & -> & ->). set (s1 := upd_ts _ s0).
  assert (WF1 : AWF s1) by (eapply AWf_same_core; [apply same_core_upd_ts| exact WF]).
  assert (HK1 : depot_ok E s1 key) by exact HK.
  eapply hoare_bind; [apply hoare_conjW; [apply (depot_put_wf E [] [] s1 key HK1 WF1)| apply (presW_from fsame _ s1 fsame_refl); apply depot_put_W]|].
  intros fid. apply hoare_pre. intros s2 ((WF2 & (SR & SC & SI & SK & STQ & SG & SS & SP) & FID & NID2) & F2).
  assert (Hcm2 : as_chunks s2 !! cb = Some cm) by (rewrite SK; exact Hcm).
  apply hoare_upd_bind. apply hoare_pre. intros s (sy & -> & ->).
  destruct (AWf_flip E [] s2 cb cm aid fid WF2 Hcm2 ST FID) as [WF3 NIN].
  change (upd_chunks _ s2) with (upd_chunks (fun m => <[cb := flipped cm aid fid]> m) s2).
  set (s3 := upd_chunks _ s2) in *.
  assert (PN : pending s3 cb (cm_n cm)).
  { split; [exists (flipped cm aid fid), aid, fid; split; [cbn; apply lookup_insert_eq| split; reflexivity]|]. exact NIN. }
  assert (ROOM3 : room s3 kBatchClass) by (unfold room, get_region in *; cbn; rewrite SR; exact ROOM).
  eapply hoare_bind.
  { apply hoare_conjW; [apply (enqueue_spec E [] s3 cb (cm_n cm) WF3 PN ROOM3)| apply enqueue_grow]. 
    eapply regs_ok_of_AWf. exact WF3. }
  intros []. apply hoare_pre. intros s4 ((WF4 & HK4 & _ & _ & _ & HKy4 & _) & G4).
  eapply hoare_conseq; [apply hoare_conjW; [apply hoare_conjW; [apply (drain_spec E [] s4 WF4)| apply (presW_from fsame _ s4 fsame_refl); apply drain_same]|
                                            eapply hoareW_conseq; [apply (drain_ks E (as_keys s4))| intros ? ->; reflexivity| intros ? ? H; exact H]]| auto|].
  cbn beta. intros s5 [] [[[WF5 LS] F5] K5]. split; [exact WF5|].
  assert (NID5 : depot_n_ids E s5 <= depot_n_ids E s0 + 1).
  { unfold depot_n_ids in *. unfold KS in K5. rewrite K5, HKy4. cbn. cbn in NID2. lia. }
  split; [| split; [| exact NID5]].
  2:{ eapply fgrow_fsame_trans; [| exact F5]. eapply fsame_fgrow_trans; [| exact G4].
      apply (fsame_regions s0 s2); [reflexivity| reflexivity|]. eapply fsame_trans; [| exact F2].
      apply (fsame_regions s0 s0); [reflexivity| reflexivity| apply fsame_refl]. }
  intros cb' cm' i Hi. rewrite (LS cb' cm' i Hi), HK4. cbn [s3 as_chunks upd_chunks]. rewrite SK.
  destruct (Z.eq_dec cb' cb) as [->|NE].
  + rewrite lookup_insert_eq. split; [intros H; injection H as <-; cbn in Hi; discriminate| intros [_ H]; exfalso; exact (H eq_refl)].
  + rewrite lookup_insert_ne by auto. split; [intros H; auto| intros [H _]; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem afree_spec : forall s0 key p,
  depot_ok E s0 key -> AWF s0 -> room s0 kBatchClass ->
  (p = 0 \/ exists cm aid, as_chunks s0 !! (p - kChunkHeaderSize) = Some cm /\ cm_state cm = CAllocated aid /\ cm_user_beg cm = p) ->
  hoare (fun s => s = s0) (afree E key p)
    (fun s' _ => AWF s' /\ fgrow kBatchClass s0 s'
                 /\ (p = 0 -> as_chunks s' = as_chunks s0)
                 /\ (p <> 0 -> freed_only s0 s' (p - kChunkHeaderSize))
                 /\ depot_n_ids E s' <= depot_n_ids E s0 + 1).
Proof.
  intros s0 key p HK WF ROOM LIVE. unfold afree, ia_init.
  apply hoare_upd_bind. apply hoare_pre. intros s (sx & -> & ->). set (s1 := upd_ia_inited true s0).
  assert (WF1 : AWF s1) by (eapply AWf_same_core; [apply same_core_upd_ia| exact WF]).
  destruct (p =? 0) eqn:PZ.
  - apply Z.eqb_eq in PZ. apply hoare_ret. intros s ->. split; [exact WF1|]. split; [apply (fgrow_regions _ s0 s0); [reflexivity| reflexivity| apply fgrow_refl]|].
    split; [reflexivity|]. split; [intros NZ; exfalso; exact (NZ PZ)| unfold depot_n_ids; cbn; lia].
  - apply Z.eqb_neq in PZ. destruct LIVE as [PZ'|(cm & aid & Hcm & ST & UB)]; [exfalso; exact (PZ PZ')|].
    eapply hoare_conseq; [apply (afree_core_spec s1 key p cm aid HK WF1 Hcm ST UB ROOM)| auto|].
    cbn beta. intros s [] (WF2 & FO & G & NI). split; [exact WF2|]. split; [| split; [intros PZ'; exfalso; exact (PZ PZ')| split; [intros _; exact FO| exact NI]]].
    eapply fsame_fgrow_trans; [| exact G]. apply (fsame_regions s0 s0); [reflexivity| reflexivity| apply fsame_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem amalloc_full_spec : forall s0 key n,
  depot_ok E s0 key -> 0 <= n < 2^40 -> AWF s0 -> malloc_pre s0 n ->
  hoare (fun s => s = s0) (amalloc E key n)
    (fun s' r => AWF s' /\ depot_n_ids E s' <= depot_n_ids E s0 + 1
       /\ match r with
          | None => as_chunks s' = as_chunks s0
          | Some p => p mod 16 = 0 /\ as_chunks s0 !! (p - kChunkHeaderSize) = None
                      /\ exists ab id, 1 <= id /\ p = ab + rz_size n
                           /\ as_chunks s' = <[p - kChunkHeaderSize := new_chunk ab n id]> (as_chunks s0)
          end
       /\ exists extra, fcall 1 [class_id (needed1 n)] extra s0 s' /\ zlen extra <= acharge n /\ (r = None -> extra = [])).
Proof.
  intros s0 key n HK Hn WF PRE.
  eapply hoare_conseq; [apply hoare_conjW; [apply (amalloc_spec E [] [] s0 key n HK Hn WF PRE)| unfold amalloc; apply amalloc_core_frame; [lia| eapply regs_ok_of_AWf; exact WF]]| auto|].
  cbn beta. intros s r [(W & N & X) (extra & F & C)]. split; [exact W|]. split; [exact N|]. split; [exact X|]. exists extra. split; [exact F|].
  destruct C as [->|(PR & NZ & ->)].
  - split; [| reflexivity]. pose proof (map_size_facts n) as (_ & _ & M2). unfold kPageSize in M2.
    assert (0 <= map_size n / 4096) by (apply Z.div_pos; lia). assert (0 <= map_size n / 32768) by (apply Z.div_pos; lia).
    unfold zlen, acharge, kCmPrim; cbn [length Z.of_nat]. destruct (from_primary n); [lia|]. destruct (map_size n <? kBigMapSize); lia.
  - split; [| intros ->; exfalso; exact (NZ eq_refl)].
    pose proof (map_size_facts n) as (_ & _ & M2). unfold kPageSize in M2.
    assert (0 <= map_size n / 4096) by (apply Z.div_pos; lia). assert (0 <= map_size n / 32768) by (apply Z.div_pos; lia).
    pose proof (residue_pages_len (match r with Some p => p - rz_size n - kPageSize | None => 0 end) (map_size n) ltac:(lia)) as RL.
    unfold acharge. rewrite PR. destruct (map_size n <? kBigMapSize); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition room2 (s : astate) (c : Z) : Prop := rg_mapped_user (get_region s c) + 2 * kUserMapSize <= kFreeArrayOffset.

(* [comment removed for export] *)
Definition depot_ok2 (s : astate) (key : list Z) : Prop := zlen key + 1 <= 2^16 /\ depot_n_ids E s + 3 < 2^31.

Theorem arealloc_spec : forall s0 key p n,
  depot_ok2 s0 key -> 0 <= n < 2^40 -> AWF s0 -> malloc_pre s0 n -> room2 s0 kBatchClass ->
  (p = 0 \/ exists cm aid, as_chunks s0 !! (p - kChunkHeaderSize) = Some cm /\ cm_state cm = CAllocated aid /\ cm_user_beg cm = p) ->
  hoare (fun s => s = s0) (arealloc E key p n)
    (fun s' r => AWF s'
       /\ (exists extra, fcall 2 [class_id (needed1 n); kBatchClass] extra s0 s' /\ zlen extra <= acharge n)
       /\ match r with
          | None => (p <> 0 /\ n = 0 -> freed_only s0 s' (p - kChunkHeaderSize))
                    /\ (p = 0 \/ n <> 0 -> as_chunks s' = as_chunks s0)
          | Some q => q mod 16 = 0 /\ as_chunks s0 !! (q - kChunkHeaderSize) = None
                      /\ exists ab id, 1 <= id /\ q = ab + rz_size n
                         /\ forall cb cm i, cm_state cm = CAllocated i ->
                              (as_chunks s' !! cb = Some cm <->
                               (<[q - kChunkHeaderSize := new_chunk ab n id]> (as_chunks s0)) !! cb = Some cm /\ (p <> 0 -> cb <> p - kChunkHeaderSize))
          end).
Proof.
  intros s0 key p n [KL IDB] Hn WF PRE ROOM2 LIVE. unfold arealloc, ia_init.
  assert (HK : depot_ok E s0 key) by (split; [exact KL| lia]).
  assert (ROOM : forall s, fcall 1 [class_id (needed1 n)] [] s0 s \/ as_regions s = as_regions s0 -> room s kBatchClass).
  { intros s [(_ & B & _)|HR]; unfold room, room2, mu, get_region in *; [| rewrite HR; unfold kUserMapSize in *; lia].
    specialize (B kBatchClass). unfold kUserMapSize in *. lia. }
  apply hoare_upd_bind. apply hoare_pre. intros s (sx & -> & ->). set (s1 := upd_ia_inited true s0).
  assert (WF1 : AWF s1) by (eapply AWf_same_core; [apply same_core_upd_ia| exact WF]).
  assert (PRE1 : malloc_pre s1 n) by exact PRE.
  assert (F01 : fsame s0 s1) by (apply (fsame_regions s0 s0); [reflexivity| reflexivity| apply fsame_refl]).
  destruct (p =? 0) eqn:PZ.
  { apply Z.eqb_eq in PZ.
    pose proof (amalloc_full_spec s1 key n HK Hn WF1 PRE1) as M. unfold amalloc in M.
    eapply hoare_conseq; [exact M| auto|]. cbn beta. intros s r (W & _ & X & (extra & F & C & _)).
    split; [exact W|]. split.
    - exists extra. split; [| exact C]. eapply fcall_mono; [| | eapply fcall_pre_same; [exact F01| exact F]]; [lia| intros c [Hc|[]]; left; exact Hc].
    - destruct r as [q|].
      + destruct X as (M16 & NONE & ab & id & ID & Hq & HK'). split; [exact M16|]. split; [exact NONE|]. exists ab, id.
        split; [exact ID|]. split; [exact Hq|]. intros cb cm i Hi. rewrite HK'. split; [intros H; split; [exact H| intros NZ; exfalso; exact (NZ PZ)]| intros [H _]; exact H].
      + split; [intros [NZ _]; exfalso; exact (NZ PZ)| intros _; exact X]. }
  apply Z.eqb_neq in PZ. destruct LIVE as [PZ'|(cm & aid & Hcm & ST & UB)]; [exfalso; exact (PZ PZ')|].
  destruct (n =? 0) eqn:NZ.
  { apply Z.eqb_eq in NZ.
    eapply hoare_bind; [apply (afree_core_spec s1 key p cm aid HK WF1 Hcm ST UB); apply ROOM; right; reflexivity|].
    intros []. apply hoare_pre. intros s2 (WF2 & FO & G & _). apply hoare_ret. intros s ->.
    split; [exact WF2|]. split.
    - exists []. split.
      2:{ pose proof (map_size_facts n) as (_ & _ & M2). unfold kPageSize in M2.
          assert (0 <= map_size n / 4096) by (apply Z.div_pos; lia). assert (0 <= map_size n / 32768) by (apply Z.div_pos; lia).
          unfold zlen, acharge, kCmPrim; cbn [length Z.of_nat]. destruct (from_primary n); [lia|]. destruct (map_size n <? kBigMapSize); lia. }
      eapply fcall_mono; [| | eapply fcall_pre_same; [exact F01| eapply fcall_of_fgrow; [| exact G]]]; [lia| intros c Hc; exact Hc| right; left; reflexivity].
    - split; [intros _; exact FO| intros [X|X]; exfalso; [exact (PZ X)| exact (X NZ)]]. }
  apply Z.eqb_neq in NZ.
  apply hoare_upd_bind. apply hoare_pre. intros s (sy & -> & ->). set (s1' := upd_ts _ s1).
  assert (WF1' : AWF s1') by (eapply AWf_same_core; [apply same_core_upd_ts| exact WF1]).
  assert (F01' : fsame s0 s1') by (apply (fsame_regions s0 s0); [reflexivity| reflexivity| apply fsame_refl]).
  pose proof (amalloc_full_spec s1' key n HK Hn WF1' PRE1) as M. unfold amalloc in M.
  eapply hoare_bind; [exact M|]. intros r. apply hoare_pre. intros s2 (WF2 & NID2 & X & (extra & F2 & C2 & CN)).
  assert (F02 : fcall 1 [class_id (needed1 n)] extra s0 s2) by (eapply fcall_pre_same; [exact F01'| exact F2]).
  destruct r as [q|].
  2:{ apply hoare_ret. intros s ->. split; [exact WF2|]. split.
      - exists extra. split; [| exact C2]. eapply fcall_mono; [| | exact F02]; [lia| intros c [Hc|[]]; left; exact Hc].
      - split; [intros [_ N0]; exfalso; exact (NZ N0)| intros _; exact X]. }
  destruct X as (M16 & NONE & ab & id & ID & Hq & HK2).
  apply hoare_get_bind. intros s ->.
  assert (NEQ : p - kChunkHeaderSize <> q - kChunkHeaderSize) by (intros EQ; rewrite EQ in Hcm; cbn in NONE; rewrite Hcm in NONE; discriminate).
  assert (Hcm2 : as_chunks s2 !! (p - kChunkHeaderSize) = Some cm) by (rewrite HK2, lookup_insert_ne by auto; exact Hcm).
  rewrite Hcm2, ST, UB, Z.eqb_refl.
  assert (ROOMs2 : room s2 kBatchClass).
  { destruct F02 as (_ & B & _). specialize (B kBatchClass). unfold room, room2, mu, kUserMapSize in *. lia. }
  assert (DOK2 : depot_ok E s2 key) by (split; [exact KL| cbn in NID2; unfold depot_n_ids in *; cbn in *; lia]).
  eapply hoare_bind; [apply (afree_core_spec s2 key p cm aid DOK2 WF2 Hcm2 ST UB ROOMs2)|].
  intros []. apply hoare_pre. intros s3 (WF3 & FO & G & _). apply hoare_ret. intros s ->.
  split; [exact WF3|]. split.
  - exists extra. split; [| exact C2].
    eapply (fcall_post_grow 1); [eapply fcall_mono; [| | exact F02]; [lia| intros c [Hc|[]]; left; exact Hc]| right; left; reflexivity| exact G].
  - split; [exact M16|]. split; [exact NONE|]. exists ab, id. split; [exact ID|]. split; [exact Hq|].
    intros cb cm' i Hi. rewrite (FO cb cm' i Hi), HK2. split; [intros [H NE]; auto| intros [H NE]; split; [exact H| apply NE; exact PZ]].
Qed.

End WF.
End RC__1.
