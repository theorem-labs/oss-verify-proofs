(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCellEx_b BatAllocG_b BatInv_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFsInv_b BatFsInvLaws_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_fsinv_set_gc : forall rn g FF LK (M M' : word -> option byte) (b : bool),
  art_fsinv rn g FF LK M -> mem_grows M M' ->
  (forall x : word, fs_zone3 rn (U x) -> U x <> ar_fs (rn_ar rn) + 96 -> M' x = M x) ->
  (forall x : word, cs_zone rn (U x) -> M' x = M x) ->
  cellA M' (ar_fs (rn_ar rn) + 96) 1 (if b then 1 else 0) ->
  art_fsinv rn (FSGH (fg_hint g) b) FF LK M'.
Proof.
  intros rn g FF LK M M' b I GR AG AGCS CG.
  pose proof (art_c_statics_keep rn M M' (fsinv_geo _ _ _ _ _ I) (fsinv_cs _ _ _ _ _ I) GR AGCS) as CS'.
  pose proof (fsinv_geo _ _ _ _ _ I) as GEO. pose proof (fsinv_frame_in _ _ _ _ _ I) as FIN.
  destruct I as (_ & W & CTP & CT & C88 & C96 & HINT & ND & FR & FL & _). cbn zeta in *.
  pose proof GEO as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & G8 & G9 & G10 & G11 & G12). unfold FS_BYTES in *.
  set (fs := ar_fs (rn_ar rn)) in *.
  assert (KEEP : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
            (forall z, a <= z < a + Z.of_nat n -> fs_zone3 rn z /\ z <> fs + 96) -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn Hb C. apply (cell_agree M M'); [|exact Ha|exact Hn|exact C].
    intros x Hx. destruct (Hb (U x) Hx) as (Z3 & NF). apply AG; [exact Z3 | exact NF]. }
  unfold art_fsinv. cbn zeta. fold fs. unfold FS_BYTES. cbn [fg_hint fg_gc].
  split; [exact GEO|]. split; [eapply wr_grows; [exact GR | exact W]|].
  split. { refine (KEEP _ _ _ _ _ _ CTP); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split. { refine (KEEP _ _ _ _ _ _ CT); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split. { refine (KEEP _ _ _ _ _ _ C88); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split; [exact CG|].
  split. { intros c Hc. destruct (HINT c Hc) as (C & R). split; [|exact R].
           refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split; [exact ND|].
  split.
  { intros f Hf. destruct (FR f Hf) as (K & (i & SL & CS) & CR & RS). pose proof (FIN f Hf) as (IN1 & IN2 & IN3).
    pose proof (ff_bytes_ge64 (ff_class f) ltac:(lia)) as B64.
    split; [exact K|]. split; [|split; [|exact RS]].
    - exists i. split; [exact SL|]. refine (KEEP _ _ _ _ _ _ CS); [lia | cbn; lia |].
      intros z Hz. cbn in Hz. unfold fs_zone3, FS_BYTES. fold fs. lia.
    - refine (KEEP _ _ _ _ _ _ CR); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split; [|exact CS'].
  intros c i Hc Hi. pose proof (fs_flag_below_frames fs c i Hc Hi) as FB.
  destruct (FL c i Hc Hi) as (b0 & C & B01 & IFF). exists b0. split; [|split; [exact B01 | exact IFF]].
  refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold fs_zone3, FS_BYTES. fold fs. lia.
Qed.

(* [comment removed for export] *)
Lemma nodup_map_lfilter : forall (A B : Type) (g : A -> B) (p : A -> bool) (l : list A), List.NoDup (map g l) -> List.NoDup (map g (List.filter p l)).
Proof.
  intros A B g p l. induction l as [|a l IH]; intros ND; [constructor|]. cbn in *. inversion ND as [|? ? NI ND']; subst.
  destruct (p a); [|exact (IH ND')]. cbn. constructor; [|exact (IH ND')].
  intros X. apply NI. apply in_map_iff in X as (y & E & Hy). apply filter_In in Hy as (Hy & _). apply in_map_iff. exists y. split; assumption.
Qed.

Definition fs_wr (rn : art_run) (k pos : Z) (LK : list fframe) (col : fframe -> bool) (a : Z) : Prop :=
  let fs := ar_fs (rn_ar rn) in let F := fs_frame fs k pos in
  fs + 8 * k <= a < fs + 8 * k + 8 \/ a = fs + 96 \/ a = fs_flag fs k pos
  \/ (exists f i, In f LK /\ col f = true /\ fs_slot fs f i /\ a = fs_flag fs (ff_class f) i)
  \/ F + 24 <= a < F + 32 \/ F + ff_bytes k - 8 <= a < F + ff_bytes k.

(* [comment removed for export] *)
