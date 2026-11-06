(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem Pm4ArtCellEx Pm4ArtAllocG Pm4ArtDepot ArtBridge Pm4ArtInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4ArtFsInv Pm4ArtFsInvLaws.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmGlobKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_c_statics_keep2 : forall rn (M M' : word -> option byte), art_fs_geo rn -> art_c_statics rn M -> (forall a : word, in_shadow_rw (U a) -> M' a <> None) ->
  (forall x : word, cs_zone rn (U x) -> M' x = M x) -> art_c_statics rn M'.
Proof.
  intros rn M M' GEO ((Q1 & Q2 & Q3) & C1 & C2 & C3 & C4 & C5 & SH & GL & SD) GR AG.
  pose proof GEO as (_ & _ & _ & _ & _ & _ & _ & _ & G11 & G12).
  assert (KEEP : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (forall z, a <= z < a + Z.of_nat n -> cs_zone rn z) -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn Hz C. apply (cell_agree M M'); [|exact Ha|exact Hn|exact C]. intros x Hx. apply AG. apply Hz. exact Hx. }
  assert (ES1 : HeapIfaceA.S 0x10000 = 2147459072) by reflexivity. assert (ES2 : HeapIfaceA.S 0x6c0000 = 2148335616) by reflexivity.
  assert (BYTE : forall x v, 2147459072 <= x < 2148335616 -> byte_at M x v -> byte_at M' x v).
  { intros x v Hx B. unfold byte_at in *. rewrite (AG (Z_to_bv 64 x)); [exact B|].
    rewrite art_u_lit by lia. unfold cs_zone. rewrite ES1, ES2. do 4 right. exact Hx. }
  split; [repeat split; assumption|].
  split. { refine (KEEP _ _ _ _ _ _ C1); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
  split. { refine (KEEP _ _ _ _ _ _ C2); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
  split. { refine (KEEP _ _ _ _ _ _ C3); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
  split. { refine (KEEP _ _ _ _ _ _ C4); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
  split. { refine (KEEP _ _ _ _ _ _ C5); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
  split. { intros x Hx OP. apply BYTE; [|exact (SH x Hx OP)]. unfold ART_IMG_LO, ART_IMG_HI in Hx. rewrite ES1, ES2 in Hx. exact Hx. }
  split. { refine (globs_keep ART_IMG_LO ART_IMG_HI ART_GLOBALS M M' _ eq_refl art_globals_in _ GL); [unfold ART_IMG_LO; lia|].
           intros x v Hx. apply BYTE. unfold ART_IMG_LO, ART_IMG_HI in Hx. rewrite ES1, ES2 in Hx. exact Hx. }
  exact GR.
Qed.

Lemma art_fsinv_core2 : forall rn g FF LK M M' FF' fl,
  art_fsinv rn g FF LK M -> (forall a : word, in_shadow_rw (U a) -> M' a <> None) ->
  (forall x : word, ar_fs (rn_ar rn) <= U x < ar_fs (rn_ar rn) + FS_BYTES -> M' x = M x) ->
  (ar_fs (rn_ar rn) + 4096 <= fl < ar_fs (rn_ar rn) + 36864 \/ fl < 0) ->
  (forall x : word, fs_zone3 rn (U x) -> ~ in_fframe FF (U x) -> U x <> fl -> M' x = M x) ->
  (forall x : word, cs_zone rn (U x) -> M' x = M x) ->
  incl FF' FF -> List.NoDup (map ff_addr (FF' ++ LK)) ->
  (forall c i, 0 <= c <= 10 -> 0 <= i < fs_nfr c -> fs_flag (ar_fs (rn_ar rn)) c i <> fl ->
     (fs_slot_taken (ar_fs (rn_ar rn)) (FF' ++ LK) c i <-> fs_slot_taken (ar_fs (rn_ar rn)) (FF ++ LK) c i)) ->
  (forall c i, 0 <= c <= 10 -> 0 <= i < fs_nfr c -> fs_flag (ar_fs (rn_ar rn)) c i = fl ->
     cellA M' fl 1 0 /\ ~ fs_slot_taken (ar_fs (rn_ar rn)) (FF' ++ LK) c i) ->
  art_fsinv rn g FF' LK M'.
Proof.
  intros rn g FF LK M M' FF' fl I GR AGW Hfl AG AGCS INC ND' TK0 TK1.
  pose proof (art_c_statics_keep2 rn M M' (fsinv_geo _ _ _ _ _ I) (fsinv_cs _ _ _ _ _ I) GR AGCS) as CS'.
  pose proof (fsinv_geo _ _ _ _ _ I) as GEO. pose proof (fsinv_rt_not_client _ _ _ _ _ I) as NC. pose proof (fsinv_frame_in _ _ _ _ _ I) as FIN.
  unfold fs_rt_byte in NC.
  destruct I as (_ & W & CTP & CT & C88 & C96 & HINT & ND & FR & FL & _). cbn zeta in *.
  pose proof GEO as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & G8 & G9 & G10 & G11 & G12). unfold FS_BYTES in *.
  set (fs := ar_fs (rn_ar rn)) in *.
  assert (INC' : forall f, In f (FF' ++ LK) -> In f (FF ++ LK)).
  { intros f Hf. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf | Hf]; [left; apply INC; exact Hf | right; exact Hf]. }
  assert (KEEP : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
            (forall b, a <= b < a + Z.of_nat n -> fs_zone3 rn b /\ b <> fl
                        /\ (b < fs + 36864 \/ fs + 11571200 <= b
                            \/ exists f, In f (FF ++ LK) /\ (ff_addr f + 24 <= b < ff_addr f + 32 \/ ff_addr f + ff_bytes (ff_class f) - 8 <= b < ff_addr f + ff_bytes (ff_class f)))) ->
            cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn Hb C. apply (cell_agree M M'); [|exact Ha|exact Hn|exact C].
    intros x Hx. destruct (Hb (U x) Hx) as (Z3 & NF & RT). apply AG; [exact Z3 | apply NC; exact RT | exact NF]. }
  unfold art_fsinv. cbn zeta. fold fs. unfold FS_BYTES.
  split; [exact GEO|]. split; [apply (wr_agree M M' fs 11571200 ltac:(lia) ltac:(lia)); [intros x Hx; apply AGW; exact Hx | exact W]|].
  split. { refine (KEEP _ _ _ _ _ _ CTP); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split. { refine (KEEP _ _ _ _ _ _ CT); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split. { refine (KEEP _ _ _ _ _ _ C88); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split. { refine (KEEP _ _ _ _ _ _ C96); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split. { intros c Hc. destruct (HINT c Hc) as (C & R). split; [|exact R].
           refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
  split; [exact ND'|].
  split.
  { intros f Hf. pose proof (INC' f Hf) as Hf0. destruct (FR f Hf0) as (K & (i & SL & CS) & CR & RS). pose proof (FIN f Hf0) as (IN1 & IN2 & IN3).
    pose proof (ff_bytes_ge64 (ff_class f) ltac:(lia)) as B64.
    split; [exact K|]. split; [|split; [|exact RS]].
    - exists i. split; [exact SL|]. refine (KEEP _ _ _ _ _ _ CS); [lia | cbn; lia |].
      intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. split; [lia|]. split; [lia|]. right; right. exists f. split; [exact Hf0 | lia].
    - refine (KEEP _ _ _ _ _ _ CR); [lia | cbn; lia |].
      intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. split; [lia|]. split; [lia|]. right; right. exists f. split; [exact Hf0 | lia]. }
  split; [|exact CS'].
  intros c i Hc Hi. pose proof (fs_flag_below_frames fs c i Hc Hi) as FB. destruct (Z.eq_dec (fs_flag fs c i) fl) as [E | NE].
  - destruct (TK1 c i Hc Hi E) as (C0 & NT). exists 0. rewrite E. split; [exact C0|]. split; [left; reflexivity|].
    split; [intros X; discriminate X | intros X; exfalso; apply NT; exact X].
  - destruct (FL c i Hc Hi) as (b & C & B01 & IFF). exists b. split; [|split; [exact B01|]].
    + refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros b' Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia.
    + rewrite IFF. symmetry. apply (TK0 c i Hc Hi NE).
Qed.


Theorem art_fsinv_frame_law2_proved : forall rn g FF LK (M M' : word -> option byte),
  art_fsinv rn g FF LK M -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) -> (forall a : word, in_shadow_rw (U a) -> M' a <> None) -> art_fsinv rn g FF LK M'.
Proof.
  intros rn g FF LK M M' I AG SD.
  destruct (fsinv_geo _ _ _ _ _ I) as (_ & G2 & _ & _ & _ & _ & _ & _ & G11 & G12). destruct (fsinv_cs _ _ _ _ _ I) as ((Q1 & Q2 & Q3) & _).
  apply (art_fsinv_core2 rn g FF LK M M' FF (-1) I SD); [ | right; lia | | | apply incl_refl | exact (fsinv_nodup _ _ _ _ _ I) | tauto | ].
  - intros x Hx. apply AG. left. exact Hx.
  - intros x Z3 _ _. apply AG. unfold art_fs_zone. destruct Z3 as [Z | [Z | Z]]; [left; exact Z | right; left; exact Z |].
    right; right; right. left. unfold art_zone_statics. lia.
  - intros x Z. apply AG. unfold art_fs_zone. destruct Z as [Z | [Z | [Z | [Z | Z]]]].
    + right; right; right; left. unfold art_zone_statics. lia.
    + right; right; right; left. unfold art_zone_statics. lia.
    + right; right; right; left. unfold art_zone_statics. lia.
    + do 5 right. lia.
    + do 4 right. left. exact Z.
  - intros c i Hc Hi E. exfalso. pose proof (fs_flag_below_frames (ar_fs (rn_ar rn)) c i Hc Hi). lia.
Qed.
