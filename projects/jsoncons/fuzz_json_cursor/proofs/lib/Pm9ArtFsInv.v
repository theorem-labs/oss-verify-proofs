(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA PmHeapIfaceA ArtMem ArtBridge Pm9ArtInv.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmGlobKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Record art_fsg : Type := FSGH {
  fg_hint : Z -> Z;
  fg_gc : bool
}.
Definition art_fsg0 : art_fsg := FSGH (fun _ => 0) false.

Definition fs_nfr (c : Z) : Z := 2 ^ (14 - c).
Definition fs_flag (fs c i : Z) : Z := fs + 4096 + 32768 - 2 * fs_nfr c + i.
Definition fs_frame (fs c i : Z) : Z := fs + 4096 + 32768 + c * 2 ^ 20 + i * ff_bytes c.
Definition fs_slot (fs : Z) (f : fframe) (i : Z) : Prop := 0 <= i < fs_nfr (ff_class f) /\ ff_addr f = fs_frame fs (ff_class f) i.

Lemma fs_flag_below_frames : forall fs c i, 0 <= c <= 10 -> 0 <= i < fs_nfr c -> fs + 4096 <= fs_flag fs c i < fs + 4096 + 32768.
Proof.
  intros fs c i Hc Hi. unfold fs_flag, fs_nfr in *.
  assert (P : 0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 2 ^ (14 - c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 14) with 16384 in Q. lia.
Qed.
Lemma fs_frame_above_flags : forall fs k j, 0 <= k -> 0 <= j -> fs + 4096 + 32768 <= fs_frame fs k j.
Proof.
  intros fs k j Hk Hj. unfold fs_frame, ff_bytes.
  assert (P : 0 <= k * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Q : 0 <= j * (64 * 2 ^ k)) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]]).
  lia.
Qed.
Lemma fs_flag_frame_apart : forall fs c i k j, 0 <= c <= 10 -> 0 <= i < fs_nfr c -> 0 <= k -> 0 <= j ->
  fs_frame fs k j + ff_bytes k <= fs_flag fs c i \/ fs_flag fs c i + 1 <= fs_frame fs k j.
Proof.
  intros fs c i k j Hc Hi Hk Hj. right.
  pose proof (fs_flag_below_frames fs c i Hc Hi). pose proof (fs_frame_above_flags fs k j Hk Hj). lia.
Qed.

Definition art_fs_geo (rn : art_run) : Prop :=
  let fs := ar_fs (rn_ar rn) in
  fs mod 4096 = 0 /\ 4096 <= fs /\ fs + FS_BYTES <= rn_HI rn /\ (fs + FS_BYTES <= 0x10000 \/ 0x6b4000 <= fs) /\ app_mem fs FS_BYTES
  /\ (fs + FS_BYTES <= rn_t rn \/ rn_t rn + 4096 <= fs)
  /\ 0 <= rn_t rn /\ rn_t rn + 4096 <= 2 ^ 47
  /\ 0x67fbe8 <= rn_tp rn /\ rn_tp rn + 8 <= 0x6b4000.

Definition ART_IMG_LO : Z := 0x10000.
Definition ART_IMG_HI : Z := 0x6b4000.
Definition ART_GLOBALS : list (Z * Z) := [(0x246a0, 17); (0x246e0, 41); (0x24740, 31); (0x24780, 31); (0x247c0, 41); (0x24820, 25); (0x24860, 29); (0x248a0, 32); (0x248e0, 22); (0x24920, 10); (0x24940, 28); (0x24980, 25); (0x249c0, 30); (0x24a00, 30); (0x24a40, 35); (0x24aa0, 26); (0x24ae0, 33); (0x24b40, 35); (0x24ba0, 25); (0x24be0, 25); (0x24c20, 23); (0x24c60, 31); (0x24ca0, 33); (0x24d00, 38); (0x24d60, 30); (0x24da0, 37); (0x24e00, 40); (0x24e60, 37); (0x24ec0, 24); (0x24f00, 36); (0x24f60, 25); (0x24fa0, 13); (0x25000, 1); (0x25020, 3); (0x25040, 10); (0x25060, 13); (0x25080, 14); (0x250c0, 35); (0x25240, 51); (0x252a0, 7); (0x253e0, 54); (0x25480, 14); (0x254a0, 23); (0x254e0, 13); (0x25500, 18); (0x25540, 52); (0x255a0, 43); (0x25600, 49); (0x25660, 28); (0x256a0, 12); (0x256c0, 27); (0x25700, 15); (0x25720, 14); (0x25740, 28); (0x25780, 36); (0x257e0, 36); (0x25840, 101); (0x258e0, 47); (0x25940, 53); (0x259a0, 36); (0x25a00, 15); (0x25a20, 34); (0x25a80, 36); (0x25ae0, 27); (0x25b20, 29); (0x25b60, 16); (0x25b80, 27); (0x25bc0, 25); (0x25c00, 43); (0x25c60, 46); (0x25cc0, 52); (0x25d20, 26); (0x25d60, 21); (0x25da0, 26); (0x25fc0, 5); (0x25fe0, 6); (0x26000, 5); (0x260c0, 39); (0x26120, 6); (0x26140, 21); (0x261c0, 6); (0x261e0, 6); (0x26200, 5496); (0x27cc0, 2748); (0x28a20, 11); (0x28a40, 70); (0x28ac0, 6); (0x28ae0, 11)].
Definition ART_POISON : list (Z * Z) := [(0x246a0, 0x24fc0); (0x25000, 0x250a0); (0x250c0, 0x25120); (0x25240, 0x252c0); (0x253e0, 0x25440); (0x25480, 0x25de0); (0x25fc0, 0x26020); (0x260c0, 0x26180); (0x261c0, 0x28b00); (0x159020, 0x15a620)].
Lemma art_globals_in : forallb (glob_in ART_IMG_LO ART_IMG_HI) ART_GLOBALS = true.
Proof. vmc_refl. Qed.
Lemma art_poison_al : aligned8 ART_POISON = true.
Proof. vmc_refl. Qed.
Definition art_c_statics (rn : art_run) (M : word -> option byte) : Prop :=
  (rn_tp rn + 16 <= 0x6b4000 /\ 4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= 2 ^ 47)
  /\ cellA M 0x156330 8 0x146da8 /\ cellA M 0x1563f8 8 0x134fcc /\ cellA M 0x156400 8 0x146d10
  /\ cellA M (rn_tp rn + 8) 8 (rn_dtls rn) /\ cellA M (rn_dtls rn + 24) 8 (rn_tp rn)
  /\ (forall x, S ART_IMG_LO <= x < S ART_IMG_HI -> off_poison ART_POISON x -> byte_at M x 0)
  /\ Forall (fun g => shadow_blk M (fst g) (snd g)) ART_GLOBALS
  /\ (forall a : word, in_shadow_rw (U a) -> M a <> None).
Definition cs_zone (rn : art_run) (a : Z) : Prop :=
  0x156330 <= a < 0x156338 \/ 0x1563f8 <= a < 0x156410 \/ rn_tp rn + 8 <= a < rn_tp rn + 16 \/ rn_dtls rn + 24 <= a < rn_dtls rn + 32 \/ S 0x10000 <= a < S 0x6b4000.

Definition art_fsinv (rn : art_run) (g : art_fsg) (FF LK : list fframe) (M : word -> option byte) : Prop :=
  let fs := ar_fs (rn_ar rn) in
  art_fs_geo rn
  /\ wrA M fs FS_BYTES
  /\ cellA M (rn_tp rn) 8 fs /\ cellA M (rn_t rn + 72) 8 fs
  /\ cellA M (fs + 88) 8 20 /\ cellA M (fs + 96) 1 (if fg_gc g then 1 else 0)
  /\ (forall c, 0 <= c <= 10 -> cellA M (fs + 8 * c) 8 (fg_hint g c) /\ 0 <= fg_hint g c < 2 ^ 64)
  /\ List.NoDup (map ff_addr (FF ++ LK))
  /\ (forall f, In f (FF ++ LK) ->
        (0 <= ff_class f <= 5)
        /\ (exists i, fs_slot fs f i /\ cellA M (ff_addr f + ff_bytes (ff_class f) - 8) 8 (fs_flag fs (ff_class f) i))
        /\ cellA M (ff_addr f + 24) 8 (ff_rs f - 32) /\ 32 <= ff_rs f <= 2 ^ 47 + 32)
  /\ (forall c i, 0 <= c <= 10 -> 0 <= i < fs_nfr c ->
        exists b, cellA M (fs_flag fs c i) 1 b /\ (b = 0 \/ b = 1)
                  /\ (b = 1 <-> exists f, In f (FF ++ LK) /\ ff_class f = c /\ ff_addr f = fs_frame fs c i))
  /\ art_c_statics rn M.

Definition art_fsinv_frame_law_goal : Prop := art_fsinv_frame_law art_fsg art_fsinv.

Definition art_fsinv_client_law : Prop :=
  forall rn g FF LK M M',
    art_fsinv rn g FF LK M -> mem_grows M M' ->
    (forall x : word, let a := U x in
        (ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES \/ rn_t rn + 72 <= a < rn_t rn + 80 \/ rn_tp rn <= a < rn_tp rn + 8) ->
        ~ in_fframe FF a -> M' x = M x) ->
    (forall x : word, cs_zone rn (U x) -> M' x = M x) ->
    art_fsinv rn g FF LK M'.

Definition art_fsinv_wf_law : Prop :=
  forall rn g FF LK M, art_fsinv rn g FF LK M ->
    (forall f, In f FF -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES
                        /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) PM_FS_CLASSES
                        /\ defined M (ff_addr f) (ff_bytes (ff_class f))
                        /\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) (ff_remove (ff_addr f) FF ++ LK))
    /\ app_mem (ar_fs (rn_ar rn)) FS_BYTES /\ ar_fs (rn_ar rn) + FS_BYTES <= ahl_ceil (rn_ar rn)
    /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x6b4000 <= ar_fs (rn_ar rn))
    /\ List.NoDup (map ff_addr (FF ++ LK)) /\ defined M (ar_fs (rn_ar rn)) FS_BYTES.

Definition art_fsinv_release_law : Prop :=
  forall rn g FF LK M M' F k rs,
    art_fsinv rn g FF LK M -> In (F, k, rs) FF -> mem_grows M M' ->
    (exists i, 0 <= i < fs_nfr k /\ F = fs_frame (ar_fs (rn_ar rn)) k i /\ cellA M' (fs_flag (ar_fs (rn_ar rn)) k i) 1 0
               /\ (forall x : word, U x <> fs_flag (ar_fs (rn_ar rn)) k i ->
                     (ar_fs (rn_ar rn) <= U x < ar_fs (rn_ar rn) + FS_BYTES \/ rn_t rn + 72 <= U x < rn_t rn + 80 \/ rn_tp rn <= U x < rn_tp rn + 8) ->
                     ~ in_fframe FF (U x) -> M' x = M x)) ->
    (forall x : word, cs_zone rn (U x) -> M' x = M x) ->
    art_fsinv rn g (ff_remove F FF) LK M'.
Definition art_fsinv_leak_law : Prop :=
  forall rn g FF LK M FX, art_fsinv rn g FF LK M -> incl FX FF ->
    art_fsinv rn g (filter (fun f => negb (existsb (fun h => Z.eqb (ff_addr h) (ff_addr f)) FX)) FF) (FX ++ LK) M.

Definition art_fsinv_handoff : Prop :=
  forall rn M, art_fs_geo rn -> wrA M (ar_fs (rn_ar rn)) FS_BYTES ->
    cellA M (rn_tp rn) 8 (ar_fs (rn_ar rn)) -> cellA M (rn_t rn + 72) 8 (ar_fs (rn_ar rn)) -> cellA M (ar_fs (rn_ar rn) + 88) 8 20 ->
    (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + 4096 + 32768 -> ~ (ar_fs (rn_ar rn) + 88 <= a < ar_fs (rn_ar rn) + 96) -> byte_at M a 0) ->
    art_c_statics rn M ->
    art_fsinv rn art_fsg0 [] [] M.

Lemma fs_frame_inj : forall fs k i i', fs_frame fs k i = fs_frame fs k i' -> 0 <= k -> i = i'.
Proof.
  intros fs k i i' E Hk. unfold fs_frame, ff_bytes in E.
  assert (P : 0 < 64 * 2 ^ k) by (assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia); lia).
  assert (E' : i * (64 * 2 ^ k) = i' * (64 * 2 ^ k)) by lia.
  apply Z.mul_reg_r in E'; lia.
Qed.
Lemma art_fsinv_flagptr : forall rn g g' FF LK FF' LK' M M' F k rs rs' fl,
  art_fsinv rn g FF LK M -> art_fsinv rn g' FF' LK' M' -> In (F, k, rs) FF -> In (F, k, rs') FF' ->
  cellA M (F + ff_bytes k - 8) 8 fl -> cellA M' (F + ff_bytes k - 8) 8 fl.
Proof.
  intros rn g g' FF LK FF' LK' M M' F k rs rs' fl I1 I2 H1 H2 C.
  destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & FR1 & _). destruct I2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2 & _).
  destruct (FR1 (F, k, rs) ltac:(apply in_or_app; left; exact H1)) as (K1 & (i & (Hi & A1) & C1) & _).
  destruct (FR2 (F, k, rs') ltac:(apply in_or_app; left; exact H2)) as (K2 & (i' & (Hi' & A2) & C2) & _).
  unfold ff_class, ff_addr in *. cbn [fst snd] in *.
  assert (E : i = i') by (apply (fs_frame_inj (ar_fs (rn_ar rn)) k); [congruence | lia]). subst i'.
  unfold cell in *. rewrite C2. rewrite <- C1. exact C.
Qed.

Lemma le8_zero : word_to_le_bytes 8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. vm_compute. repeat f_equal; apply bv_eq; reflexivity. Qed.
Lemma le1_zero : word_to_le_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. vm_compute. repeat f_equal; apply bv_eq; reflexivity. Qed.
Lemma cell_zero_bytes : forall (M : word -> option byte) a (n : nat), (n = 1 \/ n = 8)%nat -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat n -> byte_at M (a + j) 0) -> cellA M a n 0.
Proof.
  intros M a n Hn Ha Hhi HB. unfold cell.
  assert (UA : bv_unsigned (Z_to_bv 64 a) = a) by (apply art_u_lit; destruct Hn as [-> | ->]; lia).
  rewrite (MemSplit.rdn_const _ M (Z_to_bv 64 a) n (Z_to_bv 8 0)).
  - destruct Hn as [-> | ->]; [rewrite le1_zero | rewrite le8_zero]; reflexivity.
  - rewrite UA. lia.
  - intros x Hx. rewrite UA in Hx. specialize (HB (bv_unsigned x - a) ltac:(lia)). unfold byte_at in HB.
    replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in HB by lia. rewrite Z_to_bv_bv_unsigned in HB. exact HB.
Qed.
Theorem art_fsinv_handoff_proved : art_fsinv_handoff.
Proof.
  intros rn M GEO W CTP CT C88 Z0 CS. unfold art_fsinv. cbn zeta.
  pose proof GEO as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & G8). unfold FS_BYTES in *.
  set (fs := ar_fs (rn_ar rn)) in *.
  split; [exact GEO|]. split; [exact W|]. split; [exact CTP|]. split; [exact CT|]. split; [exact C88|].
  split. { cbn [fg_gc art_fsg0]. apply cell_zero_bytes; [left; reflexivity | lia | lia |]. intros j Hj. apply Z0; lia. }
  split. { intros c Hc. cbn [fg_hint art_fsg0]. split; [|lia]. apply cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. apply Z0; lia. }
  split. { cbn. constructor. }
  split. { intros f Hf. cbn in Hf. contradiction. }
  split; [|exact CS].
  intros c i Hc Hi. exists 0. pose proof (fs_flag_below_frames fs c i Hc Hi) as FB.
  split. { apply cell_zero_bytes; [left; reflexivity | lia | lia |]. intros j Hj. apply Z0; lia. }
  split; [left; reflexivity|]. split; [intros X; discriminate X | intros (f & Hf & _); cbn in Hf; contradiction].
Qed.
