(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's CfParams for the shared event-free allocator instance (YGcfNames.v).
   PER-UNIT file, not in the shared set. A Definition, NOT an exported Instance, for the same reason as
   CfImg_A (lib/A/CfImgA.v): a consumer names it, so inference can never pick another unit's parameters.
   Values and where each comes from:
   - cf_malloc_max = 2 ^ 28 + 2 ^ 27 = 402,653,184, an ADMISSION bound (the call premise 0 <= n < cf_malloc_max,
     YG0dcf.v:162; no model arm refuses above it). Preset's largest request is tx_put's realloc, at most 112 * n - 106,
     352,321,430 at a 3 MiB input (released PackFit.v pf_NMAX; SlotSizes.v), above cgif's MALLOC_MAX = 2 ^ 28.
     It is at or below 505,274,410, the largest size c-asan's widened Allocate walk runs at the model's room 2 ^ 30
     (VM_HEAD, YG0n.v:542; c-asan 14:47Z, c-omx-hpreset 15:06Z). It was 2 ^ 29 - 2 ^ 20 before 2026-10-29 15:1xZ.
     WHY A SMALLER VALUE IS SAFE: each calling walk must PROVE its site's 0 <= n < cf_malloc_max; a too-small value
     can only make a walk fail to build, never make a statement false, and no top-level statement mentions it.
     Census of every allocation site (a Theorem Labs lane, the internal file ALLOC-SITE-CENSUS-102.md):
     largest request 352,321,524; findings F1-F4 there are obligations of the walks at those sites.
   - cf_nob = 2 ^ 29: cgif's NOB (YF06.v:133, :171); cf_sizes_ok shows every admissible request maps under it.
   - cf_place_limit = 80,953: c-asan's LPS placement counting limit at NOB = 2 ^ 29
     (a Theorem Labs lane frame note, the internal file LPS-PLACEMENT-REUSE.md section 5; 80,954 fails).
   - cf_sec_live_max = 16,000: PresetOomRoom's walk-dischargeable bound is
     3 * floor(N / 1026) + 9 + floor(Q / 64513) = 13,367 at N = 3 MiB, Q = 256 MiB
     (a Theorem Labs lane oomroom note, the internal file SEC-PROOF.txt); 16,000 is above 13,367 + 1 (the call premise
     is strict) and below kPtrArrayEntriesPerCommit = 16,384.
   - cf_fs_classes = [0; 1; 3]: preset's live frame-area classes (PresetFrameClasses).
   - cf_head = 16: the harness's HEAD (preset source/alloc.c:31; own / disown poison and unpoison it, :45-63).
   - cf_kmax = preset_kmax = 2 ^ 17 = 131,072: the bound on a run's user secondary entries N = nsec_cf S (YGcfNames.v
     cf_kmax), the count half of preset's meter cf_hull_ok. The worst measured run frees 49,356 secondaries per
     4-call run (the measured worst run); 2 ^ 17 is above it and within the field bound 2 ^ 24.
   - cf_sec_live_place_lt: 16,000 < 80,953 (the field's own form).
   - cf_T_max = preset_T_max = 2 ^ 36: the bound on T = sec_T_cf S, the mapped bytes of a run's user secondary
     entries, the other half of the meter; the measured run's T is at most 6,537,494,528 < 2 ^ 33;
     2 ^ 36 is within the field bound 2 ^ 38.
   - cf_hull = sec_hulls_cf, cf_hull_ok = the meter (nsec_cf S <= preset_kmax /\ sec_T_cf S <= preset_T_max, which is
     sec_meter_ok_cf at this record: cf_hull_ok_conv_preset), cf_rec_drop = 0 (preset is on wle, no hull refund);
     the hull laws are YGcfAbudget.v section 6's preset_hull_* at K := preset_kmax, T := preset_T_max.
   Preset provenance moved here from the shared files' comments:
   - preset's images call __wrap_strcmp 19 times (12 program + 7 musl) and __wrap_strlen 14 times
     (8 + 6), measured by c-libc-stdio (the pcs are CfImg_A's cf_pc_strcmp / cf_pc_strlen);
   - the harness's realloc sites abort() on a refusal (alloc.c), which is why
     malloc_cf_success_of_room is load-bearing for preset;
   - placement: 80,953 is c-asan's counting limit at NOB = 2 ^ 29 (80,954 fails). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG08 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YGcfAbudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma preset_malloc_max_pos : 2 ^ 20 <= 2 ^ 28 + 2 ^ 27.
Proof. apply Z.leb_le. reflexivity. Qed.

(* Every admissible request maps under NOB: sec_map_size n <= req_size n + 2 ^ 14
   (cgif YG08.v:15), and req_size n <= n + 1, so at most 2 ^ 28 + 2 ^ 27 + 2 ^ 14 < 2 ^ 29. *)
Lemma preset_sizes_ok : forall n, 0 <= n < 2 ^ 28 + 2 ^ 27 -> sec_map_size n <= 2 ^ 29.
Proof.
intros n [H0 H1]. pose proof (sec_map_size_bound n H0) as B. unfold req_size in B.
change (2 ^ 29) with 536870912 in *. change (2 ^ 28) with 268435456 in *. change (2 ^ 27) with 134217728 in *.
change (2 ^ 14) with 16384 in *.
destruct (n =? 0); lia.
Qed.

Lemma preset_malloc_max_ge : MALLOC_MAX <= 2 ^ 28 + 2 ^ 27.
Proof. unfold MALLOC_MAX. apply Z.leb_le. reflexivity. Qed.

Lemma preset_nob_ok : 2 ^ 29 <= 2 ^ 30.
Proof. apply Z.leb_le. reflexivity. Qed.

Lemma preset_sec_live_nonneg : 0 <= 16000.
Proof. lia. Qed.

Lemma preset_sec_live_ok : 16000 <= 80953.
Proof. lia. Qed.

Lemma preset_nob_sec_len : SEC_LEN_MAX <= 2 ^ 29.
Proof. unfold SEC_LEN_MAX. apply Z.leb_le. reflexivity. Qed.

Lemma preset_sec_live_commit : 16000 < kPtrArrayEntriesPerCommit.
Proof. unfold kPtrArrayEntriesPerCommit. lia. Qed.

Lemma preset_head_nonneg : 0 <= 16.
Proof. lia. Qed.

Lemma preset_head_al : 16 mod 8 = 0.
Proof. reflexivity. Qed.

Lemma preset_fs_classes_ok : Forall (fun c => 0 <= c <= 10) [0; 1; 3].
Proof. repeat constructor; lia. Qed.

Lemma preset_nob_lo : 536870912 <= 2 ^ 29.
Proof. apply Z.leb_le. reflexivity. Qed.

Lemma preset_nob_al : 2 ^ 29 mod 4096 = 0.
Proof. reflexivity. Qed.

(* c-asan's counting condition at NOB = 2 ^ 29 and limit 80,953 (SecGrantP.v, 820536849e5):
   the left side is 140,734,446,088,192 against 0x7fff7f800000 = 140,735,332,483,072, a margin
   of 886,394,880 < 2 ^ 30, so 80,954 fails. *)
Lemma preset_place_ok : 0x2aaaaaaab000 + (257 * 25 + 80953) * (2 * 2 ^ 29) + 2 ^ 29 <= 0x7fff7f800000.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma preset_sec_live_pos : 0 < 16000.
Proof. lia. Qed.

(* cf_kmax: 2 ^ 17, above the 49,356 secondaries of the worst measured run. *)
Definition preset_kmax : Z := 2 ^ 17.

Lemma preset_kmax_ok : 0 <= preset_kmax <= 2 ^ 24.
Proof. unfold preset_kmax. lia. Qed.

Lemma preset_sec_live_place_lt : 16000 < 80953.
Proof. lia. Qed.

(* cf_T_max: 2 ^ 36, above the measured run's T <= 6,537,494,528 B. *)
Definition preset_T_max : Z := 2 ^ 36.

Lemma preset_T_max_ok : 0 <= preset_T_max <= 2 ^ 38.
Proof. unfold preset_T_max. split; apply Z.leb_le; reflexivity. Qed.

Lemma preset_sec_map_size_nonneg : forall n, 0 <= sec_map_size n.
Proof.
intros n. unfold sec_map_size, needed_size, needed_primary, rounded_size, rz_size, round_up.
assert (R : 0 <= Z.shiftl 16 (rz_log n)) by (apply Z.shiftl_nonneg; lia).
assert (P : 0 < kPage) by (unfold kPage; lia).
assert (M : 0 <= (Z.max n 8 + 8 - 1) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
destruct (from_primary n);
  (apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]|]; lia).
Qed.

Definition preset_hull_adm (S : astate) (n : Z) : Prop :=
nsec_cf S + (if from_primary n then 0 else 1) <= preset_kmax /\
sec_T_cf S + (if from_primary n then 0 else sec_map_size n) <= preset_T_max.

Lemma preset_charge_T_nonneg : forall n, 0 <= (if from_primary n then 0 else sec_map_size n).
Proof. intros n. destruct (from_primary n); [lia | apply preset_sec_map_size_nonneg]. Qed.

Definition CfParams_preset : CfParams := {|
  cf_malloc_max := 2 ^ 28 + 2 ^ 27;
  cf_nob := 2 ^ 29;
  cf_place_limit := 80953;
  cf_sec_live_max := 16000;
  cf_fs_classes := [0; 1; 3];
  cf_head := 16;
  cf_malloc_max_pos := preset_malloc_max_pos;
  cf_sizes_ok := preset_sizes_ok;
  cf_malloc_max_ge := preset_malloc_max_ge;
  cf_nob_ok := preset_nob_ok;
  cf_sec_live_nonneg := preset_sec_live_nonneg;
  cf_sec_live_ok := preset_sec_live_ok;
  cf_nob_sec_len := preset_nob_sec_len;
  cf_sec_live_commit := preset_sec_live_commit;
  cf_head_nonneg := preset_head_nonneg;
  cf_head_al := preset_head_al;
  cf_fs_classes_ok := preset_fs_classes_ok;
  cf_nob_lo := preset_nob_lo;
  cf_nob_al := preset_nob_al;
  cf_place_ok := preset_place_ok;
  cf_sec_live_pos := preset_sec_live_pos;
  cf_kmax := preset_kmax;
  cf_kmax_ok := preset_kmax_ok;
  cf_sec_live_place_lt := preset_sec_live_place_lt;
  cf_T_max := preset_T_max;
  cf_T_max_ok := preset_T_max_ok;
  cf_hull := sec_hulls_cf;
  cf_hull_ok := fun S => nsec_cf S <= preset_kmax /\ sec_T_cf S <= preset_T_max;
  cf_rec_drop := fun _ => 0;
  cf_hull_init := preset_hull_init;
  cf_hull_frame := fun S S' E _ => preset_hull_frame S S' E;
  cf_hull_alloc := fun S S' L z HL Hz E _ => preset_hull_alloc S S' L z HL Hz E;
  cf_hull_errb := fun S S' G _ => preset_hull_errb S S' G;
  cf_hull_recycle := fun X X2 _ _ _ r _ sm _ _ _ Hn _ _ _ ES => preset_hull_recycle X X2 r sm Hn ES;
  cf_hull_bound := preset_hull_bound preset_kmax preset_T_max (proj2 preset_kmax_ok) (proj2 preset_T_max_ok);
  cf_hull_mono_back := preset_hull_mono_back preset_kmax preset_T_max;
  cf_hull_counts := preset_hull_counts preset_kmax preset_T_max;
  cf_hull_ok_init := preset_hull_ok_init preset_kmax preset_T_max (proj1 preset_kmax_ok) (proj1 preset_T_max_ok);
  cf_hull_ok_errb := preset_hull_ok_errb preset_kmax preset_T_max;
  cf_hull_adm := preset_hull_adm;
  cf_hull_adm_post := fun S n q S' H P =>
    preset_hull_adm_post preset_kmax preset_T_max S n q S' (proj1 H) (proj2 H) (preset_charge_T_nonneg n) P
|}.

(* The admission at this record is the layer's meter sec_meter_ok_cf (YG0ncf.v), by conversion. *)
Example cf_hull_ok_conv_preset S : @cf_hull_ok CfParams_preset S <-> @sec_meter_ok_cf CfParams_preset S :=
conj (fun h => h) (fun h => h).

(* cf_hull_adm is satisfiable at this record: at init_state, the first call of every admitted size has entry headroom.
   At a later call of a run, the discharge is the driver's drv_cf_headroom_at_call_A / _B (from the run position's
   counts). *)
Lemma preset_hull_adm_init : forall n, 0 <= n < 2 ^ 28 + 2 ^ 27 -> @cf_hull_adm CfParams_preset init_state n.
Proof.
intros n Hn. cbn [cf_hull_adm CfParams_preset]. unfold preset_hull_adm, preset_kmax, preset_T_max.
pose proof (preset_sizes_ok n Hn) as Hs.
assert (E : nsec_cf init_state = 0 /\ sec_T_cf init_state = 0) by (unfold nsec_cf, sec_T_cf; cbn; lia).
destruct E as [E1 E2]. rewrite E1, E2.
destruct (from_primary n); lia.
Qed.

(* The head is at least one word (WalkKitK0's request, 07:10Z): at cf_head = 0 the harness's NUL store at the block
   start (A 0x87ea4) overwrites the ledger's word at the user pointer. A preset fact, NOT a class field: the class
   allows cf_head = 0 for a harness that hides no head, and no other unit's value is measured yet. *)
Lemma preset_head_wide : 8 <= @cf_head CfParams_preset.
Proof. cbn. lia. Qed.
