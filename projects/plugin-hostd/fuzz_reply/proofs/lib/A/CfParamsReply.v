(* fuzz_reply's CfParams for the shared event-free allocator instance (Reusable/YGcfNames.v), in the form of
   fuzz_preset's per-unit file (a working branch fuzz_preset/lib/A/CfParamsPreset.v).  PER-UNIT
   file, not in the shared set.  A Definition, NOT an exported Instance, so a consumer names it and inference can never
   pick another unit's parameters.
   It also PINS MMAX, the request bound every live-state rule and walk takes as a Section variable (W_journal.v:766,
   W_contract.v lp_spec / gm_spec / sl / dr / re, HMMAX : 0 < MMAX <= 2 ^ 30 in the drain files): the composition
   sets MMAX := fr_MMAX = @cf_malloc_max CfParams_reply, and reply_HMMAX discharges HMMAX at that value.
   Values and where each comes from:
   - cf_malloc_max = 2 ^ 30 - 2 ^ 20: the value agreed with the instance's author (W_journal.v:746, :766-769).  The
     harness's largest request is the expected list's vector at 2 ^ 25 entries of 16 bytes = 2 ^ 29 bytes
     (REPLY-INSTANCE-REQUIREMENTS.md (sha256 f19868a5803c; internal record) item 8, s1.2), above cgif's MALLOC_MAX = 2 ^ 28 and below this bound.
   - cf_nob = 2 ^ 30: the secondary map size cap that admits that bound (YGcfNames.v's class comment: 2 ^ 30 - 2 ^ 20
     fits under 2 ^ 30, 2 ^ 30 would overshoot); reply_sizes_ok shows every admissible request maps under it.
   - cf_place_limit = 37,264: a Theorem Labs lane's LPS placement counting limit at NOB = 2 ^ 30 (YGcfNames.v's class comment;
     reply_place_ok shows the counting condition, and 37,265 fails it).
   - cf_sec_live_max = 8,192: the bound counts the secondary-array entries, which are the live secondary blocks PLUS
     the ones held in quarantine.  A Theorem Labs lane's room_live_cf (a working branch
     Reusable/YGcfRoomLive.v, rl_param_ok :1206) needs QSEC_MAX + 6 < cf_sec_live_max, and its live-set premise needs
     Lsec + QSEC_MAX + 3 < cf_sec_live_max, with QSEC_MAX = (kQuarantineMax + kQuarantineCacheMax) / 64513 = 4,177
     (Reusable/YGcfSecBound.v:37).  fuzz_reply's peak live secondary blocks is 513 at K = 511 (the drain's start:
     511 pending copies + the expected vector + g_out), EXTRAPOLATED from measurements at K <= 3 where it is K + 2
     (REPLY-INSTANCE-REQUIREMENTS.md (sha256 f19868a5803c; internal record) s1.1-1.2, item 9); the source derivation gives 514 for an instant, because
     ASan's realloc grants the new block before it frees the old (expected's 32,768 -> 65,536 step).  So Lsec = 514
     needs more than 4,694.  8,192 is the value a8's header names for reply; it is below kPtrArrayEntriesPerCommit =
     16,384 and below cf_place_limit.  reply_rl_param_ok and reply_live_sec_room check both conditions (the latter
     at 513 + QSEC_MAX + 3, which covers 514 + QSEC_MAX + 2).
   - cf_fs_classes = [0; 1]: the fake-stack size classes this unit's frames use, read from the images: the only
     __asan_stack_malloc_<c> calls are to classes 0 and 1 (A: 3 calls to _0, 2 to _1; B: 1 to _0, 2 to _1;
     the objdumps of the pinned fuzz_reply.asan, sha256 42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a, and fuzz_reply.asan-ubsan, sha256
     10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c), as W_journal.v:746 says.
   - cf_head = 0: fuzz_reply's harness calls plain malloc / free / realloc and hides no head (source/fuzz_reply.c has
     no allocator wrapper).  Nothing here may assume preset's `8 <= cf_head` (CfParamsPreset.v preset_head_wide): no
     file of this unit states it.
   - cf_kmax = reply_kmax = 2 ^ 23: the bound on a run's user secondary entries N = nsec_cf S (YGcfNames.v cf_kmax),
     which is also the admission cf_hull_ok (nsec_cf S <= reply_kmax: cf_hull_ok_conv_reply).
   - cf_T_max = 0: the admission reads the count alone, so T is not used at reply.
   - cf_hull = reply_hull_cf (the live hulls + 16384 per recycled secondary), cf_rec_drop = reply_rec_drop_cf; the
     hull laws are YGcfAbudget.v section 6's reply_hull_* at K := reply_kmax. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG08 YGcfNames YGcfSecBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfAbudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma reply_malloc_max_pos : 2 ^ 20 <= 2 ^ 30 - 2 ^ 20.
Proof. apply Z.leb_le. reflexivity. Qed.

(* Every admissible request maps under NOB: sec_map_size n <= req_size n + 2 ^ 14 (YG08.v:15), and
   req_size n <= n + 1, so at most 2 ^ 30 - 2 ^ 20 + 2 ^ 14 < 2 ^ 30. *)
Lemma reply_sizes_ok : forall n, 0 <= n < 2 ^ 30 - 2 ^ 20 -> sec_map_size n <= 2 ^ 30.
Proof.
intros n [H0 H1]. pose proof (sec_map_size_bound n H0) as B. unfold req_size in B.
change (2 ^ 30) with 1073741824 in *. change (2 ^ 20) with 1048576 in *. change (2 ^ 14) with 16384 in *.
destruct (n =? 0); lia.
Qed.

Lemma reply_malloc_max_ge : MALLOC_MAX <= 2 ^ 30 - 2 ^ 20.
Proof. unfold MALLOC_MAX. apply Z.leb_le. reflexivity. Qed.

Lemma reply_nob_ok : 2 ^ 30 <= 2 ^ 30.
Proof. lia. Qed.

Lemma reply_sec_live_nonneg : 0 <= 8192.
Proof. lia. Qed.

Lemma reply_sec_live_ok : 8192 <= 37264.
Proof. lia. Qed.

Lemma reply_nob_sec_len : SEC_LEN_MAX <= 2 ^ 30.
Proof. unfold SEC_LEN_MAX. apply Z.leb_le. reflexivity. Qed.

Lemma reply_sec_live_commit : 8192 < kPtrArrayEntriesPerCommit.
Proof. unfold kPtrArrayEntriesPerCommit. lia. Qed.

Lemma reply_head_nonneg : 0 <= 0.
Proof. lia. Qed.

Lemma reply_head_al : 0 mod 8 = 0.
Proof. reflexivity. Qed.

Lemma reply_fs_classes_ok : Forall (fun c => 0 <= c <= 10) [0; 1].
Proof. repeat constructor; lia. Qed.

Lemma reply_nob_lo : 536870912 <= 2 ^ 30.
Proof. apply Z.leb_le. reflexivity. Qed.

Lemma reply_nob_al : 2 ^ 30 mod 4096 = 0.
Proof. reflexivity. Qed.

(* a Theorem Labs lane's counting condition at NOB = 2 ^ 30 and limit 37,264: the left side is 140,733,664,948,224 against
   0x7fff7f800000 = 140,735,332,483,072, a margin of 1,667,534,848 < 2 * 2 ^ 30, so 37,265 fails. *)
Lemma reply_place_ok : 0x2aaaaaaab000 + (257 * 25 + 37264) * (2 * 2 ^ 30) + 2 ^ 30 <= 0x7fff7f800000.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma reply_sec_live_pos : 0 < 8192.
Proof. lia. Qed.

(* cf_kmax and the admission's count bound: 2 ^ 23 (ruling R1 (3), 2026-10-30) covers the driver's start budget
   12 + 4 * SEC_CALL KF_KC = 6,929,028 (A/AD1pcf.v:154; calls_bound, Reusable/YL04.v:167), and the admission
   count; the field caps it at 2 ^ 24. *)
Definition reply_kmax : Z := 2 ^ 23.

Lemma reply_kmax_ok : 0 <= reply_kmax <= 2 ^ 24.
Proof. unfold reply_kmax. split; apply Z.leb_le; reflexivity. Qed.

(* cf_sec_live_place_lt (YGcfNames.v CfParams): this image's secondary live bound 8,192 lies below its placement limit
   37,264; proved once for this image. *)
Lemma reply_sec_live_place_lt : 8192 < 37264.
Proof. lia. Qed.

Lemma reply_T_max_ok : 0 <= 0 <= 2 ^ 38.
Proof. split; apply Z.leb_le; reflexivity. Qed.

(* reply_hull_bound's premise at this record: 3,087,007,744 + 16384 * 2 ^ 23 = 140,525,961,216 <= CF_HULL_MAX. *)
Lemma reply_hull_cap_ok : 3087007744 + 16384 * reply_kmax <= CF_HULL_MAX.
Proof. unfold reply_kmax, CF_HULL_MAX. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition CfParams_reply : CfParams := {|
  cf_malloc_max := 2 ^ 30 - 2 ^ 20;
  cf_nob := 2 ^ 30;
  cf_place_limit := 37264;
  cf_sec_live_max := 8192;
  cf_fs_classes := [0; 1];
  cf_head := 0;
  cf_malloc_max_pos := reply_malloc_max_pos;
  cf_sizes_ok := reply_sizes_ok;
  cf_malloc_max_ge := reply_malloc_max_ge;
  cf_nob_ok := reply_nob_ok;
  cf_sec_live_nonneg := reply_sec_live_nonneg;
  cf_sec_live_ok := reply_sec_live_ok;
  cf_nob_sec_len := reply_nob_sec_len;
  cf_sec_live_commit := reply_sec_live_commit;
  cf_head_nonneg := reply_head_nonneg;
  cf_head_al := reply_head_al;
  cf_fs_classes_ok := reply_fs_classes_ok;
  cf_nob_lo := reply_nob_lo;
  cf_nob_al := reply_nob_al;
  cf_place_ok := reply_place_ok;
  cf_sec_live_pos := reply_sec_live_pos;
  cf_kmax := reply_kmax;
  cf_kmax_ok := reply_kmax_ok;
  cf_sec_live_place_lt := reply_sec_live_place_lt;
  cf_T_max := 0;
  cf_T_max_ok := reply_T_max_ok;
  cf_hull := reply_hull_cf;
  cf_hull_ok := fun S => nsec_cf S <= reply_kmax;
  cf_rec_drop := reply_rec_drop_cf;
  cf_hull_init := reply_hull_init;
  cf_hull_frame := reply_hull_frame;
  cf_hull_alloc := reply_hull_alloc;
  cf_hull_errb := reply_hull_errb;
  cf_hull_recycle := reply_hull_recycle;
  cf_hull_bound := reply_hull_bound reply_kmax reply_hull_cap_ok;
  cf_hull_mono_back := fun S S' G H => reply_hull_mono_back S S' reply_kmax G H;
  cf_hull_counts := fun S S' HN _ H => reply_hull_counts S S' reply_kmax HN H;
  cf_hull_ok_init := reply_hull_ok_init reply_kmax (proj1 reply_kmax_ok);
  cf_hull_ok_errb := fun S S' G L H => reply_hull_ok_errb S S' reply_kmax G L H;
  (* the entry headroom in the charge form: room for the call's one user entry (none for a primary request) *)
  cf_hull_adm := fun S n => nsec_cf S + (if from_primary n then 0 else 1) <= reply_kmax;
  cf_hull_adm_post := fun S n q S' H P => reply_hull_adm_post reply_kmax S n q S' H P
|}.

(* The admission at this record is the count bound at cf_kmax, by conversion. *)
Example cf_hull_ok_conv_reply S : @cf_hull_ok CfParams_reply S <-> nsec_cf S <= @cf_kmax CfParams_reply :=
conj (fun h => h) (fun h => h).

(* room_live_cf's parameter condition (a8's rl_param_ok, YGcfRoomLive.v:1206: QSEC_MAX + 6 < cf_sec_live_max), and
   the room its live-set premise needs at fuzz_reply's extrapolated peak of 513 live secondary blocks *)
Lemma reply_rl_param_ok : QSEC_MAX + 6 < @cf_sec_live_max CfParams_reply.
Proof. cbn. unfold QSEC_MAX, kQuarantineMax, kQuarantineCacheMax. apply Z.ltb_lt. vm_compute. reflexivity. Qed.
Lemma reply_live_sec_room : 513 + QSEC_MAX + 3 < @cf_sec_live_max CfParams_reply.
Proof. cbn. unfold QSEC_MAX, kQuarantineMax, kQuarantineCacheMax. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

(* The request bound of the live-state rules and the walks, pinned to this image's allocator. *)
Definition fr_MMAX : Z := @cf_malloc_max CfParams_reply.

(* HMMAX (W_drain.v:103 and its copies), discharged at the pinned value. *)
Lemma reply_HMMAX : 0 < fr_MMAX <= 2 ^ 30.
Proof. unfold fr_MMAX; cbn. split; apply Z.ltb_lt || apply Z.leb_le; reflexivity. Qed.

(* The vector at 2 ^ 25 entries of 16 bytes, the harness's largest request, is admissible. *)
Lemma reply_largest_request_ok : 2 ^ 29 < fr_MMAX.
Proof. unfold fr_MMAX; cbn. apply Z.ltb_lt. reflexivity. Qed.
