(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO04.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition DRB : rbound := RB (2 ^ 28) 13 845 106496.
Lemma leaves_mbind {A B} (P : A * astate -> Prop) (Q : B * astate -> Prop) (m : M A) (f : A -> M B) s :
leaves P (m s) -> (forall a s' tr, yields (m s) tr (a, s') -> P (a, s') -> leaves Q (f a s')) -> leaves Q (bind m f s).
Proof.
intros Hm Hf. unfold bind. eapply leaves_ibind_yields; [exact Hm|]. intros tr [a s'] Hy HP. exact (Hf a s' tr Hy HP).
Qed.
Lemma leaves_ret {A} (a : A) s (Q : A * astate -> Prop) : Q (a, s) -> leaves Q (ret a s).
Proof. intros H. exact H. Qed.
Lemma malloc_leaves_res s b n : WF s -> res_ok s b -> room b n ->
leaves (fun r => malloc_postP s n r /\ res_ok (snd r) (rb_malloc b n)) (malloc n s).
Proof.
intros HW HR HRm. pose proof (room_size n b HRm) as [_ Hn]. apply leaves_and.
- apply itok_leaves. apply malloc_itok; [exact HW | lia].
- pose proof (OK4_malloc n s (malloc_reqs_ok s n HW ltac:(lia)) (proj1 HR) ltac:(lia) (res_room s b n HR HRm)) as [_ HL].
eapply leaves_mono; [|exact HL]. intros [r s'] HP. unfold MPost in HP. cbn [snd] in HP |- *.
destruct HR as (_ & B1 & B2 & B3 & B4). destruct HP as (II' & P1 & P2 & P3 & P4 & P5).
unfold res_ok, rb_malloc. cbn. repeat split; try exact II'; try lia. all: apply II'.
Qed.
Lemma free_leaves_res s b p n : WF s -> In (p, n) (user_blocks s) -> res_ok s b ->
leaves (fun r => free_postP s p n r /\ res_ok (snd r) (rb_free b n)) (free (Some p) s).
Proof.
intros HW Hin HR. apply leaves_and.
- apply itok_leaves. apply free_itok; [exact HW | exact Hin].
- pose proof (free_reqs_ok s p n HW Hin) as RQ.
pose proof (OK4_free (Some p) s RQ (proj1 HR)) as [_ HL].
assert (HK : leaves (fun r => res_ok (snd r) b) (free (Some p) s)).
{ eapply leaves_mono; [|exact HL]. intros [u s'] HP. unfold FPost in HP. cbn [snd] in HP |- *.
destruct HR as (_ & B1 & B2 & B3 & B4). destruct HP as (II' & P1 & P2 & P3 & P4 & P5 & _).
unfold res_ok. repeat split; try exact II'; try lia. all: apply II'. }
unfold rb_free. destruct (MMAP_THRESHOLD <? n) eqn:E; [|exact HK]. apply Z.ltb_lt in E.
pose proof (free_credit s p n HW (proj1 HR) Hin E) as [_ HC].
pose proof (leaves_and _ _ _ HK HC) as HKC. eapply leaves_mono; [|exact HKC]. intros [u s'] [H1 [C1 C2]]. cbn [snd] in *.
destruct HR as (_ & B1 & B2 & B3 & B4). destruct H1 as (II' & P1 & P2 & P3 & P4).
unfold res_ok. cbn. repeat split; try exact II'; try lia. all: apply II'.
Qed.
Lemma II_init : II init_state.
Proof.
unfold II. split; [intros r Hr; destruct Hr|]. cbn. unfold hand, nareas, METAS_PER_AREA, PGSZ. cbn. lia.
Qed.
Lemma res_ok_init : res_ok init_state (RB 0 0 0 0).
Proof. split; [exact II_init|]. cbn. unfold hand, nareas, METAS_PER_AREA. cbn. lia. Qed.
Lemma page_round_exact x : x mod PGSZ = 0 -> 0 <= x -> page_round (x + IB + UNIT) = x + PGSZ.
Proof.
intros Hm Hx. unfold page_round, IB, UNIT, PGSZ in *.
set (q := x / 4096) in *. assert (E : x = 4096 * q) by (pose proof (Z.div_mod x 4096 ltac:(lia)); lia).
replace (x + 4 + 16 + 4096 - 1) with (q * 4096 + 4115) by lia.
rewrite Z.div_add_l by lia. change (4115 / 4096) with 1. lia.
Qed.
Lemma mdelta_big x : MMAP_THRESHOLD <= x -> mdelta x = page_round (x + IB + UNIT).
Proof. intros H. unfold mdelta. replace (MMAP_THRESHOLD <=? x) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.
Lemma mdelta_small x : x < MMAP_THRESHOLD -> mdelta x = MMAX.
Proof. intros H. unfold mdelta. replace (MMAP_THRESHOLD <=? x) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.
Lemma mdelta_le x : 0 <= x -> mdelta x <= Z.max MMAX (x + IB + UNIT + 4095).
Proof.
intros Hx. pose proof (page_round_bounds (x + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold mdelta.
destruct (MMAP_THRESHOLD <=? x); lia.
Qed.
Lemma shcap_845 h : h <= 845 -> shcap h <= 18.
Proof. intros H. pose proof (shcap_mono h 845 H) as M. replace (shcap 845) with 18 in M by reflexivity. exact M. Qed.
Lemma res_ok_DRB s b : res_ok s b -> rb_bytes b <= 2 ^ 28 -> rb_cnt b <= 13 -> rb_hand b <= 845 -> rb_brk b <= 106496 -> res_ok s DRB.
Proof. intros HR H1 H2 H3 H4. eapply res_ok_mono; [|exact HR]. unfold rb_le, DRB. cbn. lia. Qed.
Definition RPinv (K c : Z) (cap : Z) (b : rbound) : Prop :=
rb_bytes b <= K + mdelta cap /\ rb_cnt b <= c /\ rb_hand b <= 65 * c /\ rb_brk b <= 2 * PGSZ * c /\ 0 <= K.
Definition capflag (cap : Z) : Z := if cap <=? MMAP_THRESHOLD then MMAX else 0.
Lemma read_phase_res : forall fuel L cap k buf s b K c,
WF s -> In (buf, cap) (user_blocks s) -> cap = 2 ^ k -> 16 <= k -> cap <= MAX_INPUT ->
res_ok s b -> RPinv K c cap b -> K + capflag cap <= 2 ^ 24 -> 0 <= c -> c + Z.of_nat fuel <= 12 ->
leaves (fun r => match fst r with
| RdLoaded buf' cap' => WF (snd r) /\ L < cap' /\ cap' <= MAX_INPUT /\
exists b', res_ok (snd r) b' /\ RPinv (K + capflag cap) (c + Z.of_nat fuel) cap' b'
| _ => res_ok (snd r) DRB
end) (read_phase fuel L cap buf s).
Proof.
induction fuel as [|fuel IH]; intros L cap k buf s b K c HW Hin Hk Hk16 Hmax HR (V1 & V2 & V3 & V4 & V5) HK Hc Hcf; cbn [read_phase].
- apply leaves_ret. cbn [fst snd]. pose proof (mdelta_le cap). pose proof (Z.pow_pos_nonneg 2 k).
assert (0 <= capflag cap) by (unfold capflag; destruct (cap <=? MMAP_THRESHOLD); unfold MMAX; lia).
eapply res_ok_DRB; [exact HR | | lia | lia | unfold PGSZ in *; lia]. unfold MAX_INPUT, MMAX, IB, UNIT in *. lia.
- assert (Hcap : 65536 <= cap).
{ subst cap. change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia. }
assert (Hfl : 0 <= capflag cap) by (unfold capflag; destruct (cap <=? MMAP_THRESHOLD); unfold MMAX; lia).
pose proof (mdelta_le cap ltac:(lia)) as Hmd.
destruct (L <? cap) eqn:EL.
{ apply Z.ltb_lt in EL. apply leaves_ret. cbn [fst snd]. split; [exact HW|]. split; [exact EL|]. split; [exact Hmax|].
exists b. split; [exact HR|]. unfold RPinv. unfold PGSZ in *. repeat split; lia. }
destruct (MAX_INPUT <=? cap) eqn:EM.
{ apply leaves_ret. cbn [fst snd]. eapply res_ok_DRB; [exact HR | | lia | lia | unfold PGSZ in *; lia]. unfold MAX_INPUT, MMAX, IB, UNIT in *. lia. }
apply Z.leb_gt in EM.
assert (Hmd2 : mdelta (2 * cap) = 2 * cap + PGSZ).
{ rewrite mdelta_big by (unfold MMAP_THRESHOLD; lia). apply page_round_exact; [|lia].
subst cap. replace (2 * 2 ^ k) with ((2 * 2 ^ (k - 12)) * PGSZ); [apply Z_mod_mult|].
unfold PGSZ. change 4096 with (2 ^ 12). rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
pose proof (shcap_845 (rb_hand b) ltac:(lia)) as SC.
eapply leaves_mbind.
{ apply (malloc_leaves_res s b (2 * cap) HW HR). unfold room. rewrite <- mdelta_big by (unfold MMAP_THRESHOLD; lia). rewrite Hmd2.
unfold MG_LIVE, MG_SLOTS, MG_REQ, MAX_INPUT, MMAX, IB, UNIT, PGSZ in *.
assert (rb_brk b / 4096 <= 2 * c) by (apply Z.div_le_upper_bound; lia).
repeat split; try lia. }
intros [nb|] s1 tr1 Hy1 [[HW1 Hb] HR1]; cbn [fst snd] in HW1, Hb, HR1.
2:{ apply leaves_ret. cbn [fst snd]. eapply res_ok_DRB; [exact HR1 | | | |]; unfold rb_malloc; cbn; [rewrite Hmd2| | |]; unfold MAX_INPUT, MMAX, IB, UNIT, PGSZ in *; lia. }
destruct Hb as (l1 & l2 & E1 & E2).
assert (Hin1 : In (buf, cap) (user_blocks s1)).
{ rewrite E1. apply in_app_iff. rewrite E2 in Hin. apply in_app_iff in Hin. destruct Hin; [left | right; right]; assumption. }
assert (Hnb1 : In (nb, 2 * cap) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
eapply leaves_mbind; [apply (free_leaves_res s1 _ buf cap HW1 Hin1 HR1)|].
intros [] s2 tr2 Hy2 [[HW2 (m1 & m2 & F1 & F2)] HR2]; cbn [fst snd] in HW2, F1, F2, HR2.
assert (Hin2 : In (nb, 2 * cap) (user_blocks s2)).
{ rewrite F2. eapply in_remove_other; [rewrite <- F1; exact Hnb1 |]. intros E. injection E. lia. }
assert (H2max : 2 * cap <= MAX_INPUT).
{ subst cap. unfold MAX_INPUT in *. change 67108864 with (2 ^ 26) in *. rewrite <- Z.pow_succ_r by lia.
apply Z.pow_le_mono_r; [lia|]. apply Z.pow_lt_mono_r_iff in EM; lia. }
assert (Hfl2 : capflag (2 * cap) = 0).
{ unfold capflag. replace (2 * cap <=? MMAP_THRESHOLD) with false by (symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD; lia). reflexivity. }
eapply leaves_mono.
2:{ apply (IH L (2 * cap) (k + 1) nb s2 (rb_free (rb_malloc b (2 * cap)) cap) (K + capflag cap) (c + 1) HW2 Hin2);
[subst cap; rewrite Z.pow_add_r by lia; lia | lia | exact H2max | exact HR2 | | rewrite Hfl2; lia | lia | lia].
unfold RPinv, rb_free, rb_malloc. rewrite Hmd2.
destruct (MMAP_THRESHOLD <? cap) eqn:Et; cbn.
- apply Z.ltb_lt in Et. rewrite <- (mdelta_big cap) by lia. unfold PGSZ in *. repeat split; lia.
- apply Z.ltb_ge in Et. unfold capflag. replace (cap <=? MMAP_THRESHOLD) with true by (symmetry; apply Z.leb_le; exact Et).
unfold PGSZ, MMAX, MMAP_THRESHOLD, IB, UNIT in *. repeat split; lia. }
intros [rd s3] Hr. cbn [fst snd] in Hr |- *. destruct rd as [ | | buf' cap']; try exact Hr.
rewrite Hfl2, Z.add_0_r in Hr. replace (c + 1 + Z.of_nat fuel) with (c + Z.of_nat (S fuel)) in Hr by lia. exact Hr.
Qed.
Theorem driver_res data : leaves (fun r => res_ok (snd r) DRB) (driver_tree data).
Proof.
unfold driver_tree, driver_m.
assert (R0 : room (RB 0 0 0 0) CAP0).
{ unfold room, CAP0. cbn -[Z.le Z.lt Z.add Z.mul Z.max Z.pow Z.div]. unfold MG_LIVE, MG_SLOTS, MG_REQ, MMAX, PGSZ, shcap, METAS_PER_AREA, page_round, IB, UNIT, PGSZ. cbn. lia. }
eapply leaves_mbind; [apply (malloc_leaves_res init_state (RB 0 0 0 0) CAP0 wf_init res_ok_init R0)|].
assert (HmdC : mdelta CAP0 = MMAX) by (apply mdelta_small; unfold CAP0, MMAP_THRESHOLD; lia).
intros [b0|] s1 tr1 Hy1 [[HW1 Hb] HR1]; cbn [fst snd] in HW1, Hb, HR1.
2:{ apply leaves_ret. cbn [snd]. eapply res_ok_DRB; [exact HR1| | | |]; unfold rb_malloc; cbn -[mdelta]; rewrite ?HmdC; unfold MMAX, PGSZ; lia. }
destruct Hb as (l1 & l2 & E1 & _).
assert (Hin1 : In (b0, CAP0) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
eapply leaves_mbind.
{ apply (read_phase_res READ_FUEL (dlen data) CAP0 16 b0 s1 (rb_malloc (RB 0 0 0 0) CAP0) 0 1 HW1 Hin1);
[reflexivity | lia | unfold CAP0, MAX_INPUT; lia | exact HR1 | | | lia | unfold READ_FUEL; cbn; lia].
- unfold RPinv, rb_malloc. cbn -[mdelta]. rewrite HmdC. unfold PGSZ. repeat split; lia.
- unfold capflag, CAP0, MMAP_THRESHOLD, MMAX. cbn. lia. }
intros rd s2 tr2 Hy2 Hr. cbn [fst snd] in Hr.
assert (Hfl : capflag CAP0 = MMAX) by reflexivity. rewrite Hfl in Hr. unfold READ_FUEL in Hr. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in Hr.
destruct rd as [ | | buf cap]; [apply leaves_ret; exact Hr | apply leaves_ret; exact Hr |].
destruct Hr as (HW2 & HL & Hmax & b' & HR2 & (V1 & V2 & V3 & V4 & V5)).
assert (Hdl : 0 <= dlen data) by (unfold dlen; lia).
pose proof (mdelta_le cap ltac:(lia)) as Hmd.
assert (DRB2 : res_ok s2 DRB).
{ eapply res_ok_DRB; [exact HR2 | | lia | lia | unfold PGSZ in *; lia]. unfold MAX_INPUT, MMAX, IB, UNIT in *. lia. }
destruct (dlen data <? HDR_MIN); [apply leaves_ret; exact DRB2|].
destruct (dlen data <? HDR_MIN + config_len data) eqn:E6; [apply leaves_ret; exact DRB2|].
destruct (payload_len data =? 0) eqn:Ep; [apply leaves_ret; exact DRB2|].
assert (Hpl : 0 <= payload_len data < cap).
{ unfold payload_len, HDR_MIN in *. apply Z.ltb_ge in E6. pose proof (Z.mod_pos_bound (cfg_word data) 32768 ltac:(lia)). unfold config_len in *. lia. }
pose proof (mdelta_le (payload_len data) ltac:(lia)) as Hmdp.
pose proof (shcap_845 (rb_hand b') ltac:(lia)) as SC.
eapply leaves_mbind.
{ apply (malloc_leaves_res s2 b' (payload_len data) HW2 HR2). unfold room.
pose proof (page_round_bounds (payload_len data + IB + UNIT) ltac:(unfold IB, UNIT; lia)).
unfold MG_LIVE, MG_SLOTS, MG_REQ, MAX_INPUT, MMAX, IB, UNIT, PGSZ in *.
assert (rb_brk b' / 4096 <= 2 * 12) by (apply Z.div_le_upper_bound; lia).
repeat split; try lia. }
intros [q|] s3 tr3 Hy3 [[HW3 _] HR3]; cbn [fst snd] in HR3; apply leaves_ret; cbn [snd].
all: eapply res_ok_DRB; [exact HR3 | | | |]; unfold rb_malloc; cbn -[mdelta]; unfold MAX_INPUT, MMAX, IB, UNIT, PGSZ in *; lia.
Qed.
End d.
