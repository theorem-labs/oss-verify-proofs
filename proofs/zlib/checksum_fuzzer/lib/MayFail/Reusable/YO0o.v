(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0o.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: preserved allocator resources for both successful and failed allocation results; changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Record rbound := RB { rb_bytes : Z; rb_cnt : Z; rb_hand : Z; rb_brk : Z }.
Definition res_ok (s : astate) (b : rbound) : Prop :=
II s /\ map_bytes s <= rb_bytes b /\ map_count s <= rb_cnt b /\ hand s <= rb_hand b /\ brk_bytes s <= rb_brk b.
Definition rb_malloc (b : rbound) (n : Z) : rbound :=
RB (rb_bytes b + mdelta n) (rb_cnt b + 1) (rb_hand b + 65) (rb_brk b + 2 * PGSZ).
Definition rb_free (b : rbound) (n : Z) : rbound :=
if MMAP_THRESHOLD <? n then RB (rb_bytes b - page_round (n + IB + UNIT)) (rb_cnt b - 1) (rb_hand b) (rb_brk b) else b.
Definition rb_le (b b' : rbound) : Prop :=
rb_bytes b <= rb_bytes b' /\ rb_cnt b <= rb_cnt b' /\ rb_hand b <= rb_hand b' /\ rb_brk b <= rb_brk b'.
Lemma rb_le_refl b : rb_le b b. Proof. unfold rb_le. lia. Qed.
Lemma rb_le_trans b1 b2 b3 : rb_le b1 b2 -> rb_le b2 b3 -> rb_le b1 b3. Proof. unfold rb_le. lia. Qed.
Lemma rb_le_malloc b n : 0 <= n -> rb_le b (rb_malloc b n).
Proof. intros Hn. pose proof (mdelta_nonneg n Hn). unfold rb_le, rb_malloc, PGSZ. cbn. lia. Qed.
Lemma rb_free_le b n : rb_le (rb_free b n) b.
Proof. unfold rb_le, rb_free. destruct (MMAP_THRESHOLD <? n) eqn:E; cbn; [|lia]. apply Z.ltb_lt in E. pose proof (page_round_bounds (n + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT in *. lia. Qed.
Lemma res_ok_mono s b b' : rb_le b b' -> res_ok s b -> res_ok s b'.
Proof. unfold rb_le, res_ok. intros H1 H2. repeat split; try apply H2; lia. Qed.
Definition shcap (h : Z) : Z := 2 * (h / METAS_PER_AREA) + 2.
Lemma pow2_ge_succ k : 0 <= k -> k + 1 <= 2 ^ k.
Proof.
intros Hk. pattern k. apply natlike_ind; [cbn; lia | | exact Hk].
intros x Hx IH. rewrite Z.pow_succ_r by lia. lia.
Qed.
Lemma shcap_ok s : II s -> 2 ^ shift s <= shcap (hand s).
Proof.
intros (_ & Hsh & _ & _ & _ & _ & _ & _ & He). unfold shcap. unfold METAS_PER_AREA in *.
destruct (Z.eq_dec (shift s) 0) as [E|NE].
- rewrite E in *. cbn in He |- *. pose proof (Z.div_pos (hand s) 101). lia.
- pose proof (pow2_ge_succ (shift s - 1) ltac:(lia)) as Hp.
replace (2 ^ shift s) with (2 * 2 ^ (shift s - 1)) in * by (rewrite <- pow2_succ by lia; f_equal; lia).
assert (2 ^ (shift s - 1) - 1 <= hand s / 101); [|lia].
apply Z.div_le_lower_bound; lia.
Qed.
Lemma shcap_mono h h' : h <= h' -> shcap h <= shcap h'.
Proof. intros H. unfold shcap, METAS_PER_AREA. pose proof (Z.div_le_mono h h' 101 ltac:(lia) H). lia. Qed.
Definition room (b : rbound) (n : Z) : Prop :=
0 <= n /\
rb_bytes b + rb_brk b + 4 * PGSZ * shcap (rb_hand b) + 3 * PGSZ + Z.max MMAX (page_round (n + IB + UNIT)) <= MG_LIVE /\
rb_cnt b + rb_brk b / PGSZ + shcap (rb_hand b) + 5 <= MG_SLOTS /\
2 * PGSZ * shcap (rb_hand b) <= MG_REQ /\ page_round (n + IB + UNIT) <= MG_REQ.
Lemma page_round_mono x y : x <= y -> page_round x <= page_round y.
Proof. intros H. unfold page_round, PGSZ. pose proof (Z.div_le_mono (x + 4096 - 1) (y + 4096 - 1) 4096 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma room_mono b b' n n' : rb_le b b' -> 0 <= n <= n' -> room b' n' -> room b n.
Proof.
unfold rb_le, room. intros (L1 & L2 & L3 & L4) Hn (R0 & R1 & R2 & R3 & R4).
pose proof (shcap_mono _ _ L3). pose proof (page_round_mono (n + IB + UNIT) (n' + IB + UNIT) ltac:(lia)).
pose proof (Z.div_le_mono _ _ PGSZ ltac:(unfold PGSZ; lia) L4). unfold PGSZ in *. repeat split; try lia.
Qed.
Lemma res_room s b n : res_ok s b -> room b n -> ROOM4 s n.
Proof.
intros (HII & B1 & B2 & B3 & B4) (R0 & R1 & R2 & R3 & R4).
pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & _).
pose proof (shcap_ok s HII) as SC. pose proof (shcap_mono _ _ B3) as SM.
pose proof (Z.div_le_mono _ _ PGSZ ltac:(unfold PGSZ; lia) B4) as DB.
pose proof (Z.pow_pos_nonneg 2 (shift s) ltac:(lia) Hsh).
unfold ROOM4, LIVE_UB, SLOT_UB, area. rewrite Hrt. unfold PGSZ in *.
repeat split; try lia; try nia.
Qed.
Lemma room_size n b : room b n -> size_overflows n = false /\ 0 <= n < 2 ^ 62.
Proof.
intros (R0 & _ & _ & _ & R4). pose proof (page_round_bounds (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)).
unfold MG_REQ, IB, UNIT in *. split; [|lia]. unfold size_overflows. apply Z.leb_gt. lia.
Qed.
Theorem malloc_ok04_res s b n : WF s -> res_ok s b -> room b n -> ok04 mgrant (malloc n s).
Proof.
intros HW HR HRm. pose proof (room_size n b HRm) as [_ Hn].
exact (proj1 (OK4_malloc n s (malloc_reqs_ok s n HW ltac:(lia)) (proj1 HR) ltac:(lia) (res_room s b n HR HRm))).
Qed.
Theorem malloc_leaf04_res s b n tr r s' : WF s -> res_ok s b -> room b n ->
cpath04 (malloc n s) tr (r, s') -> res_ok s' (rb_malloc b n).
Proof.
intros HW HR HRm Hp. pose proof (room_size n b HRm) as [Ho Hn].
pose proof (OK4_malloc n s (malloc_reqs_ok s n HW ltac:(lia)) (proj1 HR) ltac:(lia) (res_room s b n HR HRm)) as [_ HL].
pose proof (leaves_cpath04 _ _ _ _ HL Hp) as HP. unfold MPost in HP. cbn [snd] in HP.
destruct HR as (_ & B1 & B2 & B3 & B4). destruct HP as (II' & P1 & P2 & P3 & P4 & P5).
unfold res_ok, rb_malloc. cbn. repeat split; try exact II'; try lia. all: apply II'.
Qed.
Theorem free_ok04_res s b p : reqs_ok (free p s) -> res_ok s b -> ok04 mgrant (free p s).
Proof. intros RQ HR. exact (proj1 (OK4_free p s RQ (proj1 HR))). Qed.
Theorem free_leaf04_keep s b p tr u s' : reqs_ok (free p s) -> res_ok s b ->
cpath04 (free p s) tr (u, s') -> res_ok s' b.
Proof.
intros RQ HR Hp. pose proof (OK4_free p s RQ (proj1 HR)) as [_ HL].
pose proof (leaves_cpath04 _ _ _ _ HL Hp) as HP. unfold FPost in HP. cbn [snd] in HP.
destruct HR as (_ & B1 & B2 & B3 & B4). destruct HP as (II' & P1 & P2 & P3 & P4 & P5 & _).
unfold res_ok. repeat split; try exact II'; try lia. all: apply II'.
Qed.
Theorem free_leaf04_res s b p n tr u s' : WF s -> In (p, n) (user_blocks s) -> res_ok s b ->
cpath04 (free (Some p) s) tr (u, s') -> res_ok s' (rb_free b n).
Proof.
intros HW Hin HR Hp. pose proof (free_reqs_ok s p n HW Hin) as RQ.
pose proof (free_leaf04_keep s b (Some p) tr u s' RQ HR Hp) as HK.
unfold rb_free. destruct (MMAP_THRESHOLD <? n) eqn:E; [|exact HK]. apply Z.ltb_lt in E.
pose proof (free_credit s p n HW (proj1 HR) Hin E) as [_ HL].
pose proof (leaves_cpath04 _ _ _ _ HL Hp) as [C1 C2]. cbn [snd] in C1, C2.
destruct HR as (_ & B1 & B2 & B3 & B4). destruct HK as (II' & P1 & P2 & P3 & P4).
unfold res_ok. cbn. repeat split; try exact II'; try lia. all: apply II'.
Qed.
Section c.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
(** The old success-only malloc_SR_res is deliberately absent: full
    may-fail executions can return NULL even when the budget has room. *)
Theorem free_SR_res :
free_realizes B MR ->
forall L A regs mem md p n b,
call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> res_ok A b ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => exists A' tr, cpath04 (free (Some p) A) tr (tt, A') /\
free_leaf B MR L A regs mem md p n (tt, A') c' /\ res_ok A' (rb_free b n)).
Proof.
intros HF L A regs mem md p n b Hpre Hin Hp HR.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof (free_reqs_ok A p n HW Hin) as RQ.
eapply SR_mono; [apply (free_SR_ok B MR HF L A regs mem md p n Hpre Hin Hp (free_ok04_res A b (Some p) RQ HR))|].
intros c' ([[] A'] & tr & Hcp & HL). exists A', tr. split; [exact Hcp|]. split; [exact HL|].
eapply free_leaf04_res; [exact HW | exact Hin | exact HR | exact Hcp].
Qed.
End c.
End a.
