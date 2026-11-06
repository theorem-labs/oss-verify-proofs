(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1r3 X1og.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
nia.
Qed.

Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.

Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.

Lemma alloc_ceiling_hi_lt : alloc_ceiling_hi < 2^47.
Proof. reflexivity. Qed.
Lemma ld_ceil_lt L pbrk mo : KL L pbrk mo -> 0 < ld_ceil L < 2^47.
Proof. intros HK. pose proof (kl_ceil _ _ _ HK) as [_ H]. unfold alloc_ceiling_lo, alloc_ceiling_hi in H. lia. Qed.

Lemma event_post_ld_ceil L e z : ld_ceil (event_post L e z) = ld_ceil L.
Proof.
destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
- destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
- destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
- destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.
Lemma cpath_ld_ceil {R} L (t : stree ev Z R) L' r : cpath L t L' r -> ld_ceil L' = ld_ceil L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_ld_ceil. Qed.

Lemma kl_ceil_keep (h h' : VmMaps) (c : Z) (R : Prop) :
vm_init_sp h' = vm_init_sp h -> alloc_top h = c /\ R -> alloc_top h' = c /\ R.
Proof. intros E [H1 H2]. split; [| exact H2]. unfold alloc_top in *. rewrite E. exact H1. Qed.
Ltac kl_ceil_tac K := refine (kl_ceil_keep _ _ _ _ eq_refl K).

Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.

