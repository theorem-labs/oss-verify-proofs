(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP0l YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Definition blk_data (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m (a + i) = nth_error bs (Z.to_nat i).
Lemma blk_data_nil : forall m a, blk_data m a [].
Proof. intros m a i Hi. cbn in Hi. lia. Qed.
Lemma wr_check_not_block : forall L A m md E G keep rs p sz i,
MR L A m md -> facts_ok E G -> stack_anchored E G   -> wr_check B G keep rs = true ->
In (p, sz) (user_blocks A) -> 0 <= i < sz ->
~ in_wrange E rs (ptr_addr L p + i).
Proof.
intros L A m md E G keep rs p sz i HMR HG HSA Hck Hp Hi Hw.
unfold wr_check in Hck. apply andb_prop in Hck as [Hck Hall]. apply andb_prop in Hck as [Hkc Herr].
pose proof (mr_blocks B MR LAWS L A m md p sz i HMR Hp Hi) as (_ & Hlo & Hhi & Hno).
destruct Hw as (r & Hin & Ha). pose proof (forallb_In _ _ r Hall Hin) as Hr. unfold wr_region_ok in Hr.
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
destruct (r_base r) as [n|] eqn:Hb; cbn [base_val] in Ha.
- destruct (anch_lo G n) as [K|] eqn:HK; [|discriminate]. apply Z.leb_le in Hr.
pose proof (stack_anchored_sound E G n K HSA HK). lia.
- apply orb_prop in Hr as [Hr|Hr].
+ pose proof (sub_ivl_sound _ _ _ (ptr_addr L p + i) Hr ltac:(lia)) as Hx.
destruct (keep_check_sound B keep _ Hkc Hx) as (Himg & _).
exact (ax_blocks_img AX L A m md p sz i HMR Hp Hi Himg).
+ pose proof (sub_ivl_sound _ _ _ (ptr_addr L p + i) Hr ltac:(lia)) as Hx.
destruct (in_ivl_In _ _ Hx) as (q & [<-|[]] & Hq). cbn [fst snd] in Hq.
destruct (errno_check_sound B _ Herr Hq) as (Himg & _).
exact (ax_blocks_img AX L A m md p sz i HMR Hp Hi Himg).
Qed.
Theorem blk_after_frame : forall L A (m m' : word -> option byte) md E G keep rs p sz,
MR L A m md -> facts_ok E G -> stack_anchored E G   ->
wr_check B G keep rs = true ->
frame_of E rs m m' ->
In (p, sz) (user_blocks A) ->
forall i, 0 <= i < sz -> mbyte segs m' (ptr_addr L p + i) = mbyte segs m (ptr_addr L p + i).
Proof.
intros L A m m' md E G keep rs p sz HMR HG HSA Hck HF Hp i Hi.
pose proof (mr_blocks B MR LAWS L A m md p sz i HMR Hp Hi) as (_ & Hlo & Hhi & _).
assert (Hac : alloc_ceiling < 2 ^ 64) by (pose proof YM05.alloc_ceiling_val; lia).
unfold mbyte. rewrite (HF (Z_to_bv 64 (ptr_addr L p + i))); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
eapply wr_check_not_block; eassumption.
Qed.
Corollary blk_data_after_frame : forall L A (m m' : word -> option byte) md E G keep rs p sz a bs,
MR L A m md -> facts_ok E G -> stack_anchored E G   ->
wr_check B G keep rs = true ->
frame_of E rs m m' ->
In (p, sz) (user_blocks A) -> ptr_addr L p <= a -> a + Z.of_nat (length bs) <= ptr_addr L p + sz ->
blk_data m a bs -> blk_data m' a bs.
Proof.
intros L A m m' md E G keep rs p sz a bs HMR HG HSA Hck HF Hp Ha1 Ha2 HD i Hi.
rewrite <- (HD i Hi). replace (a + i) with (ptr_addr L p + (a + i - ptr_addr L p)) by lia.
apply (blk_after_frame L A m m' md E G keep rs p sz HMR HG HSA Hck HF Hp). lia.
Qed.
Lemma blk_data_kept : forall (m m' : word -> option byte) a bs,
(forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
blk_data m a bs -> blk_data m' a bs.
Proof. intros m m' a bs Hk HD i Hi. rewrite (Hk i Hi). apply HD. exact Hi. Qed.
Lemma blk_data_sub : forall m a bs k n,
blk_data m a bs -> (k + n <= length bs)%nat ->
blk_data m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
intros m a bs k n HD Hkn i Hi.
rewrite firstn_length, skipn_length in Hi.
rewrite <- Z.add_assoc. rewrite (HD (Z.of_nat k + i)) by lia.
rewrite (nth_error_firstn n (skipn k bs)).
destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) n); [| lia].
rewrite nth_error_skipn. f_equal. lia.
Qed.
End c.
End b.
