(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1nw X1qz X1r0 X1nt X1rg X1nv X1qt.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CoreSafe.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Variable lib_malloc : Z -> M St (option ptr).
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable spx_warning : list Z -> M St unit.

Variable KROOM : nat.

Hypothesis Hmal : forall X n, 0 <= n -> n < MMAP_THRESHOLD -> (length X < KROOM)%nat ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).
Hypothesis Hcal : forall X n m, 0 <= n -> 0 <= m -> n * m < MMAP_THRESHOLD -> (length X < KROOM)%nat ->
mspec (own X) (lib_calloc n m) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).
Variable reall : ptr -> Prop.
Local Notation REALL_MIN := X1nv.REALL_MIN.
Hypothesis Hmal_big : forall X n, REALL_MIN <= n -> n < MMAP_THRESHOLD -> (length X < KROOM)%nat ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hcal_big : forall X n m, 0 <= n -> 0 <= m -> REALL_MIN <= n * m -> n * m < MMAP_THRESHOLD -> (length X < KROOM)%nat ->
mspec (own X) (lib_calloc n m) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hrea : forall X p n, reall p -> REALL_MIN <= n < MMAP_THRESHOLD -> (length X + 1 < KROOM)%nat ->
mspec (own (p :: X)) (lib_realloc p n) (fun r s mo => match r with Some q => own (q :: X) s mo /\ reall q | None => own (p :: X) s mo end).
Hypothesis Hfree : forall X p, mspec (own (p :: X)) (lib_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hnotify : forall X msg, msg_ok msg -> mspec (own X) (spx_notify msg) (fun _ => own X).
Hypothesis Hwarning : forall X msg, msg_ok msg -> mspec (own X) (spx_warning msg) (fun _ => own X).

Local Notation sy_ptrs := (@sy_ptrs ptr).
Local Notation os_ptrs := (@os_ptrs ptr).
Local Notation os_reall := (os_reall reall).

#[using="Hperm"] Lemma own_perm_pre {A} (X Y : list ptr) (m : M St A) Q :
Permutation Y X -> mspec (own Y) m Q -> mspec (own X) m Q.
Proof. intros HP Hm. eapply mspec_pre; [exact Hm|]. intros s mo H. eapply Hperm; [apply Permutation_sym; exact HP| exact H]. Qed.

#[using="Hfree"] Lemma ogg_sync_clear_spec : forall X sy,
mspec (own (sy_ptrs sy ++ X)) (ogg_sync_clear lib_free sy) (fun sy' s mo => own X s mo /\ sy' = ogg_sync_init).
Proof.
intros X sy. unfold ogg_sync_clear, sy_ptrs. destruct (sy_data sy) as [p|]; cbn.
- eapply mspec_seq; [apply Hfree|]. intros _. apply mspec_ret. auto.
- apply mspec_ret. auto.
Qed.

#[using="Hfree"] Lemma ogg_stream_clear_spec : forall X os,
mspec (own (os_ptrs os ++ X)) (ogg_stream_clear lib_free os) (fun os' s mo => own X s mo /\ os' = stream_zero).
Proof.
intros X os. unfold ogg_stream_clear, os_ptrs.
destruct (os_body_data os) as [b|]; destruct (os_lacing_vals os) as [l|]; destruct (os_granule_vals os) as [g|]; cbn;
repeat (eapply mspec_seq; [first [apply Hfree | apply mspec_ret; intros s mo H; exact H] | intros _]);
apply mspec_ret; auto.
Qed.

#[using="Hcal_big"] Lemma speex_bits_init_spec : forall X, (length X < KROOM)%nat ->
mspec (own X) (speex_bits_init lib_calloc)
(fun r s mo => match r with
| Some b => own (sb_chars b :: X) s mo /\ bits_ok b /\ sb_owner b = 1 /\ sb_nbBits b = 0 /\
reall (sb_chars b) /\ sb_buf_size b = MAX_CHARS_PER_FRAME
| None => own X s mo
end).
Proof.
intros X HR. unfold speex_bits_init.
eapply mspec_bind; [apply Hcal_big; unfold MAX_CHARS_PER_FRAME, X1nv.REALL_MIN, MMAP_THRESHOLD; try lia; exact HR|]. intros [p|]; cbn beta iota.
- apply mspec_pure. intros Hp. apply mspec_ret. intros s mo H. cbn. split; [exact H|]. split; [|split; [reflexivity| split; [reflexivity| split; [exact Hp| reflexivity]]]].
unfold bits_ok, speex_bits_reset, bits_pos; cbn -[zupd zrepeat MAX_CHARS_PER_FRAME Z.mul Z.add].
rewrite zlength_zupd. rewrite zlength_zrepeat by (unfold MAX_CHARS_PER_FRAME; lia).
unfold MAX_CHARS_PER_FRAME. lia.
- apply mspec_ret. intros s mo H. exact H.
Qed.

#[using="Hfree"] Lemma speex_bits_destroy_spec : forall X b, sb_owner b <> 0 ->
mspec (own (sb_chars b :: X)) (speex_bits_destroy lib_free b) (fun _ => own X).
Proof.
intros X b Ho. unfold speex_bits_destroy. destruct (Z.eqb_spec (sb_owner b) 0); [lia|]. cbn. apply Hfree.
Qed.

#[using="Hrea Hnotify Hwarning"] Lemma speex_bits_read_from_spec : forall X b pkt len, bits_ok b -> 0 <= len <= zlength pkt ->
reall (sb_chars b) -> REALL_MIN <= sb_buf_size b ->
(sb_buf_size b < len -> len < MMAP_THRESHOLD) -> (length X + 1 < KROOM)%nat ->
mspec (own (sb_chars b :: X)) (speex_bits_read_from lib_realloc spx_notify spx_warning b pkt len)
(fun b' s mo => own (sb_chars b' :: X) s mo /\ (reall (sb_chars b') /\ sb_buf_size b <= sb_buf_size b') /\ bits_ok b' /\ sb_owner b' = sb_owner b /\
bits_pos b' = 0 /\ sb_overflow b' = 0 /\
(sb_nbBits b' = len * 8 \/ (sb_nbBits b' = sb_buf_size b * 8 /\ sb_buf_size b < len))).
Proof.
intros X b pkt len Hok Hlen Hrl Hbig Hbound HR. pose proof Hok as (L & S1 & N & C & B & P & O). unfold speex_bits_read_from.
eapply mspec_bind with
(Q1 := fun r s mo => let '(b1, nchars) := r in own (sb_chars b1 :: X) s mo /\ reall (sb_chars b1) /\ sb_owner b1 = sb_owner b /\
0 <= nchars <= zlength pkt /\ sb_data b1 = sb_data b /\
((nchars = len /\ sb_buf_size b1 = len /\ sb_buf_size b < len) \/ (nchars = len /\ sb_buf_size b1 = sb_buf_size b /\ len <= sb_buf_size b)
\/ (nchars = sb_buf_size b /\ sb_buf_size b1 = sb_buf_size b /\ sb_buf_size b < len))).
{ apply mspec_if; intros Hgt.
- apply Z.ltb_lt in Hgt. eapply mspec_seq; [apply Hnotify; msg_ok_tac|]. intros _.
apply mspec_if; intros _.
+ eapply mspec_bind; [apply Hrea; [exact Hrl| split; [unfold X1nv.REALL_MIN in *; lia| apply Hbound; lia]| exact HR]|]. intros [q|]; cbn beta iota.
* apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia.
* eapply mspec_seq; [apply Hwarning; msg_ok_tac|]. intros _. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia.
+ eapply mspec_seq; [apply Hwarning; msg_ok_tac|]. intros _. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia.
- apply Z.ltb_ge in Hgt. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia. }
intros [b1 nchars]. cbn beta iota. apply mspec_pointwise. intros s0 mo0 (Hown & Hrl1 & Eo & Hn & Ed & Hcases).
apply mspec_ret. intros s mo [-> ->]. cbn. split; [exact Hown|].
split. { split; [exact Hrl1|]. destruct Hcases as [(_ & E2 & ?)|[(_ & E2 & ?)|(_ & E2 & ?)]]; rewrite E2; lia. }
assert (HL : zlength (ztake nchars pkt ++ zdrop nchars (sb_data b1)) = sb_buf_size b1).
{ rewrite zlength_app, zlength_ztake by lia. rewrite Ed.
destruct Hcases as [(-> & -> & ?)|[(-> & -> & ?)|(-> & -> & ?)]].
- unfold zdrop, zlength in *. rewrite length_skipn. lia.
- rewrite zlength_zdrop by lia. lia.
- rewrite zlength_zdrop by lia. lia. }
split.
{ unfold bits_ok, bits_pos; cbn. rewrite HL. destruct Hcases as [(-> & -> & ?)|[(-> & -> & ?)|(-> & -> & ?)]]; repeat split; try lia. }
unfold bits_pos; cbn. repeat split; auto; try lia.
all: destruct Hcases as [(-> & E2 & ?)|[(-> & E2 & ?)|(-> & E2 & ?)]]; first [left; lia | right; lia].
Qed.

#[using="Hcal Hfree Hnotify"] Lemma speex_packet_to_header_spec : forall X pkt size, (length X < KROOM)%nat ->
mspec (own X) (speex_packet_to_header lib_calloc lib_free spx_notify pkt size)
(fun r s mo => match r with Some (blk, h) => own (blk :: X) s mo /\ 0 <= hd_mode h < SPEEX_NB_MODES | None => own X s mo end).
Proof.
intros X pkt size HR. unfold speex_packet_to_header.
apply mspec_if; intros _. { eapply mspec_seq; [apply Hnotify; msg_ok_tac|]. intros _. apply mspec_ret. intros s mo H; exact H. }
apply mspec_if; intros _. { apply mspec_ret. intros s mo H; exact H. }
eapply mspec_bind; [apply Hcal; unfold SIZEOF_SPEEX_HEADER, MMAP_THRESHOLD; try lia; exact HR|]. intros [blk|]; cbn beta iota.
- destruct ((SPEEX_NB_MODES <=? hd_mode (header_of_bytes pkt)) || (hd_mode (header_of_bytes pkt) <? 0)) eqn:E.
+ eapply mspec_seq; [apply Hnotify; msg_ok_tac|]. intros _. eapply mspec_seq; [apply Hfree|]. intros _. apply mspec_ret. intros s mo H; exact H.
+ apply mspec_ret. intros s mo H. split; [exact H|]. unfold set_nb_channels; cbn -[SPEEX_NB_MODES Z.le Z.lt].
apply Bool.orb_false_iff in E. destruct E as [E1 E2]. apply Z.leb_gt in E1. apply Z.ltb_ge in E2. unfold SPEEX_NB_MODES in *.
cbn in E1, E2. lia.
- apply mspec_munr.
Qed.
End CoreSafe.
