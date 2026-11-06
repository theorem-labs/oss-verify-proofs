(* The struct spec_frame of the walk of io_send (lib/Prog/T/io_send.v): the 80 bytes sf_bytes (TContract.v) has
   (sf_bytes_length), and bytes_at of them gives sframe_at when every field is in its C range (sf_bytes_sframe):
   each field is the `put` chunk at its offset, read back by u_at_put. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract.
Import ListNotations.
Open Scope Z_scope.

(* ---- reads of a concatenation (the proofs of io_send_keep.v's u_at_app_l / _r) ---- *)

Lemma sf_u_at_app_l : forall (x y : list byte) (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= Z.of_nat (length x) ->
  u_at (x ++ y) k n = u_at x k n.
Proof.
  intros x y k n Hk Hn. unfold u_at, sub. f_equal.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length x - Z.to_nat k))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma sf_u_at_app_r : forall (x y : list byte) (k : Z) (n : nat), Z.of_nat (length x) <= k ->
  u_at (x ++ y) k n = u_at y (k - Z.of_nat (length x)) n.
Proof.
  intros x y k n Hk. unfold u_at, sub. f_equal.
  rewrite skipn_app.
  assert (E : skipn (Z.to_nat k) x = []) by (apply skipn_all2; lia).
  rewrite E, app_nil_l.
  replace (Z.to_nat (k - Z.of_nat (length x))) with (Z.to_nat k - length x)%nat by lia.
  reflexivity.
Qed.

(* ---- one field: the put chunk at offset 0 of the rest, its value in range ---- *)

Lemma sf_u_at_fld : forall (y : list byte) (n : nat) (v k : Z), k = 0 -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  u_at (put n v ++ y) k n = v.
Proof.
  intros y n v k Hk Hv. subst k.
  rewrite sf_u_at_app_l by (rewrite ?length_put; lia).
  rewrite u_at_put. apply Z.mod_small. exact Hv.
Qed.

(* Strip the chunks before the field (each step: the chunk's literal length is at most the offset left), then
   read the field's put chunk. *)
Ltac sf_len := rewrite ?length_put, ?repeat_length; lia.
Ltac sf_field :=
  repeat (rewrite sf_u_at_app_r by sf_len);
  apply sf_u_at_fld; [sf_len | assumption].

(* ---- the lemmas the walk applies ---- *)

Lemma sf_bytes_length : forall (fa : Z) (f : spec_frame), length (sf_bytes fa f) = 80%nat.
Proof.
  intros fa f. unfold sf_bytes.
  rewrite !length_app, !length_put, !repeat_length. reflexivity.
Qed.

Lemma sf_bytes_sframe : forall (m : word -> option byte) (fp fa : Z) (f : spec_frame),
  0 < fp -> fp mod 8 = 0 ->
  bytes_at rsegs m fp (sf_bytes fa f) ->
  - 2 ^ 31 <= sf_code f < 2 ^ 31 ->
  0 <= sf_ptr fa f (sf_dst f) < 2 ^ 64 ->
  0 <= sf_ptr fa f (sf_src f) < 2 ^ 64 ->
  0 <= sf_ethertype f < 2 ^ 16 ->
  0 <= sf_numbytes f < 2 ^ 16 ->
  0 <= sf_sum f < 2 ^ 16 ->
  0 <= sf_retry f < 2 ^ 16 ->
  0 <= sf_send f < 2 ^ 32 ->
  0 <= sf_ack f < 2 ^ 32 ->
  0 <= sf_cmd f < 2 ^ 8 ->
  0 <= sf_ncmds f < 2 ^ 8 ->
  0 <= sf_ptr fa f (sf_body f) < 2 ^ 64 ->
  0 <= sf_body_len f < 2 ^ 64 ->
  0 <= sf_pad_len f < 2 ^ 64 ->
  0 <= sf_body_sum f < 2 ^ 16 ->
  sframe_at m fp fa f.
Proof.
  intros m fp fa f Hfp Hal HB Hc Hdst Hsrc Heth Hnum Hsum Hret Hsend Hack Hcmd Hncmds Hbody Hblen Hplen Hbsum.
  split; [exact Hfp|]. split; [exact Hal|].
  exists (sf_bytes fa f). split; [exact HB|]. split; [apply sf_bytes_length|].
  split.
  - unfold s32_at, sf_bytes.
    rewrite sf_u_at_app_l by sf_len.
    rewrite u_at_put. change (8 * Z.of_nat 4) with 32.
    change (sf_code f mod 2 ^ 32) with (bv_wrap 32 (sf_code f)). rewrite bv_swrap_wrap.
    apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia.
  - unfold sf_bytes.
    repeat match goal with |- _ /\ _ => split end; sf_field.
Qed.
