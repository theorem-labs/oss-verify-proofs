(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi ZApiInst ZApiInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inflate HarnessSmall InflateCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition cint (v : Z) : Prop := - 2^31 <= v < 2^31.

Definition drc4 (rc : Z) : Prop := rc = Z_OK \/ rc = Z_STREAM_END \/ rc = Z_STREAM_ERROR \/ rc = Z_BUF_ERROR.

Lemma drc4_cint : forall rc, drc4 rc -> cint rc.
Proof. intros rc [-> |[-> |[-> | ->]]]; unfold cint, Z_OK, Z_STREAM_END, Z_STREAM_ERROR, Z_BUF_ERROR; lia. Qed.

Lemma zlib_header_rc : forall s, snd (deflate_zlib_header s) = None \/ snd (deflate_zlib_header s) = Some Z_OK.
Proof. intros s. unfold deflate_zlib_header. cbv zeta. destruct (negb (ds_pending _ =? 0)); cbn [snd]; auto. Qed.

Lemma gzip_header_rc : forall s, snd (deflate_gzip_header s) = None \/ snd (deflate_gzip_header s) = Some Z_OK.
Proof. intros s. unfold deflate_gzip_header. cbv zeta. destruct (negb (ds_pending _ =? 0)); cbn [snd]; auto. Qed.

Lemma trailer_rc : forall s, drc4 (snd (deflate_trailer s)).
Proof. intros s. unfold deflate_trailer. cbv zeta. cbn [snd]. destruct (negb (ds_pending _ =? 0)); unfold drc4; auto. Qed.

Lemma blocks_rc : forall s flush, snd (deflate_blocks s flush) = None \/ snd (deflate_blocks s flush) = Some Z_OK.
Proof.
  intros s flush. unfold deflate_blocks.
  match goal with |- context [if ?c then _ else (s, None)] => destruct c end; [|left; reflexivity].
  destruct (run_compress_func s flush) as [s1 b]. cbv zeta.
  destruct (block_state_eqb b need_more || block_state_eqb b finish_started); [right; reflexivity|].
  destruct (block_state_eqb b block_done); [|left; reflexivity].
  destruct (cs_avail_out _ =? 0); [right; reflexivity | left; reflexivity].
Qed.

Lemma deflate_core_rc : forall s flush, drc4 (snd (deflate_core s flush)).
Proof.
  intros s flush. unfold deflate_core.
  destruct (deflateStateCheck s || (Z_BLOCK <? flush) || (flush <? 0)); [cbn [snd]; unfold drc4; auto|].
  destruct ((ds_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)); [cbn [err_return snd]; unfold drc4; auto|].
  destruct (cs_avail_out (ds_strm s) =? 0); [cbn [err_return snd]; unfold drc4; auto|].
  cbv zeta.
  match goal with |- drc4 (snd (let '(s0, r) := ?t in _)) => destruct t as [s1 [rc1|]] eqn:E1 end.
  { cbn [snd]. revert E1.
    destruct (negb (ds_pending _ =? 0)); [destruct (cs_avail_out _ =? 0); intros E1; [injection E1; intros <- _; unfold drc4; auto | discriminate E1]|].
    destruct (_ && _ && _); intros E1; [| discriminate E1]. unfold err_return in E1. injection E1; intros <- _. unfold drc4; auto. }
  clear E1.
  destruct ((ds_status s1 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s1) =? 0)); [cbn [err_return snd]; unfold drc4; auto|].
  set (s2 := if (ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0) then set_status s1 BUSY_STATE else s1). clearbody s2.
  match goal with |- drc4 (snd (let '(s0, r) := ?t in _)) => destruct t as [s3 [rc3|]] eqn:E3 end.
  { cbn [snd]. revert E3. destruct (ds_status s2 =? INIT_STATE); intros E3; [| discriminate E3].
    destruct (zlib_header_rc s2) as [X|X]; rewrite E3 in X; cbn [snd] in X; [discriminate X | injection X; intros ->; unfold drc4; auto]. }
  clear E3.
  match goal with |- drc4 (snd (let '(s0, r) := ?t in _)) => destruct t as [s4 [rc4|]] eqn:E4 end.
  { cbn [snd]. revert E4. destruct (ds_status s3 =? GZIP_STATE); intros E4; [| discriminate E4].
    destruct (gzip_header_rc s3) as [X|X]; rewrite E4 in X; cbn [snd] in X; [discriminate X | injection X; intros ->; unfold drc4; auto]. }
  clear E4.
  destruct (deflate_blocks s4 flush) as [s5 [rc5|]] eqn:E5.
  { cbn [snd]. destruct (blocks_rc s4 flush) as [X|X]; rewrite E5 in X; cbn [snd] in X; [discriminate X | injection X; intros ->; unfold drc4; auto]. }
  destruct (negb (flush =? Z_FINISH)); [cbn [snd]; unfold drc4; auto|].
  destruct (ds_wrap s5 <=? 0); [cbn [snd]; unfold drc4; auto|].
  apply trailer_rc.
Qed.

Lemma deflate_m_rc : forall s zc flush, drc4 (zr_rc (snd (deflate_m s zc flush))).
Proof.
  intros s zc flush. unfold deflate_m. cbv zeta.
  pose proof (deflate_core_rc (set_strm s (cstrm_of_call zc)) flush) as H.
  destruct (deflate_core _ flush) as [s' rc]. cbn [snd zret_of_cs zr_rc] in *. exact H.
Qed.

Lemma zdc_rc : forall inp x aout flush, cint (snd (zdc_deflate inp x aout flush)).
Proof.
  intros inp x aout flush. unfold zdc_deflate.
  pose proof (deflate_m_rc (dz_s x) (mkZCall inp aout (dz_z x)) flush) as H.
  destruct (deflate_m _ _ flush) as [s' zr]. cbn [snd] in *. apply drc4_cint. exact H.
Qed.

Lemma zic_rc : forall inp x aout ok, cint (snd (zic_inflate inp x aout ok)).
Proof.
  intros inp x aout ok. unfold zic_inflate, cint.
  pose proof (inflate_p_rc_range (wans ok) (iz_s x) (mkZCall inp aout (iz_z x)) Z_NO_FLUSH) as H.
  destruct (inflate_p _ _ _ _) as [[s' zr] asked]. cbn [fst snd] in *. exact H.
Qed.
