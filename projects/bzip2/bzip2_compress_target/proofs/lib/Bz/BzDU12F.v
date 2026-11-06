(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasT BzLemmasT2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition be_aft (L : dsv) (d3 : dst) (s : dstrm) : dres :=
  let nblock := sv_nblock L in
  let cap := 100000 * d_bs100k d3 in
  let tt1 := d_tt d3 in
  let L3 := sv_set_i L nblock in
  let d4 := d_set_nused (d_set_tPos d3 (Z.shiftr (zget tt1 (d_origPtr d3)) 8)) 0 in
  let d5 := if d_rand d4 =? 0 then d4 else d_set_rTPos (d_set_rNToGo d4 0) 0 in
  if cap <=? d_tPos d5 then DRetNoSave 1 L3 d5 s else
  let w := zget tt1 (d_tPos d5) in
  let d6 := d_set_nused (d_set_tPos (d_set_k0 d5 (Z.land w 255)) (Z.shiftr w 8)) 1 in
  let d7 := if d_rand d6 =? 0 then d6
            else let d' := rand_upd d6 in d_set_k0 d' (Z.lxor (d_k0 d') (rand_mask d')) in
  DRet BZ_OK L3 d7 s.

Lemma be_fast_aft : forall L d s,
  be_fast L d s = let '(tt1, cf3) := tinv_fast (Z.to_nat (sv_nblock L)) 0 (d_tt d) (d_cftab d) in
                  be_aft L (d_set_cftab (d_set_tt d tt1) cf3) s.
Proof.
  intros L d s. unfold be_fast, be_aft. destruct (tinv_fast _ _ _ _) as [tt1 cf3]. destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
Definition K_L29 (F : nat) (L : dsv) (d : dst) (s : dstrm) (i : Z) : dres :=
  dgo F (let '(tt1, cf3) := tinv_fast (Z.to_nat (sv_nblock L - i)) i (d_tt d) (d_cftab d) in
         be_aft L (d_set_cftab (d_set_tt d tt1) cf3) s).

Lemma K_HFAST_L29 : forall F L d s, K_HFAST F L d s = K_L29 F L d s 0.
Proof. intros. unfold K_HFAST, K_L29. rewrite be_fast_aft, Z.sub_0_r. reflexivity. Qed.

Lemma K_L29_step : forall F L d s i, 0 <= i < sv_nblock L ->
  K_L29 F L d s i =
  K_L29 F L (d_set_cftab (d_set_tt d (zset (d_tt d) (zget (d_cftab d) (Z.land (zget (d_tt d) i) 255))
                                        (Z.lor (zget (d_tt d) (zget (d_cftab d) (Z.land (zget (d_tt d) i) 255))) (Z.shiftl i 8))))
                         (zset (d_cftab d) (Z.land (zget (d_tt d) i) 255) (zget (d_cftab d) (Z.land (zget (d_tt d) i) 255) + 1)))
        s (i + 1).
Proof.
  intros F L d s i Hi. unfold K_L29.
  replace (Z.to_nat (sv_nblock L - i)) with (S (Z.to_nat (sv_nblock L - (i + 1)))) by lia.
  cbn [tinv_fast]. destruct d; reflexivity.
Qed.

Lemma K_L29_exit : forall F L d s, K_L29 F L d s (sv_nblock L) = dgo F (be_aft L d s).
Proof. intros. unfold K_L29. rewrite Z.sub_diag. cbn [Z.to_nat tinv_fast]. destruct d; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aft_tp (d : dst) : Z := Z.shiftr (zget (d_tt d) (d_origPtr d)) 8.
Definition aft_w (d : dst) : Z := zget (d_tt d) (aft_tp d).
(* [comment removed for export] *)
Definition aft_nr (d : dst) : dst :=
  d_set_nused (d_set_tPos (d_set_k0 (d_set_nused (d_set_tPos d (aft_tp d)) 0) (Z.land (aft_w d) 255)) (Z.shiftr (aft_w d) 8)) 1.
(* [comment removed for export] *)
Definition aft_r (d : dst) : dst :=
  d_set_k0 (d_set_rNToGo (d_set_rTPos (d_set_rNToGo
    (d_set_nused (d_set_tPos (d_set_k0 (d_set_rTPos (d_set_rNToGo (d_set_nused (d_set_tPos d (aft_tp d)) 0) 0) 0)
                                       (Z.land (aft_w d) 255)) (Z.shiftr (aft_w d) 8)) 1)
    619) 1) 618) (Z.land (aft_w d) 255).

Lemma rNums_0 : rNums 0 = 619. Proof. reflexivity. Qed.

Lemma be_aft_nr : forall L d s, d_rand d = 0 -> aft_tp d < 100000 * d_bs100k d ->
  be_aft L d s = DRet BZ_OK (sv_set_i L (sv_nblock L)) (aft_nr d) s.
Proof.
  intros L d s R TP. unfold be_aft, aft_nr, aft_w, aft_tp in *. destruct d; cbv -[Z.shiftr Z.land Z.leb Z.eqb Z.mul Z.lt Z.lxor Z.add Z.sub zget rNums rand_upd rand_mask] in *.
  rewrite R. cbv -[Z.shiftr Z.land Z.leb Z.mul Z.lt Z.lxor Z.add Z.sub zget rNums rand_upd rand_mask].
  destruct (Z.leb_spec (100000 * d_bs100k) (Z.shiftr (zget d_tt d_origPtr) 8)); [lia|]. reflexivity.
Qed.

Lemma be_aft_r : forall L d s, d_rand d = 1 -> aft_tp d < 100000 * d_bs100k d ->
  be_aft L d s = DRet BZ_OK (sv_set_i L (sv_nblock L)) (aft_r d) s.
Proof.
  intros L d s R TP. unfold be_aft, aft_r, aft_w, aft_tp in *. destruct d; cbv -[Z.shiftr Z.land Z.leb Z.eqb Z.mul Z.lt Z.lxor Z.add Z.sub zget rNums rand_upd rand_mask] in *.
  rewrite R. cbv -[Z.shiftr Z.land Z.leb Z.mul Z.lt Z.lxor Z.add Z.sub zget rNums rand_upd rand_mask].
  destruct (Z.leb_spec (100000 * d_bs100k) (Z.shiftr (zget d_tt d_origPtr) 8)); [lia|].
  unfold rand_upd, rand_mask. cbv -[Z.shiftr Z.land Z.mul Z.lxor zget rNums]. rewrite rNums_0. cbv -[Z.shiftr Z.land Z.mul Z.lxor zget].
  rewrite Z.lxor_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dinv_L29 (L : dsv) (d : dst) (i : Z) (sym tt0 : Z -> Z) : Prop :=
  0 <= i <= sv_nblock L /\ 0 <= d_origPtr d < sv_nblock L /\
  sv_nblock L <= 100000 * d_bs100k d /\ sv_nblock L <= 900000 /\
  hdr_ok d /\ tset d /\ d_small d = 0 /\
  (forall k, 0 <= k < sv_nblock L -> 0 <= sym k < 256) /\
  hist_ok (zget (d_unzftab d)) sym (Z.to_nat (sv_nblock L)) /\
  (forall k, 0 <= k < sv_nblock L -> tt0 k = sym k) /\
  (forall k, 0 <= tt0 k < 2 ^ 32) /\
  (forall k, zget (d_tt d) k = fst (tinv 0 (Z.to_nat i) tt0 (psum (zget (d_unzftab d)))) k) /\
  (forall b, 0 <= b < 256 -> zget (d_cftab d) b = snd (tinv 0 (Z.to_nat i) tt0 (psum (zget (d_unzftab d)))) b).
(* [comment removed for export] *)
Definition dinv_AFT (L : dsv) (d : dst) (sym tt0 : Z -> Z) : Prop := dinv_L29 L d (sv_nblock L) sym tt0.

(* [comment removed for export] *)
Lemma dinv_L29_entry : forall L d, dinv_HFAST L d -> (forall k, 0 <= zget (d_tt d) k < 2 ^ 32) ->
  dinv_L29 L d 0 (bsym d) (zget (d_tt d)).
Proof.
  (intros L d; cps_intros (EOB & ORIG & CFP & TS & SM); intros TTR). cps_destruct EOB as (NB1 & NB9 & SYMB & HIST & HDR).
  unfold dinv_L29. cbn [Z.to_nat tinv fst snd].
  split; [lia|]. split; [exact ORIG|]. split; [lia|]. split; [lia|]. split; [exact HDR|]. split; [exact TS|]. split; [exact SM|].
  split; [exact SYMB|]. split; [exact HIST|]. split; [intros k Hk; unfold bsym; rewrite SM; reflexivity|]. split; [exact TTR|].
  split; [intros k; reflexivity|]. intros b Hb. apply CFP. lia.
Qed.

Section Step.
  Variables (L : dsv) (d : dst) (i : Z) (sym tt0 : Z -> Z).
  Hypothesis DI : dinv_L29 L d i sym tt0.
  Hypothesis LT : i < sv_nblock L.
  Let nb := sv_nblock L.
  Let unz := zget (d_unzftab d).
  Let r := tinv 0 (Z.to_nat i) tt0 (psum unz).
  (* [comment removed for export] *)
  Definition l29_uc : Z := Z.land (zget (d_tt d) i) 255.
  Definition l29_k : Z := zget (d_cftab d) l29_uc.
  Definition l29_v : Z := Z.lor (zget (d_tt d) l29_k) (Z.shiftl i 8).
  Definition l29_d' : dst :=
    d_set_cftab (d_set_tt d (zset (d_tt d) l29_k l29_v)) (zset (d_cftab d) l29_uc (l29_k + 1)).

  Lemma l29_facts :
    l29_uc = sym i /\ 0 <= l29_uc < 256 /\ 0 <= l29_k < nb /\ 0 <= zget (d_tt d) l29_k < 2 ^ 28 /\
    (forall k, 0 <= k < nb -> 0 <= zget (d_tt d) k < 2 ^ 28) /\ 0 <= l29_v < 2 ^ 28 /\
    tinv 0 (Z.to_nat (i + 1)) tt0 (psum unz) = (zfupd (fst r) l29_k l29_v, zfupd (snd r) l29_uc (l29_k + 1)).
  Proof.
    cps_destruct DI as (Hi & ORIG & NB1 & NB9 & HDR & TS & SM & SYMB & HIST & HT0 & HT0R & TTV & CFV).
    pose proof (fast_step_pack sym unz tt0 nb ltac:(unfold nb; lia) SYMB HIST HT0 HT0R i ltac:(unfold nb; lia)) as P.
    cbn zeta in P. fold r in P. cps_destruct P as (UC & UCR & IDXR & VR & ALLR & STEP).
    assert (EUC : l29_uc = sym i).
    { unfold l29_uc. rewrite TTV. unfold lo8 in UC. exact UC. }
    assert (EK : l29_k = snd r (sym i)).
    { unfold l29_k. rewrite EUC. rewrite CFV by lia. reflexivity. }
    assert (EV : l29_v = Z.lor (fst r (snd r (sym i))) (i * 256)).
    { unfold l29_v. rewrite TTV, EK. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    split; [exact EUC|]. split; [lia|]. split; [rewrite EK; exact IDXR|].
    split; [rewrite TTV, EK; exact VR|].
    split; [intros k Hk; rewrite TTV; apply ALLR; exact Hk|].
    split; [rewrite EV; apply lor_lt_pow2; lia|].
    rewrite EK, EV, EUC. exact STEP.
  Qed.

  Lemma dinv_L29_step : dinv_L29 L l29_d' (i + 1) sym tt0.
  Proof.
    cps_pose l29_facts as (EUC & UCR & KR & VR & ALLR & VR2 & STEP).
    cps_destruct DI as (Hi & ORIG & NB1 & NB9 & HDR & TS & SM & SYMB & HIST & HT0 & HT0R & TTV & CFV).
    unfold dinv_L29, l29_d'. unfold hdr_ok, tset in *.
    destruct d; cbn -[Z.pow Z.to_nat tinv psum Z.add Z.mul Z.land Z.lor Z.shiftl l29_k l29_v l29_uc] in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - intros k. fold unz. rewrite STEP. cbn [fst]. rewrite zget_zset, zfupd_eq.
      destruct (Z.eqb_spec k l29_k); [reflexivity| apply TTV].
    - intros b Hb. fold unz. rewrite STEP. cbn [snd]. rewrite zget_zset, zfupd_eq.
      destruct (Z.eqb_spec b l29_uc); [reflexivity| apply CFV; exact Hb].
  Qed.
End Step.

(* [comment removed for export] *)
Lemma dinv_AFT_facts : forall L d sym tt0, dinv_AFT L d sym tt0 ->
  0 <= aft_tp d < sv_nblock L /\ (forall k, 0 <= k < sv_nblock L -> 0 <= zget (d_tt d) k < 2 ^ 28) /\
  (forall k, 0 <= zget (d_tt d) k < 2 ^ 32).
Proof.
  (intros L d sym tt0; cps_intros (Hi & ORIG & NB1 & NB9 & HDR & TS & SM & SYMB & HIST & HT0 & HT0R & TTV & CFV)).
  pose proof (fast_final_pack sym (zget (d_unzftab d)) tt0 (sv_nblock L) ltac:(lia) SYMB HIST HT0 HT0R) as [SHR ALLR].
  split; [unfold aft_tp; rewrite TTV; apply SHR; lia|].
  split; [intros k Hk; rewrite TTV; apply ALLR; exact Hk|].
  intros k. rewrite TTV.
  set (nbn := Z.to_nat (sv_nblock L)).
  assert (HsymN : forall q, 0 <= q < Z.of_nat nbn -> 0 <= sym q < 256) by (intros; apply SYMB; lia).
  assert (HhistN : hist_ok (zget (d_unzftab d)) sym nbn) by exact HIST.
  assert (Hcf : forall b, 0 <= b <= 256 -> psum (zget (d_unzftab d)) b = psum (zget (d_unzftab d)) b) by reflexivity.
  assert (Hcf256 : psum (zget (d_unzftab d)) 256 <= Z.of_nat nbn) by (rewrite (psum_256 sym _ nbn HsymN HhistN); lia).
  assert (Htt0' : forall q, 0 <= q < Z.of_nat nbn -> lo8 (tt0 q) = sym q).
  { intros q Hq. rewrite HT0 by lia. apply lo8_small. apply SYMB. lia. }
  assert (HnN : Z.of_nat nbn <= 900000) by lia.
  cps_destruct (tinv_inv sym (zget (d_unzftab d)) (psum (zget (d_unzftab d))) tt0 nbn HsymN HhistN Hcf Hcf256 Htt0' HT0R HnN nbn ltac:(lia))
    as (_ & _ & _ & _ & A5).
  apply A5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
