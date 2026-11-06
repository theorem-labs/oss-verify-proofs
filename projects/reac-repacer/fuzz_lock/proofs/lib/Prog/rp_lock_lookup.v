(* Walk of reac-repacer's rp_lock_lookup (src/repace_conf.c:114-145 at 3ac1cf10) in fuzz_lock.plain, 0x13118.
   rp_lock_lookup_holds proves rp_lock_lookup_contract (rp_lock_lookup_c.v) from the libc contracts of strlen, memchr
   and bcmp (premises) and field_holds (field.v). The loop of repace_conf.c:122-143 (0x131f4) is walked by [loop], by
   induction on the text still to read, with one lemma per segment of its body (body_a .. body_f) and one per inlined
   digit loop (per_loop, lab_loop); each body lemma takes the rest of the iteration as a continuation (KT).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import StrFun LockSpec LockSpecRp.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import field_c field strlen_c memchr_c bcmp_c rp_lock_lookup_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
Ltac fix_ret := try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(** * Generic facts *)

Lemma bytes_at_sub : forall m A (bs : list byte) k n, bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma bytes_at_skip : forall m A (bs : list byte) k, bytes_at rsegs m A bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma rw8 : forall m A v, rw_cells rsegs m A [C8 v] -> rw_cells rsegs m A [CB 8 (le8 v)].
Proof.
  intros m A v [[W B] V]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply length_le8 | exact I].
  - cbn [cells_bytes cbytes] in *. exact B.
  - exact V.
Qed.

Lemma byte_lt : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H. cbn in H. lia. Qed.

(* the compiler's digit test: c - 58 <u -10 iff c is no digit *)
Lemma dig_test : forall b : byte, bv_ltu (Z_to_bv 64 (bv_unsigned b + -58)) (Z_to_bv 64 (-10)) = negb (isdig (bz b)).
Proof.
  intros b. pose proof (byte_lt b) as R.
  pose proof (brute256_ok (fun c => Bool.eqb (bv_ltu (Z_to_bv 64 (c + -58)) (Z_to_bv 64 (-10))) (negb (isdig c)))
                ltac:(vm_compute; reflexivity) (bz b) R) as H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma dig_land : forall b : byte, isdig (bz b) = true -> Z.land (bv_unsigned b) 15 = bz b - 48.
Proof.
  intros b D. pose proof (byte_lt b) as R.
  pose proof (brute256_ok (fun c => implb (isdig c) (Z.land c 15 =? c - 48)) ltac:(vm_compute; reflexivity) (bz b) R) as H.
  unfold bz in *. rewrite D in H. cbn in H. apply Z.eqb_eq in H. exact H.
Qed.

Lemma isdig_range : forall c, isdig c = true -> 48 <= c <= 57.
Proof. intros c H. unfold isdig in H. apply andb_true_iff in H as [A B]. apply Z.leb_le in A, B. lia. Qed.

(** * The digit loop of repace_conf.c:106-110 for the period field, at 0x132c4 *)
Section DIG1.
Variables (xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (d : list byte) (Q : machine_state -> Prop).
Hypothesis BD : bytes_at rsegs m A d.
Hypothesis HA : 0 <= A.
Hypothesis HAd : A + Z.of_nat (length d) < 2^64.
Hypothesis Hd18 : (length d <= 18)%nat.

Local Notation ST pc a0 a1 a2 a3 s6 :=
  (MS (mkR xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 a0 a1 a2 a3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (-10)) xs3 xs4 xs5 s6 xs7 xs8 xs9 xs10 (Z_to_bv 64 10) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma per_loop : forall k (i : nat) (v : Z) (a2 a3 : word) (v1 v6 : Z),
  (i + S k = length d)%nat -> dig_go d 0 = dig_go (skipn i d) v -> 0 <= v < 10 ^ Z.of_nat i ->
  v1 = A + Z.of_nat i -> v6 = Z.of_nat (S k) ->
  (forall (a1' a2' a3' s6' : word), evt rsegs Q (ST 0x132f0 (Z_to_bv 64 (dig_go d 0)) a1' a2' a3' s6')) ->
  evt rsegs Q (ST 0x132c4 (Z_to_bv 64 v) (Z_to_bv 64 v1) a2 a3 (Z_to_bv 64 v6)).
Proof.
  induction k as [|k IH]; intros i v a2 a3 v1 v6 Hk Hdg Hv -> -> K.
  all: assert (P18 : 10 ^ Z.of_nat i <= 100000000000000000)
         by (change 100000000000000000 with (10 ^ 17); apply Z.pow_le_mono_r; lia).
  all: destruct (nth_error d i) as [b|] eqn:Nb; [|apply nth_error_None in Nb; lia].
  all: pose proof (rdb m A d i b BD Nb) as R; pose proof (byte_lt b) as Rb.
  all: step; unfold zxb; step; step.
  all: rewrite dig_test; destruct (isdig (bz b)) eqn:D; cbn [negb]; cbv iota.
  all: [> | | | ].
  2, 4: step; replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (dig_go d 0))
          by (rewrite Hdg, (dig_go_skip_bad d i b v Nb D); reflexivity); apply K.
  all: pose proof (isdig_range _ D) as Dr.
  all: do 6 step.
  all: rewrite (unsigned_lit v), (unsigned_lit (bv_unsigned b)) by lia; rewrite (dig_land b D).
  - br false. step.
    replace (Z_to_bv 64 (v * 10 + (bz b - 48))) with (Z_to_bv 64 (dig_go d 0)); [apply K|].
    rewrite Hdg, (dig_go_skip_ok d i b v Nb D). replace (S i) with (length d) by lia. rewrite dig_go_end. reflexivity.
  - br true.
    eapply (IH (S i) (v * 10 + (bz b - 48)));
      [lia | rewrite Hdg; apply (dig_go_skip_ok d i b v Nb D) | apply dig_step_bound; assumption | lia | lia | exact K].
Qed.

End DIG1.

(** * The digit loop of repace_conf.c:106-110 for the rate-label field, at 0x1330c *)
Section DIG2.
Variables (xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa5 xa6 xa7 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (d : list byte) (Q : machine_state -> Prop).
Hypothesis BD : bytes_at rsegs m A d.
Hypothesis HA : 0 <= A.
Hypothesis HAd : A + Z.of_nat (length d) < 2^64.
Hypothesis Hd18 : (length d <= 18)%nat.

Local Notation ST pc a1 a2 a3 a4 s5 :=
  (MS (mkR xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 a1 a2 a3 a4 xa5 xa6 xa7
           (Z_to_bv 64 (-10)) xs3 xs4 s5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 10) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma lab_loop : forall k (i : nat) (v : Z) (a3 a4 : word) (v1 v5 : Z),
  (i + S k = length d)%nat -> dig_go d 0 = dig_go (skipn i d) v -> 0 <= v < 10 ^ Z.of_nat i ->
  v1 = A + Z.of_nat i -> v5 = Z.of_nat (S k) ->
  (forall (a1' a3' a4' s5' : word), evt rsegs Q (ST 0x13330 a1' (Z_to_bv 64 (dig_go d 0)) a3' a4' s5')) ->
  evt rsegs Q (ST 0x1330c (Z_to_bv 64 v1) (Z_to_bv 64 v) a3 a4 (Z_to_bv 64 v5)).
Proof.
  induction k as [|k IH]; intros i v a3 a4 v1 v5 Hk Hdg Hv -> -> K.
  all: assert (P18 : 10 ^ Z.of_nat i <= 100000000000000000)
         by (change 100000000000000000 with (10 ^ 17); apply Z.pow_le_mono_r; lia).
  all: destruct (nth_error d i) as [b|] eqn:Nb; [|apply nth_error_None in Nb; lia].
  all: pose proof (rdb m A d i b BD Nb) as R; pose proof (byte_lt b) as Rb.
  all: step; unfold zxb; step; step.
  all: rewrite dig_test; destruct (isdig (bz b)) eqn:D; cbn [negb]; cbv iota.
  all: [> | | | ].
  2, 4: step; step; replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (dig_go d 0))
          by (rewrite Hdg, (dig_go_skip_bad d i b v Nb D); reflexivity); apply K.
  all: pose proof (isdig_range _ D) as Dr.
  all: do 6 step.
  all: rewrite (unsigned_lit v), (unsigned_lit (bv_unsigned b)) by lia; rewrite (dig_land b D).
  - br false.
    replace (Z_to_bv 64 (v * 10 + (bz b - 48))) with (Z_to_bv 64 (dig_go d 0)); [apply K|].
    rewrite Hdg, (dig_go_skip_ok d i b v Nb D). replace (S i) with (length d) by lia. rewrite dig_go_end. reflexivity.
  - br true.
    eapply (IH (S i) (v * 10 + (bz b - 48)));
      [lia | rewrite Hdg; apply (dig_go_skip_ok d i b v Nb D) | apply dig_step_bound; assumption | lia | lia | exact K].
Qed.

End DIG2.

(** * The callees, with continuations *)

Lemma strlen_call : strlen_contract ->
  forall (xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
          xt3 xt4 xt5 xt6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z)
         (str slack : list byte) (Q : machine_state -> Prop),
  bv_unsigned xa0 = A -> bytes_at rsegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> mem_inv rsegs m ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR xra xsp xgp xtp t0' t1' t2' xs0 xs1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
                          xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                     F (ret_pc xra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                  F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs)).
Proof.
  intros SLc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 F fc m A str slack Q EA B NZ PAD MI K. subst A.
  eapply evt_cut; [eapply SLc; eassumption|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & _).
  apply K; assumption.
Qed.

Lemma memchr_call : memchr_contract ->
  forall (xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
          xt3 xt4 xt5 xt6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c n : Z)
         (buf : list byte) (Q : machine_state -> Prop),
  bv_unsigned xa0 = A -> bv_unsigned xa1 mod 256 = c -> bv_unsigned xa2 = n ->
  bytes_at rsegs m A buf -> memchr_ok A c n buf -> mem_inv rsegs m ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR xra xsp xgp xtp t0' t1' t2' xs0 xs1 (Z_to_bv 64 (memchr_res A c n buf)) a1' a2' a3' a4' a5' a6' a7'
                          xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                     F (ret_pc xra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                  F (Z_to_bv 64 MEMCHR) fc None m (seg_rom rsegs)).
Proof.
  intros MCc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 F fc m A c n buf Q EA EC EN B OK MI K. subst A c n.
  eapply evt_cut; [eapply MCc; eassumption|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & _).
  apply K; assumption.
Qed.

Lemma bcmp_call : bcmp_contract ->
  forall (xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
          xt3 xt4 xt5 xt6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A B : Z) (n : nat)
         (ls rs : list byte) (v : Z) (Q : machine_state -> Prop),
  bv_unsigned xa0 = A -> bv_unsigned xa1 = B -> Z.to_nat (bv_unsigned xa2) = n ->
  bytes_at rsegs m A ls -> bytes_at rsegs m B rs -> memcmp_model ls rs n = Some v -> mem_inv rsegs m ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR xra xsp xgp xtp t0' t1' t2' xs0 xs1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
                          xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                     F (ret_pc xra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                  F (Z_to_bv 64 BCMP) fc None m (seg_rom rsegs)).
Proof.
  intros BCc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 F fc m A B n ls rs v Q EA EB EN BA BB HV MI K. subst A B n.
  eapply evt_cut; [eapply BCc; eassumption|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & _).
  apply K; assumption.
Qed.

Lemma field_call :
  forall (xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
          xt3 xt4 xt5 xt6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pp ap s s' : Z)
         (l J : list byte) (Q : machine_state -> Prop),
  bv_unsigned xa0 = pp -> bv_unsigned xa1 = s + Z.of_nat (length l) -> bv_unsigned xa2 = ap ->
  0 <= s -> s + Z.of_nat (length l) < 2^64 -> bytes_at rsegs m s l ->
  rw_cells rsegs m pp [C8 (Z_to_bv 64 s')] -> rw_cells rsegs m ap [CB 8 J] -> pp + 8 <= ap \/ ap + 8 <= pp ->
  mem_inv rsegs m -> s' = s ->
  (forall (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
     munch [(pp, pp + 8); (ap, ap + 8)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     rw_cells rsegs m' pp [C8 (Z_to_bv 64 (s + Z.of_nat (fld_s l + fld_n l)))] ->
     rw_cells rsegs m' ap [C8 (Z_to_bv 64 (s + Z.of_nat (fld_s l)))] ->
     evt rsegs Q (MS (mkR xra xsp xgp xtp t0' xt1 xt2 xs0 xs1 (Z_to_bv 64 (Z.of_nat (fld_n l))) a1' a2' a3' a4' a5' a6' a7'
                          xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                     F (ret_pc xra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                  F (Z_to_bv 64 FIELD) fc None m (seg_rom rsegs)).
Proof.
  intros xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 F fc m pp ap s s' l J Q E0 E1 E2 Hs He BL CP CA DPA MI -> K.
  rewrite <- (Z_to_bv_bv_unsigned xa0), <- (Z_to_bv_bv_unsigned xa1), <- (Z_to_bv_bv_unsigned xa2), E0, E1, E2.
  eapply evt_cut; [eapply field_holds; eassumption|].
  intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MUc & WMc & MIc & C1 & C2).
  apply K; assumption.
Qed.

(** * Facts about one line's fields and the branch tests *)

Definition f_k2 (L : list byte) : nat := (fld_s L + fld_n L)%nat.
Definition f_s2 (L : list byte) : nat := (f_k2 L + fld_s (skipn (f_k2 L) L))%nat.
Definition f_l2 (L : list byte) : nat := fld_n (skipn (f_k2 L) L).
Definition f_k3 (L : list byte) : nat := (f_s2 L + f_l2 L)%nat.
Definition f_s3 (L : list byte) : nat := (f_k3 L + fld_s (skipn (f_k3 L) L))%nat.
Definition f_l3 (L : list byte) : nat := fld_n (skipn (f_k3 L) L).

Lemma fld_n_skip : forall L k, fld_n (skipn k L) = tok_run (skipn (k + fld_s (skipn k L)) L).
Proof. intros L k. unfold fld_n, fld_s. rewrite skipn_skipn. f_equal. f_equal. lia. Qed.

Lemma f_bounds : forall L, (fld_s L + fld_n L <= length L)%nat /\ (f_s2 L + f_l2 L <= length L)%nat /\
  (f_s3 L + f_l3 L <= length L)%nat.
Proof.
  intros L.
  assert (G : forall k, (k <= length L)%nat -> (k + fld_s (skipn k L) + fld_n (skipn k L) <= length L)%nat).
  { intros k Hk. unfold fld_s, fld_n. pose proof (sep_run_le (skipn k L)) as A.
    pose proof (tok_run_le (skipn (sep_run (skipn k L)) (skipn k L))) as B. rewrite length_skipn in A. rewrite !length_skipn in B. lia. }
  pose proof (G 0%nat ltac:(lia)) as G0. change (skipn 0 L) with L in G0. cbn [Nat.add] in G0.
  pose proof (G (f_k2 L) ltac:(unfold f_k2; lia)) as G2.
  pose proof (G (f_k3 L) ltac:(unfold f_k3, f_s2, f_l2; lia)) as G3.
  unfold f_s3, f_l3, f_k3 in *. unfold f_s2, f_l2 in *. unfold f_k2 in *. lia.
Qed.

Lemma line_val_f : forall p rate L, line_val p rate L =
  if is_some (find_byte 0 L) then None
  else if (fld_n L =? 0)%nat || (bz (nth (fld_s L) L (Z_to_bv 8 0)) =? 35) then None
  else if (15 <? fld_n L)%nat || negb (fld_n L =? length p)%nat
          || negb (match memcmp_model (slice L (fld_s L) (fld_n L)) p (fld_n L) with Some 0 => true | _ => false end)
  then None
  else
    let per := digits (slice L (f_s2 L) (f_l2 L)) in
    let lab := digits (slice L (f_s3 L) (f_l3 L)) in
    if (per <? 0) || negb (lab =? rate) then None
    else if (per <? std_period rate - std_period rate / 20) || (std_period rate + std_period rate / 20 <? per)
    then None
    else Some per.
Proof.
  intros p rate L. apply line_val_spec; try reflexivity.
  - unfold f_l2, f_s2. rewrite fld_n_skip. reflexivity.
  - unfold f_l3, f_s3. rewrite fld_n_skip. reflexivity.
Qed.

Lemma upd_ok : forall p rate L found, find_byte 0 L = None -> fld_n L <> 0%nat ->
  bz (nth (fld_s L) L (Z_to_bv 8 0)) <> 35 -> (fld_n L <= 15)%nat -> fld_n L = length p ->
  memcmp_model (slice L (fld_s L) (fld_n L)) p (fld_n L) = Some 0 ->
  upd p rate L found = tail_val rate (digits (slice L (f_s2 L) (f_l2 L))) (digits (slice L (f_s3 L) (f_l3 L))) found.
Proof.
  intros p rate L found FN N0 NH N15 NP MC. unfold upd, tail_val. rewrite line_val_f, FN, MC. cbn [is_some].
  replace ((fld_n L =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; exact N0).
  replace (bz (nth (fld_s L) L (Z_to_bv 8 0)) =? 35) with false by (symmetry; apply Z.eqb_neq; exact NH).
  replace ((15 <? fld_n L)%nat) with false by (symmetry; apply Nat.ltb_ge; exact N15).
  replace ((fld_n L =? length p)%nat) with true by (symmetry; apply Nat.eqb_eq; exact NP).
  cbn [orb negb].
  destruct ((digits (slice L (f_s2 L) (f_l2 L)) <? 0) || negb (digits (slice L (f_s3 L) (f_l3 L)) =? rate)); [reflexivity|].
  destruct ((digits (slice L (f_s2 L) (f_l2 L)) <? std_period rate - std_period rate / 20)
            || (std_period rate + std_period rate / 20 <? digits (slice L (f_s2 L) (f_l2 L)))); reflexivity.
Qed.

Lemma memchr_ok_all : forall A c buf, memchr_ok A c (Z.of_nat (length buf)) buf.
Proof. intros A c buf. unfold memchr_ok. rewrite Nat2Z.id, firstn_all. destruct (find_byte c buf); [left|]; lia. Qed.

Lemma memchr_res_all : forall A c buf, memchr_res A c (Z.of_nat (length buf)) buf =
  match find_byte c buf with Some i => A + Z.of_nat i | None => 0 end.
Proof. intros. unfold memchr_res. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

Lemma len_test : forall n, 0 <= n < 2^64 ->
  bv_ltu (Z_to_bv 64 (n + -19)) (Z_to_bv 64 (-18)) = negb ((1 <=? n) && (n <=? 18)).
Proof.
  intros n Hn. rewrite bv_ltu_Z, !unsigned_lit_wrap.
  assert (E18 : -18 mod 2^64 = 2^64 - 18) by reflexivity. rewrite E18.
  assert (EM : (n + -19) mod 2^64 = if n <? 19 then n + -19 + 2^64 else n + -19).
  { destruct (Z.ltb_spec n 19).
    - rewrite <- (Z.mod_add (n + -19) 1) by lia. apply Z.mod_small. lia.
    - apply Z.mod_small. lia. }
  rewrite EM.
  destruct (Z.ltb_spec n 19); destruct (Z.leb_spec 1 n); destruct (Z.leb_spec n 18); cbn [andb negb];
    first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Lemma ltz_lit : forall v, -1 <= v < 2^63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. rewrite bv_lts_zero_r, unsigned_lit_wrap.
  destruct (Z.ltb_spec v 0).
  - assert (v = -1) by lia. subst. reflexivity.
  - rewrite Z.mod_small by lia. apply Z.leb_gt. lia.
Qed.

Lemma eqb_lit : forall a b, -2^63 <= a < 2^63 -> 0 <= b < 2^63 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap, (Z.mod_small b) by lia.
  destruct (Z.ltb_spec a 0).
  - rewrite <- (Z.mod_add a 1) by lia. rewrite Z.mod_small by lia.
    replace (a + 1 * 2^64 =? b) with false by (symmetry; apply Z.eqb_neq; lia). symmetry; apply Z.eqb_neq; lia.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma slt_lit : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 ->
  v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = if a <? b then Z_to_bv 64 1 else Z_to_bv 64 0.
Proof.
  intros a b Ha Hb. unfold v_slt, c_lts. replace (bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b)) with (a <? b); [reflexivity|].
  unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (a <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rw_split1 : forall m A B c cs, rw_cells rsegs m A (c :: cs) -> B = A + Z.of_nat (csize c) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m B cs.
Proof.
  intros m A B c cs [[W Bt] V] ->. cbn [cells_wf cells_bytes cells_size] in *. destruct W as [W1 W2].
  pose proof (cbytes_length c W1) as Lc.
  apply bytes_at_app in Bt. destruct Bt as [B1 B2]. rewrite Lc in B2.
  destruct V as (V1 & V2 & V3). split; (split; [split|]).
  - cbn. tauto.
  - cbn [cells_bytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply V3. lia.
  - exact W2.
  - exact B2.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia.
    apply V3. lia.
Qed.

Lemma stk_rel : forall m lo A B cs, stk rsegs m lo A -> rw_cells rsegs m B cs -> B = A -> lo <= A ->
  stk rsegs m lo (B + Z.of_nat (cells_size cs)).
Proof. intros m lo A B cs S R -> H. apply stk_release; assumption. Qed.

Ltac tr MUc WMc :=
  lazymatch type of MUc with munch _ ?mo ?mn =>
    transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
    try lazymatch goal with H : mem_inv rsegs mo |- _ => clear H end;
    try clear mo
  end; fix_ret.

(* rewrite the innermost [bv_unsigned (Z_to_bv 64 e)] first *)
Ltac uns2 := repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
  lazymatch e with context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => rewrite (unsigned_lit e) by lia end end).

Lemma bytes_at_firstn : forall m A (bs : list byte) n, bytes_at rsegs m A bs -> (n <= length bs)%nat ->
  bytes_at rsegs m A (firstn n bs).
Proof.
  intros m A bs n H Hn. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Ltac brw v tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; tac]
  end.

(** * The walk *)
Section RP.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (tx pa rate lo : Z) (T P SL : list byte).
Hypothesis MCc : memchr_contract.
Hypothesis BCc : bcmp_contract.
Hypothesis Htx : 0 < tx.
Hypothesis HtxE : tx + Z.of_nat (length T) < 2^64.
Hypothesis Hpa : 0 < pa.
Hypothesis HPb : pa + Z.of_nat (length P + S (length SL)) <= 2^64.
Hypothesis Hlo : 0 <= lo.
Hypothesis HLO : lo + 176 <= bv_unsigned sp.
Hypothesis Rsp : bv_unsigned sp < 2^64.
Hypothesis DT : tx + Z.of_nat (length T) <= bv_unsigned sp - 176 \/ bv_unsigned sp <= tx.
Hypothesis DP : pa + Z.of_nat (length P + 1 + length SL) <= bv_unsigned sp - 176 \/ bv_unsigned sp <= pa.

Definition Post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lock_lookup T P rate)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 176, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

(* the frame cells that the loop does not change, and the memory facts the walk keeps *)
Definition FRAMEc (m : word -> option byte) : Prop :=
  (exists J0, rw_cells rsegs m (bv_unsigned sp + -176) [CB 8 J0]) /\
  rw_cells rsegs m (bv_unsigned sp + -168) [C8 (Z_to_bv 64 (std_period rate + std_period rate / 20))] /\
  rw_cells rsegs m (bv_unsigned sp + -160) [C8 (Z_to_bv 64 (std_period rate - std_period rate / 20))] /\
  rw_cells rsegs m (bv_unsigned sp + -152) [C8 (Z_to_bv 64 pa)] /\
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (bv_unsigned sp + -176) /\
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  bytes_at rsegs m tx T /\ bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL).

Lemma mkFRAMEc : forall m J0,
  rw_cells rsegs m (bv_unsigned sp + -176) [CB 8 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -168) [C8 (Z_to_bv 64 (std_period rate + std_period rate / 20))] ->
  rw_cells rsegs m (bv_unsigned sp + -160) [C8 (Z_to_bv 64 (std_period rate - std_period rate / 20))] ->
  rw_cells rsegs m (bv_unsigned sp + -152) [C8 (Z_to_bv 64 pa)] ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -176) ->
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) -> FRAMEc m.
Proof.
  intros m J0 R0 RH RL RP RS ST MU WM MI BT BP.
  exact (conj (ex_intro _ J0 R0) (conj RH (conj RL (conj RP (conj RS (conj ST (conj MU (conj WM (conj MI (conj BT BP)))))))))).
Qed.

Ltac unpack FC := destruct FC as ([J0 R0] & RH & RL & RP & RS & ST & MU & WM & MI & BT & BP).
Ltac pack := eapply mkFRAMEc; eassumption.

Local Notation LS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 mm :=
  (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp xt0 xt1 xt2 (Z_to_bv 64 rate) (Z_to_bv 64 35)
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (-10)) xs3 (Z_to_bv 64 (Z.of_nat (length P))) xs5 xs6 xs7 xs8 xs9
           (Z_to_bv 64 (tx + Z.of_nat (length T))) (Z_to_bv 64 10) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* what the loop body owes its caller at 0x132a4: the found cell holds fexp, s3 holds line' *)
Definition KT (line' fexp : Z) : Prop :=
  forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word)
         (m : word -> option byte) (f' : Z) (J5 J6 J7 J8 : list byte),
    f' = fexp -> FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 f')] ->
    rw_cells rsegs m (bv_unsigned sp + -136) [CB 8 J5] -> rw_cells rsegs m (bv_unsigned sp + -128) [CB 8 J6] ->
    rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
    evt rsegs Post (LS 0x132a4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 line') xs5 xs6 xs7 xs8 xs9
                       xt3 xt4 xt5 xt6 m).

Ltac slot8 := first [ eassumption | apply rw8; eassumption ].
Ltac goK K f := eapply K with (f' := f); [ | pack | eassumption | slot8 | slot8 | slot8 | slot8 ].

(** ** The return, at 0x1335c *)
Lemma lr_exit : forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (f : Z) (J5 J6 J7 J8 : list byte),
  f = lock_lookup T P rate ->
  FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 f)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [CB 8 J5] -> rw_cells rsegs m (bv_unsigned sp + -128) [CB 8 J6] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  evt rsegs Post (LS 0x1335c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof.
  intros xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m f J5 J6 J7 J8 ->
    FC RF R5 R6 R7 R8.
  unpack FC.
  assert (STf : stk rsegs m lo (bv_unsigned sp)).
  { eapply stk_rel in ST; [| exact R0 | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact RH | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact RL | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact RP | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact RF | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact R5 | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact R6 | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact R7 | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact R8 | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    eapply stk_rel in ST; [| exact RS | lia | lia]. cbn [cells_size csize Nat.add] in ST.
    replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in ST by lia. exact ST. }
  do 16 step.
  apply evt_done. unfold Post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact STf.
Qed.

(** ** The early return of repace_conf.c:117-118 (and of n = 0), at 0x13358 *)
Lemma early_exit : forall (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                           xt3 xt4 xt5 xt6 : word) (m : word -> option byte) (J : list byte),
  lock_lookup T P rate = 0 ->
  rw_cells rsegs m (bv_unsigned sp + -176)
    [CB 72 J; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -176) -> munch [(bv_unsigned sp - 176, bv_unsigned sp)] m0 m -> wmono rsegs m0 m ->
  mem_inv rsegs m ->
  evt rsegs Post (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x13358) fc None m (seg_rom rsegs)).
Proof.
  intros xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m J
    E FR ST MU WM MI.
  do 17 step.
  lazymatch goal with FR' : rw_cells rsegs ?mm (bv_unsigned sp + -176) _ |- _ =>
    pose proof (stk_rel _ _ _ _ _ ST FR' eq_refl ltac:(lia)) as STf end.
  cbn [cells_size csize Nat.add] in STf. replace (bv_unsigned sp + -176 + Z.of_nat 176) with (bv_unsigned sp) in STf by lia.
  apply evt_done. unfold Post. rewrite E. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. exact STf.
Qed.

(** ** The tests of repace_conf.c:138-142, at 0x13330: per in a0, lab in a2 *)
Lemma body_f : forall (line' found fexp dper dlab : Z)
    (xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (m : word -> option byte)
    (J5 J6 J7 J8 : list byte),
  rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  -1 <= dper < 1000000000000000000 -> -1 <= dlab < 1000000000000000000 -> fexp = tail_val rate dper dlab found ->
  FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 found)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [CB 8 J5] -> rw_cells rsegs m (bv_unsigned sp + -128) [CB 8 J6] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  KT line' fexp ->
  evt rsegs Post (LS 0x13330 xra xt0 xt1 xt2 (Z_to_bv 64 dper) xa1 (Z_to_bv 64 dlab) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 line')
                     xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof.
  intros line' found fexp dper dlab xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m
    J5 J6 J7 J8 HR Hp Hl -> FC RF R5 R6 R7 R8 K.
  pose proof (std_period_pos rate HR) as Hstd.
  assert (Hr : 0 <= rate < 2^63) by (destruct HR as [->|[->| ->]]; lia).
  assert (H20 : 0 <= std_period rate / 20 <= std_period rate) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unpack FC.
  step. rewrite ltz_lit by lia.
  destruct (Z.ltb_spec dper 0) as [Hn|Hn]; cbv iota.
  { goK K found. unfold tail_val. replace (dper <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec dlab rate) as [Heq|Hne]; cbn [negb]; cbv iota.
  2: { goK K found. unfold tail_val. replace (dper <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
       replace (dlab =? rate) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  do 6 step.
  change (Sem.alu64 Instr.ALU_SLT (Z_to_bv 64 (std_period rate + std_period rate / 20)) (Z_to_bv 64 dper))
    with (v_slt (Z_to_bv 64 (std_period rate + std_period rate / 20)) (Z_to_bv 64 dper)).
  rewrite (slt_lit dper (std_period rate - std_period rate / 20)), (slt_lit (std_period rate + std_period rate / 20) dper)
    by lia.
  assert (TV : tail_val rate dper dlab found =
               if (dper <? std_period rate - std_period rate / 20) || (std_period rate + std_period rate / 20 <? dper)
               then found else dper).
  { unfold tail_val. replace (dper <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (dlab =? rate) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
  destruct (dper <? std_period rate - std_period rate / 20) eqn:C1;
    destruct (std_period rate + std_period rate / 20 <? dper) eqn:C2.
  1-3: brw true ltac:(vm_compute; reflexivity); goK K found; rewrite TV; rewrite ?C1, ?C2; reflexivity.
  brw false ltac:(vm_compute; reflexivity).
  step. step. goK K dper. rewrite TV; rewrite ?C1, ?C2; reflexivity.
Qed.

(** ** The rate-label field, repace_conf.c:137, at 0x132f0: per in a0 *)
Lemma body_e : forall (line line' found fexp vl3 vlab dper : Z) (L : list byte)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (m : word -> option byte)
    (J6 J7 J8 : list byte),
  rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  tx <= line -> line + Z.of_nat (length L) <= tx + Z.of_nat (length T) -> bytes_at rsegs m line L ->
  vl3 = Z.of_nat (f_l3 L) -> vlab = line + Z.of_nat (f_s3 L) -> -1 <= dper < 1000000000000000000 ->
  fexp = tail_val rate dper (digits (slice L (f_s3 L) (f_l3 L))) found ->
  FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 found)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [C8 (Z_to_bv 64 vlab)] -> rw_cells rsegs m (bv_unsigned sp + -128) [CB 8 J6] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  KT line' fexp ->
  evt rsegs Post (LS 0x132f0 xra xt0 xt1 xt2 (Z_to_bv 64 dper) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 line') (Z_to_bv 64 vl3)
                     xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof.
  intros line line' found fexp vl3 vlab dper L xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m
    J6 J7 J8 HR Hl HLL BL -> -> Hp -> FC RF R5 R6 R7 R8 K.
  destruct (f_bounds L) as (FB1 & FB2 & FB3).
  pose proof (bytes_at_bound _ _ _ _ BL) as BLb.
  pose proof (digits_range (slice L (f_s3 L) (f_l3 L))) as DR. change (10 ^ 18) with 1000000000000000000 in DR.
  unpack FC.
  step. step. step.
  rewrite len_test by lia.
  destruct ((1 <=? Z.of_nat (f_l3 L)) && (Z.of_nat (f_l3 L) <=? 18)) eqn:LR; cbn [negb]; cbv iota.
  - apply andb_true_iff in LR as [LR1 LR2]. apply Z.leb_le in LR1, LR2.
    step. step.
    eapply lab_loop with (A := line + Z.of_nat (f_s3 L)) (d := slice L (f_s3 L) (f_l3 L)) (k := (f_l3 L - 1)%nat)
                         (i := 0%nat) (v := 0).
    all: lazymatch goal with
         | |- bytes_at _ _ _ _ => unfold slice; apply bytes_at_sub; [exact BL | lia]
         | |- forall _, _ => idtac
         | |- dig_go _ _ = dig_go _ _ => reflexivity
         | |- _ <= _ < 10 ^ _ => cbn; lia
         | _ => rewrite ?slice_length by lia; lia
         end.
    intros a1' a3' a4' s5'.
    assert (DO : digits (slice L (f_s3 L) (f_l3 L)) = dig_go (slice L (f_s3 L) (f_l3 L)) 0)
      by (apply digits_ok; rewrite slice_length by lia; lia).
    eapply body_f with (dper := dper) (dlab := dig_go (slice L (f_s3 L) (f_l3 L)) 0) (found := found)
                       (fexp := tail_val rate dper (digits (slice L (f_s3 L) (f_l3 L))) found);
      [ exact HR | exact Hp | rewrite <- DO; exact DR | rewrite DO; reflexivity | pack | eassumption
      | slot8 | slot8 | slot8 | slot8 | exact K ].
  - assert (LRn : (f_l3 L = 0 \/ 18 < f_l3 L)%nat)
      by (apply andb_false_iff in LR; destruct LR as [LR|LR]; apply Z.leb_gt in LR; lia).
    step. step.
    eapply body_f with (dper := dper) (dlab := -1) (found := found)
                       (fexp := tail_val rate dper (digits (slice L (f_s3 L) (f_l3 L))) found);
      [ exact HR | exact Hp | lia | rewrite digits_bad; [reflexivity | rewrite slice_length by lia; lia] | pack
      | eassumption | slot8 | slot8 | slot8 | slot8 | exact K ].
Qed.

(** ** The period field, repace_conf.c:137, at 0x132ac *)
Lemma body_d : forall (line line' found fexp vl2 vl3 vper vlab : Z) (L : list byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (m : word -> option byte)
    (J7 J8 : list byte),
  rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  tx <= line -> line + Z.of_nat (length L) <= tx + Z.of_nat (length T) -> bytes_at rsegs m line L ->
  vl2 = Z.of_nat (f_l2 L) -> vl3 = Z.of_nat (f_l3 L) -> vper = line + Z.of_nat (f_s2 L) ->
  vlab = line + Z.of_nat (f_s3 L) ->
  fexp = tail_val rate (digits (slice L (f_s2 L) (f_l2 L))) (digits (slice L (f_s3 L) (f_l3 L))) found ->
  FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 found)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [C8 (Z_to_bv 64 vlab)] ->
  rw_cells rsegs m (bv_unsigned sp + -128) [C8 (Z_to_bv 64 vper)] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  KT line' fexp ->
  evt rsegs Post (LS 0x132ac xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 line') (Z_to_bv 64 vl3)
                     (Z_to_bv 64 vl2) xs7 xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof.
  intros line line' found fexp vl2 vl3 vper vlab L xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs8 xs9
    xt3 xt4 xt5 xt6 m J7 J8 HR Hl HLL BL -> -> -> -> -> FC RF R5 R6 R7 R8 K.
  destruct (f_bounds L) as (FB1 & FB2 & FB3).
  pose proof (bytes_at_bound _ _ _ _ BL) as BLb.
  pose proof (digits_range (slice L (f_s2 L) (f_l2 L))) as DR. change (10 ^ 18) with 1000000000000000000 in DR.
  unpack FC.
  step. step. step. step.
  rewrite len_test by lia.
  destruct ((1 <=? Z.of_nat (f_l2 L)) && (Z.of_nat (f_l2 L) <=? 18)) eqn:LR; cbn [negb]; cbv iota.
  - apply andb_true_iff in LR as [LR1 LR2]. apply Z.leb_le in LR1, LR2.
    step. step.
    eapply per_loop with (A := line + Z.of_nat (f_s2 L)) (d := slice L (f_s2 L) (f_l2 L)) (k := (f_l2 L - 1)%nat)
                         (i := 0%nat) (v := 0).
    all: lazymatch goal with
         | |- bytes_at _ _ _ _ => unfold slice; apply bytes_at_sub; [exact BL | lia]
         | |- forall _, _ => idtac
         | |- dig_go _ _ = dig_go _ _ => reflexivity
         | |- _ <= _ < 10 ^ _ => cbn; lia
         | _ => rewrite ?slice_length by lia; lia
         end.
    intros a1' a2' a3' s6'.
    assert (DO : digits (slice L (f_s2 L) (f_l2 L)) = dig_go (slice L (f_s2 L) (f_l2 L)) 0)
      by (apply digits_ok; rewrite slice_length by lia; lia).
    eapply body_e with (line := line) (L := L) (dper := dig_go (slice L (f_s2 L) (f_l2 L)) 0) (found := found)
      (fexp := tail_val rate (digits (slice L (f_s2 L) (f_l2 L))) (digits (slice L (f_s3 L) (f_l3 L))) found);
      [ exact HR | exact Hl | exact HLL | exact BL | reflexivity | reflexivity | rewrite <- DO; exact DR
      | rewrite DO; reflexivity | pack | eassumption | eassumption | slot8 | slot8 | slot8 | exact K ].
  - assert (LRn : (f_l2 L = 0 \/ 18 < f_l2 L)%nat)
      by (apply andb_false_iff in LR; destruct LR as [LR|LR]; apply Z.leb_gt in LR; lia).
    eapply body_e with (line := line) (L := L) (dper := -1) (found := found)
      (fexp := tail_val rate (digits (slice L (f_s2 L) (f_l2 L))) (digits (slice L (f_s3 L) (f_l3 L))) found);
      [ exact HR | exact Hl | exact HLL | exact BL | reflexivity | reflexivity | lia
      | rewrite digits_bad; [reflexivity | rewrite slice_length by lia; lia] | pack | eassumption | eassumption
      | slot8 | slot8 | slot8 | exact K ].
Qed.

(** ** The name tests of repace_conf.c:131-136, at 0x13274 *)
Lemma body_c : forall (line line' found vl1 vl2 vl3 vnul vname vper vlab : Z) (L : list byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 : word) (m : word -> option byte)
    (J8 : list byte),
  rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  tx <= line -> line + Z.of_nat (length L) <= tx + Z.of_nat (length T) -> bytes_at rsegs m line L ->
  vl1 = Z.of_nat (fld_n L) -> vl2 = Z.of_nat (f_l2 L) -> vl3 = Z.of_nat (f_l3 L) ->
  vnul = memchr_res line 0 (Z.of_nat (length L)) L ->
  vname = line + Z.of_nat (fld_s L) -> vper = line + Z.of_nat (f_s2 L) -> vlab = line + Z.of_nat (f_s3 L) ->
  FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 found)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [C8 (Z_to_bv 64 vlab)] ->
  rw_cells rsegs m (bv_unsigned sp + -128) [C8 (Z_to_bv 64 vper)] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [C8 (Z_to_bv 64 vname)] ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  KT line' (upd P rate L found) ->
  evt rsegs Post (LS 0x13274 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 line') (Z_to_bv 64 vl3)
                     (Z_to_bv 64 vl2) xs7 (Z_to_bv 64 vl1) (Z_to_bv 64 vnul) xt3 xt4 xt5 xt6 m).
Proof.
  intros line line' found vl1 vl2 vl3 vnul vname vper vlab L xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7
    xt3 xt4 xt5 xt6 m J8 HR Hl HLL BL -> -> -> -> -> -> -> FC RF R5 R6 R7 R8 K.
  destruct (f_bounds L) as (FB1 & FB2 & FB3).
  pose proof (bytes_at_bound _ _ _ _ BL) as BLb.
  rewrite memchr_res_all.
  unpack FC.
  step.
  destruct (find_byte 0 L) as [i|] eqn:FN.
  { pose proof (find_byte_Some _ _ _ FN) as (Hi & _).
    br true. goK K found. unfold upd. rewrite line_val_f, FN. reflexivity. }
  br false.
  step.
  destruct (Nat.eq_dec (fld_n L) 0) as [E1|E1].
  { br true. goK K found. unfold upd. rewrite line_val_f, FN, E1. reflexivity. }
  br false.
  destruct (nth_error L (fld_s L)) as [b|] eqn:Nb; [|apply nth_error_None in Nb; lia].
  pose proof (rdb m line L (fld_s L) b BL Nb) as RB. pose proof (byte_lt b) as Bb.
  assert (NT : nth (fld_s L) L (Z_to_bv 8 0) = b) by (apply nth_error_nth; exact Nb).
  step. step. unfold zxb. step.
  destruct (Z.eq_dec (bv_unsigned b) 35) as [EH|EH].
  { br true. goK K found. unfold upd. rewrite line_val_f, FN, NT. unfold bz. rewrite EH.
    replace ((fld_n L =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; exact E1). reflexivity. }
  br false.
  step. step.
  destruct (Nat.lt_ge_cases 15 (fld_n L)) as [E15|E15].
  { br true. goK K found. unfold upd. rewrite line_val_f, FN, NT. unfold bz.
    replace ((fld_n L =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; exact E1).
    replace (bv_unsigned b =? 35) with false by (symmetry; apply Z.eqb_neq; exact EH).
    replace ((15 <? fld_n L)%nat) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
  br false.
  step.
  destruct (Nat.eq_dec (fld_n L) (length P)) as [EP|EP].
  2: { br true. goK K found. unfold upd. rewrite line_val_f, FN, NT. unfold bz.
       replace ((fld_n L =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; exact E1).
       replace (bv_unsigned b =? 35) with false by (symmetry; apply Z.eqb_neq; exact EH).
       replace ((15 <? fld_n L)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
       replace ((fld_n L =? length P)%nat) with false by (symmetry; apply Nat.eqb_neq; exact EP). reflexivity. }
  br false.
  step. step. step.
  destruct (memcmp_model_total (slice L (fld_s L) (fld_n L)) P (fld_n L)) as [v HV];
    [rewrite slice_length by lia; lia | lia |].
  pose proof (memcmp_model_range _ _ _ _ HV) as VR.
  pose proof BP as BPP. apply bytes_at_app in BPP. destruct BPP as [BPP _].
  eapply (bcmp_call BCc) with (A := line + Z.of_nat (fld_s L)) (B := pa) (n := fld_n L)
                              (ls := slice L (fld_s L) (fld_n L)) (rs := P) (v := v);
    [ uns; reflexivity | uns; reflexivity | uns; lia | unfold slice; apply bytes_at_sub; [exact BL | lia]
    | exact BPP | exact HV | exact MI | ].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 MUc WMc MIc.
  tr MUc WMc. rename MIc into MI.
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  - subst v.
    eapply body_d with (line := line) (L := L) (found := found) (fexp := upd P rate L found);
      [ exact HR | exact Hl | exact HLL | exact BL | reflexivity | reflexivity | reflexivity | reflexivity
      | apply upd_ok; [exact FN | exact E1 | rewrite NT; exact EH | exact E15 | exact EP | exact HV]
      | pack | eassumption | eassumption | eassumption | slot8 | slot8 | exact K ].
  - goK K found. unfold upd. rewrite line_val_f, FN, NT, HV. unfold bz.
    replace ((fld_n L =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; exact E1).
    replace (bv_unsigned b =? 35) with false by (symmetry; apply Z.eqb_neq; exact EH).
    replace ((15 <? fld_n L)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace ((fld_n L =? length P)%nat) with true by (symmetry; apply Nat.eqb_eq; exact EP).
    destruct v; [contradiction | reflexivity | reflexivity].
Qed.

(** ** The three [field] calls of repace_conf.c:126-130, at 0x13214 *)
Lemma body_b : forall (line vend s7v line' found : Z) (L : list byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs9 xt3 xt4 xt5 xt6 : word) (m : word -> option byte)
    (J5 J6 J7 J8 : list byte),
  rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  tx <= line -> vend = line + Z.of_nat (length L) -> vend <= tx + Z.of_nat (length T) ->
  (s7v = 0 /\ line' = tx + Z.of_nat (length T)) \/ (s7v = vend /\ line' = vend + 1) ->
  bytes_at rsegs m line L -> FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 found)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [CB 8 J5] -> rw_cells rsegs m (bv_unsigned sp + -128) [CB 8 J6] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  KT line' (upd P rate L found) ->
  evt rsegs Post (LS 0x13214 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 line) (Z_to_bv 64 vend) xs6
                     (Z_to_bv 64 s7v) xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof.
  intros line vend s7v line' found L xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs9 xt3 xt4 xt5 xt6 m
    J5 J6 J7 J8 HR Hl -> HE E7 BL FC RF R5 R6 R7 R8 K.
  destruct (f_bounds L) as (FB1 & FB2 & FB3).
  pose proof (bytes_at_bound _ _ _ _ BL) as BLb.
  unpack FC.
  step. step. step. step. step.
  eapply (memchr_call MCc) with (A := line) (c := 0) (n := Z.of_nat (length L)) (buf := L);
    [ uns2; reflexivity | vm_compute; reflexivity | uns2; lia | exact BL | apply memchr_ok_all | eassumption | ].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mA MUc WMc MIc.
  tr MUc WMc. rename MIc into MI.
  step. step. step. step. step.
  eapply field_call with (pp := bv_unsigned sp + -112) (ap := bv_unsigned sp + -120) (s := line) (l := L);
    [ uns2; reflexivity | uns2; reflexivity | uns2; reflexivity | lia | lia | exact BL | eassumption | eassumption
    | lia | eassumption | reflexivity | ].
  clear t0' a1' a2' a3' a4' a5' a6' a7'.
  intros t0' a1' a2' a3' a4' a5' a6' a7' mB MUc WMc MIc C1 C2.
  tr MUc WMc. rename MIc into MI. rename C1 into R8. rename C2 into R7.
  step. step. step. step. step.
  eapply field_call with (pp := bv_unsigned sp + -112) (ap := bv_unsigned sp + -128) (s := line + Z.of_nat (f_k2 L))
                         (l := skipn (f_k2 L) L);
    [ uns2; reflexivity | uns2; rewrite length_skipn; unfold f_k2; lia | uns2; reflexivity | lia
    | rewrite length_skipn; unfold f_k2; lia | apply bytes_at_skip; [exact BL | unfold f_k2; lia] | eassumption
    | eassumption | lia | eassumption | unfold f_k2; reflexivity | ].
  clear t0' a1' a2' a3' a4' a5' a6' a7'.
  intros t0' a1' a2' a3' a4' a5' a6' a7' mC MUc WMc MIc C1 C2.
  tr MUc WMc. rename MIc into MI. rename C1 into R8. rename C2 into R6.
  step. step. step. step. step.
  eapply field_call with (pp := bv_unsigned sp + -112) (ap := bv_unsigned sp + -136) (s := line + Z.of_nat (f_k3 L))
                         (l := skipn (f_k3 L) L);
    [ uns2; reflexivity | uns2; rewrite length_skipn; unfold f_k3; lia | uns2; reflexivity | lia
    | rewrite length_skipn; unfold f_k3; lia | apply bytes_at_skip; [exact BL | unfold f_k3; lia] | eassumption
    | eassumption | lia | eassumption | unfold f_k3, f_s2, f_l2; lia | ].
  clear t0' a1' a2' a3' a4' a5' a6' a7'.
  intros t0' a1' a2' a3' a4' a5' a6' a7' mD MUc WMc MIc C1 C2.
  tr MUc WMc. rename MIc into MI. rename C1 into R8. rename C2 into R5.
  step. step. step.
  destruct E7 as [[-> ->] | [-> ->]].
  - br true.
    eapply body_c with (line := line) (L := L) (found := found) (vname := line + Z.of_nat (fld_s L))
      (vper := line + Z.of_nat (f_k2 L) + Z.of_nat (fld_s (skipn (f_k2 L) L)))
      (vlab := line + Z.of_nat (f_k3 L) + Z.of_nat (fld_s (skipn (f_k3 L) L)));
      [ exact HR | exact Hl | lia | exact BL | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | unfold f_s2; lia | unfold f_s3; lia | pack | eassumption | eassumption | eassumption | eassumption | slot8
      | exact K ].
  - br false. step.
    eapply body_c with (line := line) (L := L) (found := found) (vname := line + Z.of_nat (fld_s L))
      (vper := line + Z.of_nat (f_k2 L) + Z.of_nat (fld_s (skipn (f_k2 L) L)))
      (vlab := line + Z.of_nat (f_k3 L) + Z.of_nat (fld_s (skipn (f_k3 L) L)));
      [ exact HR | exact Hl | lia | exact BL | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | unfold f_s2; lia | unfold f_s3; lia | pack | eassumption | eassumption | eassumption | eassumption | slot8
      | exact K ].
Qed.

(** ** The end of the line, repace_conf.c:124, at 0x13204: memchr's result in a0 *)
Lemma body_a : forall (line s7v line' found : Z) (L : list byte)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (m : word -> option byte)
    (J5 J6 J7 J8 : list byte),
  rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  tx <= line -> line + Z.of_nat (length L) <= tx + Z.of_nat (length T) ->
  (s7v = 0 /\ line + Z.of_nat (length L) = tx + Z.of_nat (length T) /\ line' = tx + Z.of_nat (length T)) \/
  (s7v = line + Z.of_nat (length L) /\ line' = s7v + 1) ->
  bytes_at rsegs m line L -> FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 found)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [CB 8 J5] -> rw_cells rsegs m (bv_unsigned sp + -128) [CB 8 J6] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  KT line' (upd P rate L found) ->
  evt rsegs Post (LS 0x13204 xra xt0 xt1 xt2 (Z_to_bv 64 s7v) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 line) xs5 xs6 xs7
                     xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof.
  intros line s7v line' found L xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m
    J5 J6 J7 J8 HR Hl HLL E7 BL FC RF R5 R6 R7 R8 K.
  pose proof (bytes_at_bound _ _ _ _ BL) as BLb.
  step. step. step.
  destruct E7 as [(-> & EL & ->) | (-> & ->)].
  - br true.
    eapply body_b with (line := line) (L := L) (vend := tx + Z.of_nat (length T)) (s7v := 0)
                       (line' := tx + Z.of_nat (length T)) (found := found);
      [ exact HR | exact Hl | lia | lia | left; split; reflexivity | exact BL | exact FC | exact RF | exact R5
      | exact R6 | exact R7 | exact R8 | exact K ].
  - br false. step.
    eapply body_b with (line := line) (L := L) (vend := line + Z.of_nat (length L))
                       (s7v := line + Z.of_nat (length L)) (line' := line + Z.of_nat (length L) + 1) (found := found);
      [ exact HR | exact Hl | reflexivity | lia | right; split; reflexivity | exact BL | exact FC | exact RF
      | exact R5 | exact R6 | exact R7 | exact R8 | exact K ].
Qed.

(** ** The loop of repace_conf.c:122-143, at 0x131f4: the text from offset k on is still to read *)
Lemma loop : forall (n k : nat) (found : Z)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (J5 J6 J7 J8 : list byte),
  rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  (length T - k = n)%nat -> (k < length T)%nat ->
  lock_lookup T P rate = lk (length (skipn k T)) P rate (skipn k T) found ->
  FRAMEc m -> rw_cells rsegs m (bv_unsigned sp + -144) [C8 (Z_to_bv 64 found)] ->
  rw_cells rsegs m (bv_unsigned sp + -136) [CB 8 J5] -> rw_cells rsegs m (bv_unsigned sp + -128) [CB 8 J6] ->
  rw_cells rsegs m (bv_unsigned sp + -120) [CB 8 J7] -> rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 J8] ->
  evt rsegs Post (LS 0x131f4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (tx + Z.of_nat k))
                     xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros k found xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m J5 J6 J7 J8
    HR Hn Hk RES FC RF R5 R6 R7 R8.
  set (t := skipn k T) in *.
  assert (Lt : length t = (length T - k)%nat) by apply length_skipn.
  assert (NE : t <> []) by (intros E; rewrite E in Lt; cbn in Lt; lia).
  unpack FC.
  assert (BTt : bytes_at rsegs m (tx + Z.of_nat k) t) by (apply bytes_at_skip; [exact BT | lia]).
  step. step. step. step.
  eapply (memchr_call MCc) with (A := tx + Z.of_nat k) (c := 10) (n := Z.of_nat (length t)) (buf := t);
    [ uns2; reflexivity | vm_compute; reflexivity | uns2; lia | exact BTt | apply memchr_ok_all | exact MI | ].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mA MUc WMc MIc.
  tr MUc WMc. rename MIc into MI.
  rewrite memchr_res_all.
  destruct (find_byte 10 t) as [j|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hj & _).
    pose proof (bytes_at_firstn _ _ _ j BTt ltac:(lia)) as BL.
    eapply body_a with (line := tx + Z.of_nat k) (L := firstn j t) (line' := tx + Z.of_nat k + Z.of_nat j + 1)
                       (found := found);
      [ exact HR | lia | rewrite length_firstn; lia | right; split; [rewrite length_firstn; lia | reflexivity]
      | exact BL | pack | exact RF | exact R5 | exact R6 | exact R7 | exact R8 | ].
    intros xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs5' xs6' xs7' xs8' xs9' xt3' xt4' xt5' xt6'
      mB f' J5' J6' J7' J8' Hf FC2 RF2 R5' R6' R7' R8'.
    rewrite (lk_some P rate t found j NE FB) in RES. unfold t in RES. rewrite skipn_skipn in RES.
    step.
    destruct (Nat.lt_ge_cases (k + j + 1) (length T)) as [Lk|Lk].
    + br true.
      replace (Z_to_bv 64 (tx + Z.of_nat k + Z.of_nat j + 1)) with (Z_to_bv 64 (tx + Z.of_nat (k + j + 1)))
        by (f_equal; lia).
      eapply (IH (length T - (k + j + 1))%nat) with (k := (k + j + 1)%nat) (found := f');
        [ lia | exact HR | reflexivity | exact Lk | | exact FC2 | exact RF2 | exact R5' | exact R6' | exact R7'
        | exact R8' ].
      rewrite RES, Hf. replace (S j + k)%nat with (k + j + 1)%nat by lia. reflexivity.
    + br false. step.
      eapply lr_exit with (f := f'); [ | exact FC2 | exact RF2 | exact R5' | exact R6' | exact R7' | exact R8' ].
      rewrite RES, Hf. rewrite skipn_all2 by lia. rewrite lk_nil. reflexivity.
  - eapply body_a with (line := tx + Z.of_nat k) (L := t) (line' := tx + Z.of_nat (length T)) (found := found);
      [ exact HR | lia | lia | left; split; [reflexivity | split; [lia | reflexivity]]
      | exact BTt | pack | exact RF | exact R5 | exact R6 | exact R7 | exact R8 | ].
    intros xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs5' xs6' xs7' xs8' xs9' xt3' xt4' xt5' xt6'
      mB f' J5' J6' J7' J8' Hf FC2 RF2 R5' R6' R7' R8'.
    step. br false. step.
    eapply lr_exit with (f := f'); [ | exact FC2 | exact RF2 | exact R5' | exact R6' | exact R7' | exact R8' ].
    rewrite Hf, RES, (lk_none P rate t found NE FB). reflexivity.
Qed.

End RP.

(** * The theorem *)

Ltac pack' := eapply mkFRAMEc; eassumption.

(* from 0x131a4, once s2 holds the standard period: the n > 65536 test, strlen, the n = 0 test, the setup, the loop *)
Ltac rp_common SLc NZ PAD Er Es T P SL rate pa tx :=
  step; step;
  destruct (Z.ltb_spec 65536 (Z.of_nat (length T))) as [Lbig|Lsmall];
  [ br true; eapply early_exit; try eassumption;
    unfold lock_lookup; rewrite Es;
    replace (65536 <? Z.of_nat (length T)) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
  | br false; step; step;
    eapply (strlen_call SLc) with (A := pa) (str := P) (slack := SL);
    [ uns2; reflexivity | eassumption | exact NZ | exact PAD | eassumption | ];
    let mA := fresh "mA" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? mA MUc WMc MIc;
    tr MUc WMc;
    step;
    destruct (Nat.eq_dec (length T) 0) as [L0|L0];
    [ br true; eapply early_exit; try eassumption;
      unfold lock_lookup; rewrite L0; destruct ((std_period rate =? 0) || (65536 <? Z.of_nat 0)); reflexivity
    | br false;
      do 15 step;
      lazymatch goal with FR : rw_cells rsegs ?mm (bv_unsigned ?sp + -176) _ |- _ =>
        destruct (rw_split1 _ _ (bv_unsigned sp + -168) _ _ FR ltac:(cbn; lia)) as [R0 FR1]; clear FR;
        destruct (rw_split1 _ _ (bv_unsigned sp + -160) _ _ FR1 ltac:(cbn; lia)) as [RH FR2]; clear FR1;
        destruct (rw_split1 _ _ (bv_unsigned sp + -152) _ _ FR2 ltac:(cbn; lia)) as [RL FR3]; clear FR2;
        destruct (rw_split1 _ _ (bv_unsigned sp + -144) _ _ FR3 ltac:(cbn; lia)) as [RP FR4]; clear FR3;
        destruct (rw_split1 _ _ (bv_unsigned sp + -136) _ _ FR4 ltac:(cbn; lia)) as [RF FR5]; clear FR4;
        destruct (rw_split1 _ _ (bv_unsigned sp + -104) _ _ FR5 ltac:(cbn; lia)) as [R32 RS]; clear FR5;
        apply (rw_cells_split_CB rsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in R32; [|reflexivity];
        cbn [app mk_CB_cells] in R32;
        destruct (rw_split1 _ _ (bv_unsigned sp + -128) _ _ R32 ltac:(cbn; lia)) as [R5 R33]; clear R32;
        destruct (rw_split1 _ _ (bv_unsigned sp + -120) _ _ R33 ltac:(cbn; lia)) as [R6 R34]; clear R33;
        destruct (rw_split1 _ _ (bv_unsigned sp + -112) _ _ R34 ltac:(cbn; lia)) as [R7 R8]; clear R34;
        lazymatch type of RH with rw_cells _ _ _ [C8 (Z_to_bv 64 ?v)] =>
          replace (Z_to_bv 64 v) with (Z_to_bv 64 (std_period rate + std_period rate / 20)) in RH
            by (rewrite Er; reflexivity) end;
        lazymatch type of RL with rw_cells _ _ _ [C8 (Z_to_bv 64 ?v)] =>
          replace (Z_to_bv 64 v) with (Z_to_bv 64 (std_period rate - std_period rate / 20)) in RL
            by (rewrite Er; reflexivity) end;
        replace (Z_to_bv 64 tx) with (Z_to_bv 64 (tx + Z.of_nat 0)) by (f_equal; lia);
        assert (HR : rate = 44100 \/ rate = 48000 \/ rate = 96000) by lia;
        eapply loop with (n := (length T - 0)%nat) (k := 0%nat) (found := 0); try eassumption;
        first [ pack'
              | unfold lock_lookup; rewrite Es;
                replace (65536 <? Z.of_nat (length T)) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
              | lia ]
      end ] ].

Theorem rp_lock_lookup_holds : strlen_contract -> memchr_contract -> bcmp_contract -> rp_lock_lookup_contract.
Proof.
  intros SLc MCc BCc. unfold rp_lock_lookup_contract, RP_LOCK_LOOKUP, RP_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tx pa rate lo T P SL
    Htx HtxE BT Hpa BP NZ PAD Hrate ST HLO DT DP MI.
  pose proof (bytes_at_bound _ _ _ _ BP) as BPb. rewrite length_app in BPb; cbn [length] in BPb. destruct BPb as [_ HPb].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp. destruct Rsp as [_ Rsp].
  assert (Hlo : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  lazymatch goal with |- evt _ ?Q _ =>
    change Q with (Post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m rate lo T P) end.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 176%nat ST.
  do 20 step.
  destruct (std_period_cases rate) as [E0|[[Er Es]|[[Er Es]|[Er Es]]]].
  - assert (N1 : rate <> 44100) by (intros E; rewrite E in E0; discriminate E0).
    assert (N2 : rate <> 48000) by (intros E; rewrite E in E0; discriminate E0).
    assert (N3 : rate <> 96000) by (intros E; rewrite E in E0; discriminate E0).
    step. br false. step. step. step. br false. step. step. step. br true.
    eapply early_exit; try eassumption.
    unfold lock_lookup. rewrite E0. reflexivity.
  - step. br true. step. step. rp_common SLc NZ PAD Er Es T P SL rate pa tx.
  - step. br false. step. step. step. br false. step. step. step. br false. step. step. step. rp_common SLc NZ PAD Er Es T P SL rate pa tx.
  - step. br false. step. step. step. br true. step. step. step. rp_common SLc NZ PAD Er Es T P SL rate pa tx.
Qed.
