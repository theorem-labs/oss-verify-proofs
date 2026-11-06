(* Walks of fuzz_lock's LLVMFuzzerTestOneInput (fuzz_lock.c:181-207) in fuzz_lock.plain, 0x12b78: the pieces
   between its two calls (check_no_overread at 0x12cac, check_lookup at 0x12da0), on Exec.evt.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(* 0x12b78-0x12b84: size - 2^26 >= -2^26 + 2 (unsigned), that is 2 <= size < 2^26 *)
Lemma lt_head_taken : forall n, 2 <= n < 2 ^ 26 ->
  negb (bv_ltu (Z_to_bv 64 (n + -67108864)) (Z_to_bv 64 (-67108862))) = true.
Proof.
  intros n Hn. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Bool.negb_true_iff, Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma lt_head_early : forall n, 0 <= n < 2 ^ 64 -> n < 2 \/ 2 ^ 26 <= n ->
  negb (bv_ltu (Z_to_bv 64 (n + -67108864)) (Z_to_bv 64 (-67108862))) = false.
Proof.
  intros n Hn Hc. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Bool.negb_false_iff, Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Lemma lt_firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma lt_rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply lt_firstn1_skipn. exact N.
Qed.

Lemma lt_byte_at : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof. intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|]. apply nth_error_None in N. lia. Qed.

Lemma lt_firstn_S : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn (S i) l = firstn i l ++ [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - rewrite (IH i b N). reflexivity.
Qed.

Lemma lt_port_upd : forall (Qb J : list byte) i b, nth_error Qb i = Some b -> (i < length J)%nat ->
  Arr.upd (firstn i Qb ++ skipn i J) i b = firstn (S i) Qb ++ skipn (S i) J.
Proof.
  intros Qb J i b N Hi.
  assert (Hq : (i < length Qb)%nat) by (apply nth_error_Some; rewrite N; discriminate).
  assert (Lf : length (firstn i Qb) = i) by (rewrite length_firstn; lia).
  rewrite upd_firstn_skipn by (rewrite length_app, length_skipn; lia).
  rewrite (lt_firstn_S Qb i b N), <- app_assoc. cbn [app].
  rewrite firstn_app, Lf, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia.
  rewrite skipn_app, Lf. replace (S i - i)%nat with 1%nat by lia.
  rewrite skipn_all2 by lia. cbn [app]. rewrite skipn_skipn. replace (1 + i)%nat with (S i) by lia. reflexivity.
Qed.

Lemma lt_bad_in : forall (Qb : list byte) i b, nth_error Qb i = Some b -> lock_bad b = true ->
  existsb lock_bad Qb = true.
Proof. intros Qb i b N Hb. apply existsb_exists. exists b. split; [exact (nth_error_In Qb i N) | exact Hb]. Qed.

(* the name-byte test the compiler emits: c > 32 is no bad byte, else bit c of 0x100002601 *)
Definition bad_mach (c : Z) : bool :=
  if bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 c) then false
  else negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977025 (bv_unsigned (Z_to_bv 64 c) mod 64)))) 1))
                    (Z_to_bv 64 0)).

Lemma bad_mach_ok : forall c, 0 <= c < 256 -> bad_mach c = (c =? 0) || (c =? 10) || is_sep c.
Proof.
  intros c Hc.
  pose proof (brute256_ok (fun c => Bool.eqb (bad_mach c) ((c =? 0) || (c =? 10) || is_sep c))
    ltac:(vm_compute; reflexivity) c Hc) as H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma bad_hi : forall b : byte, bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b)) = true -> lock_bad b = false.
Proof.
  intros b H. pose proof (byte_range b) as R. unfold lock_bad. rewrite <- (bad_mach_ok (bz b) R).
  unfold bad_mach, bz. rewrite H. reflexivity.
Qed.

Lemma bad_lo : forall b : byte, bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b)) = false ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977025 (bv_unsigned (Z_to_bv 64 (bv_unsigned b)) mod 64)))) 1))
         (Z_to_bv 64 0) = negb (lock_bad b).
Proof.
  intros b H. pose proof (byte_range b) as R. unfold lock_bad. rewrite <- (bad_mach_ok (bz b) R).
  unfold bad_mach, bz. rewrite H. rewrite Bool.negb_involutive. reflexivity.
Qed.

Lemma le1_byte : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. exact le1_zxb. Qed.

(* the name loop, 0x12c1c-0x12c40: byte i of the name Qb at D + i, copied to the port at A0 + i *)
Section Loop.
Variables (ra xsp gp tp t1 t2 xs0 xs1 xa0 xa1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (D A0 : Z) (Qb J : list byte).
Hypothesis HJ : length J = 16%nat.
Hypothesis HQ : (length Qb <= 15)%nat.
Hypothesis HD : 0 <= D.
Hypothesis HDA : D + Z.of_nat (length Qb) <= A0.
Hypothesis HA : A0 + 16 <= 2 ^ 64.

Local Notation ST pc t0 a2 a5 a6 a7 m :=
  (MS (mkR ra xsp gp tp t0 t1 t2 xs0 xs1 xa0 xa1 a2 (Z_to_bv 64 32) (Z_to_bv 64 4294977025) a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma lt_loop : forall (Q : machine_state -> Prop) r (i : nat) (t0 a7 : word) (m : word -> option byte) (v2 v5 v6 : Z),
  (i + S r = length Qb)%nat ->
  v2 = A0 + Z.of_nat i -> v5 = D + Z.of_nat i -> v6 = Z.of_nat (S r) ->
  munch [(A0, A0 + 16)] m0 m -> wmono rsegs m0 m -> bytes_at rsegs m D Qb ->
  u8arr rsegs m A0 (firstn i Qb ++ skipn i J) ->
  existsb lock_bad (firstn i Qb) = false ->
  (forall (t0' a2' a5' a6' a7' : word) (m' : word -> option byte), existsb lock_bad Qb = true ->
     munch [(A0, A0 + 16)] m0 m' -> wmono rsegs m0 m' -> evt rsegs Q (ST 0x12c8c t0' a2' a5' a6' a7' m')) ->
  (forall (t0' a2' a5' a6' a7' : word) (m' : word -> option byte), existsb lock_bad Qb = false ->
     munch [(A0, A0 + 16)] m0 m' -> wmono rsegs m0 m' -> bytes_at rsegs m' D Qb ->
     u8arr rsegs m' A0 (Qb ++ skipn (length Qb) J) ->
     evt rsegs Q (ST 0x12c44 t0' a2' a5' a6' a7' m')) ->
  evt rsegs Q (ST 0x12c1c t0 (Z_to_bv 64 v2) (Z_to_bv 64 v5) (Z_to_bv 64 v6) a7 m).
Proof.
  intros Q r. induction r as [|r IH]; intros i t0 a7 m v2 v5 v6 Hi -> -> Hv6 MU WM BD PA NB KB KD.
  all: destruct (lt_byte_at Qb i ltac:(lia)) as [b Nb].
  all: pose proof (lt_rdb m D Qb i b BD Nb) as R.
  all: pose proof (byte_range b) as Rb.
  all: assert (LC : length (firstn i Qb ++ skipn i J) = 16%nat)
         by (rewrite length_app, length_firstn, length_skipn; lia).
  all: assert (STORE : lock_bad b = false -> forall t0',
         evt rsegs Q (ST 0x12c30 t0' (Z_to_bv 64 (A0 + Z.of_nat i)) (Z_to_bv 64 (D + Z.of_nat i))
                        (Z_to_bv 64 v6) (Z_to_bv 64 (bv_unsigned b)) m)).
  1, 3: intros Gb t0';
    pose proof (u8arr_store_ok rsegs m A0 _ (Z.of_nat i) _ PA ltac:(rewrite LC; lia) eq_refl) as HS;
    step; rewrite le1_byte;
    pose proof (u8arr_write rsegs m A0 _ (Z.of_nat i) b PA ltac:(rewrite LC; lia)) as PA';
    rewrite Nat2Z.id, (lt_port_upd Qb J i b Nb ltac:(lia)) in PA';
    pose proof (bytes_at_write_other rsegs m (A0 + Z.of_nat i) [b] D Qb BD ltac:(lia) ltac:(cbn; lia)
      ltac:(cbn; lia)) as BD';
    pose proof (munch_write [(A0, A0 + 16)] m0 m (A0 + Z.of_nat i) [b] MU ltac:(lia) ltac:(cbn; lia)
      ltac:(cbn [inside length]; simpl_sizes; slia)) as MU';
    pose proof (wmono_write rsegs m0 m (wa (A0 + Z.of_nat i)) [b] WM) as WM';
    assert (NB' : existsb lock_bad (firstn (S i) Qb) = false)
      by (rewrite (lt_firstn_S Qb i b Nb), existsb_app, NB; cbn [existsb]; rewrite Gb; reflexivity);
    do 4 step.
  (* the byte test, in both cases *)
  3, 4: step; unfold zxb; step;
    destruct (bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b))) eqn:C1; cbv iota;
    [apply (STORE (bad_hi b C1)) |];
    do 3 step; rewrite (bad_lo b C1); destruct (lock_bad b) eqn:Bd; cbn [negb]; cbv iota;
    [apply KB; [exact (lt_bad_in Qb i b Nb Bd) | exact MU | exact WM] | apply (STORE eq_refl)].
  - (* the last byte: fall through to 0x12c44 *)
    br false.
    assert (EQ : firstn (S i) Qb = Qb) by (apply firstn_all2; lia).
    rewrite EQ in PA', NB'. replace (S i) with (length Qb) in PA' by lia.
    apply KD; [exact NB' | exact MU' | exact WM' | exact BD' | exact PA'].
  - (* more bytes: back to 0x12c1c *)
    br true. eapply (IH (S i)); [lia | lia | lia | lia | exact MU' | exact WM' | exact BD' | exact PA' | exact NB'
      | exact KB | exact KD].
Qed.

End Loop.

(* the name length k and the name (fuzz_lock.c:188, 194-198) *)
Definition lk_k (pl : list byte) : Z := bz (nth 1 pl (Z_to_bv 8 0)) mod 16.
Definition lk_port (pl : list byte) : list byte := firstn (Z.to_nat (lk_k pl)) (skipn 2 pl).

Lemma lk_k_range : forall pl, 0 <= lk_k pl < 16.
Proof. intros pl. unfold lk_k. apply Z.mod_pos_bound. lia. Qed.

Lemma lk_k_of : forall pl b1, nth_error pl 1 = Some b1 -> lk_k pl = bv_unsigned b1 mod 16.
Proof. intros pl b1 N. unfold lk_k, bz. rewrite (nth_error_nth pl 1 (Z_to_bv 8 0) N). reflexivity. Qed.

Lemma lk_port_length : forall pl, 2 + lk_k pl <= Z.of_nat (length pl) -> Z.of_nat (length (lk_port pl)) = lk_k pl.
Proof.
  intros pl H. pose proof (lk_k_range pl). unfold lk_port. rewrite length_firstn, length_skipn. lia.
Qed.

Section Ret.
Variable pl : list byte.
Hypothesis HN : 2 <= Z.of_nat (length pl) < 2 ^ 26.

Lemma lock_ret_mid : forall r, (if Z.of_nat (length pl) <? 2 + lk_k pl then 0
    else if lk_k pl =? 0 then -1 else if existsb lock_bad (lk_port pl) then -1 else 0) = r -> lock_ret pl = r.
Proof.
  intros r H. rewrite <- H. unfold lock_ret, lk_port, lk_k. cbv zeta.
  replace ((Z.of_nat (length pl) <? 2) || (2 ^ 26 <=? Z.of_nat (length pl))) with false
    by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  reflexivity.
Qed.

Lemma lock_ret_short : Z.of_nat (length pl) < 2 + lk_k pl -> lock_ret pl = 0.
Proof. intros H. apply lock_ret_mid. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma lock_ret_k0 : 2 + lk_k pl <= Z.of_nat (length pl) -> lk_k pl = 0 -> lock_ret pl = -1.
Proof.
  intros H K. apply lock_ret_mid. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite K. reflexivity.
Qed.

Lemma lock_ret_bad : 2 + lk_k pl <= Z.of_nat (length pl) -> lk_k pl <> 0 -> existsb lock_bad (lk_port pl) = true ->
  lock_ret pl = -1.
Proof.
  intros H K E. apply lock_ret_mid. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (lk_k pl =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). rewrite E. reflexivity.
Qed.

Lemma lock_ret_ok : 2 + lk_k pl <= Z.of_nat (length pl) -> lk_k pl <> 0 -> existsb lock_bad (lk_port pl) = false ->
  lock_ret pl = 0.
Proof.
  intros H K E. apply lock_ret_mid. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (lk_k pl =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). rewrite E. reflexivity.
Qed.

End Ret.

Lemma lock_ret_early : forall pl, Z.of_nat (length pl) < 2 \/ 2 ^ 26 <= Z.of_nat (length pl) -> lock_ret pl = 0.
Proof.
  intros pl H. unfold lock_ret. cbv zeta.
  replace ((Z.of_nat (length pl) <? 2) || (2 ^ 26 <=? Z.of_nat (length pl))) with true; [reflexivity|].
  symmetry. apply orb_true_iff. destruct H; [left; apply Z.ltb_lt | right; apply Z.leb_le]; lia.
Qed.

Lemma lt_kreg : forall b : byte, Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) 15 = bv_unsigned b mod 16.
Proof.
  intros b. pose proof (byte_range b). rewrite unsigned_lit by lia. change 15 with (Z.ones 4).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma lt_brute_eq : forall f g : Z -> Z, forallb (fun c => f c =? g c) (zseq 256) = true ->
  forall c, 0 <= c < 256 -> f c = g c.
Proof. intros f g H c Hc. apply Z.eqb_eq. exact (brute256_ok (fun c => f c =? g c) H c Hc). Qed.

Lemma lt_bytes_sub : forall m a l (i j : nat), bytes_at rsegs m a l -> (i + j <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat i) (firstn j (skipn i l)).
Proof.
  intros m a l i j H Hij. rewrite <- (firstn_skipn i l) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min i (length l)) with i in H by lia.
  rewrite <- (firstn_skipn j (skipn i l)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Lemma lt_port_zero : forall (P J : list byte), (length P < length J)%nat ->
  Arr.upd (P ++ skipn (length P) J) (length P) (Z_to_bv 8 0) = P ++ Z_to_bv 8 0 :: skipn (S (length P)) J.
Proof.
  intros P J H. rewrite upd_firstn_skipn by (rewrite length_app, length_skipn; lia).
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  rewrite skipn_app, Nat.sub_succ_l, Nat.sub_diag by lia. rewrite skipn_all2 by lia. cbn [app].
  rewrite skipn_skipn. replace (1 + length P)%nat with (S (length P)) by lia. reflexivity.
Qed.

Lemma lt_sp_back : forall (x : word) v, v = bv_unsigned x -> Z_to_bv 64 v = x.
Proof. intros x v ->. apply Z_to_bv_bv_unsigned. Qed.

(* LLVMFuzzerTestOneInput from its entry, for 2 <= size < 2^26, to its return (-1, or 0 for a short input) or to
   the call of check_no_overread (0x12c6c jal), with the name and its NUL in the port char[16] at sp - 56. *)
Section Main.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (pl : list byte).
Hypothesis HLO : lo + 64 <= bv_unsigned sp.
Hypothesis HN : 2 <= Z.of_nat (length pl) < 2 ^ 26.
Hypothesis HP : 0 < p.
Hypothesis HPL : p + Z.of_nat (length pl) <= lo.

Definition lt_post : machine_state -> Prop := fun ms' =>
  (exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
     ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (lock_ret pl)) a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
     munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m') \/
  (exists (t0' a4' a5' a6' a7' w : word) (SL : list byte) (m' : word -> option byte),
     lock_ret pl = 0 /\ 1 <= lk_k pl /\ 2 + lk_k pl <= Z.of_nat (length pl) /\
     length SL = (15 - Z.to_nat (lk_k pl))%nat /\
     ms' = MS (mkR (Z_to_bv 64 0x12c70) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0' t1 t2 (Z_to_bv 64 (lk_k pl)) w
                   (Z_to_bv 64 (p + 2 + lk_k pl)) (Z_to_bv 64 (Z.of_nat (length pl) - 2 - lk_k pl))
                   (Z_to_bv 64 (bv_unsigned sp - 56)) w a4' a5' a6' a7'
                   (Z_to_bv 64 (p + 2 + lk_k pl)) (Z_to_bv 64 (Z.of_nat (length pl) - 2 - lk_k pl))
                   s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x12cac) fc None m' (seg_rom rsegs) /\
     munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
     stk rsegs m' lo (bv_unsigned sp - 64) /\
     rw_cells rsegs m' (bv_unsigned sp - 40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
     bytes_at rsegs m' (bv_unsigned sp - 56) (lk_port pl ++ Z_to_bv 8 0 :: SL) /\
     bytes_at rsegs m' p pl).

(* 0x12c04: the separator mask, the name loop, the NUL, the arguments and the call of check_no_overread *)
Lemma lt_rest : forall (m1 : word -> option byte) (t0' a4' a5' a6' a7' w : word) (J : list byte) (vsp v0 v10 v12 : Z),
  vsp = bv_unsigned sp + -64 -> v0 = lk_k pl -> v10 = p + 2 -> v12 = bv_unsigned sp + -56 ->
  1 <= lk_k pl -> 2 + lk_k pl <= Z.of_nat (length pl) ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells rsegs m1 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m1 (bv_unsigned sp + -56) [CB 16 J] ->
  bytes_at rsegs m1 p pl ->
  evt rsegs lt_post (MS (mkR ra (Z_to_bv 64 vsp) gp tp t0' t1 t2 (Z_to_bv 64 v0) w (Z_to_bv 64 v10)
                           (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 v12) (Z_to_bv 64 32) a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x12c04) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 t0' a4' a5' a6' a7' w J vsp v0 v10 v12 -> -> -> -> Hk1 Hk2 MU WM ST FR PJ BL.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (lk_k_range pl) as Hk.
  pose proof (lk_port_length pl Hk2) as HQl.
  assert (HJ : length J = 16%nat) by (destruct PJ as [[Hwf _] _]; exact (proj1 Hwf)).
  pose proof (u8arr_of_rw_cells rsegs m1 _ _ J PJ) as PA.
  assert (BQ : bytes_at rsegs m1 (p + 2) (lk_port pl)).
  { pose proof (lt_bytes_sub m1 p pl 2 (Z.to_nat (lk_k pl)) BL ltac:(lia)) as B. exact B. }
  do 6 step.
  eapply (lt_loop ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t1 t2 (Z_to_bv 64 (lk_k pl)) w (Z_to_bv 64 (p + 2))
    (Z_to_bv 64 (Z.of_nat (length pl))) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (p + 2)
    (bv_unsigned sp + -56) (lk_port pl) J HJ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) lt_post
    (Z.to_nat (lk_k pl) - 1) 0%nat).
  - lia.
  - lia.
  - lia.
  - lia.
  - apply munch_refl.
  - apply wmono_refl.
  - exact BQ.
  - cbn [firstn skipn app]. exact PA.
  - reflexivity.
  - (* a bad name byte: return -1 *)
    intros x0 x2 x5 x6 x7 m' Bd MU' WM'.
    pose proof (rw_cells_transport rsegs _ m1 m' _ _ FR MU' WM' ltac:(cbn; split; [lia | exact I])) as FR'.
    assert (MUc : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m').
    { eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
      unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
    pose proof (wmono_trans rsegs _ _ _ WM WM') as WMc.
    clear MU' WM' FR ST BL PA PJ BQ.
    do 8 step.
    apply evt_done. left. rewrite (lock_ret_bad pl HN Hk2 ltac:(lia) Bd).
    do 9 eexists. split; [reflexivity | split; [exact MUc | exact WMc]].
  - intros x0 x2 x5 x6 x7 m' NB MU' WM' BD' PA'.
    pose proof (rw_cells_transport rsegs _ m1 m' _ _ FR MU' WM' ltac:(cbn; split; [lia | exact I])) as FR'.
    pose proof (stk_transport_disjoint rsegs _ m1 m' _ _ ST MU' WM' ltac:(cbn; split; [lia | exact I])) as ST'.
    pose proof (bytes_at_transport rsegs _ m1 m' p pl BL MU' ltac:(cbn; split; [lia | exact I])) as BL'.
    assert (MUc : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m').
    { eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
      unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
    pose proof (wmono_trans rsegs _ _ _ WM WM') as WMc.
    clear MU' WM' FR ST BL PA PJ BQ.
    do 4 step.
    pose proof (u8arr_store_ok rsegs m' (bv_unsigned sp + -56) _ (lk_k pl) _ PA'
      ltac:(rewrite length_app, length_skipn; lia) eq_refl) as HS.
    step.
    rewrite le1_zero.
    pose proof (u8arr_write rsegs m' (bv_unsigned sp + -56) _ (lk_k pl) (Z_to_bv 8 0) PA'
      ltac:(rewrite length_app, length_skipn; lia)) as PA2.
    replace (Z.to_nat (lk_k pl)) with (length (lk_port pl)) in PA2 by lia.
    rewrite lt_port_zero in PA2 by lia.
    pose proof (rw_cells_frame rsegs m' _ _ (bv_unsigned sp + -56 + lk_k pl) [Z_to_bv 8 0] FR' ltac:(lia)
      ltac:(cbn; lia) ltac:(cbn; lia)) as FR2.
    pose proof (stk_write rsegs m' lo _ (bv_unsigned sp + -56 + lk_k pl) [Z_to_bv 8 0] ST' ltac:(lia)
      ltac:(cbn; lia)) as ST2.
    pose proof (bytes_at_write_other rsegs m' (bv_unsigned sp + -56 + lk_k pl) [Z_to_bv 8 0] p pl BL' ltac:(lia)
      ltac:(cbn; lia) ltac:(cbn; lia)) as BL2.
    pose proof (munch_write [(bv_unsigned sp - 64, bv_unsigned sp)] m m' (bv_unsigned sp + -56 + lk_k pl)
      [Z_to_bv 8 0] MUc ltac:(lia) ltac:(cbn; lia) ltac:(cbn [inside length]; simpl_sizes; slia)) as MU2.
    pose proof (wmono_write rsegs m m' (wa (bv_unsigned sp + -56 + lk_k pl)) [Z_to_bv 8 0] WMc) as WM2.
    do 6 step.
    apply evt_done. right.
    exists x0, (Z_to_bv 64 4294977025), x5, x6, x7, w, (skipn (S (length (lk_port pl))) J),
      (write_to_mem m' (wa (bv_unsigned sp + -56 + lk_k pl)) [Z_to_bv 8 0]).
    split; [exact (lock_ret_ok pl HN Hk2 ltac:(lia) NB) |].
    split; [exact Hk1 |]. split; [exact Hk2 |].
    split; [rewrite length_skipn; lia |].
    split.
    { f_equal. unfold mkR.
      repeat match goal with
      | |- TNode _ _ _ = TNode _ _ _ => f_equal
      | |- Some _ = Some _ => f_equal
      end.
      all: first [ reflexivity | f_equal; lia
                 | rewrite ?unsigned_lit by lia; f_equal; lia ]. }
    split; [exact MU2 |]. split; [exact WM2 |].
    split; [replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact ST2 |].
    split; [replace (bv_unsigned sp - 40) with (bv_unsigned sp + -40) by lia; exact FR2 |].
    split; [replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) by lia; exact (proj1 PA2) |].
    exact BL2.
Qed.

Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis BL : bytes_at rsegs m p pl.
Hypothesis MI : mem_inv rsegs m.

(* 0x12b78: the size test, the frame, k = data[1] % 16, size < 2 + k, k == 0, rate = RATES[data[0] % 5] *)
Lemma lt_main :
  evt rsegs lt_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length pl))) a2 a3 a4 a5
                           a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x12b78) fc None m (seg_rom rsegs)).
Proof.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof ST as ST1. pose proof BL as BL1. pose proof MI as MI1. pose proof (lk_k_range pl) as Hk.
  carve_frame 40%nat ST1. carve_frame 16%nat ST1. carve_frame 8%nat ST1.
  do 4 step. if_true_by (lt_head_taken _ HN).
  do 6 step.
  destruct (lt_byte_at pl 1 ltac:(lia)) as [b1 N1].
  pose proof (lt_rdb _ p pl 1 b1 BL1 N1) as R1.
  step. unfold zxb. step. rewrite lt_kreg, <- (lk_k_of pl b1 N1). step. step.
  destruct (Z_lt_le_dec (Z.of_nat (length pl)) (2 + lk_k pl)) as [Hs|Hs].
  - (* size < 2 + k: return 0 *)
    br false. do 9 step.
    apply evt_done. left. rewrite (lock_ret_short pl HN Hs).
    do 9 eexists. split; [reflexivity | split; [exact MU | exact WM]].
  - br true. step.
    destruct (Z.eq_dec (lk_k pl) 0) as [K0|K0].
    + (* k == 0: return -1 *)
      br true. do 8 step.
      apply evt_done. left. rewrite (lock_ret_k0 pl HN Hs K0).
      do 9 eexists. split; [reflexivity | split; [exact MU | exact WM]].
    + br false.
      destruct (lt_byte_at pl 0 ltac:(lia)) as [b0 N0].
      pose proof (lt_rdb _ p pl 0 b0 BL1 N0) as R0.
      step. unfold zxb. do 14 step.
      (* a4 = RATES + 8 * (data[0] % 5): 66448 = 0x10390 = auipc 0x12bcc - 0x3000 + 0x7c4, the symbol RATES of the
         unstripped ELF; the load below reads RATES[data[0] % 5] from Img0 (solve_load_image) in each of 5 cases *)
      lazymatch goal with |- context [Z_to_bv 64 (66448 + ?X)] =>
        let HX := fresh "HX" in
        assert (HX : X = 8 * (bv_unsigned b0 mod 5))
          by (generalize (byte_range b0); generalize (bv_unsigned b0);
              refine (lt_brute_eq (fun z => _) (fun z => 8 * (z mod 5)) _); vm_compute; reflexivity);
        rewrite HX
      end.
      assert (C5 : bv_unsigned b0 mod 5 = 0 \/ bv_unsigned b0 mod 5 = 1 \/ bv_unsigned b0 mod 5 = 2 \/
                   bv_unsigned b0 mod 5 = 3 \/ bv_unsigned b0 mod 5 = 4) by lia.
      destruct C5 as [E|[E|[E|[E|E]]]]; rewrite E; step;
        (eapply lt_rest; [ lia | reflexivity | lia | lia | lia | exact Hs | exact MU | exact WM
                         | exact ST1 | exact FR | exact FR0 | exact BL1 ]).
Qed.

End Main.

(* 0x12b78: size < 2 or size >= 2^26, return 0 before the frame *)
Lemma lt_early_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
    0 <= n < 2 ^ 64 -> n < 2 \/ 2 ^ 26 <= n ->
    evt rsegs (fun ms' => exists a2' a3' : word,
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 n) a2' a3' a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12b78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n Hn Hc.
  do 4 step. if_false_by (lt_head_early n Hn Hc). do 2 step.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

(* 0x12c70: back from check_no_overread, the arguments of check_lookup and its call *)
Lemma lt_mid :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x12c88) sp gp tp t0 t1 t2 s0 s1 s2 s3
                                       (Z_to_bv 64 (bv_unsigned sp + 8)) s0 s1 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x12da0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12c70) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 6 step. apply evt_done. reflexivity.
Qed.

(* 0x12c88: back from check_lookup, return 0 through the epilogue *)
Lemma lt_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 v1 v2 v3 vra : word),
    rw_cells rsegs m (bv_unsigned sp + 24) [C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 (Z_to_bv 64 0)
                                       a1 a2 a3 a4 a5 a6 a7 v2 v3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12c88) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v1 v2 v3 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 10 step. apply evt_done. reflexivity.
Qed.
