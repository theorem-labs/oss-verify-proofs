(** The walk of read_channel(rest = K + 13) in the UBSan LLVMFuzzerTestOneInput up to the byte after the digits,
    0x14374 -> 0x14438 (U/Prog/HeadCheck/KeyCut.v [rc_stmt]; fuzz_headamp.c:67-85). Section RcWalk fixes the frame
    (the registers the piece leaves alone, the FP state, the memory), the key k NUL-terminated at K and the
    continuation. Walked backwards: the exit 0x14438 ([rc_exit]), the digits loop 0x143f4 with the acc > 1000000 'big'
    rule and the acc * 10 check (by induction on the bytes left, [rc_dig_ok]), the check 0x143e0 and the loop's
    set-up ([rc_sgn_done]), the sign ([rc_minus_ok], [rc_sign_ok]), the blanks loop 0x1439c (by induction on the
    bytes left, [rc_blank_ok]) and the entry: the constants, the k + 13 check 0x1438c, rest and ~rest
    ([rc_entry]). Each test the code makes decides one step of Pod/Headamp.v [rc_blanks], [rc_sign] and
    [rc_digits] (Prog/HeadCheck/KeyFacts.v). Every trap is not taken: rest + i stays inside k ++ [NUL], which ends
    below 2^64 - 1, and acc * 10 does not overflow for acc <= 1000000. No memory is written. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts KeyFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut KeyCut.
Import ListNotations.
Open Scope Z_scope.

(* Register equations at a lemma's entry. *)
Ltac rc_weq := first [ reflexivity
                     | (f_equal; lia)
                     | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

(** ** Word and list facts of the walk *)
(** `mulh a6, s9, 10` and `srai t0, s9 * 10, 63` for 0 <= acc <= 1000000: both 0, so the overflow check
    `bne a6, t0` is not taken. *)
Lemma rc_mulh0 : forall acc, 0 <= acc <= 1000000 -> Z.shiftr (acc * 10) 64 = 0.
Proof. intros acc H. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma rc_srai0 : forall acc, 0 <= acc <= 1000000 -> Z.shiftr (acc * 10) 63 = 0.
Proof. intros acc H. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma rc_nth_skipn : forall (l : list byte) n i, nth i (skipn n l) NUL = nth (n + i) l NUL.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; cbn [skipn]; [destruct i; reflexivity | exact (IH l i)].
Qed.

Lemma rc_digit_nonnul : forall b, rc_digit b = true -> bv_unsigned b <> 0.
Proof. intros b H. unfold rc_digit in H. apply andb_prop in H as [H1 _]. apply Z.leb_le in H1. lia. Qed.

Section RcWalk.
Variables (Q : machine_state -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s10 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (K : Z) (k : list byte).

Local Abbreviation RS := (skipn 13 k).
Local Abbreviation BL := (rc_blanks (skipn 13 k)).

Hypothesis HKB : bytes_at rsegs m K (k ++ [NUL]).
Hypothesis HKL : (13 <= length k)%nat.
Hypothesis HK0 : 0 < K.
Hypothesis HKW : K + Z.of_nat (length k) + 1 < 2^64.
Hypothesis HQ : forall (t0' a5' : word) (neg : bool) (sn nd : nat) (acc : Z) (big : bool),
  rc_sign (skipn BL RS) = (neg, sn) ->
  rc_digits 0 false (skipn (BL + sn) RS) = (acc, big, nd) ->
  0 <= acc <= 10000009 -> (BL + sn + nd <= length RS)%nat ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0' (Z_to_bv 64 9) (Z_to_bv 64 10) s0 s1 (Z_to_bv 64 (K + 13))
             (Z_to_bv 64 (Z.of_nat (BL + sn))) (Z_to_bv 64 (2^64 - 1 - (K + 13)))
             (Z_to_bv 64 (if neg then 0 else 1)) (Z_to_bv 64 (Z.of_nat nd)) a5'
             (Z_to_bv 64 (K + Z.of_nat (BL + sn + nd))) (zxb (nth (BL + sn + nd) RS NUL))
             s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 acc) s10 (Z_to_bv 64 K) (Z_to_bv 64 RC_BIG)
             (Z_to_bv 64 (if big then 1 else 0)) t5 t6)
        F (Z_to_bv 64 0x14438) fc None m (seg_rom rsegs)).

Lemma rc_len : length RS = (length k - 13)%nat.
Proof. apply length_skipn. Qed.

(** The byte rest[i] for i <= length rest (rest[length rest] is the NUL). *)
Lemma rc_byte : forall i, (i <= length RS)%nat ->
  ov_read_bytes rsegs m (wa (K + 13 + Z.of_nat i)) 1 = Some [nth i RS NUL].
Proof.
  intros i Hi. rewrite rc_len in Hi.
  assert (L : (13 + i + 1 <= length (k ++ [NUL]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (bytes_at_ov_read rsegs m K (k ++ [NUL]) (13 + i) 1 HKB L) as R.
  replace (K + Z.of_nat (13 + i)) with (K + 13 + Z.of_nat i) in R by lia.
  rewrite R. f_equal.
  rewrite (skipn_nth_cons (k ++ [NUL]) (13 + i) NUL) by lia. cbn [firstn]. f_equal.
  rewrite nth_app_nul. symmetry. apply rc_nth_skipn.
Qed.

(** ** 0x14438: the exit *)
Lemma rc_exit : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word) (neg : bool) (sn nd : nat) (acc : Z)
    (big : bool),
  rc_sign (skipn BL RS) = (neg, sn) ->
  rc_digits 0 false (skipn (BL + sn) RS) = (acc, big, nd) ->
  0 <= acc <= 10000009 -> (BL + sn + nd <= length RS)%nat ->
  t1 = Z_to_bv 64 9 -> t2 = Z_to_bv 64 10 -> t3 = Z_to_bv 64 RC_BIG ->
  a0 = Z_to_bv 64 (K + 13) -> a1 = Z_to_bv 64 (Z.of_nat (BL + sn)) -> a2 = Z_to_bv 64 (2^64 - 1 - (K + 13)) ->
  a3 = Z_to_bv 64 (if neg then 0 else 1) -> a4 = Z_to_bv 64 (Z.of_nat nd) ->
  a6 = Z_to_bv 64 (K + Z.of_nat (BL + sn + nd)) -> a7 = zxb (nth (BL + sn + nd) RS NUL) ->
  s9 = Z_to_bv 64 acc -> t4 = Z_to_bv 64 (if big then 1 else 0) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x14438) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 neg sn nd acc big HS HD HA HL
    -> -> -> -> -> -> -> -> -> -> -> ->.
  exact (HQ t0 a5 neg sn nd acc big HS HD HA HL).
Qed.

(** ** The digits loop 0x143f4 .. 0x14434 (fuzz_headamp.c:79-85) after j digits *)
Definition rc_dig_P (j : nat) : Prop :=
  forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word) (neg : bool) (sn : nat) (acc : Z) (big : bool),
  rc_sign (skipn BL RS) = (neg, sn) ->
  rc_digits 0 false (skipn (BL + sn) RS) =
    (fst (fst (rc_digits acc big (skipn (BL + sn + j) RS))), snd (fst (rc_digits acc big (skipn (BL + sn + j) RS))),
     (j + snd (rc_digits acc big (skipn (BL + sn + j) RS)))%nat) ->
  0 <= acc <= 10000009 -> (BL + sn + j <= length RS)%nat ->
  t1 = Z_to_bv 64 9 -> t2 = Z_to_bv 64 10 -> t3 = Z_to_bv 64 RC_BIG ->
  a0 = Z_to_bv 64 (K + 13) -> a1 = Z_to_bv 64 (Z.of_nat (BL + sn)) -> a2 = Z_to_bv 64 (2^64 - 1 - (K + 13)) ->
  a3 = Z_to_bv 64 (if neg then 0 else 1) -> a4 = Z_to_bv 64 (Z.of_nat j) ->
  a5 = Z_to_bv 64 (K + Z.of_nat (BL + sn)) -> s9 = Z_to_bv 64 acc -> t4 = Z_to_bv 64 (if big then 1 else 0) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x143f4) fc None m (seg_rom rsegs)).

Lemma rc_dig_ok : forall L j, (length RS - j <= L)%nat -> rc_dig_P j.
Proof.
  induction L as [|L IH]; intros j HL; unfold rc_dig_P;
    intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 neg sn acc big HSG HI Hacc Hj
      -> -> -> -> -> -> -> -> -> -> ->;
    assert (IHH : (BL + sn + j < length RS)%nat -> rc_dig_P (S j))
      by (intros Hs; first [exfalso; lia | apply IH; lia]);
    pose proof rc_len as LRS; pose proof HKW as HW; pose proof HKL as HL13; unfold RC_BIG.
  all: (* 0x143f4 add a6,a5,a4; lbu a7,0xd(a6) *)
    step; pose proof (rc_byte (BL + sn + j) Hj) as HR;
    replace (K + 13 + Z.of_nat (BL + sn + j)) with (K + Z.of_nat (BL + sn) + Z.of_nat j + 13) in HR by lia;
    step; clear HR;
    (* 0x143fc addi t0,a7,-0x30; bltu t1,t0 *)
    step; step; rewrite digit_gtu9;
    destruct (rc_digit (nth (BL + sn + j) RS NUL)) eqn:HDG; cbn [negb]; cbv beta iota;
    pose proof (rc_digits_at RS (BL + sn + j) acc big) as RD; rewrite HDG in RD; cbv beta iota zeta in RD.
  2, 4: (* not a digit: the exit *)
    rewrite RD in HI; cbn [fst snd] in HI; rewrite Nat.add_0_r in HI;
    eapply (rc_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ neg sn j acc big HSG HI Hacc Hj); rc_weq.
  all: assert (Hlt : (BL + sn + j < length RS)%nat)
         by (apply nth_nonnul_lt; apply rc_digit_nonnul; exact HDG);
    pose proof (IHH Hlt) as IH1; unfold rc_dig_P in IH1;
    pose proof HDG as Hc; unfold rc_digit in Hc; apply andb_prop in Hc as [Hc1 Hc2];
    apply Z.leb_le in Hc1; apply Z.leb_le in Hc2.
  all: (* 0x14404 bge t3,s9 *)
    step; rewrite lts_s by lia;
    destruct (Z.ltb_spec 1000000 acc) as [Hb|Hb]; cbn [negb]; cbv beta iota.
  all: try first [ rewrite (proj2 (Z.ltb_lt 1000000 acc) Hb) in RD | rewrite (proj2 (Z.ltb_ge 1000000 acc) Hb) in RD ];
    cbv beta iota in RD.
  (* Each of the two cases L = 0 and L + 1 has the two goals acc > 1000000 and acc <= 1000000. *)
  1, 3: (* acc > 1000000: 0x14408 addi t4,zero,1; j 0x14428; addi a4,a4,1; add a6,a1,a4; bgeu a2,a6 *)
    do 5 step; rewrite ltu_u by lia; if_true;
    eapply (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ neg sn acc true);
      [ exact HSG
      | rewrite HI, RD; replace (BL + sn + S j)%nat with (S (BL + sn + j)) by lia; cbn [fst snd]; f_equal; lia
      | lia | lia | rc_weq .. ].
  all: (* acc <= 1000000: 0x14410 mulh a6,s9,t2; mul s9,s9,t2; srai t0,s9,0x3f; bne a6,t0 *)
    do 3 step;
    rewrite ?(unsigned_lit acc) by lia; rewrite ?(signed_lit acc) by lia; rewrite ?(signed_lit (acc * 10)) by lia;
    rewrite (rc_mulh0 acc), (rc_srai0 acc) by lia;
    step; if_false;
    (* 0x14420 andi a6,a7,0xf; add s9,s9,a6 *)
    step; rewrite (digit_land _ HDG); step;
    (* 0x14428 addi a4,a4,1; add a6,a1,a4; bgeu a2,a6 *)
    do 3 step; rewrite ltu_u by lia; if_true;
    eapply (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ neg sn (acc * 10 + (bv_unsigned (nth (BL + sn + j) RS NUL) - 48)) big);
      [ exact HSG
      | rewrite HI, RD; replace (BL + sn + S j)%nat with (S (BL + sn + j)) by lia; cbn [fst snd]; f_equal; lia
      | lia | lia | rc_weq .. ].
Qed.

(** ** 0x143e0 .. 0x143f0: the check of rest + d (trap not taken) and the digits loop's set-up *)
Lemma rc_sgn_done : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word) (neg : bool) (sn : nat),
  rc_sign (skipn BL RS) = (neg, sn) -> (BL + sn <= length RS)%nat ->
  t1 = Z_to_bv 64 9 -> t2 = Z_to_bv 64 10 -> t3 = Z_to_bv 64 RC_BIG ->
  a0 = Z_to_bv 64 (K + 13) -> a1 = Z_to_bv 64 (Z.of_nat (BL + sn)) -> a2 = Z_to_bv 64 (2^64 - 1 - (K + 13)) ->
  a3 = Z_to_bv 64 (if neg then 0 else 1) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x143e0) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 neg sn HSG Hd -> -> -> -> -> -> ->.
  pose proof rc_len as LRS. pose proof HKW as HW. pose proof HKL as HL13.
  (* 0x143e0 bltu a2,a1 *)
  step. rewrite ltu_u by lia. if_false.
  (* 0x143e4 mv a4,zero; mv t4,zero; mv s9,zero; add a5,s11,a1 *)
  step. step. step. step.
  eapply (rc_dig_ok (length RS) 0 ltac:(lia) _ _ _ _ _ _ _ _ _ _ _ _ _ _ neg sn 0 false);
    [exact HSG | | lia | lia | rc_weq ..].
  rewrite Nat.add_0_r. destruct (rc_digits 0 false (skipn (BL + sn) RS)) as [[x y] z]. reflexivity.
Qed.

(** ** 0x143cc .. 0x143d8: after a '+' or a '-' at rest[BL]: d = BL + 1, the sign flag *)
Lemma rc_minus_ok : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word),
  bv_unsigned (nth BL RS NUL) = 43 \/ bv_unsigned (nth BL RS NUL) = 45 ->
  t1 = Z_to_bv 64 9 -> t2 = Z_to_bv 64 10 -> t3 = Z_to_bv 64 RC_BIG ->
  a0 = Z_to_bv 64 (K + 13) -> a1 = Z_to_bv 64 (Z.of_nat BL) -> a2 = Z_to_bv 64 (2^64 - 1 - (K + 13)) ->
  a3 = zxb (nth BL RS NUL) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x143cc) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 Hc -> -> -> -> -> -> ->.
  pose proof rc_len as LRS. pose proof HKW as HW. pose proof HKL as HL13.
  assert (Hlt : (BL < length RS)%nat) by (apply nth_nonnul_lt; lia).
  (* 0x143cc addi a1,a1,1; addi a3,a3,-0x2d; snez a3,a3; j 0x143e0 *)
  step. step. step. rewrite (snez_sign _ Hc). step.
  pose proof (rc_sign_at RS BL) as HSG.
  replace ((bv_unsigned (nth BL RS NUL) =? 43) || (bv_unsigned (nth BL RS NUL) =? 45)) with true in HSG
    by (destruct Hc as [Hc|Hc]; rewrite Hc; reflexivity).
  cbv beta iota in HSG.
  eapply (rc_sgn_done _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned (nth BL RS NUL) =? 45) 1 HSG ltac:(lia)); rc_weq.
Qed.

(** ** 0x143bc .. 0x143dc: the sign (fuzz_headamp.c:74-75) at rest[BL] *)
Lemma rc_sign_ok : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word),
  t1 = Z_to_bv 64 9 -> t2 = Z_to_bv 64 10 -> t3 = Z_to_bv 64 RC_BIG ->
  a0 = Z_to_bv 64 (K + 13) -> a1 = Z_to_bv 64 (Z.of_nat BL) -> a2 = Z_to_bv 64 (2^64 - 1 - (K + 13)) ->
  a3 = zxb (nth BL RS NUL) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x143bc) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 -> -> -> -> -> -> ->.
  pose proof (rc_blanks_le RS) as Hbl.
  (* 0x143bc addi a4,zero,0x2b; beq a3,a4 *)
  step. step. rewrite zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth BL RS NUL)) 43) as [E43|E43]; cbv beta iota.
  { eapply rc_minus_ok; [left; exact E43 | rc_weq ..]. }
  (* 0x143c4 addi a4,zero,0x2d; bne a3,a4 *)
  step. step. rewrite zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth BL RS NUL)) 45) as [E45|E45]; cbn [negb]; cbv beta iota.
  { eapply rc_minus_ok; [right; exact E45 | rc_weq ..]. }
  (* 0x143dc addi a3,zero,1 *)
  step.
  pose proof (rc_sign_at RS BL) as HSG.
  rewrite (proj2 (Z.eqb_neq _ _) E43), (proj2 (Z.eqb_neq _ _) E45) in HSG. cbn [orb] in HSG.
  eapply (rc_sgn_done _ _ _ _ _ _ _ _ _ _ _ _ _ _ false 0 HSG ltac:(lia)); rc_weq.
Qed.

(** ** The blanks loop 0x1439c .. 0x143b8 (fuzz_headamp.c:70-72) at byte i <= BL *)
Definition rc_blank_P (i : nat) : Prop :=
  forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word),
  (i <= BL)%nat ->
  t1 = Z_to_bv 64 9 -> t2 = Z_to_bv 64 10 -> t3 = Z_to_bv 64 RC_BIG ->
  a0 = Z_to_bv 64 (K + 13) -> a1 = Z_to_bv 64 (Z.of_nat i) -> a2 = Z_to_bv 64 (2^64 - 1 - (K + 13)) ->
  a5 = Z_to_bv 64 5 -> a6 = Z_to_bv 64 32 ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x1439c) fc None m (seg_rom rsegs)).

(** 0x143ac .. 0x143b0: a blank at i: i + 1, and rest + i + 1 does not wrap (trap 0x143b4 not taken). *)
Lemma rc_blank_back : forall i (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word),
  (S i <= BL)%nat -> rc_blank_P (S i) ->
  t1 = Z_to_bv 64 9 -> t2 = Z_to_bv 64 10 -> t3 = Z_to_bv 64 RC_BIG ->
  a0 = Z_to_bv 64 (K + 13) -> a1 = Z_to_bv 64 (Z.of_nat i) -> a2 = Z_to_bv 64 (2^64 - 1 - (K + 13)) ->
  a5 = Z_to_bv 64 5 -> a6 = Z_to_bv 64 32 ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x143ac) fc None m (seg_rom rsegs)).
Proof.
  intros i t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 Hs HP -> -> -> -> -> -> -> ->.
  pose proof (rc_blanks_le RS) as Hbl. pose proof rc_len as LRS. pose proof HKW as HW. pose proof HKL as HL13.
  (* 0x143ac addi a1,a1,1; bgeu a2,a1 *)
  step. step. rewrite ltu_u by lia. if_true.
  eapply HP; [exact Hs | rc_weq ..].
Qed.

Lemma rc_blank_ok : forall L i, (length RS - i <= L)%nat -> rc_blank_P i.
Proof.
  induction L as [|L IH]; intros i HL;
    assert (IHH : (S i <= BL)%nat -> rc_blank_P (S i))
      by (intros Hs; pose proof (rc_blanks_le RS) as Hbl; first [exfalso; lia | apply IH; lia]);
    unfold rc_blank_P; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 Hi -> -> -> -> -> -> -> ->;
    pose proof (rc_blanks_le RS) as Hbl; pose proof rc_len as LRS; pose proof HKW as HW; pose proof HKL as HL13.
  all: (* 0x1439c add a3,a0,a1; lbu a3,0(a3); addi a4,a3,-9; bgeu a4,a5 *)
    step; pose proof (rc_byte i ltac:(lia)) as HR; step; clear HR; step; step;
    rewrite zxb_add_ltu by lia;
    pose proof (rc_blank_code (nth i RS NUL)) as BC;
    destruct ((0 <=? bv_unsigned (nth i RS NUL) + -9) && (bv_unsigned (nth i RS NUL) + -9 <? 5)) eqn:B1;
    rewrite ?B1 in BC; cbn [negb orb] in BC |- *; cbv beta iota.
  all: try solve [eapply (rc_blank_back i);
                  [exact (rc_blanks_go RS i Hi BC) | exact (IHH (rc_blanks_go RS i Hi BC)) | rc_weq ..]].
  all: (* 0x143b8 beq a3,a6 *)
    step; rewrite zxb_eqb by lia;
    destruct (bv_unsigned (nth i RS NUL) =? 32) eqn:B2; rewrite ?B2 in BC; cbv beta iota.
  all: try solve [eapply (rc_blank_back i);
                  [exact (rc_blanks_go RS i Hi BC) | exact (IHH (rc_blanks_go RS i Hi BC)) | rc_weq ..]].
  all: pose proof (rc_blanks_stop RS i Hi BC) as Ei; subst i; eapply rc_sign_ok; rc_weq.
Qed.

(** ** 0x14374 .. 0x14398: the constants, the k + 13 check (trap 0x1438c not taken), rest and ~rest *)
Lemma rc_entry : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 : word),
  bytes_at rsegs m (bv_unsigned sp + 0x88) (le8 (Z_to_bv 64 RC_BIG)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 K)
                       t3 t4 t5 t6) F (Z_to_bv 64 0x14374) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 H88.
  pose proof rc_len as LRS. pose proof HKW as HW. pose proof HKL as HL13.
  (* 0x14374 addi a0,zero,-0xd; addi a5,zero,5; addi a6,zero,0x20; addi t1,zero,9; addi t2,zero,0xa;
     ld t3,0x88(sp) *)
  step. step. step. step. step.
  pose proof (read_le8 rsegs m (bv_unsigned sp + 0x88) _ H88) as HR. step. clear HR.
  (* 0x1438c bgeu s11,a0 *)
  step. unfold bv_ltu. rewrite (unsigned_lit K) by lia. if_false.
  (* 0x14390 mv a1,zero; addi a0,s11,0xd; not a2,a0 *)
  step. step. step. rewrite (unsigned_lit (K + 13)) by lia. rewrite zb_lxor_ones by lia.
  eapply (rc_blank_ok (length RS) 0 ltac:(lia)); [lia | rc_weq ..].
Qed.

End RcWalk.

Theorem rc_holds : rc_stmt.
Proof.
  unfold rc_stmt.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m K k
    -> HKB _ HKL HK0 HKW H88 HQ.
  eapply rc_entry; eassumption.
Qed.
