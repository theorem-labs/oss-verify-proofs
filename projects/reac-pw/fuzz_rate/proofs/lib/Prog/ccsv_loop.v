(** check_csv's outer loop (plain image), 0x14788 .. 0x14820: pass i (0, 1, 2) leaves csv_prefix mask (i + 1) at the
    start of want (Pod/RateCsv.v, csv_prefix_S); a clear bit skips to 0x14818 (`beqz t4`), a set bit runs
    ccsv_pass_set; then `addi a0, a0, 1; bne a0, a4` with a4 = 3. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import ccsv_lem ccsv_pass.
Import ListNotations.
Open Scope Z_scope.

Definition ccsv_combo_b (i n : Z) : bool :=
  ((i =? 0) && (n =? 0)) || ((i =? 1) && ((n =? 0) || (n =? 5)))
  || ((i =? 2) && ((n =? 0) || (n =? 5) || (n =? 11))).

Lemma ccsv_combo_b_ok : forall i n, ccsv_combo_b i n = true -> ccsv_combo i n.
Proof.
  intros i n H. unfold ccsv_combo_b in H. unfold ccsv_combo.
  repeat match goal with
  | H : _ || _ = true |- _ => apply orb_true_iff in H; destruct H as [H|H]
  | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end; lia.
Qed.

(** n = |csv_prefix mask i| is 0 for i = 0, 0 or 5 for i = 1, 0, 5 or 11 for i = 2 (computation on mask mod 8). *)
Lemma ccsv_combo_prefix : forall X i, 0 <= X -> 0 <= i < 3 ->
  ccsv_combo i (Z.of_nat (length (csv_prefix X (Z.to_nat i)))).
Proof.
  intros X i HX Hi. apply ccsv_combo_b_ok. rewrite csv_prefix_bits by lia.
  assert (0 <= X mod 8 < 8) as H by (apply Z.mod_pos_bound; lia).
  assert (C : X mod 8 = 0 \/ X mod 8 = 1 \/ X mod 8 = 2 \/ X mod 8 = 3 \/ X mod 8 = 4 \/
              X mod 8 = 5 \/ X mod 8 = 6 \/ X mod 8 = 7) by lia.
  assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
  destruct Hi3 as [-> | [-> | ->]]; destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; reflexivity.
Qed.

Section CCSV.
Variables (ra gp tp s0 s1 e2 e3 e4 s5 s6 s7 s8 s9 s10 s11 bufw lenw a1 a3 : word) (F : bvmap 5 word) (fc : bv 32)
  (Sp lo : Z) (m0 : word -> option byte) (Q : machine_state -> Prop).
Hypothesis RS0 : 0 <= Sp + -96.
Hypothesis RS1 : Sp <= 2^64.

Local Abbreviation SV := (ccsv_SV ra s0 s1 e2 e3 e4).
Local Abbreviation CS := (ccsv_CS ra gp tp bufw lenw a1 a3 s5 s6 s7 s8 s9 s10 s11 F fc Sp).

Lemma ccsv_pass : forall i (m : word -> option byte) (dj wj : list byte) (y18 y19 y20 y29 y30 y31 : word),
  0 <= i < 3 ->
  rw_cells rsegs m (Sp + -96) (CB 8 dj :: CB 40 (csv_bytes (csv_prefix (bv_unsigned a3) (Z.to_nat i)) ++ wj) :: SV) ->
  munch [(Sp + -96, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (Sp + -96) ->
  (forall (m' : word -> option byte) (dj' wj' : list byte) (z18 z19 z20 z29 z30 z31 : word),
     rw_cells rsegs m' (Sp + -96)
       (CB 8 dj' :: CB 40 (csv_bytes (csv_prefix (bv_unsigned a3) (Z.to_nat (i + 1))) ++ wj') :: SV) ->
     munch [(Sp + -96, Sp)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> stk rsegs m' lo (Sp + -96) ->
     evt rsegs Q (CS 0x14818 i (Z.of_nat (length (csv_prefix (bv_unsigned a3) (Z.to_nat (i + 1)))))
                     z18 z19 z20 z29 z30 z31 m')) ->
  evt rsegs Q (CS 0x14788 i (Z.of_nat (length (csv_prefix (bv_unsigned a3) (Z.to_nat i)))) y18 y19 y20 y29 y30 y31 m).
Proof.
  intros i m dj wj y18 y19 y20 y29 y30 y31 Hi FR MU WM MI ST K.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3. unfold bv_modulus in Ra3.
  assert (EP : csv_prefix (bv_unsigned a3) (Z.to_nat (i + 1)) =
    if Z.testbit (bv_unsigned a3) i
    then csv_prefix (bv_unsigned a3) (Z.to_nat i)
         ++ (match csv_prefix (bv_unsigned a3) (Z.to_nat i) with [] => [] | _ :: _ => [44] end)
         ++ csv_dec (nth (Z.to_nat i) closed_list 0)
    else csv_prefix (bv_unsigned a3) (Z.to_nat i)).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite csv_prefix_S. rewrite Z2Nat.id by lia.
    reflexivity. }
  rewrite EP in K.
  destruct (Z.testbit (bv_unsigned a3) i) eqn:HB; cbv beta iota in K.
  - (* bit i set *)
    pose proof (ccsv_combo_prefix (bv_unsigned a3) i ltac:(lia) Hi) as HC.
    set (P := csv_prefix (bv_unsigned a3) (Z.to_nat i)) in *.
    assert (ET : csv_bytes (P ++ (match P with [] => [] | _ :: _ => [44] end) ++ csv_dec (nth (Z.to_nat i) closed_list 0))
                 = csv_bytes P ++ ccsv_T i (Z.of_nat (length P))).
    { rewrite csv_bytes_app. f_equal. unfold ccsv_T. f_equal. f_equal. destruct P; reflexivity. }
    assert (EN : Z.of_nat (length (P ++ (match P with [] => [] | _ :: _ => [44] end)
                                     ++ csv_dec (nth (Z.to_nat i) closed_list 0)))
                 = Z.of_nat (length P) + Z.of_nat (length (ccsv_T i (Z.of_nat (length P))))).
    { rewrite <- (csv_bytes_length (P ++ _)), ET, length_app, csv_bytes_length. lia. }
    rewrite ET, EN in K. clearbody P.
    eapply (ccsv_pass_set ra gp tp s0 s1 e2 e3 e4 s5 s6 s7 s8 s9 s10 s11 bufw lenw a1 a3 F fc Sp lo m0 Q RS0 RS1
              i (Z.of_nat (length P)) m dj (csv_bytes P) wj);
      [ exact HC | exact HB | rewrite csv_bytes_length; lia | exact FR | exact MU | exact WM | exact MI | exact ST | ].
    intros m' dj' wj' z18 z19 z20 z29 z30 z31 FR' MU' WM' MI' ST'.
    eapply K; eassumption.
  - (* bit i clear: srlw, andi, beqz -> 0x14818 *)
    unfold ccsv_CS, ccsv_SV in *.
    cstep. cstep. cstep.
    rewrite (unsigned_lit i) by lia. rewrite ccsv_bit by lia. rewrite HB. if_true.
    eapply K; eassumption.
Qed.

Lemma ccsv_loop : forall (m : word -> option byte) (dj wj : list byte) (y18 y19 y20 y29 y30 y31 : word),
  rw_cells rsegs m (Sp + -96) (CB 8 dj :: CB 40 wj :: SV) ->
  munch [(Sp + -96, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (Sp + -96) ->
  (forall (m' : word -> option byte) (dj' wj' : list byte) (z18 z19 z20 z29 z30 z31 : word),
     rw_cells rsegs m' (Sp + -96) (CB 8 dj' :: CB 40 (csv_bytes (csv_list (bv_unsigned a3)) ++ wj') :: SV) ->
     munch [(Sp + -96, Sp)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> stk rsegs m' lo (Sp + -96) ->
     evt rsegs Q (CS 0x14820 3 (Z.of_nat (length (csv_list (bv_unsigned a3)))) z18 z19 z20 z29 z30 z31 m')) ->
  evt rsegs Q (CS 0x14788 0 0 y18 y19 y20 y29 y30 y31 m).
Proof.
  intros m dj wj y18 y19 y20 y29 y30 y31 FR MU WM MI ST K.
  change (CS 0x14788 0 0 y18 y19 y20 y29 y30 y31 m)
    with (CS 0x14788 0 (Z.of_nat (length (csv_prefix (bv_unsigned a3) (Z.to_nat 0)))) y18 y19 y20 y29 y30 y31 m).
  change wj with (csv_bytes (csv_prefix (bv_unsigned a3) (Z.to_nat 0)) ++ wj) in FR.
  eapply (ccsv_pass 0 m dj wj); [lia | exact FR | exact MU | exact WM | exact MI | exact ST | ].
  intros m1 dj1 wj1 z18 z19 z20 z29 z30 z31 FR1 MU1 WM1 MI1 ST1.
  unfold ccsv_CS. cstep. cstep. cbr.
  eapply (ccsv_pass 1 m1 dj1 wj1); [lia | exact FR1 | exact MU1 | exact WM1 | exact MI1 | exact ST1 | ].
  intros m2 dj2 wj2 x18 x19 x20 x29 x30 x31 FR2 MU2 WM2 MI2 ST2.
  unfold ccsv_CS. cstep. cstep. cbr.
  eapply (ccsv_pass 2 m2 dj2 wj2); [lia | exact FR2 | exact MU2 | exact WM2 | exact MI2 | exact ST2 | ].
  intros m3 dj3 wj3 w18 w19 w20 w29 w30 w31 FR3 MU3 WM3 MI3 ST3.
  unfold ccsv_CS. cstep. cstep. cbr.
  eapply K; eassumption.
Qed.

End CCSV.
