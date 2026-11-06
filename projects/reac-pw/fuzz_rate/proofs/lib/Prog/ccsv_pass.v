(** One pass of check_csv's outer loop (plain image) for a set bit, 0x14788 .. 0x14818: load closed_list[i], the
    do-while digit loop 0x147a8-0x147dc writes the digits to d[] backwards, then "," at want[n] when n > 0 and the
    copy loop 0x14804-0x14814 appends the digits to want. The rate and n are concrete in each case, so the walk
    steps the code as it runs. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import ccsv_lem.
Import ListNotations.
Open Scope Z_scope.

(** What a pass for a set bit appends to want: "," when want is not empty, then the decimal digits of the rate. *)
Definition ccsv_T (i n : Z) : list byte :=
  csv_bytes ((if n =? 0 then [] else [44]) ++ csv_dec (nth (Z.to_nat i) closed_list 0)).

(** The (i, n) pairs a set bit meets: n = |csv_prefix mask i| is 0, 5 or 11. *)
Definition ccsv_combo (i n : Z) : Prop :=
  (i = 0 /\ n = 0) \/ (i = 1 /\ (n = 0 \/ n = 5)) \/ (i = 2 /\ (n = 0 \/ n = 5 \/ n = 11)).

Section CCSV.
Variables (ra gp tp s0 s1 e2 e3 e4 s5 s6 s7 s8 s9 s10 s11 bufw lenw a1 a3 : word) (F : bvmap 5 word) (fc : bv 32)
  (Sp lo : Z) (m0 : word -> option byte) (Q : machine_state -> Prop).
Hypothesis RS0 : 0 <= Sp + -96.
Hypothesis RS1 : Sp <= 2^64.

Local Abbreviation SV := (ccsv_SV ra s0 s1 e2 e3 e4).
Local Abbreviation CS := (ccsv_CS ra gp tp bufw lenw a1 a3 s5 s6 s7 s8 s9 s10 s11 F fc Sp).

Lemma ccsv_pass_set : forall i n (m : word -> option byte) (dj Pb wj : list byte) (y18 y19 y20 y29 y30 y31 : word),
  ccsv_combo i n -> Z.testbit (bv_unsigned a3) i = true -> length Pb = Z.to_nat n ->
  rw_cells rsegs m (Sp + -96) (CB 8 dj :: CB 40 (Pb ++ wj) :: SV) ->
  munch [(Sp + -96, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (Sp + -96) ->
  (forall (m' : word -> option byte) (dj' wj' : list byte) (z18 z19 z20 z29 z30 z31 : word),
     rw_cells rsegs m' (Sp + -96) (CB 8 dj' :: CB 40 ((Pb ++ ccsv_T i n) ++ wj') :: SV) ->
     munch [(Sp + -96, Sp)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> stk rsegs m' lo (Sp + -96) ->
     evt rsegs Q (CS 0x14818 i (n + Z.of_nat (length (ccsv_T i n))) z18 z19 z20 z29 z30 z31 m')) ->
  evt rsegs Q (CS 0x14788 i n y18 y19 y20 y29 y30 y31 m).
Proof.
  intros i n m dj Pb wj y18 y19 y20 y29 y30 y31 HC HB LP FR MU WM MI ST K.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3. unfold bv_modulus in Ra3.
  unfold ccsv_CS, ccsv_SV in *.
  remember (Pb ++ wj) as X eqn:EX.
  destruct HC as [[-> ->]|[[-> [-> | ->]]|[-> [-> | [-> | ->]]]]];
    (cstep; cstep; cstep; rewrite ccsv_bit by lia; rewrite HB; if_false; run_to 0x14818);
    lazymatch goal with
    | LP : length ?Pb = Z.to_nat 0 |- _ =>
        destruct Pb; [|discriminate]; ccsv_join K 6%nat; reflexivity
    | _ =>
        ccsv_join K 8%nat; subst X; rewrite firstn_app_len by exact LP; rewrite <- !app_assoc; reflexivity
    end.
Qed.

End CCSV.
