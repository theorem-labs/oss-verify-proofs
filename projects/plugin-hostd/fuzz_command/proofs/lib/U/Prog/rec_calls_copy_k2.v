From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c memcpy_c rec_calls_copy_k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma k2_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  destruct (Z.ltb_spec x (2 ^ 63)); [|lia]. destruct (Z.ltb_spec y (2 ^ 63)); [|lia]. reflexivity.
Qed.

Lemma k2_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite (unsigned_lit x), (unsigned_lit y) by lia. reflexivity. Qed.

Lemma k2_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Section K2.
Variables (sw dw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 : word)
  (F : bvmap 5 word) (fc : bv 32).
Variable n : nat.
Hypothesis HOK : KOK sw dw n.

Lemma k_tail_next : forall (Q : machine_state -> Prop) (i : nat) m,
  (S i < n)%nat -> rw_cells rsegs m (bv_unsigned sw + -128) (FRL dw) ->
  st_head sw dw gp tp F fc n Q (S i) m -> st_tl sw dw gp tp F fc n Q i m.
Proof using HOK.
  intros Q i m Hi FL HK.
  pose proof HOK as HK0. unfold KOK in HK0. destruct HK0 as (HN & HSW & HDW & HDN).
  unfold st_tl. intros y1 y5 y6 y7 y8 y9 y10 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31.
  unfold SPW, S7, S8. unfold FRL in FL.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  do 5 step.
  rewrite k2_lts by lia.
  replace (Z.of_nat i + 1 <? Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  apply evt_done.
  unfold st_head, head_ms, SPW, S7, S8 in HK.
  replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
  replace (Z_to_bv 64 (0x34040 + 56 * Z.of_nat i + 56)) with (Z_to_bv 64 (0x34040 + 56 * Z.of_nat (S i)))
    by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i + 56))
    with (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat (S i))) by (f_equal; lia).
  apply HK.
Qed.

Lemma k_tail_last : forall (Q : machine_state -> Prop) (i : nat) m,
  (S i = n)%nat -> rw_cells rsegs m (bv_unsigned sw + -128) (FRL dw) ->
  rw_cells rsegs m (bv_unsigned sw + -104)
    (FRS ra0 s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0) ->
  st_ret sw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 F fc n Q m ->
  st_tl sw dw gp tp F fc n Q i m.
Proof using HOK.
  intros Q i m Hi FL FS HK.
  pose proof HOK as HK0. unfold KOK in HK0. destruct HK0 as (HN & HSW & HDW & HDN).
  unfold st_tl. intros y1 y5 y6 y7 y8 y9 y10 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31.
  unfold SPW, S7, S8. unfold FRL in FL. unfold FRS in FS.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  do 5 step.
  rewrite k2_lts by lia.
  replace (Z.of_nat i + 1 <? Z.of_nat n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
  do 16 step.
  replace (Z_to_bv 64 (bv_unsigned sw + -128 + 128)) with sw by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  apply evt_done.
  exact (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_after_next : forall (Q : machine_state -> Prop) (i j : nat) (str : list byte) (len : Z) (pw : word)
    (p nargs : Z) (junk jj : list byte) y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m,
  memcpy_contract ->
  (i < n)%nat -> Z.of_nat (S j) < nargs <= 6 -> Z.of_nat (length str) = len ->
  0 < p -> p + (len + 1) <= bv_unsigned sw - 128 ->
  mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned pw) (str ++ [Z_to_bv 8 0]) ->
  (bv_unsigned pw + (len + 1) <= p \/ p + (len + 1) <= bv_unsigned pw) ->
  rw_cells rsegs m p [CB (Z.to_nat (len + 1)) junk] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i + 4) [C4 (Z_to_bv 64 nargs)] ->
  rw_cells rsegs m (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [CB 8 jj] ->
  (forall m', rw_cells rsegs m' p [CB (Z.to_nat (len + 1)) (str ++ [Z_to_bv 8 0])] ->
     rw_cells rsegs m' (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 (Z_to_bv 64 p)] ->
     rw_cells rsegs m' (bv_unsigned dw + 56 * Z.of_nat i + 4) [C4 (Z_to_bv 64 nargs)] ->
     munch [(p, p + (len + 1));
            (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
             bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' ->
     st_lp sw dw gp tp F fc Q i (S j) m') ->
  evt rsegs Q (af_ms sw dw gp tp F fc i j len pw p y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m).
Proof using HOK.
  intros Q i j str len pw p nargs junk jj y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m
    MC Hi Hj HL P0 PS MI SRC SEP DST NC SL HK.
  pose proof HOK as HK0. unfold KOK in HK0. destruct HK0 as (HN & HSW & HDW & HDN).
  unfold af_ms, SPW, N4, N9, S7, S8.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  pose proof (zr_word pw) as Rpw. unfold inr64 in Rpw.
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 (len + 1)) = len + 1) by (apply unsigned_lit; lia).
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  remember (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Z8 eqn:HZ8.
  pose proof (munch_refl [(p, p + (len + 1)); (Z8, Z8 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  call (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (str ++ [Z_to_bv 8 0]) junk).
  1: exact SRC.
  1: rewrite UL, length_app; cbn [length]; lia.
  1: rewrite UP, UL; exact DST.
  1: rewrite UP, UL; lia.
  1: exact MI.
  rewrite ?UP, ?UL in *.
  step.
  rewrite k2_ltu by lia.
  match goal with |- context [?a <? ?b] => replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) end.
  cbn [negb].
  step.
  rewrite k2_sx32 by lia.
  step.
  rewrite <- HZ8.
  do 4 step.
  rewrite k2_lts by lia.
  replace (Z.of_nat j + 1 <? nargs) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  subst X Z8.
  replace (Z_to_bv 64 (Z.of_nat j + 1)) with (Z_to_bv 64 (Z.of_nat (S j))) by (f_equal; lia).
  replace (Z_to_bv 64 (8 * Z.of_nat j + 8)) with (Z_to_bv 64 (8 * Z.of_nat (S j))) by (f_equal; lia).
  unfold st_lp, lp_ms, SPW, N4, N9, S7, S8 in HK.
  eapply HK; eassumption.
Qed.

Lemma k_after_last : forall (Q : machine_state -> Prop) (i j : nat) (str : list byte) (len : Z) (pw : word)
    (p nargs : Z) (junk jj : list byte) y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m,
  memcpy_contract ->
  (i < n)%nat -> Z.of_nat (S j) = nargs -> nargs <= 6 -> Z.of_nat (length str) = len ->
  0 < p -> p + (len + 1) <= bv_unsigned sw - 128 -> (p + (len + 1) <= 0x34030 \/ 0x34034 <= p) ->
  mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned pw) (str ++ [Z_to_bv 8 0]) ->
  (bv_unsigned pw + (len + 1) <= p \/ p + (len + 1) <= bv_unsigned pw) ->
  rw_cells rsegs m p [CB (Z.to_nat (len + 1)) junk] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i + 4) [C4 (Z_to_bv 64 nargs)] ->
  rw_cells rsegs m (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [CB 8 jj] ->
  rw_cells rsegs m 0x34030 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  (forall m', rw_cells rsegs m' p [CB (Z.to_nat (len + 1)) (str ++ [Z_to_bv 8 0])] ->
     rw_cells rsegs m' (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 (Z_to_bv 64 p)] ->
     rw_cells rsegs m' (bv_unsigned dw + 56 * Z.of_nat i + 4) [C4 (Z_to_bv 64 nargs)] ->
     rw_cells rsegs m' 0x34030 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
     munch [(p, p + (len + 1));
            (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
             bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' ->
     st_tl sw dw gp tp F fc n Q i m') ->
  evt rsegs Q (af_ms sw dw gp tp F fc i j len pw p y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m).
Proof using HOK.
  intros Q i j str len pw p nargs junk jj y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m
    MC Hi Hj Hn HL P0 PS PG MI SRC SEP DST NC SL GN HK.
  pose proof HOK as HK0. unfold KOK in HK0. destruct HK0 as (HN & HSW & HDW & HDN).
  unfold af_ms, SPW, N4, N9, S7, S8.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  pose proof (zr_word pw) as Rpw. unfold inr64 in Rpw.
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 (len + 1)) = len + 1) by (apply unsigned_lit; lia).
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  remember (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Z8 eqn:HZ8.
  pose proof (munch_refl [(p, p + (len + 1)); (Z8, Z8 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  call (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (str ++ [Z_to_bv 8 0]) junk).
  1: exact SRC.
  1: rewrite UL, length_app; cbn [length]; lia.
  1: rewrite UP, UL; exact DST.
  1: rewrite UP, UL; lia.
  1: exact MI.
  rewrite ?UP, ?UL in *.
  step.
  rewrite k2_ltu by lia.
  match goal with |- context [?a <? ?b] => replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) end.
  cbn [negb].
  step.
  rewrite k2_sx32 by lia.
  step.
  rewrite <- HZ8.
  do 4 step.
  rewrite k2_lts by lia.
  replace (Z.of_nat j + 1 <? nargs) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
  do 2 step.
  rewrite k2_sx32 by lia.
  subst X Z8.
  unfold st_tl, SPW, S7, S8 in HK.
  eapply HK; eassumption.
Qed.

End K2.
