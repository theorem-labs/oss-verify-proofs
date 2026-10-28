(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import PrintfModelA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope list_scope.

Definition FMT_emit : list Z := [37; 100; 10; 0].
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0].
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].
Definition FMT_precond : list Z := str "p11-kit: '%s' not true at %s" ++ [10; 0].
Definition FMT_unreached : list Z := str "p11-kit: shouldn't be reached at %s" ++ [10; 0].
Definition FMT_msg : list Z := str "%s:%zu: %s" ++ [0].

Definition pieces_emit (i : Z) : list (list Z) :=
  if i =? 0 then [[]; []; [48]; []; [10]]
  else if i <? 0 then [[]; [45]; dec_digits (- i); [10]]
  else [[]; []; dec_digits i; [10]].
Definition pieces_msg (file : list Z) (line : Z) (msg : list Z) : list (list Z) :=
  [ []; []; file; [58]; []; [] ] ++ (if line =? 0 then [[48]; []] else [dec_digits line]) ++ [ str ": "; []; []; msg ].

Example pieces_emit_ex0 : printf_pieces FMT_emit [PA_i 0] = Some (pieces_emit 0, 2).
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_ex1 : printf_pieces FMT_emit [PA_i (-2147483648)] = Some (pieces_emit (-2147483648), 12).
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_ex2 : printf_pieces FMT_emit [PA_i 7] = Some (pieces_emit 7, 2).
Proof. vm_compute. reflexivity. Qed.
Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some ([ str "usage: "; []; []; str "prog"; str " INPUT" ++ [10] ], 18).
Proof. vm_compute. reflexivity. Qed.
Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some ([ str "cli: cannot open "; []; []; str "f"; [10] ], 19).
Proof. vm_compute. reflexivity. Qed.
Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some ([ str "cli: read error on "; []; []; str "f"; [10] ], 21).
Proof. vm_compute. reflexivity. Qed.
Example pieces_too_big_ex : printf_pieces FMT_too_big [PA_u 67108864] = Some ([ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ], 38).
Proof. vm_compute. reflexivity. Qed.
Example pieces_precond_ex : printf_pieces FMT_precond [PA_s (str "lexer != NULL"); PA_s (str "p11_lexer_next")]
                            = Some ([ str "p11-kit: '"; []; []; str "lexer != NULL"; str "' not true at "; []; []; str "p11_lexer_next"; [10] ], 52).
Proof. vm_compute. reflexivity. Qed.
Example pieces_unreached_ex : printf_pieces FMT_unreached [PA_s (str "p11_lexer_next")]
                              = Some ([ str "p11-kit: shouldn't be reached at "; []; []; str "p11_lexer_next"; [10] ], 48).
Proof. vm_compute. reflexivity. Qed.
Example pieces_msg_ex1 : printf_pieces FMT_msg [PA_s (str "fuzz-input"); PA_z 12; PA_s (str "invalid field line: no colon")]
                         = Some (pieces_msg (str "fuzz-input") 12 (str "invalid field line: no colon"), 43).
Proof. vm_compute. reflexivity. Qed.
Example pieces_msg_ex2 : printf_pieces FMT_msg [PA_sn; PA_z 0; PA_s (str "x")]
                         = Some ([[]; []; str "(null)"; [58]; []; []; [48]; []; str ": "; []; []; str "x"], 11).
Proof. vm_compute. reflexivity. Qed.
Example pieces_msg_ex3 : printf_pieces FMT_msg [PA_sn; PA_z (2^64-1); PA_s []]
                         = Some ([[]; []; str "(null)"; [58]; []; []; str "18446744073709551615"; str ": "; []; []; []], 29).
Proof. vm_compute. reflexivity. Qed.
Example pass1_ok_ex : map pass1_ok [FMT_emit; FMT_usage; FMT_too_big; FMT_cannot_open; FMT_read_error; FMT_precond; FMT_unreached; FMT_msg]
                      = repeat true 8.
Proof. vm_compute. reflexivity. Qed.

Example unmodelled_ex : (printf_pieces (str "%zd" ++ [0]) [PA_z 1], printf_pieces (str "%g" ++ [0]) [PA_g 0], parse_dir (str "zx" ++ [0])) = (None, None, None).
Proof. vm_compute. reflexivity. Qed.

Lemma digits_aux_S : forall f b d y acc,
  digits_aux (S f) b d y acc = if y =? 0 then acc else digits_aux f b d (y / b) (d (y mod b) :: acc).
Proof. reflexivity. Qed.
Lemma digits_aux_acc : forall f b d y acc, digits_aux f b d y acc = digits_aux f b d y [] ++ acc.
Proof.
  induction f as [|f IH]; intros b d y acc; [reflexivity|]. rewrite !digits_aux_S.
  destruct (y =? 0)%Z; [reflexivity|]. rewrite (IH _ _ _ (d (y mod b)%Z :: acc)), (IH _ _ _ [d (y mod b)%Z]). rewrite <- app_assoc. reflexivity.
Qed.
Lemma digits_aux_fuel : forall b f d y acc, (1 < b)%Z -> (0 <= y < b ^ Z.of_nat f)%Z ->
  digits_aux f b d y acc = digits_aux (S f) b d y acc.
Proof.
  intros b. induction f as [|f IH]; intros d y acc Hb Hy.
  - rewrite digits_aux_S. rewrite Z.pow_0_r in Hy. replace y with 0%Z by lia. reflexivity.
  - rewrite !digits_aux_S. destruct (Z.eqb_spec y 0); [reflexivity|].
    apply IH; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hy by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. reflexivity. Qed.
Lemma dec_digits_small : forall x, (1 <= x <= 9)%Z -> dec_digits x = [48 + x]%Z.
Proof.
  intros x Hx. unfold dec_digits. change 20%nat with (S (S 18)). rewrite !digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite Z.div_small by lia. cbn [Z.eqb]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec_digits_step : forall x, (10 <= x < 2^64)%Z -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10]%Z.
Proof.
  intros x Hx. unfold dec_digits at 1. change 20%nat with (S 19). rewrite digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold dec_digits. apply digits_aux_fuel; [lia|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  apply Z.lt_trans with (2^64)%Z; [lia|]. vm_compute. reflexivity.
Qed.
Lemma digits_aux_length : forall f b d y acc, (Datatypes.length (digits_aux f b d y acc) <= f + Datatypes.length acc)%nat.
Proof.
  induction f as [|f IH]; intros b d y acc; [cbn; lia|]. rewrite digits_aux_S.
  destruct (y =? 0)%Z; [cbn; lia|]. specialize (IH b d (y / b)%Z (d (y mod b)%Z :: acc)). cbn [Datatypes.length] in IH. lia.
Qed.
Lemma dec_digits_length : forall x, (Datatypes.length (dec_digits x) <= 20)%nat.
Proof. intros x. unfold dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v)%Z x []) as L. cbn [Datatypes.length Nat.add] in L. exact L. Qed.
Lemma dec_digits_nz : forall x, (1 <= x < 2^64)%Z -> dec_digits x <> [].
Proof.
  intros x Hx. destruct (Z_lt_le_dec x 10).
  - rewrite dec_digits_small by lia. discriminate.
  - rewrite dec_digits_step by lia. intros E. apply app_eq_nil in E. destruct E as [_ E]. discriminate.
Qed.
Lemma dec_digits_zlength : forall x, 0 <= zlength (dec_digits x) <= 20.
Proof. intros x. unfold zlength. pose proof (dec_digits_length x). lia. Qed.
