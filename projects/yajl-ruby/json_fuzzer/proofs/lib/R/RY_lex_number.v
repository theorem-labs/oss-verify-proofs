(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMalloc_iface RYajlRep RYajl_iface RY_lib RY_lex_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex YajlFactsDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition num_res : Type := (Z * Z * ytok) + (ytok * Z * option lex_error).

(* [comment removed for export] *)
Definition num_tail (ex : num_res) : ytok * Z * option lex_error :=
  match ex with inr res => res | inl (c, off, tok) => (tok, off - 1, None) end.

(* [comment removed for export] *)
Definition num_exp (txt : list Z) (len off : Z) : num_res :=
  match read1 txt len off with
  | RD_eof => inr (TK_eof, len, @None lex_error)
  | RD_char c off =>
      let r := if (c =? c_plus) || (c =? c_minus) then read1 txt len off else RD_char c off in
      match r with
      | RD_eof => inr (TK_eof, len, None)
      | RD_char c off =>
          if is_digit c then
            match read_past_digits (lex_fuel len off) txt len off with
            | RD_eof => inr (TK_eof, len, None)
            | RD_char c off => inl (c, off, TK_double)
            end
          else inr (TK_error, off - 1, Some LE_missing_integer_after_exponent)
      end
  end.

(* [comment removed for export] *)
Definition num_echeck (txt : list Z) (len c off : Z) (tok : ytok) : ytok * Z * option lex_error :=
  num_tail (if (c =? c_e) || (c =? c_E) then num_exp txt len off else inl (c, off, tok)).

(* [comment removed for export] *)
Definition num_frac (txt : list Z) (len off : Z) : num_res :=
  match read1 txt len off with
  | RD_eof => inr (TK_eof, len, @None lex_error)
  | RD_char c off =>
      if is_digit c then
        match read_past_digits (lex_fuel len off) txt len off with
        | RD_eof => inr (TK_eof, len, None)
        | RD_char c off => inl (c, off, TK_double)
        end
      else inr (TK_error, off - 1, Some LE_missing_integer_after_decimal)
  end.

(* [comment removed for export] *)
Definition num_dotcheck (txt : list Z) (len c off : Z) : ytok * Z * option lex_error :=
  match (if c =? c_dot then num_frac txt len off else inl (c, off, TK_integer)) with
  | inr res => res
  | inl (c, off, tok) => num_echeck txt len c off tok
  end.

(* [comment removed for export] *)
Definition num_after_first (txt : list Z) (len c off : Z) : ytok * Z * option lex_error :=
  match (if c =? c_0 then Some (read1 txt len off)
         else if (c_1 <=? c) && (c <=? c_9) then Some (read_past_digits (lex_fuel len off) txt len off)
         else None) with
  | None => (TK_error, off - 1, Some LE_missing_integer_after_minus)
  | Some RD_eof => (TK_eof, len, None)
  | Some (RD_char c off) => num_dotcheck txt len c off
  end.

Lemma ylex_number_eq : forall txt len off0,
  ylex_number txt len off0 =
  match read1 txt len off0 with
  | RD_eof => (TK_eof, off0, None)
  | RD_char c off =>
      match (if c =? c_minus then read1 txt len off else RD_char c off) with
      | RD_eof => (TK_eof, len, None)
      | RD_char c off => num_after_first txt len c off
      end
  end.
Proof.
  intros txt len off0. unfold ylex_number, num_after_first, num_dotcheck, num_echeck, num_frac, num_exp, num_tail.
  destruct (read1 txt len off0) as [|c off]; [reflexivity|].
  destruct (if c =? c_minus then read1 txt len off else RD_char c off) as [|c1 off1]; [reflexivity|].
  destruct (if c1 =? c_0 then _ else _) as [[|c2 off2]|]; [reflexivity| |reflexivity].
  destruct (c2 =? c_dot).
  - destruct (read1 txt len off2) as [|c3 off3]; [reflexivity|].
    destruct (is_digit c3); [|reflexivity].
    destruct (read_past_digits _ _ _ _) as [|c4 off4]; [reflexivity|].
    destruct ((c4 =? c_e) || (c4 =? c_E)); [|reflexivity].
    destruct (read1 txt len off4) as [|c5 off5]; reflexivity.
  - destruct ((c2 =? c_e) || (c2 =? c_E)); [|reflexivity].
    destruct (read1 txt len off2) as [|c5 off5]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land223_eE : forall c, 0 <= c < 256 -> (Z.land c 223 =? 69) = (c =? c_e) || (c =? c_E).
Proof.
  intros c Hc. unfold c_e, c_E.
  pose proof (byte_forall (fun c => Bool.eqb (Z.land c 223 =? 69) ((c =? 101) || (c =? 69))) ltac:(vm_compute; reflexivity) c Hc) as H.
  cbn beta in H. apply Bool.eqb_prop in H. exact H.
Qed.

Lemma sub_mod64 : forall c k, 0 <= c < 2^32 -> 0 <= k < 2^32 ->
  (c + - k) mod 2^64 = (if k <=? c then c - k else c - k + 2^64).
Proof.
  intros c k Hc Hk. destruct (Z.leb_spec k c).
  - apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
Qed.

Lemma land64_sub : forall c k, 0 <= c < 2^32 -> - 2^32 < k <= 0 ->
  Z.land (c + k) 18446744073709551615 = (if - k <=? c then c + k else c + k + 2^64).
Proof.
  intros c k Hc Hk. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  replace (c + k) with (c + - (- k)) by lia. rewrite sub_mod64 by lia.
  destruct (Z.leb_spec (- k) c); lia.
Qed.

Lemma is_digit_true : forall c, 48 <= c <= 57 -> is_digit c = true.
Proof. intros c H. unfold is_digit, c_0, c_9. apply andb_true_iff. split; apply Z.leb_le; lia. Qed.
Lemma is_digit_false : forall c, c < 48 \/ 57 < c -> is_digit c = false.
Proof.
  intros c H. unfold is_digit, c_0, c_9.
  destruct (Z.leb_spec 48 c); destruct (Z.leb_spec c 57); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
End RC__1.
Ltac digk K :=
  rewrite ?land64_sub in K by lia;
  repeat match type of K with context [if ?k <=? ?c then _ else _] => destruct (Z.leb_spec k c) end; try lia.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

(* [comment removed for export] *)
Definition dig_post (m0 : mem) (e start : Z) (P : Z -> Z -> machine_state -> Prop) (r : rdres) : machine_state -> Prop :=
  match r with
  | RD_eof => fun ms' => exists s0v, lex_at K m0 J_EOF s0v e (zlength (k_txt K)) start ms'
  | RD_char c o => P c o
  end.

(* [comment removed for export] *)
Lemma num_final : forall (rav s1v s7v s8v s9v s10v s11v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start tokc : Z),
  lexmem K m0 m e off -> 0 < off <= zlength (k_txt K) ->
  evt rsegs (lex_at K m0 J_TOK (wz tokc) e (off - 1) start)
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz tokc) s1v (wz off) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14db0) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until tokc. intros (MU & WM & MI & STK & FR & OFF & LX & BC) BO.
  lex_prep ENV BC.
  zstep. if_cases K0; zify_cond K0. 1:{ kill K0. } clear K0.
  zstep. zstep. zstep.
  replace (off + -1) with (off - 1) in OFF by lia. fin_at.
Qed.


(* [comment removed for export] *)
Lemma exp_loop : forall (fuel : nat) (rav s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evt rsegs (dig_post m0 e start (fun c o => lex_at K m0 J_TOK (wz 11) e (o - 1) start)
               (read_past_digits fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 10) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14d3c) (k_fc K) None m (seg_rom rsegs)).
Proof.
  induction fuel as [|fuel IH]; intros until start; intros TX0 LM BO FUEL; [lia|].
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  cbn [read_past_digits]. unfold read1.
  eofchk K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [dig_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    zstep. zstep. if_cases K1; zify_cond K1; digk K1.
    + rewrite (is_digit_true (znth (k_txt K) off)) by lia.
      eapply IH; [exact TX0| fin_lexmem| lia| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      zstep. rewrite ?ysx32_small by lia. zstep.
      eapply num_final; [fin_lexmem| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      zstep. rewrite ?ysx32_small by lia. zstep.
      eapply num_final; [fin_lexmem| lia].
Qed.
Lemma dig_post_exp : forall m0 e start r ms,
  dig_post m0 e start (fun c o => lex_at K m0 J_TOK (wz 11) e (o - 1) start) r ms ->
  sub_post K m0 e start (num_tail (match r with RD_eof => inr (TK_eof, zlength (k_txt K), @None lex_error)
                                              | RD_char c o => inl (c, o, TK_double) end)) ms.
Proof. intros m0 e start [|c o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma num_expdig_walk : forall (rav s0v s1v s7v s8v s9v s10v s11v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e o1 start c1 : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e o1 -> 0 < o1 <= zlength (k_txt K) -> 0 <= c1 < 256 ->
  evt rsegs (sub_post K m0 e start (num_tail
        (if is_digit c1 then
           match read_past_digits (lex_fuel (zlength (k_txt K)) o1) (k_txt K) (zlength (k_txt K)) o1 with
           | RD_eof => inr (TK_eof, zlength (k_txt K), None)
           | RD_char c off => inl (c, off, TK_double)
           end
         else inr (TK_error, o1 - 1, Some LE_missing_integer_after_exponent))))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v (wz c1) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14d2c) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until c1. intros TX0 LM BO CR1. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  zstep. zstep. zstep. if_cases K4; zify_cond K4; digk K4.
  - rewrite (is_digit_false c1) by lia. cbn [num_tail sub_post err_upd lex_error_code tok_code].
    unread. zstep. zstep. zstep. zstep. zstep. replace (o1 + -1) with (o1 - 1) in OFF by lia. fin_at.
  - rewrite (is_digit_false c1) by lia. cbn [num_tail sub_post err_upd lex_error_code tok_code].
    unread. zstep. zstep. zstep. zstep. zstep. replace (o1 + -1) with (o1 - 1) in OFF by lia. fin_at.
  - rewrite (is_digit_true c1) by lia.
    zstep. eapply evt_mono; [eapply (exp_loop (lex_fuel (zlength (k_txt K)) o1)); [exact TX0| fin_lexmem| lia| unfold lex_fuel; lia]|].
    intros ms Hs. exact (dig_post_exp _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
Lemma num_exp_walk : forall (rav s0v s1v s7v s8v s9v s10v s11v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (sub_post K m0 e start (num_tail (num_exp (k_txt K) (zlength (k_txt K)) off)))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v (wz off) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14adc) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  unfold num_exp, read1.
  zstep. if_cases K0; zify_cond K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [num_tail sub_post err_upd].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    zstep. zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      replace ((znth (k_txt K) off =? c_plus) || (znth (k_txt K) off =? c_minus)) with true
        by (symmetry; apply orb_true_iff; right; apply Z.eqb_eq; unfold c_minus; lia).
      eofchk K2.
      * replace (zlength (k_txt K) <=? off + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [num_tail sub_post err_upd].
        assert (E : off + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
      * replace (zlength (k_txt K) <=? off + 1) with false by (symmetry; apply Z.leb_gt; lia).
        rdchar MU TX0 (off + 1).
        eapply num_expdig_walk; [exact TX0| fin_lexmem| lia| lia].
    + zstep. zstep. if_cases K2; zify_cond K2.
      * (* [comment removed for export] *)
        replace ((znth (k_txt K) off =? c_plus) || (znth (k_txt K) off =? c_minus)) with false
          by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; unfold c_plus, c_minus; lia).
        eapply num_expdig_walk; [exact TX0| fin_lexmem| lia| lia].
      * (* [comment removed for export] *)
        replace ((znth (k_txt K) off =? c_plus) || (znth (k_txt K) off =? c_minus)) with true
          by (symmetry; apply orb_true_iff; left; apply Z.eqb_eq; unfold c_plus; lia).
        eofchk K3.
        -- replace (zlength (k_txt K) <=? off + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [num_tail sub_post err_upd].
           assert (E : off + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
        -- replace (zlength (k_txt K) <=? off + 1) with false by (symmetry; apply Z.leb_gt; lia).
           rdchar MU TX0 (off + 1).
           eapply num_expdig_walk; [exact TX0| fin_lexmem| lia| lia].
Qed.
End S.
End RC__2.
