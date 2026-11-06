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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_lex_kit UY_lex_kw UY_lex_comment UY_lex_number UY_lex_number2 UY_lex_string UY_lex_string_u8 UY_lex_string2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlFactsLex YajlFactsBuf YajlFactsDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma ylex_loop_S : forall fuel lx txt len off start,
  ylex_loop (S fuel) lx txt len off start =
  (yassert (off <=? len) ;;;
      if len <=? off then YRet (lx, TK_eof, off, start)
      else
        let c := znth txt off in
        let off1 := off + 1 in
        if c =? c_lbrace then YRet (lx, TK_left_bracket, off1, start)
        else if c =? c_rbrace then YRet (lx, TK_right_bracket, off1, start)
        else if c =? c_lbracket then YRet (lx, TK_left_brace, off1, start)
        else if c =? c_rbracket then YRet (lx, TK_right_brace, off1, start)
        else if c =? c_comma then YRet (lx, TK_comma, off1, start)
        else if c =? c_colon then YRet (lx, TK_colon, off1, start)
        else if is_lex_ws c then ylex_loop fuel lx txt len off1 (start + 1)
        else if c =? c_t then
          match ylex_want want_rue txt len off1 with
          | W_ok o => YRet (lx, TK_bool, o, start)
          | W_eof o => YRet (lx, TK_eof, o, start)
          | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start)
          end
        else if c =? c_f then
          match ylex_want want_alse txt len off1 with
          | W_ok o => YRet (lx, TK_bool, o, start)
          | W_eof o => YRet (lx, TK_eof, o, start)
          | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start)
          end
        else if c =? c_n then
          match ylex_want want_ull txt len off1 with
          | W_ok o => YRet (lx, TK_null, o, start)
          | W_eof o => YRet (lx, TK_eof, o, start)
          | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start)
          end
        else if c =? c_quote then
          let '(tok, o, err) := ylex_string (lx_validateUTF8 lx) txt len off1 in
          YRet (lx_set_error_opt lx err, tok, o, start)
        else if (c =? c_minus) || is_digit c then
          let '(tok, o, err) := ylex_number txt len off in
          YRet (lx_set_error_opt lx err, tok, o, start)
        else if c =? c_slash then
          if lx_allowComments lx =? 0 then
            YRet (lx_set_error lx LE_unallowed_comment, TK_error, off, start)
          else
            let '(tok, o, err) := ylex_comment txt len off1 in
            match tok with
            | TK_comment =>
                b' <- ybuf_clear (lx_buf lx) ;;
                ylex_loop fuel (lx_set_buf lx b' (lx_bufOff lx) 0) txt len o o
            | _ => YRet (lx_set_error_opt lx err, tok, o, start)
            end
        else YRet (lx_set_error lx LE_invalid_char, TK_error, off1, start)).
Proof. reflexivity. Qed.

Lemma is_lex_ws_cases : forall c, is_lex_ws c = true -> (9 <= c <= 13) \/ c = 32.
Proof.
  intros c H. unfold is_lex_ws, c_tab, c_lf, c_vt, c_ff, c_cr, c_sp in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]); apply Z.eqb_eq in H; lia.
Qed.
Lemma is_lex_ws_false : forall c, c < 9 \/ (13 < c /\ c <> 32) -> is_lex_ws c = false.
Proof.
  intros c H. unfold is_lex_ws, c_tab, c_lf, c_vt, c_ff, c_cr, c_sp.
  repeat (apply orb_false_iff; split); apply Z.eqb_neq; lia.
Qed.
Lemma minus_digit_false : forall c, c <> 45 -> (c < 48 \/ 57 < c) -> (c =? c_minus) || is_digit c = false.
Proof.
  intros c H1 H2. apply orb_false_iff. split; [apply Z.eqb_neq; unfold c_minus; lia| apply is_digit_false; exact H2].
Qed.
Lemma minus_digit_cases : forall c, (c =? c_minus) || is_digit c = true -> c = 45 \/ 48 <= c <= 57.
Proof.
  intros c H. apply orb_true_iff in H. destruct H as [H|H].
  - apply Z.eqb_eq in H. unfold c_minus in H. lia.
  - unfold is_digit, c_0, c_9 in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma minus_digit_not : forall c, (c =? c_minus) || is_digit c = false -> c <> 45 /\ (c < 48 \/ 57 < c).
Proof.
  intros c H. apply orb_false_iff in H. destruct H as [H1 H2]. apply Z.eqb_neq in H1. unfold c_minus in H1.
  unfold is_digit, c_0, c_9 in H2. apply andb_false_iff in H2.
  destruct H2 as [H2|H2]; apply Z.leb_gt in H2; lia.
Qed.

(* [comment removed for export] *)
Lemma jt_read_ws : forall m c, mem_inv usegs m -> is_lex_ws c = true ->
  ov_read_bytes usegs m (wa (RY_JT_LEX + 4 * (c - 9))) 4 = Some jt_ws_b.
Proof.
  intros m c MI H. pose proof (is_lex_ws_cases c H). rewrite jt_lex_read by (auto; lia). unfold jt_class. rewrite H. reflexivity.
Qed.
Lemma jt_read_lit : forall m c bs, mem_inv usegs m -> 9 <= c <= 58 -> jt_class c = bs ->
  ov_read_bytes usegs m (wa (RY_JT_LEX + 4 * (c - 9))) 4 = Some bs.
Proof. intros m c bs MI Hc <-. apply jt_lex_read; assumption. Qed.
Lemma jt_read_num : forall m c, mem_inv usegs m -> is_lex_ws c = false -> c <> 34 -> c <> 44 ->
  (c =? c_minus) || is_digit c = true ->
  ov_read_bytes usegs m (wa (RY_JT_LEX + 4 * (c - 9))) 4 = Some jt_num_b.
Proof.
  intros m c MI W Q CM H. pose proof (minus_digit_cases c H).
  rewrite jt_lex_read by (auto; lia). unfold jt_class. rewrite W, H.
  replace (c =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
  replace (c =? c_comma) with false by (symmetry; apply Z.eqb_neq; unfold c_comma; lia). reflexivity.
Qed.
Lemma jt_read_def : forall m c, mem_inv usegs m -> 9 <= c <= 58 -> is_lex_ws c = false -> c <> 34 -> c <> 44 ->
  (c =? c_minus) || is_digit c = false -> c <> 47 -> c <> 58 ->
  ov_read_bytes usegs m (wa (RY_JT_LEX + 4 * (c - 9))) 4 = Some jt_def_b.
Proof.
  intros m c MI Hc W Q CM H SL CO.
  rewrite jt_lex_read by (auto; lia). unfold jt_class. rewrite W, H.
  replace (c =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
  replace (c =? c_comma) with false by (symmetry; apply Z.eqb_neq; unfold c_comma; lia).
  replace (c =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
  replace (c =? c_colon) with false by (symmetry; apply Z.eqb_neq; unfold c_colon; lia). reflexivity.
Qed.

(* [comment removed for export] *)
End RC__1.
Ltac mfalse x y := replace (x =? y) with false by (symmetry; apply Z.eqb_neq; try unfold y; lia).
Ltac mtrue x y := replace (x =? y) with true by (symmetry; apply Z.eqb_eq; try unfold y; lia).

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

Definition tok_post (m0 : mem) (tok : ytok) (e1 off1 start1 : Z) : machine_state -> Prop :=
  match tok with
  | TK_eof => lex_at K m0 J_EOF (wz 3) e1 off1 start1
  | _ => lex_at K m0 J_TOK (wz (tok_code tok)) e1 off1 start1
  end.

Definition loop_post (m0 : mem) (fuel : nat) (lx : ylexer) (off start : Z) : machine_state -> Prop :=
  fun ms' => exists lx1 tok off1 start1,
    yleaf (ylex_loop fuel lx (k_txt K) (zlength (k_txt K)) off start) (lx1, tok, off1, start1)
    /\ lex_inv lx1
    /\ tok_post m0 tok (lex_error_code (lx_error lx1)) off1 start1 ms'.

Lemma sub_post_tok : forall m0 e start tok o err ms,
  sub_post K m0 e start (tok, o, err) ms -> tok_post m0 tok (err_upd e err) o start ms.
Proof. intros m0 e start tok o err ms H. destruct tok; exact H. Qed.

(* [comment removed for export] *)
Ltac lia_cheap_lk := LiaTuning.zify_prune; first [ LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Ltac mfalse_c x y := replace (x =? y) with false by (symmetry; apply Z.eqb_neq; try unfold y; lia_cheap_lk).
Ltac mtrue_c x y := replace (x =? y) with true by (symmetry; apply Z.eqb_eq; try unfold y; lia_cheap_lk).
(* [comment removed for export] *)
Ltac mnav c IA :=
  repeat (first
    [ match goal with |- context [c =? ?y] => first [ mfalse_c c y | mtrue_c c y | mtrue c y | mfalse c y ] end
    | match goal with |- context [is_lex_ws c] => first [ rewrite (is_lex_ws_false c) by lia | match goal with W : is_lex_ws c = true |- _ => rewrite W end ] end
    | match goal with |- context [is_digit c] => first [ rewrite (is_digit_true c) by lia | rewrite (is_digit_false c) by lia ] end
    | match goal with |- context [lx_allowComments _ =? 0] => rewrite IA; change (1 =? 0) with false end ];
    cbv beta iota zeta).

(* [comment removed for export] *)
Lemma loop_step_leaf : forall (fuel : nat) (lx : ylexer) (off start : Z),
  0 <= off -> off < zlength (k_txt K) ->
  forall r, yleaf (let c := znth (k_txt K) off in let off1 := off + 1 in if c =? c_lbrace then YRet (lx, TK_left_bracket, off1, start) else if c =? c_rbrace then YRet (lx, TK_right_bracket, off1, start) else if c =? c_lbracket then YRet (lx, TK_left_brace, off1, start) else if c =? c_rbracket then YRet (lx, TK_right_brace, off1, start) else if c =? c_comma then YRet (lx, TK_comma, off1, start) else if c =? c_colon then YRet (lx, TK_colon, off1, start) else if is_lex_ws c then ylex_loop fuel lx (k_txt K) (zlength (k_txt K)) off1 (start + 1) else if c =? c_t then match ylex_want want_rue (k_txt K) (zlength (k_txt K)) off1 with | W_ok o => YRet (lx, TK_bool, o, start) | W_eof o => YRet (lx, TK_eof, o, start) | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start) end else if c =? c_f then match ylex_want want_alse (k_txt K) (zlength (k_txt K)) off1 with | W_ok o => YRet (lx, TK_bool, o, start) | W_eof o => YRet (lx, TK_eof, o, start) | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start) end else if c =? c_n then match ylex_want want_ull (k_txt K) (zlength (k_txt K)) off1 with | W_ok o => YRet (lx, TK_null, o, start) | W_eof o => YRet (lx, TK_eof, o, start) | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start) end else if c =? c_quote then let '(tok, o, err) := ylex_string (lx_validateUTF8 lx) (k_txt K) (zlength (k_txt K)) off1 in YRet (lx_set_error_opt lx err, tok, o, start) else if (c =? c_minus) || is_digit c then let '(tok, o, err) := ylex_number (k_txt K) (zlength (k_txt K)) off in YRet (lx_set_error_opt lx err, tok, o, start) else if c =? c_slash then if lx_allowComments lx =? 0 then YRet (lx_set_error lx LE_unallowed_comment, TK_error, off, start) else let '(tok, o, err) := ylex_comment (k_txt K) (zlength (k_txt K)) off1 in match tok with | TK_comment => (b' <- ybuf_clear (lx_buf lx) ;; ylex_loop fuel (lx_set_buf lx b' (lx_bufOff lx) 0) (k_txt K) (zlength (k_txt K)) o o) | _ => YRet (lx_set_error_opt lx err, tok, o, start) end else YRet (lx_set_error lx LE_invalid_char, TK_error, off1, start)) r ->
  yleaf (ylex_loop (S fuel) lx (k_txt K) (zlength (k_txt K)) off start) r.
Proof.
  intros fuel lx off start BO0 K0.
  intros r Hr. rewrite ylex_loop_S. unfold yassert. replace (off <=? zlength (k_txt K)) with true by (symmetry; apply Z.leb_le; lia). cbn [ybind]. replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia). exact Hr.
Qed.

(* [comment removed for export] *)
Definition loop_walk_at (fuel : nat) : Prop :=
  forall (lx : ylexer) (rav s1v s10v s11v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m0 m : mem) (off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) -> lex_inv lx ->
  lexmem K m0 m (lex_error_code (lx_error lx)) off start ->
  0 <= start <= off -> off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evt usegs (loop_post m0 fuel lx off start)
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 90) s1v (wz off) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz 42)
          (wz RY_JT_LEX) (wz 0) (wz 1) s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14110) (k_fc K) None m (seg_rom usegs)).

(* [comment removed for export] *)
Ltac leaf MS1 IA c lx1 tok o st1 :=
  apply evt_done; cbv beta; unfold loop_post; exists lx1, tok, o, st1;
  split; [ apply MS1; mnav c IA; apply yl_ret
        | split; [ first [ assumption | apply lex_inv_set_error; assumption ]
                 | cbn [tok_post lex_error_code lx_error lx_set_error tok_code]; fin_at ] ].

(* [comment removed for export] *)
Lemma lex_hi_walk : forall (fuel : nat) (lx : ylexer) (rav s1v t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) -> lex_inv lx ->
  lexmem K m0 m (lex_error_code (lx_error lx)) (off + 1) start ->
  0 <= start <= off -> off < zlength (k_txt K) -> 90 < znth (k_txt K) off -> 0 <= znth (k_txt K) off < 256 ->
  evt usegs (loop_post m0 (S fuel) lx off start)
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 90) s1v (wz (znth (k_txt K) off)) (wz (off + k_T K)) a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz 42)
          (wz RY_JT_LEX) (wz 0) (wz 1) (wz 3) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x144f0) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until start; intros TX0 LI LM BS K0 K1 CR.
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). pose proof ENV as ENV0. lex_prep ENV0 BC. unfold RY_JT_LEX.
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  pose proof (lex_error_code_range (lx_error lx)) as ER.
  pose proof (loop_step_leaf fuel lx off start ltac:(lia) K0) as MS1. cbv zeta in MS1.
  set (c := znth (k_txt K) off) in *.
  zstep. zstep. if_cases K2; zify_cond K2; rewrite ?signed_small in K2 by lia.
  * (* [comment removed for export] *)
    zstep. zstep. if_cases K3; zify_cond K3.
    -- zstep. zstep. leaf MS1 IA c lx TK_left_brace (off + 1) start.
    -- zstep. zstep. if_cases K4; zify_cond K4.
       ++ zstep. zstep. leaf MS1 IA c lx TK_right_brace (off + 1) start.
       ++ zstep. zstep. if_cases K5; zify_cond K5.
          ** (* [comment removed for export] *) zstep. zstep. zstep. zstep. leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
          ** (* [comment removed for export] *)
             eapply evt_mono; [eapply (lex_kw_alse K ENV); [exact TX0| fin_lexmem| lia| reflexivity]|].
             intros ms Hs. unfold loop_post.
             destruct (ylex_want want_alse (k_txt K) (zlength (k_txt K)) (off + 1)) as [o|o|o] eqn:EW; cbn [kw_post] in Hs.
             +++ exists lx, TK_bool, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
             +++ exists lx, TK_eof, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
             +++ exists (lx_set_error lx LE_invalid_string), TK_error, o, start.
                 split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [apply lex_inv_set_error; exact LI| exact Hs]].
  * zstep. zstep. if_cases K3; zify_cond K3; rewrite ?signed_small in K3 by lia.
    -- (* [comment removed for export] *)
       zstep. zstep. if_cases K4; zify_cond K4.
       ++ zstep. zstep. leaf MS1 IA c lx TK_left_bracket (off + 1) start.
       ++ zstep. zstep. if_cases K5; zify_cond K5.
          ** zstep. zstep. zstep. zstep. leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
          ** zstep. zstep. leaf MS1 IA c lx TK_right_bracket (off + 1) start.
    -- (* [comment removed for export] *)
       zstep. zstep. if_cases K4; zify_cond K4.
       ++ (* [comment removed for export] *)
          eapply evt_mono; [eapply (lex_kw_ull K ENV); [exact TX0| fin_lexmem| lia]|].
          intros ms Hs. unfold loop_post.
          destruct (ylex_want want_ull (k_txt K) (zlength (k_txt K)) (off + 1)) as [o|o|o] eqn:EW; cbn [kw_post] in Hs.
          +++ exists lx, TK_null, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
          +++ exists lx, TK_eof, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
          +++ exists (lx_set_error lx LE_invalid_string), TK_error, o, start.
              split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [apply lex_inv_set_error; exact LI| exact Hs]].
       ++ zstep. zstep. if_cases K5; zify_cond K5.
          ** zstep. zstep. zstep. zstep. leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
          ** (* [comment removed for export] *)
             eapply evt_mono; [eapply (lex_kw_rue K ENV); [exact TX0| fin_lexmem| lia]|].
             intros ms Hs. unfold loop_post.
             destruct (ylex_want want_rue (k_txt K) (zlength (k_txt K)) (off + 1)) as [o|o|o] eqn:EW; cbn [kw_post] in Hs.
             +++ exists lx, TK_bool, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
             +++ exists lx, TK_eof, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
             +++ exists (lx_set_error lx LE_invalid_string), TK_error, o, start.
                 split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [apply lex_inv_set_error; exact LI| exact Hs]].
Qed.
End S.
End RC__2.
