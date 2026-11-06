(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlFactsLex YajlFactsBuf YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_number RY_lex_main1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_ubkit BY_rz BY_lex_rdck BY_lex_kit BY_lex_kw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac mfalse x y := replace (x =? y) with false by (symmetry; apply Z.eqb_neq; try unfold y; lia).
Ltac mtrue x y := replace (x =? y) with true by (symmetry; apply Z.eqb_eq; try unfold y; lia).
(* [comment removed for export] *)
Ltac lia_cheap_lk := LiaTuning.zify_prune; first [ LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Ltac mfalse_c x y := replace (x =? y) with false by (symmetry; apply Z.eqb_neq; try unfold y; lia_cheap_lk).
Ltac mtrue_c x y := replace (x =? y) with true by (symmetry; apply Z.eqb_eq; try unfold y; lia_cheap_lk).
Ltac mnav c IA :=
  repeat (first
    [ match goal with |- context [c =? ?y] => first [ mfalse_c c y | mtrue_c c y | mtrue c y | mfalse c y ] end
    | match goal with |- context [is_lex_ws c] => first [ rewrite (is_lex_ws_false c) by lia | match goal with W : is_lex_ws c = true |- _ => rewrite W end ] end
    | match goal with |- context [is_digit c] => first [ rewrite (is_digit_true c) by lia | rewrite (is_digit_false c) by lia ] end
    | match goal with |- context [lx_allowComments _ =? 0] => rewrite IA; change (1 =? 0) with false end ];
    cbv beta iota zeta).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : alexK.
Variable m0 : mem.
Hypothesis ENV : kenvA K.
Hypothesis KP : kpolA K.
Hypothesis SH : alexsh K m0.

Definition loop_post (fuel : nat) (lx : ylexer) (off start : Z) : machine_state -> Prop :=
  fun ms' => exists lx1 tok off1 start1,
    yleaf (ylex_loop fuel lx (k_txt K) (zlength (k_txt K)) off start) (lx1, tok, off1, start1)
    /\ lex_inv lx1
    /\ tok_post K m0 tok (lex_error_code (lx_error lx1)) off1 start1 ms'.

(* [comment removed for export] *)
Lemma loop_step_leaf : forall (fuel : nat) (lx : ylexer) (off start : Z),
  0 <= off -> off < zlength (k_txt K) ->
  forall r, yleaf (let c := znth (k_txt K) off in let off1 := off + 1 in if c =? c_lbrace then YRet (lx, TK_left_bracket, off1, start) else if c =? c_rbrace then YRet (lx, TK_right_bracket, off1, start) else if c =? c_lbracket then YRet (lx, TK_left_brace, off1, start) else if c =? c_rbracket then YRet (lx, TK_right_brace, off1, start) else if c =? c_comma then YRet (lx, TK_comma, off1, start) else if c =? c_colon then YRet (lx, TK_colon, off1, start) else if is_lex_ws c then ylex_loop fuel lx (k_txt K) (zlength (k_txt K)) off1 (start + 1) else if c =? c_t then match ylex_want want_rue (k_txt K) (zlength (k_txt K)) off1 with | W_ok o => YRet (lx, TK_bool, o, start) | W_eof o => YRet (lx, TK_eof, o, start) | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start) end else if c =? c_f then match ylex_want want_alse (k_txt K) (zlength (k_txt K)) off1 with | W_ok o => YRet (lx, TK_bool, o, start) | W_eof o => YRet (lx, TK_eof, o, start) | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start) end else if c =? c_n then match ylex_want want_ull (k_txt K) (zlength (k_txt K)) off1 with | W_ok o => YRet (lx, TK_null, o, start) | W_eof o => YRet (lx, TK_eof, o, start) | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start) end else if c =? c_quote then let '(tok, o, err) := ylex_string (lx_validateUTF8 lx) (k_txt K) (zlength (k_txt K)) off1 in YRet (lx_set_error_opt lx err, tok, o, start) else if (c =? c_minus) || is_digit c then let '(tok, o, err) := ylex_number (k_txt K) (zlength (k_txt K)) off in YRet (lx_set_error_opt lx err, tok, o, start) else if c =? c_slash then if lx_allowComments lx =? 0 then YRet (lx_set_error lx LE_unallowed_comment, TK_error, off, start) else let '(tok, o, err) := ylex_comment (k_txt K) (zlength (k_txt K)) off1 in match tok with | TK_comment => (b' <- ybuf_clear (lx_buf lx) ;; ylex_loop fuel (lx_set_buf lx b' (lx_bufOff lx) 0) (k_txt K) (zlength (k_txt K)) o o) | _ => YRet (lx_set_error_opt lx err, tok, o, start) end else YRet (lx_set_error lx LE_invalid_char, TK_error, off1, start)) r ->
  yleaf (ylex_loop (S fuel) lx (k_txt K) (zlength (k_txt K)) off start) r.
Proof. aceil.
  intros fuel lx off start BO0 K0.
  intros r Hr. rewrite ylex_loop_S. unfold yassert. replace (off <=? zlength (k_txt K)) with true by (symmetry; apply Z.leb_le; lia). cbn [ybind]. replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia). exact Hr.
Qed.

(* [comment removed for export] *)
Definition loop_walk_at (fuel : nat) : Prop :=
  forall (lx : ylexer) (rav s2v s6v s9v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k112 : word) (m : mem) (off start : Z),
  lex_inv lx ->
  alexmem K m0 m (lex_error_code (lx_error lx)) off start (wz ((k_L K + 32) / 8 + ASB)) (wz (k_L K + 32)) k112 ->
  0 <= start <= off -> off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evtA bsegs (k_P K) (loop_post fuel lx off start)
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz 0) (wz off) a1 a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) s6v (wz (k_T K)) (wz (zlength (k_txt K))) s9v (wz ASB) (wz AY_JT_LEX)
          t3 t4 t5 t6)
        (k_F K) (wz J_HD) (k_fc K) None m (seg_rom bsegs)).

(* [comment removed for export] *)
Ltac leaf MS1 IA c lx1 tok o st1 :=
  apply evtA_done; cbv beta; unfold loop_post; exists lx1, tok, o, st1;
  split; [ apply MS1; mnav c IA; apply yl_ret
        | split; [ first [ assumption | apply lex_inv_set_error; assumption ]
                 | cbn [tok_post lex_error_code lx_error lx_set_error tok_code]; fin_at ] ].

(* [comment removed for export] *)
Ltac errchar K m0 ENV SH MU WM :=
  stepA; zstepA; zstepA; zstepA; shadow_addr; zstepA;                  (* [comment removed for export] *)
  shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)); zstepA; try if_true;   (* [comment removed for export] *)
  stepA; stepA; zstoreA ENV; stepA.                                     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lex_hi_walk : forall (fuel : nat) (lx : ylexer) (rav s2v s6v s9v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m : mem) (off start : Z),
  lex_inv lx ->
  alexmem K m0 m (lex_error_code (lx_error lx)) (off + 1) start (wz ((k_L K + 32) / 8 + ASB)) (wz (k_L K + 32)) (wz 3) ->
  0 <= start <= off -> off < zlength (k_txt K) -> 90 < znth (k_txt K) off -> 0 <= znth (k_txt K) off < 256 ->
  evtA bsegs (k_P K) (loop_post (S fuel) lx off start)
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz 0) (wz (znth (k_txt K) off)) a1 a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) s6v (wz (k_T K)) (wz (zlength (k_txt K))) s9v (wz ASB) (wz AY_JT_LEX)
          t3 t4 t5 t6)
        (k_F K) (wz 0x83a18) (k_fc K) None m (seg_rom bsegs)).
Proof. aceil.
  intros until start; intros LI LM BS K0 K1 CR.
  pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC). lex_prep ENV BC. unfold AY_JT_LEX.
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  pose proof (lex_error_code_range (lx_error lx)) as ER.
  pose proof (loop_step_leaf fuel lx off start ltac:(lia) K0) as MS1. cbv zeta in MS1.
  set (c := znth (k_txt K) off) in *.
  polu KP kp_Ls PLS. polu KP kp_L PL. polu KP kp_stk PSTK.
  stepA. zstepA. if_cases K2; zify_cond K2; rewrite ?signed_small in K2 by lia.    (* [comment removed for export] *)
  - (* [comment removed for export] *)
    stepA. zstepA. if_cases K3; zify_cond K3.                                        (* [comment removed for export] *)
    + stepA. zstepA. if_cases K4; zify_cond K4.                                      (* [comment removed for export] *)
      * stepA. zstepA. if_cases K5; zify_cond K5.                                    (* [comment removed for export] *)
        -- (* [comment removed for export] *)
           clear PLS PL PSTK.
           eapply evtA_mono; [eapply (lex_kw_alse K m0 ENV KP SH); [exact LM| lia| lia| lia]|].
           intros ms Hs. unfold loop_post.
           destruct (ylex_want want_alse (k_txt K) (zlength (k_txt K)) (off + 1)) as [o|o|o] eqn:EW; cbn [kw_post] in Hs.
           ++ exists lx, TK_bool, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
           ++ exists lx, TK_eof, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
           ++ exists (lx_set_error lx LE_invalid_string), TK_error, o, start.
              split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [apply lex_inv_set_error; exact LI| exact Hs]].
        -- (* [comment removed for export] *)
           errchar K m0 ENV SH MU WM.
           leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
      * stepA. stepA. stepA. leaf MS1 IA c lx TK_right_brace (off + 1) start.    (* [comment removed for export] *)
    + stepA. stepA. stepA. leaf MS1 IA c lx TK_left_brace (off + 1) start.       (* [comment removed for export] *)
  - stepA. zstepA. if_cases K3; zify_cond K3; rewrite ?signed_small in K3 by lia.  (* [comment removed for export] *)
    + (* [comment removed for export] *)
      stepA. zstepA. if_cases K4; zify_cond K4.                                      (* [comment removed for export] *)
      * stepA. zstepA. if_cases K5; zify_cond K5.                                    (* [comment removed for export] *)
        -- stepA. stepA. leaf MS1 IA c lx TK_right_bracket (off + 1) start.      (* [comment removed for export] *)
        -- errchar K m0 ENV SH MU WM.
           leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
      * stepA. stepA. stepA. leaf MS1 IA c lx TK_left_bracket (off + 1) start.   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      stepA. zstepA. if_cases K4; zify_cond K4.                                      (* [comment removed for export] *)
      * stepA. zstepA. if_cases K5; zify_cond K5.                                    (* [comment removed for export] *)
        -- (* [comment removed for export] *)
           clear PLS PL PSTK.
           eapply evtA_mono; [eapply (lex_kw_rue K m0 ENV KP SH); [exact LM| lia| lia| lia]|].
           intros ms Hs. unfold loop_post.
           destruct (ylex_want want_rue (k_txt K) (zlength (k_txt K)) (off + 1)) as [o|o|o] eqn:EW; cbn [kw_post] in Hs.
           ++ exists lx, TK_bool, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
           ++ exists lx, TK_eof, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
           ++ exists (lx_set_error lx LE_invalid_string), TK_error, o, start.
              split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [apply lex_inv_set_error; exact LI| exact Hs]].
        -- errchar K m0 ENV SH MU WM.
           leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
      * (* [comment removed for export] *)
        stepA. clear PLS PL PSTK.
        eapply evtA_mono; [eapply (lex_kw_ull K m0 ENV KP SH); [exact LM| lia| lia| lia]|].
        intros ms Hs. unfold loop_post.
        destruct (ylex_want want_ull (k_txt K) (zlength (k_txt K)) (off + 1)) as [o|o|o] eqn:EW; cbn [kw_post] in Hs.
        ++ exists lx, TK_null, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
        ++ exists lx, TK_eof, o, start. split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [exact LI| exact Hs]].
        ++ exists (lx_set_error lx LE_invalid_string), TK_error, o, start.
           split; [apply MS1; mnav c IA; rewrite ?EW; apply yl_ret| split; [apply lex_inv_set_error; exact LI| exact Hs]].
Qed.
End S.
End RC__1.
