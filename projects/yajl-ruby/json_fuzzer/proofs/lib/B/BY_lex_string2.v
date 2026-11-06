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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_number RY_lex_string RY_lex_string_u8.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_ubkit BY_rz BY_lex_rdck BY_lex_rdck2 BY_lex_kit BY_lex_string1 BY_lex_string_u8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
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

Ltac pols := polu KP kp_imgsh PIMGSH; polu KP kp_img PIMG; polu KP kp_Ls PLS; polu KP kp_L PL; polu KP kp_T PT;
             polu KP kp_Hs PHS; polu KP kp_H PH; polu KP kp_stk PSTK.
Ltac prep LM BC := pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC); lex_prep ENV BC; unfold AY_CHARTAB in *; pols.

Lemma str_loop : forall (fuel : nat) (esc : bool) (rav s1v s2v s6v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k56 : word)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k56 (wz (k_L K + 36)) (wz 3) -> 0 <= off < zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  0 <= e <= 11 ->
  evtA bsegs (k_P K) (str_post K m0 e start (ylex_string_loop fuel 1 (k_txt K) (zlength (k_txt K)) off esc))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) s1v a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) s6v (wz (k_T K)) (wz (zlength (k_txt K))) (wz (Z.b2z esc)) (wz ASB) s11v
          t3 t4 t5 t6)
        (k_F K) (wz J_SBODY) (k_fc K) None m (seg_rom bsegs)).
Proof. aceil.
  induction fuel as [|fuel IH]; intros until start; intros LM BO FUEL ER; [lia|].
  (* [comment removed for export] *)
  assert (CONT : forall esc' o ms1, astr_at K m0 J_STR esc' e o start ms1 -> off < o <= zlength (k_txt K) ->
            evtA bsegs (k_P K) (str_post K m0 e start (ylex_string_loop fuel 1 (k_txt K) (zlength (k_txt K)) o esc')) ms1).
  { intros esc' o ms1 (rav' & s1' & s2' & s6' & s11' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & k56' & m1 & -> & LM1) BO1.
    pose proof LM1 as (MU & WM & MI & ST & FR & OFF & LX & BC). lex_prep ENV BC. unfold J_STR, J_SBODY, AY_CHARTAB in *. pols.
    eofchkA K m0 ENV SH MU WM KC.
    - eapply IH; [exact LM1| lia| lia| lia].
    - stepA. destruct fuel as [|fuel']; cbn [ylex_string_loop];
        [| replace (zlength (k_txt K) <=? o) with true by (symmetry; apply Z.leb_le; lia)]; cbn [str_post err_upd];
        eapply (str_eof4 K m0); first [exact ENV| exact KP| exact SH| exact LM1]. }
  prep LM BC. unfold J_SBODY.
  assert (EB : 0 <= Z.b2z esc <= 1) by (destruct esc; cbn; lia).
  cbn [ylex_string_loop].
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  rdcharA K m0 ENV KP SH MU WM rdck_10abb4 off.                             (* [comment removed for export] *)
  stepA. zstepA.                                                             (* [comment removed for export] *)
  stepA. zstepA. if_cases K1; zify_cond K1.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
    replace (znth (k_txt K) off =? c_bslash) with true by (symmetry; apply Z.eqb_eq; unfold c_bslash; lia).
    eapply evtA_cut; [eapply (escape_walk K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]|].
    intros ms1 HE. unfold esc_model in HE.
    destruct (Z.leb_spec (zlength (k_txt K)) (off + 1)).
    { cbn [esc_post] in HE. apply evtA_done. exact HE. }
    cbv zeta in HE.
    destruct (Z.eqb_spec (znth (k_txt K) (off + 1)) c_u).
    + pose proof (ylex_hex4_spec 4 (k_txt K) (zlength (k_txt K)) (off + 2) ltac:(lia)) as HX.
      replace (off + 1 + 1) with (off + 2) in HE by lia.
      destruct (ylex_hex4 4 (k_txt K) (zlength (k_txt K)) (off + 2)) as [o|o|o]; cbn [esc_post] in HE.
      * eapply CONT; [exact HE| cbn in HX; lia].
      * apply evtA_done. exact HE.
      * apply evtA_done. exact HE.
    + replace (off + 1 + 1) with (off + 2) in HE by lia.
      destruct (is_vec (znth (k_txt K) (off + 1))); cbn [esc_post] in HE.
      * eapply CONT; [exact HE| lia].
      * apply evtA_done. exact HE.
  - replace (znth (k_txt K) off =? c_bslash) with false by (symmetry; apply Z.eqb_neq; unfold c_bslash; lia).
    stepA. zstepA. if_cases K2; zify_cond K2.                                (* [comment removed for export] *)
    2:{ (* [comment removed for export] *)
      replace (znth (k_txt K) off =? c_quote) with true by (symmetry; apply Z.eqb_eq; unfold c_quote; lia).
      cbn [str_post err_upd].
      stepA. stepA. stepA. stepA.                                            (* [comment removed for export] *)
      eapply (str_finish_tok K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]. }
    replace (znth (k_txt K) off =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
    zstepA. try rewrite (lxor_ones64 136512) by lia. ugd.                    (* [comment removed for export] *)
    zstepA.                                                                  (* [comment removed for export] *)
    rdcltA K m0 ENV SH MU WM MI (znth (k_txt K) off).
    zstepA. zstepA. zstepA. if_cases K3; zify_cond K3.                       (* [comment removed for export] *)
    2:{ (* [comment removed for export] *)
      assert (HJ : is_ijc (znth (k_txt K) off) = true).
      { pose proof (clt_ijc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_neq _ _) K3) in X. destruct (is_ijc _); [reflexivity| discriminate X]. }
      rewrite HJ. cbn [str_post err_upd lex_error_code tok_code].
      stepA.                                                                 (* [comment removed for export] *)
      unread3 K m0 ENV SH MU WM OFF off. stepA. stepA.                       (* [comment removed for export] *)
      eapply (str_err0f8 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]. }
    assert (HJ : is_ijc (znth (k_txt K) off) = false).
    { pose proof (clt_ijc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_eq _ _) K3) in X. destruct (is_ijc _); [discriminate X| reflexivity]. }
    rewrite HJ. cbn [Z.eqb negb].
    zstepA. shadow_addr. zstepA.                                             (* [comment removed for export] *)
    shld (rd_shL K m0 _ ENV SH MU WM 36 ltac:(lia)). zstepA. iflit.          (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia.                                     (* [comment removed for export] *)
    zstepA. if_cases KV; zify_cond KV. 1:{ kill KV. } clear KV.              (* [comment removed for export] *)
    eapply evtA_cut; [eapply (utf8_walk K m0 ENV KP SH esc); [fin_lexmem| lia| lia| lia]|].
    intros ms1 HU.
    pose proof (ylex_utf8_char_bounds (k_txt K) (zlength (k_txt K)) (off + 1) (znth (k_txt K) off) ltac:(lia)) as UB.
    destruct (ylex_utf8_char (k_txt K) (zlength (k_txt K)) (off + 1) (znth (k_txt K) off)) as [o|o|o]; cbn [u8_post] in HU.
    + eapply CONT; [exact HU| lia].
    + cbn [str_post err_upd]. apply evtA_done. exact HU.
    + cbn [str_post err_upd lex_error_code tok_code]. apply evtA_done. exact HU.
Qed.

Lemma str_post_sub : forall e start r ms,
  str_post K m0 e start r ms ->
  sub_post K m0 e start (let '(tok, o, err, esc) := r in
                         (match tok with TK_string => if esc then TK_string_esc else TK_string | t => t end, o, err)) ms.
Proof. aceil.
  intros e start [[[tok o] err] esc] ms H. destruct tok; try exact H.
  cbn in H |- *. destruct esc; exact H.
Qed.

(* [comment removed for export] *)
Lemma lex_string_proof : lex_string_stmt K m0.
Proof. aceil.
  unfold lex_string_stmt. intros until start. intros LM BS BO ER. prep LM BC. unfold J_STRE.
  unfold ylex_string.
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.            (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K0; zify_cond K0.    (* [comment removed for export] *)
  2:{ stepA. unfold lex_fuel. cbn [ylex_string_loop].
      replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd]. fin_at. }
  stepA. zstepA. zstepA. zstoreA ENV.                                        (* [comment removed for export] *)
  change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.b2z false)) at 1.
  eapply evtA_mono; [eapply (str_loop (lex_fuel (zlength (k_txt K)) off) false); [fin_lexmem| lia| unfold lex_fuel; lia| lia]|].
  intros ms Hs. apply str_post_sub in Hs.
  destruct (ylex_string_loop _ _ _ _ _ _) as [[[tok o] err] esc]. exact Hs.
Qed.
End S.
End RC__1.
