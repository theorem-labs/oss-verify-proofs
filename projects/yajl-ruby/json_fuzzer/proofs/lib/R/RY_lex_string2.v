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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMalloc_iface RYajlRep RYajl_iface RY_lib RY_lex_kit RY_lex_string RY_lex_string_u8.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex YajlFactsDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

(* [comment removed for export] *)
Lemma str_loop : forall (fuel : nat) (esc : bool) (rav s0v s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off < zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evt rsegs (str_post K m0 e start (ylex_string_loop fuel 1 (k_txt K) (zlength (k_txt K)) off esc))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start)
          (wz 92) (wz 117) (wz 34) (wz (Z.b2z esc)) (wz RY_CHARTAB) t3 t4 t5 t6)
        (k_F K) (wz 0x14538) (k_fc K) None m (seg_rom rsegs)).
Proof.
  induction fuel as [|fuel IH]; intros until start; intros TX0 LM BO FUEL; [lia|].
  (* [comment removed for export] *)
  assert (CONT : forall esc' o ms1, str_at K m0 J_STR esc' e o start ms1 -> off < o <= zlength (k_txt K) ->
            evt rsegs (str_post K m0 e start (ylex_string_loop fuel 1 (k_txt K) (zlength (k_txt K)) o esc')) ms1).
  { intros esc' o ms1 (rav' & s0' & s1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & LM1) BO1.
    pose proof LM1 as (MU & WM & MI & STK & FR & OFF & LX & BC).
    pose proof ENV as ENV'. lex_prep ENV' BC. unfold J_STR, RY_CHARTAB.
    zstep. rewrite ?ysx32_small by lia. zstep. if_cases KC; zify_cond KC.
    - eapply IH; [exact TX0| exact LM1| lia| lia].
    - zstep. destruct fuel as [|fuel']; cbn [ylex_string_loop];
        [| replace (zlength (k_txt K) <=? o) with true by (symmetry; apply Z.leb_le; lia)]; cbn [str_post err_upd]; fin_at. }
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). pose proof ENV as ENV0. lex_prep ENV0 BC. unfold RY_CHARTAB.
  cbn [ylex_string_loop].
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  rdchar MU TX0 off.
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
    replace (znth (k_txt K) off =? c_bslash) with true by (symmetry; apply Z.eqb_eq; unfold c_bslash; lia).
    eapply evt_cut; [eapply (escape_walk K ENV); [exact TX0| fin_lexmem| lia]|].
    intros ms1 HE. unfold esc_model in HE.
    destruct (Z.leb_spec (zlength (k_txt K)) (off + 1)).
    { cbn [esc_post] in HE. apply evt_done. exact HE. }
    cbv zeta in HE.
    destruct (Z.eqb_spec (znth (k_txt K) (off + 1)) c_u).
    + pose proof (ylex_hex4_spec 4 (k_txt K) (zlength (k_txt K)) (off + 2) ltac:(lia)) as HX.
      replace (off + 1 + 1) with (off + 2) in HE by lia.
      destruct (ylex_hex4 4 (k_txt K) (zlength (k_txt K)) (off + 2)) as [o|o|o]; cbn [esc_post] in HE.
      * eapply CONT; [exact HE| cbn in HX; lia].
      * apply evt_done. exact HE.
      * apply evt_done. exact HE.
    + replace (off + 1 + 1) with (off + 2) in HE by lia.
      destruct (is_vec (znth (k_txt K) (off + 1))); cbn [esc_post] in HE.
      * eapply CONT; [exact HE| lia].
      * apply evt_done. exact HE.
  - replace (znth (k_txt K) off =? c_bslash) with false by (symmetry; apply Z.eqb_neq; unfold c_bslash; lia).
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? c_quote) with true by (symmetry; apply Z.eqb_eq; unfold c_quote; lia).
      cbn [str_post err_upd]. destruct esc; cbn [Z.b2z]; zstep; zstep; zstep; fin_at.
    + replace (znth (k_txt K) off =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
      rdclt MI (znth (k_txt K) off).
      zstep. zstep. if_cases K3; zify_cond K3.
      * (* [comment removed for export] *)
        assert (HJ : is_ijc (znth (k_txt K) off) = true).
        { pose proof (clt_ijc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_neq _ _) K3) in X. destruct (is_ijc _); [reflexivity| discriminate X]. }
        rewrite HJ. cbn [str_post err_upd lex_error_code tok_code].
        unread. zstep. zstep. zstep. replace (off + 1 + -1) with off in OFF by lia.
        eapply (str_c78 K ENV). fin_lexmem.
      * assert (HJ : is_ijc (znth (k_txt K) off) = false).
        { pose proof (clt_ijc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_eq _ _) K3) in X. destruct (is_ijc _); [discriminate X| reflexivity]. }
        rewrite HJ. cbn [Z.eqb negb].
        eapply evt_cut; [eapply (utf8_walk K ENV esc); [exact TX0| fin_lexmem| lia| lia]|].
        intros ms1 HU.
        pose proof (ylex_utf8_char_bounds (k_txt K) (zlength (k_txt K)) (off + 1) (znth (k_txt K) off) ltac:(lia)) as UB.
        destruct (ylex_utf8_char (k_txt K) (zlength (k_txt K)) (off + 1) (znth (k_txt K) off)) as [o|o|o]; cbn [u8_post] in HU.
        -- eapply CONT; [exact HU| lia].
        -- cbn [str_post err_upd]. apply evt_done. exact HU.
        -- cbn [str_post err_upd lex_error_code tok_code]. apply evt_done. exact HU.
Qed.

Lemma str_post_sub : forall m0 e start r ms,
  str_post K m0 e start r ms ->
  sub_post K m0 e start (let '(tok, o, err, esc) := r in
                         (match tok with TK_string => if esc then TK_string_esc else TK_string | t => t end, o, err)) ms.
Proof.
  intros m0 e start [[[tok o] err] esc] ms H. destruct tok; try exact H.
  cbn in H |- *. destruct esc; exact H.
Qed.

(* [comment removed for export] *)
Lemma lex_string_walk : forall (rav s0v s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (sub_post K m0 e start (ylex_string 1 (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14518) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC).
  pose proof ENV as ENV0. lex_prep ENV0 BC.
  unfold ylex_string.
  eofchk K0.
  - unfold lex_fuel. cbn [ylex_string_loop].
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd]. fin_at.
  - zstep. zstep. zstep. zstep. zstep. zstep.
    change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.b2z false)).
    eapply evt_mono; [eapply (str_loop (lex_fuel (zlength (k_txt K)) off) false); [exact TX0| fin_lexmem| lia| unfold lex_fuel; lia]|].
    intros ms Hs. apply str_post_sub in Hs.
    destruct (ylex_string_loop _ _ _ _ _ _) as [[[tok o] err] esc]. exact Hs.
Qed.
End S.
End RC__1.
