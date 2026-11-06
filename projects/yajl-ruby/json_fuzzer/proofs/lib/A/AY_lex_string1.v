(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_number RY_lex_string.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_rdck2 AY_lex_kit.
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
Definition J_STR : Z := 0x8447c.
Definition astr_at (K : alexK) (m0 : mem) (pc : Z) (esc : bool) (e off start : Z) : machine_state -> Prop :=
  fun ms' => exists (rav s2v s3v s6v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (k0 : list byte) (k8 : word) (m' : mem),
    ms' = MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
                  s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v (wz (Z.b2z esc)) (wz (zlength (k_txt K))) (wz ASB) (wz (k_L K + 36))
                  (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
             (k_F K) (wz pc) (k_fc K) None m' (seg_rom asegs)
    /\ alexmem K m0 m' e off start k0 k8 (wz AY_CHARTAB).

(* [comment removed for export] *)
Definition str_post (K : alexK) (m0 : mem) (e start : Z) (r : ytok * Z * option lex_error * bool) : machine_state -> Prop :=
  let '(tok, o, err, esc) := r in
  match tok with
  | TK_eof => fun ms' => exists s7v, alex_at K m0 J_EOF s7v (err_upd e err) o start ms'
  | TK_string => alex_at K m0 J_TOK (wz (if esc then 13 else 12)) (err_upd e err) o start
  | _ => alex_at K m0 J_TOK (wz (tok_code tok)) (err_upd e err) o start
  end.
Definition hx_post (K : alexK) (m0 : mem) (e start : Z) (r : hxres) : machine_state -> Prop :=
  match r with
  | HX_ok o => astr_at K m0 J_STR true e o start
  | HX_eof o => fun ms' => exists s7v, alex_at K m0 J_EOF s7v e o start ms'
  | HX_bad o => alex_at K m0 J_TOK (wz 4) 4 o start
  end.
Definition esc_post (K : alexK) (m0 : mem) (e start : Z) (r : Z + (ytok * Z * option lex_error * bool)) : machine_state -> Prop :=
  match r with
  | inl o => astr_at K m0 J_STR true e o start
  | inr res => str_post K m0 e start res
  end.

End RC__1.
Ltac fin_str :=
  lazymatch goal with |- evtA _ _ _ _ => apply evtA_done | _ => idtac end; cbv beta;
  unfold astr_at; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _;
  split; [reflexivity| fin_lexmem].

(* [comment removed for export] *)
Ltac unread3 K m0 ENV SH MU WM OFF off :=
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)); zstepA; iflit;
  zstepA; rewrite ?ysx32_small by lia;
  (let KU := fresh "KU" in zstepA; if_cases KU; zify_cond KU; [kill KU| clear KU]);
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)); zstepA; iflit;
  zstepA; zstoreA ENV;
  try replace (off + 1 + -1) with off in OFF by lia.
(* [comment removed for export] *)
Ltac err_store15c K m0 ENV SH MU WM :=
  zstepA; zstepA; zstepA; shadow_addr; zstepA;
  shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)); zstepA; iflit;
  zstoreA ENV; stepA.

(* [comment removed for export] *)
Ltac rdcltA K m0 ENV SH MU WM MI c :=
  zstepA; shadow_addr; zstepA;                                               (* [comment removed for export] *)
  (let RD := fresh "RD" in
   pose proof (rd_shC K m0 _ ENV SH MU WM c ltac:(lia)) as RD; unfold AY_CHARTAB in RD;
   zstepA; clear RD; rewrite ?zxb_small, ?sxb_small by lia); zstepA; iflit;  (* [comment removed for export] *)
  (let RD := fresh "RD" in
   pose proof (chartab_read _ c MI ltac:(lia)) as RD; unfold AY_CHARTAB in RD;
   zstepA; cbn beta; clear RD);
  rewrite (u8_val (clt c)) by (pose proof (clt_range8 c); lia);
  try (lazymatch goal with H : 0 <= clt c < 8 |- _ => idtac | |- _ => pose proof (clt_range8 c) end).


Section RC__2.
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

(* [comment removed for export] *)
Lemma str_finish_tok : forall (esc : bool) (rav s2v s3v s6v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k64 : word) (k0 : list byte)
    (m : mem) (e off start t t' : Z),
  alexmem K m0 m e off start k0 (wz (Z.b2z esc)) k64 -> 0 <= t <= 14 -> 0 <= t' <= 14 -> t <> 3 -> t' <> 3 ->
  evtA asegs (k_P K) (alex_at K m0 J_TOK (wz (if esc then t' else t)) e off start)
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) (wz t') a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v (wz t) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x857e8) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until t'. intros LM TR TR' N3 N3'. prep LM BC.
  zstepA.                                                                    (* [comment removed for export] *)
  destruct esc; cbn [Z.b2z] in *.
  - zstepA. iflit. stepA. stepA. zstepA. if_cases K0; zify_cond K0; [| kill K0]. fin_at.   (* [comment removed for export] *)
  - zstepA. iflit. stepA. zstepA. if_cases K0; zify_cond K0; [| kill K0]. fin_at.          (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma str_finish_eof : forall (rav s2v s3v s6v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 ->
  evtA asegs (k_P K) (fun ms' => exists s7v, alex_at K m0 J_EOF s7v e off start ms')
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v (wz 3) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x856bc) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start. intros LM. prep LM BC.
  stepA. stepA. zstepA.                                                      (* [comment removed for export] *)
  zstepA. if_cases K0; try zify_cond K0.                                     (* [comment removed for export] *)
  - stepA. zstepA. iflit. fin_at.                                            (* [comment removed for export] *)
  - stepA. stepA. zstepA. iflit. fin_at.                                     (* [comment removed for export] *)
Qed.
Lemma str_eof184 : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 ->
  evtA asegs (k_P K) (fun ms' => exists s7v, alex_at K m0 J_EOF s7v e off start ms')
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x856b4) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start. intros LM. prep LM BC.
  zstoreA ENV. stepA.                                                        (* [comment removed for export] *)
  eapply str_finish_eof. fin_lexmem.
Qed.

(* [comment removed for export] *)
Lemma str_err290 : forall (rav s2v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start ec : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= ec <= 11 ->
  evtA asegs (k_P K) (alex_at K m0 J_TOK (wz 4) ec off start)
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz ec) (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x857c0) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until ec. intros LM ER. prep LM BC.
  zstoreA ENV.                                                               (* [comment removed for export] *)
  zstepA. zstepA. zstepA. shadow_addr. zstepA.                               (* [comment removed for export] *)
  shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. iflit.             (* [comment removed for export] *)
  zstoreA ENV. stepA. stepA.                                                 (* [comment removed for export] *)
  zstepA. zstepA. if_cases K0; try zify_cond K0.                             (* [comment removed for export] *)
  - stepA. zstepA. iflit. fin_at.
  - stepA. stepA. zstepA. iflit. fin_at.
Qed.

(* [comment removed for export] *)
Lemma hex4_loop : forall (n : nat) (rav s2v s6v s7v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 (wz AY_CHARTAB) -> 0 <= off <= zlength (k_txt K) -> (1 <= n <= 4)%nat ->
  evtA asegs (k_P K) (hx_post K m0 e start (ylex_hex4 n (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz (Z.of_nat n)) (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) (wz (k_L K + 36))
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x842ec) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction n as [|n IH]; intros until start; intros LM BO HN; [lia|]. prep LM BC.
  cbn [ylex_hex4].
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
  eofchkA K m0 ENV SH MU WM K0.
  2:{ stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [hx_post]. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdcharA K m0 ENV KP SH MU WM rdck_10ae80 off.
  zstepA. zstepA.                                                            (* [comment removed for export] *)
  rdcltA K m0 ENV SH MU WM MI (znth (k_txt K) off).
  zstepA. zstepA. if_cases K1; zify_cond K1.                                 (* [comment removed for export] *)
  - (* [comment removed for export] *)
    assert (HV : is_vhc (znth (k_txt K) off) = false).
    { pose proof (clt_vhc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_eq _ _) K1) in X. destruct (is_vhc _); [discriminate X| reflexivity]. }
    rewrite HV. cbn [hx_post].
    unread3 K m0 ENV SH MU WM OFF off. stepA. stepA. err_store15c K m0 ENV SH MU WM. fin_at.   (* [comment removed for export] *)
  - assert (HV : is_vhc (znth (k_txt K) off) = true).
    { pose proof (clt_vhc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_neq _ _) K1) in X. destruct (is_vhc _); [reflexivity| discriminate X]. }
    rewrite HV.
    zstepA. rewrite (swrap32_small (Z.of_nat n + 1 + -1)) by lia. replace (Z.of_nat n + 1 + -1) with (Z.of_nat n) by lia.   (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2.                                       (* [comment removed for export] *)
    + (* [comment removed for export] *)
      eapply IH; [fin_lexmem| lia| lia].
    + (* [comment removed for export] *)
      destruct n; [| lia]. cbn [ylex_hex4 hx_post].
      stepA. stepA. fin_str.                                                 (* [comment removed for export] *)
Qed.

Lemma hx_post_esc : forall e start r ms,
  hx_post K m0 e start r ms ->
  esc_post K m0 e start (match r with HX_ok o => inl o | HX_eof o => inr (TK_eof, o, @None lex_error, true)
                                     | HX_bad o => inr (TK_error, o, Some LE_string_invalid_hex_char, true) end) ms.
Proof. aceil. intros e start [o|o|o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma escape_walk : forall (rav s2v s3v s6v s7v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 : word) (k0 : list byte)
    (m : mem) (e off1 start : Z),
  alexmem K m0 m e off1 start k0 k8 (wz AY_CHARTAB) -> 0 < off1 <= zlength (k_txt K) ->
  evtA asegs (k_P K) (esc_post K m0 e start (esc_model (k_txt K) (zlength (k_txt K)) off1))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) (wz (k_L K + 36))
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x84208) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start. intros LM BO. prep LM BC.
  unfold esc_model.
  eofchkA K m0 ENV SH MU WM K0.
  2:{ stepA. replace (zlength (k_txt K) <=? off1) with true by (symmetry; apply Z.leb_le; lia). cbn [esc_post str_post err_upd]. fin_at. }
  replace (zlength (k_txt K) <=? off1) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  rdcharA K m0 ENV KP SH MU WM rdck_10ad9c off1.
  stepA. zstepA. if_cases K1; zify_cond K1.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off1 =? c_u) with false by (symmetry; apply Z.eqb_neq; unfold c_u; lia).
    zstepA. zstepA.                                                          (* [comment removed for export] *)
    rdcltA K m0 ENV SH MU WM MI (znth (k_txt K) off1).
    zstepA. zstepA. if_cases K2; zify_cond K2.                               (* [comment removed for export] *)
    + assert (HV : is_vec (znth (k_txt K) off1) = true).
      { pose proof (clt_vec (znth (k_txt K) off1) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_neq _ _) K2) in X. destruct (is_vec _); [reflexivity| discriminate X]. }
      rewrite HV. cbn [esc_post].
      stepA. fin_str.                                                        (* [comment removed for export] *)
    + assert (HV : is_vec (znth (k_txt K) off1) = false).
      { pose proof (clt_vec (znth (k_txt K) off1) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_eq _ _) K2) in X. destruct (is_vec _); [discriminate X| reflexivity]. }
      rewrite HV. cbn [esc_post str_post err_upd lex_error_code tok_code].
      stepA.                                                                 (* [comment removed for export] *)
      unread3 K m0 ENV SH MU WM OFF off1. stepA. stepA. stepA. err_store15c K m0 ENV SH MU WM. fin_at.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off1 =? c_u) with true by (symmetry; apply Z.eqb_eq; unfold c_u; lia).
    stepA. change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat 4)) at 1.      (* [comment removed for export] *)
    eapply evtA_mono; [eapply (hex4_loop 4); [fin_lexmem| lia| lia]|].
    intros ms Hs. exact (hx_post_esc _ _ _ _ Hs).
Qed.
End S.
End RC__2.
