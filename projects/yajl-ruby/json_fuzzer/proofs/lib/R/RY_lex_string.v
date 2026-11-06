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

Ltac byte_refl f c Hc :=
  let H := fresh in
  pose proof (byte_forall f ltac:(vm_compute; reflexivity) c Hc) as H; cbn beta in H;
  first [ apply Bool.eqb_prop in H | apply Z.eqb_eq in H ]; exact H.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition sext8w (c : Z) : Z := Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56) 18446744073709551615.

Lemma sext8w_nonneg : forall c, 0 <= c < 256 -> (sext8w c <? 9223372036854775808) = (c <=? 127).
Proof. intros c Hc. byte_refl (fun c => Bool.eqb (sext8w c <? 9223372036854775808) (c <=? 127)) c Hc. Qed.
Lemma sext8w_zext : forall c, 0 <= c < 256 -> Z.land (sext8w c) 255 = c.
Proof. intros c Hc. byte_refl (fun c => Z.land (sext8w c) 255 =? c) c Hc. Qed.

(* [comment removed for export] *)
Lemma lead2_eq : forall c, 0 <= c < 256 -> (Z.land c 224 =? 192) = (Z.shiftr c 5 =? 6).
Proof. intros c Hc. byte_refl (fun c => Bool.eqb (Z.land c 224 =? 192) (Z.shiftr c 5 =? 6)) c Hc. Qed.
Lemma lead3_eq : forall c, 0 <= c < 256 -> (Z.land c 240 =? 224) = (Z.shiftr c 4 =? 14).
Proof. intros c Hc. byte_refl (fun c => Bool.eqb (Z.land c 240 =? 224) (Z.shiftr c 4 =? 14)) c Hc. Qed.
Lemma lead4_eq : forall c, 0 <= c < 256 -> (Z.land c 248 =? 240) = (Z.shiftr c 3 =? 30).
Proof. intros c Hc. byte_refl (fun c => Bool.eqb (Z.land c 248 =? 240) (Z.shiftr c 3 =? 30)) c Hc. Qed.
Lemma lead_excl3 : forall c, 0 <= c < 256 -> Z.land c 224 = 192 -> (Z.shiftr c 4 =? 14) = false /\ (Z.shiftr c 3 =? 30) = false.
Proof.
  intros c Hc H. split.
  - byte_refl (fun c => Bool.eqb (implb (Z.land c 224 =? 192) (negb (Z.shiftr c 4 =? 14))) true) c Hc || idtac.
    pose proof (byte_forall (fun c => implb (Z.land c 224 =? 192) (negb (Z.shiftr c 4 =? 14))) ltac:(vm_compute; reflexivity) c Hc) as X.
    cbn beta in X. rewrite (proj2 (Z.eqb_eq _ _) H) in X. cbn in X. destruct (Z.shiftr c 4 =? 14); [discriminate X| reflexivity].
  - pose proof (byte_forall (fun c => implb (Z.land c 224 =? 192) (negb (Z.shiftr c 3 =? 30))) ltac:(vm_compute; reflexivity) c Hc) as X.
    cbn beta in X. rewrite (proj2 (Z.eqb_eq _ _) H) in X. cbn in X. destruct (Z.shiftr c 3 =? 30); [discriminate X| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma sxb_val : forall c, 0 <= c < 256 -> bv_signed (sxb (Z_to_bv 8 c)) = (if c <? 128 then c else c - 256).
Proof. intros c Hc. byte_refl (fun c => bv_signed (sxb (Z_to_bv 8 c)) =? (if c <? 128 then c else c - 256)) c Hc. Qed.
Lemma u8cont_true : forall c, 128 <= c <= 191 -> is_utf8_cont c = true.
Proof.
  intros c Hc.
  pose proof (byte_forall (fun c => implb ((128 <=? c) && (c <=? 191)) (is_utf8_cont c)) ltac:(vm_compute; reflexivity) c ltac:(lia)) as X.
  cbn beta in X. replace (128 <=? c) with true in X by (symmetry; apply Z.leb_le; lia).
  replace (c <=? 191) with true in X by (symmetry; apply Z.leb_le; lia). cbn in X. destruct (is_utf8_cont c); [reflexivity| discriminate X].
Qed.
Lemma u8cont_false : forall c, 0 <= c < 256 -> c < 128 \/ 191 < c -> is_utf8_cont c = false.
Proof.
  intros c Hc H.
  pose proof (byte_forall (fun c => implb (is_utf8_cont c) ((128 <=? c) && (c <=? 191))) ltac:(vm_compute; reflexivity) c Hc) as X.
  cbn beta in X. destruct (is_utf8_cont c); [| reflexivity]. cbn in X.
  apply andb_true_iff in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

(* [comment removed for export] *)
Lemma clt_vhc : forall c, 0 <= c < 256 -> (Z.land (clt c) 4 =? 0) = negb (is_vhc c).
Proof. intros c Hc. byte_refl (fun c => Bool.eqb (Z.land (clt c) 4 =? 0) (negb (is_vhc c))) c Hc. Qed.
Lemma clt_vec : forall c, 0 <= c < 256 -> (Z.land (clt c) 1 =? 0) = negb (is_vec c).
Proof. intros c Hc. byte_refl (fun c => Bool.eqb (Z.land (clt c) 1 =? 0) (negb (is_vec c))) c Hc. Qed.
Lemma clt_ijc : forall c, 0 <= c < 256 -> (Z.land (clt c) 2 =? 0) = negb (is_ijc c).
Proof. intros c Hc. byte_refl (fun c => Bool.eqb (Z.land (clt c) 2 =? 0) (negb (is_ijc c))) c Hc. Qed.

(* [comment removed for export] *)
End RC__1.
Ltac rdclt MI c :=
  zstep;
  (let RD := fresh "RD" in
   pose proof (chartab_read _ c MI ltac:(lia)) as RD; unfold RY_CHARTAB in RD;
   zstep; cbn beta; clear RD);
  rewrite (u8_val (clt c)) by (pose proof (clt_range8 c); lia);
  try (lazymatch goal with H : 0 <= clt c < 8 |- _ => idtac | |- _ => pose proof (clt_range8 c) end).

(* [comment removed for export] *)
Ltac rdchar_s MU TX0 off :=
  zstep; rewrite ?ysx32_small by lia;
  zstep; (let K := fresh "KB" in if_cases K; zify_cond K; [ clear K | kill K ]);
  zstep; rewrite ?ysx32_small by lia;
  zstep; zstep; zstep; zstep; zstep;
  rewrite (land_M32_small off) by lia;
  zstep;
  (let RD := fresh "RD" in
   pose proof (text_read _ _ _ _ _ off TX0 MU ltac:(intros; cbn; lia) ltac:(lia)) as RD;
   zstep; cbn beta; clear RD);
  try (lazymatch goal with H : 0 <= znth _ off < 256 |- _ => idtac
       | |- _ => pose proof (text_byte_range _ off (proj1 (proj2 TX0))) end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition esc_model (txt : list Z) (len off1 : Z) : Z + (ytok * Z * option lex_error * bool) :=
  if len <=? off1 then inr (TK_eof, off1, @None lex_error, true)
  else let c2 := znth txt off1 in let off2 := off1 + 1 in
    if c2 =? c_u then
      match ylex_hex4 4 txt len off2 with
      | HX_ok o => inl o
      | HX_eof o => inr (TK_eof, o, None, true)
      | HX_bad o => inr (TK_error, o, Some LE_string_invalid_hex_char, true)
      end
    else if is_vec c2 then inl off2 else inr (TK_error, off1, Some LE_string_invalid_escaped_char, true).

(* [comment removed for export] *)
Definition str_at (K : lexK) (m0 : mem) (pc : Z) (esc : bool) (e off start : Z) : machine_state -> Prop :=
  fun ms' => exists (rav s0v s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                  (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start)
                  (wz 92) (wz 117) (wz 34) (wz (Z.b2z esc)) (wz RY_CHARTAB) t3 t4 t5 t6)
             (k_F K) (wz pc) (k_fc K) None m' (seg_rom rsegs)
    /\ lexmem K m0 m' e off.
Definition J_STR : Z := 0x14714.

(* [comment removed for export] *)
Definition str_post (K : lexK) (m0 : mem) (e start : Z) (r : ytok * Z * option lex_error * bool) : machine_state -> Prop :=
  let '(tok, o, err, esc) := r in
  match tok with
  | TK_eof => fun ms' => exists s0v, lex_at K m0 J_EOF s0v (err_upd e err) o start ms'
  | TK_string => lex_at K m0 J_TOK (wz (if esc then 13 else 12)) (err_upd e err) o start
  | _ => lex_at K m0 J_TOK (wz (tok_code tok)) (err_upd e err) o start
  end.

(* [comment removed for export] *)
Definition hx_post (K : lexK) (m0 : mem) (e start : Z) (r : hxres) : machine_state -> Prop :=
  match r with
  | HX_ok o => str_at K m0 J_STR true e o start
  | HX_eof o => fun ms' => exists s0v, lex_at K m0 J_EOF s0v e o start ms'
  | HX_bad o => lex_at K m0 J_TOK (wz 4) 4 o start
  end.

(* [comment removed for export] *)
Definition esc_post (K : lexK) (m0 : mem) (e start : Z) (r : Z + (ytok * Z * option lex_error * bool)) : machine_state -> Prop :=
  match r with
  | inl o => str_at K m0 J_STR true e o start
  | inr res => str_post K m0 e start res
  end.

End RC__2.
Ltac fin_str :=
  lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end; cbv beta;
  unfold str_at; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _;
  split; [reflexivity| fin_lexmem].

Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

(* [comment removed for export] *)
Lemma str_c78 : forall (rav s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start ec : Z),
  lexmem K m0 m e off ->
  evt rsegs (lex_at K m0 J_TOK (wz 4) ec off start)
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz ec) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14d04) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until ec. intros (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  zstep. zstep. zstep. fin_at.
Qed.

(* [comment removed for export] *)
Lemma hex4_loop : forall (n : nat) (rav s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s10v : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) -> (1 <= n <= 4)%nat ->
  evt rsegs (hx_post K m0 e start (ylex_hex4 n (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (Z.of_nat n)) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start)
          (wz 92) (wz 117) (wz 34) s10v (wz RY_CHARTAB) t3 t4 t5 t6)
        (k_F K) (wz 0x14680) (k_fc K) None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros until start; intros TX0 LM BO HN; [lia|].
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC. unfold RY_CHARTAB.
  cbn [ylex_hex4].
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
  eofchk K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [hx_post]. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    rdclt MI (znth (k_txt K) off).
    zstep. zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      apply (f_equal negb) in K1 || idtac.
      assert (HV : is_vhc (znth (k_txt K) off) = false).
      { pose proof (clt_vhc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_eq _ _) K1) in X. destruct (is_vhc _); [discriminate X| reflexivity]. }
      rewrite HV. cbn [hx_post].
      unread. zstep. zstep. replace (off + 1 + -1) with off in OFF by lia.
      eapply str_c78. fin_lexmem.
    + assert (HV : is_vhc (znth (k_txt K) off) = true).
      { pose proof (clt_vhc (znth (k_txt K) off) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_neq _ _) K1) in X. destruct (is_vhc _); [reflexivity| discriminate X]. }
      rewrite HV.
      zstep. rewrite (swrap32_small (Z.of_nat n + 1 + -1)) by lia. replace (Z.of_nat n + 1 + -1) with (Z.of_nat n) by lia.
      zstep. if_cases K2; zify_cond K2.
      * (* [comment removed for export] *)
        eapply IH; [exact TX0| fin_lexmem| lia| lia].
      * (* [comment removed for export] *)
        destruct n; [| lia]. cbn [ylex_hex4 hx_post].
        zstep. zstep. fin_str.
Qed.

Lemma hx_post_esc : forall m0 e start r ms,
  hx_post K m0 e start r ms ->
  esc_post K m0 e start (match r with HX_ok o => inl o | HX_eof o => inr (TK_eof, o, @None lex_error, true)
                                  | HX_bad o => inr (TK_error, o, Some LE_string_invalid_hex_char, true) end) ms.
Proof. intros m0 e start [o|o|o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma escape_walk : forall (rav s0v s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s10v : word)
    (m0 m : mem) (e off1 start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off1 -> 0 < off1 <= zlength (k_txt K) ->
  evt rsegs (esc_post K m0 e start (esc_model (k_txt K) (zlength (k_txt K)) off1))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start)
          (wz 92) (wz 117) (wz 34) s10v (wz RY_CHARTAB) t3 t4 t5 t6)
        (k_F K) (wz 0x14614) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC. unfold RY_CHARTAB.
  unfold esc_model.
  eofchk K0.
  - replace (zlength (k_txt K) <=? off1) with true by (symmetry; apply Z.leb_le; lia). cbn [esc_post str_post err_upd]. fin_at.
  - replace (zlength (k_txt K) <=? off1) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
    rdchar MU TX0 off1.
    zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off1 =? c_u) with false by (symmetry; apply Z.eqb_neq; unfold c_u; lia).
      rdclt MI (znth (k_txt K) off1).
      zstep. zstep. if_cases K2; zify_cond K2.
      * assert (HV : is_vec (znth (k_txt K) off1) = false).
        { pose proof (clt_vec (znth (k_txt K) off1) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_eq _ _) K2) in X. destruct (is_vec _); [discriminate X| reflexivity]. }
        rewrite HV. cbn [esc_post str_post err_upd lex_error_code tok_code].
        unread. zstep. zstep. zstep. replace (off1 + 1 + -1) with off1 in OFF by lia.
        eapply str_c78. fin_lexmem.
      * assert (HV : is_vec (znth (k_txt K) off1) = true).
        { pose proof (clt_vec (znth (k_txt K) off1) ltac:(lia)) as X. rewrite (proj2 (Z.eqb_neq _ _) K2) in X. destruct (is_vec _); [reflexivity| discriminate X]. }
        rewrite HV. cbn [esc_post].
        zstep. fin_str.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off1 =? c_u) with true by (symmetry; apply Z.eqb_eq; unfold c_u; lia).
      zstep. change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat 4)) at 1.
      eapply evt_mono; [eapply (hex4_loop 4); [exact TX0| fin_lexmem| lia| lia]|].
      intros ms Hs. exact (hx_post_esc _ _ _ _ _ Hs).
Qed.
End S.
End RC__3.
