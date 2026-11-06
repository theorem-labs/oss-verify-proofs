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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_lex_kit UY_lex_string.
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
Lemma sext8w_lo : forall c, 0 <= c <= 127 ->
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56) 18446744073709551615 = c.
Proof.
  intros c Hc.
  pose proof (byte_forall (fun c => implb (c <=? 127) (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56) 18446744073709551615 =? c))
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as X.
  cbn beta in X. replace (c <=? 127) with true in X by (symmetry; apply Z.leb_le; lia). cbn [implb] in X.
  apply Z.eqb_eq in X. exact X.
Qed.
Lemma sext8w_hi : forall c, 128 <= c < 256 ->
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56) 18446744073709551615 = c + 18446744073709551360.
Proof.
  intros c Hc.
  pose proof (byte_forall (fun c => implb (128 <=? c) (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56) 18446744073709551615 =? c + 18446744073709551360))
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as X.
  cbn beta in X. replace (128 <=? c) with true in X by (symmetry; apply Z.leb_le; lia). cbn [implb] in X.
  apply Z.eqb_eq in X. exact X.
Qed.

Lemma sext8w_zext : forall c, 0 <= c < 256 ->
  Z.land (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56) 18446744073709551615) 255 = c.
Proof.
  intros c Hc.
  pose proof (byte_forall (fun c => Z.land (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56) 18446744073709551615) 255 =? c)
                ltac:(vm_compute; reflexivity) c Hc) as X.
  cbn beta in X. apply Z.eqb_eq in X. exact X.
Qed.

(* [comment removed for export] *)
End RC__1.
Ltac contk K c :=
  rewrite (sxb_val c) in K by lia;
  first [ rewrite (u8cont_true c) by (destruct (Z.ltb_spec c 128); lia)
        | rewrite (u8cont_false c) by (destruct (Z.ltb_spec c 128); lia) ].

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition u8c1 (txt : list Z) (len off : Z) : u8res :=
  if len <=? off then U8_eof off else
  let c1 := znth txt off in let off := off + 1 in
  if is_utf8_cont c1 then U8_ok off else U8_error off.
Definition u8c2 (txt : list Z) (len off : Z) : u8res :=
  if len <=? off then U8_eof off else
  let c1 := znth txt off in let off := off + 1 in
  if is_utf8_cont c1 then u8c1 txt len off else U8_error off.
Definition u8c3 (txt : list Z) (len off : Z) : u8res :=
  if len <=? off then U8_eof off else
  let c1 := znth txt off in let off := off + 1 in
  if is_utf8_cont c1 then u8c2 txt len off else U8_error off.
Lemma ylex_utf8_char_eq : forall txt len off cur,
  ylex_utf8_char txt len off cur =
  if cur <=? 127 then U8_ok off
  else if Z.shiftr cur 5 =? 6 then u8c1 txt len off
  else if Z.shiftr cur 4 =? 14 then u8c2 txt len off
  else if Z.shiftr cur 3 =? 30 then u8c3 txt len off
  else U8_error off.
Proof. intros. reflexivity. Qed.

Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

Definition u8_post (m0 : mem) (e start : Z) (esc : bool) (r : u8res) : machine_state -> Prop :=
  match r with
  | U8_ok o => str_at K m0 J_STR esc e o start
  | U8_eof o => lex_at K m0 J_EOF (wz 3) e o start
  | U8_error o => lex_at K m0 J_TOK (wz 4) 1 o start
  end.

(* [comment removed for export] *)
Lemma u8c1_walk : forall (esc : bool) (rav s0v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) ->
  evt usegs (u8_post m0 e start esc (u8c1 (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v (wz (Z.b2z esc)) a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz nCT)
          (wz RY_CHARTAB) (wz 92) (wz 1) (wz 3) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14c68) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC. unfold RY_CHARTAB, nCT.
  unfold u8c1.
  eofchk K0.
  { replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post]. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  rdchar_s MU TX0 off.
  zstep. zstep. if_cases K1; zify_cond K1; contk K1 (znth (k_txt K) off).
  { cbn [u8_post]. eapply (err_u8 K ENV). fin_lexmem. }
  cbn [u8_post]. fin_str.
Qed.

(* [comment removed for export] *)
Lemma u8c2_walk : forall (esc : bool) (rav s0v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) ->
  evt usegs (u8_post m0 e start esc (u8c2 (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v (wz (Z.b2z esc)) a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz nCT)
          (wz RY_CHARTAB) (wz 92) (wz 1) (wz 3) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14bd8) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC. unfold RY_CHARTAB, nCT.
  unfold u8c2.
  eofchk K0.
  { replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post]. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  rdchar_s MU TX0 off.
  zstep. zstep. if_cases K1; zify_cond K1; contk K1 (znth (k_txt K) off).
  { cbn [u8_post]. eapply (err_u8 K ENV). fin_lexmem. }
  eapply u8c1_walk; [exact TX0| fin_lexmem| lia].
Qed.

(* [comment removed for export] *)
Lemma u8c3_walk : forall (esc : bool) (rav s0v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) ->
  evt usegs (u8_post m0 e start esc (u8c3 (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v (wz (Z.b2z esc)) a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz nCT)
          (wz RY_CHARTAB) (wz 92) (wz 1) (wz 3) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x149f4) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC. unfold RY_CHARTAB, nCT.
  unfold u8c3.
  eofchk K0.
  { replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post]. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  rdchar_s MU TX0 off.
  zstep. zstep. if_cases K1; zify_cond K1; contk K1 (znth (k_txt K) off).
  { cbn [u8_post]. eapply (err_u8 K ENV). fin_lexmem. }
  eapply u8c2_walk; [exact TX0| fin_lexmem| lia].
Qed.

(* [comment removed for export] *)
Lemma utf8_walk : forall (esc : bool) (rav s0v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off1 start c : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off1 start -> 0 < off1 <= zlength (k_txt K) -> 0 <= c < 256 ->
  evt usegs (u8_post m0 e start esc (ylex_utf8_char (k_txt K) (zlength (k_txt K)) off1 c))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v (wz (Z.b2z esc)) (wz c) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz nCT)
          (wz RY_CHARTAB) (wz 92) (wz 1) (wz 3) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x149b8) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until c. intros TX0 LM BO CR. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC. unfold RY_CHARTAB, nCT.
  rewrite ylex_utf8_char_eq.
  zstep. rewrite ?ysx32_small by lia.
  zstep. if_cases KV; zify_cond KV. 1:{ kill KV. } clear KV.
  zstep. zstep. zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    destruct (Z.le_gt_cases c 127); [| rewrite sext8w_hi in K0 by lia; exfalso; lia].
    replace (c <=? 127) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post]. fin_str.
  - destruct (Z.le_gt_cases c 127); [rewrite sext8w_lo in K0 by lia; exfalso; lia|].
    replace (c <=? 127) with false by (symmetry; apply Z.leb_gt; lia).
    zstep. rewrite sext8w_zext by lia.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      replace (Z.shiftr c 5 =? 6) with true by (rewrite <- lead2_eq by lia; symmetry; apply Z.eqb_eq; exact K1).
      eapply u8c1_walk; [exact TX0| fin_lexmem| lia].
    + replace (Z.shiftr c 5 =? 6) with false by (rewrite <- lead2_eq by lia; symmetry; apply Z.eqb_neq; exact K1).
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      * (* [comment removed for export] *)
        replace (Z.shiftr c 4 =? 14) with true by (rewrite <- lead3_eq by lia; symmetry; apply Z.eqb_eq; exact K2).
        eapply u8c2_walk; [exact TX0| fin_lexmem| lia].
      * replace (Z.shiftr c 4 =? 14) with false by (rewrite <- lead3_eq by lia; symmetry; apply Z.eqb_neq; exact K2).
        zstep. zstep. zstep. if_cases K3; zify_cond K3.
        -- (* [comment removed for export] *)
           replace (Z.shiftr c 3 =? 30) with false by (rewrite <- lead4_eq by lia; symmetry; apply Z.eqb_neq; exact K3).
           cbn [u8_post]. eapply (err_u8 K ENV). fin_lexmem.
        -- replace (Z.shiftr c 3 =? 30) with true by (rewrite <- lead4_eq by lia; symmetry; apply Z.eqb_eq; exact K3).
           eapply u8c3_walk; [exact TX0| fin_lexmem| lia].
Qed.
End S.
End RC__2.
