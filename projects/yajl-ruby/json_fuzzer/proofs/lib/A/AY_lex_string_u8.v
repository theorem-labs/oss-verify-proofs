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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_number RY_lex_string RY_lex_string_u8.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_rdck2 AY_lex_kit AY_lex_string1.
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

Definition u8_post (e start : Z) (esc : bool) (r : u8res) : machine_state -> Prop :=
  match r with
  | U8_ok o => astr_at K m0 J_STR esc e o start
  | U8_eof o => fun ms' => exists s7v, alex_at K m0 J_EOF s7v e o start ms'
  | U8_error o => alex_at K m0 J_TOK (wz 4) 1 o start
  end.

(* [comment removed for export] *)
Ltac txtld_s K m0 ENV SH MU off :=
  let RD := fresh "RD" in
  pose proof (rd_txt K m0 _ ENV SH MU off ltac:(lia)) as RD; zstepA; cbn beta; clear RD;
  try (lazymatch goal with H : 0 <= znth _ off < 256 |- _ => idtac | |- _ => pose proof (txt_range K m0 SH off) end).
Ltac contk K c :=
  rewrite (sxb_val c) in K by lia; rewrite ?signed_lit_small in K by (destruct (Z.ltb_spec c 128); lia);
  first [ rewrite (u8cont_true c) by (destruct (Z.ltb_spec c 128); lia)
        | rewrite (u8cont_false c) by (destruct (Z.ltb_spec c 128); lia) ].
(* [comment removed for export] *)
Ltac rdchar_reload K m0 ENV KP SH MU WM RDCK off :=
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)); zstepA; iflit;
  zstepA; rewrite ?ysx32_small by lia;
  zstepA; zstoreA ENV;
  zstepA; zstepA;                                                (* [comment removed for export] *)
  zstepA; zstepA; rewrite (land_M32_small off) by lia;
  zstepA;
  rdckA K m0 ENV KP SH MU WM RDCK off;
  txtld_s K m0 ENV SH MU off.

Lemma utf8_walk : forall (esc : bool) (rav s2v s3v s6v t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 : word) (k0 : list byte)
    (m : mem) (e off1 start c : Z),
  alexmem K m0 m e off1 start k0 k8 (wz AY_CHARTAB) -> 0 < off1 <= zlength (k_txt K) -> 0 <= c < 256 -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (u8_post e start esc (ylex_utf8_char (k_txt K) (zlength (k_txt K)) off1 c))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 (wz c) a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v (wz (Z.b2z esc)) (wz (zlength (k_txt K))) (wz ASB) (wz (k_L K + 36))
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x8414c) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until c. intros LM BO CR ER. prep LM BC.
  assert (EB : 0 <= Z.b2z esc <= 1) by (destruct esc; cbn; lia).
  unfold ylex_utf8_char. cbv zeta.
  zstepA. zstepA. zstepA. if_cases K0; zify_cond K0.                        (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct (Z.le_gt_cases c 127); [| rewrite sext8w_hi in K0 by lia; exfalso; lia].
    replace (c <=? 127) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post]. fin_str.
  - destruct (Z.le_gt_cases c 127); [rewrite sext8w_lo in K0 by lia; exfalso; lia|].
    replace (c <=? 127) with false by (symmetry; apply Z.leb_gt; lia).
    zstepA. rewrite sext8w_zext by lia.                                      (* [comment removed for export] *)
    zstepA. stepA. zstepA. if_cases K1; zify_cond K1.                        (* [comment removed for export] *)
    + (* [comment removed for export] *)
      replace (Z.shiftr c 5 =? 6) with false by (rewrite <- lead2_eq by lia; symmetry; apply Z.eqb_neq; exact K1).
      zstepA. stepA. zstoreA ENV. zstepA. if_cases K2; zify_cond K2.         (* [comment removed for export] *)
      * (* [comment removed for export] *)
        replace (Z.shiftr c 4 =? 14) with false by (rewrite <- lead3_eq by lia; symmetry; apply Z.eqb_neq; exact K2).
        zstepA. stepA. stepA. zstepA. if_cases K3; zify_cond K3.              (* [comment removed for export] *)
        -- replace (Z.shiftr c 3 =? 30) with true by (rewrite <- lead4_eq by lia; symmetry; apply Z.eqb_eq; exact K3).
           (* [comment removed for export] *)
           shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
           zstepA. rewrite ?ysx32_small by lia. stepA. zstepA. if_cases K4; zify_cond K4.   (* [comment removed for export] *)
           2:{ stepA. replace (zlength (k_txt K) <=? off1) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post].
               eapply (str_finish_eof K m0); first [exact ENV| exact KP| exact SH| fin_lexmem]. }
           replace (zlength (k_txt K) <=? off1) with false by (symmetry; apply Z.leb_gt; lia).
           zstoreA ENV.                                                      (* [comment removed for export] *)
           rdcharA0 K m0 ENV KP SH MU WM rdck_10b224 off1. txtld_s K m0 ENV SH MU off1.
           stepA. zstepA. if_cases K5; zify_cond K5; contk K5 (znth (k_txt K) off1).   (* [comment removed for export] *)
           2:{ cbn [u8_post]. stepA. zstepA. stepA. eapply (str_err290 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]. }   (* [comment removed for export] *)
           shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
           zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K6; zify_cond K6.   (* [comment removed for export] *)
           { replace (zlength (k_txt K) <=? off1 + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post].
             eapply (str_finish_eof K m0); first [exact ENV| exact KP| exact SH| fin_lexmem]. }
           replace (zlength (k_txt K) <=? off1 + 1) with false by (symmetry; apply Z.leb_gt; lia).
           zstepA. shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)). zstepA. iflit.   (* [comment removed for export] *)
           zstepA. rewrite ?ysx32_small by lia. zstepA. iflit.              (* [comment removed for export] *)
           rdchar_reload K m0 ENV KP SH MU WM rdck_10b354 (off1 + 1).      (* [comment removed for export] *)
           stepA. zstepA. if_cases K7; zify_cond K7; contk K7 (znth (k_txt K) (off1 + 1)).   (* [comment removed for export] *)
           2:{ cbn [u8_post]. stepA. zstepA. stepA. eapply (str_err290 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]. }
           shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
           zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K8; zify_cond K8.
           { replace (zlength (k_txt K) <=? off1 + 2) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post].
             eapply (str_finish_eof K m0); first [exact ENV| exact KP| exact SH| fin_lexmem]. }
           replace (zlength (k_txt K) <=? off1 + 2) with false by (symmetry; apply Z.leb_gt; lia).
           zstepA. shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)). zstepA. iflit.
           zstepA. rewrite ?ysx32_small by lia. zstepA. iflit.
           rdchar_reload K m0 ENV KP SH MU WM rdck_10b43c (off1 + 2).  (* [comment removed for export] *)
           stepA. zstepA. if_cases K9; zify_cond K9; contk K9 (znth (k_txt K) (off1 + 2)).   (* [comment removed for export] *)
           { cbn [u8_post]. destruct esc; cbn [Z.b2z]; eapply (str_err290 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]. }
           cbn [u8_post]. stepA. destruct esc; cbn [Z.b2z]; fin_str.
        -- (* [comment removed for export] *)
           replace (Z.shiftr c 3 =? 30) with false by (rewrite <- lead4_eq by lia; symmetry; apply Z.eqb_neq; exact K3).
           cbn [u8_post]. stepA. eapply (str_err290 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia].
      * replace (Z.shiftr c 4 =? 14) with true by (rewrite <- lead3_eq by lia; symmetry; apply Z.eqb_eq; exact K2).
        (* [comment removed for export] *)
        shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
        zstepA. rewrite ?ysx32_small by lia. stepA. zstepA. if_cases K4; zify_cond K4.   (* [comment removed for export] *)
        2:{ stepA. replace (zlength (k_txt K) <=? off1) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post].
            eapply (str_finish_eof K m0); first [exact ENV| exact KP| exact SH| fin_lexmem]. }
        replace (zlength (k_txt K) <=? off1) with false by (symmetry; apply Z.leb_gt; lia).
        rdcharA0 K m0 ENV KP SH MU WM rdck_10b138 off1. txtld_s K m0 ENV SH MU off1.
        stepA. stepA. zstepA. if_cases K5; zify_cond K5; contk K5 (znth (k_txt K) off1).   (* [comment removed for export] *)
        2:{ cbn [u8_post]. stepA. zstepA. stepA. eapply (str_err290 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]. }
        shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
        zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K6; zify_cond K6.      (* [comment removed for export] *)
        2:{ stepA. replace (zlength (k_txt K) <=? off1 + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post].
            eapply (str_finish_eof K m0); first [exact ENV| exact KP| exact SH| fin_lexmem]. }
        replace (zlength (k_txt K) <=? off1 + 1) with false by (symmetry; apply Z.leb_gt; lia).
        zstepA. shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)). zstepA. iflit.
        zstepA. rewrite ?ysx32_small by lia. zstepA. iflit.
        rdchar_reload K m0 ENV KP SH MU WM rdck_10b30c (off1 + 1).         (* [comment removed for export] *)
        stepA. zstepA. if_cases K7; zify_cond K7; contk K7 (znth (k_txt K) (off1 + 1)).   (* [comment removed for export] *)
        { cbn [u8_post]. destruct esc; cbn [Z.b2z]; eapply (str_err290 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia]. }
        cbn [u8_post]. stepA. destruct esc; cbn [Z.b2z]; fin_str.
    + replace (Z.shiftr c 5 =? 6) with true by (rewrite <- lead2_eq by lia; symmetry; apply Z.eqb_eq; exact K1).
      (* [comment removed for export] *)
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
      zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K4; zify_cond K4.        (* [comment removed for export] *)
      2:{ stepA. replace (zlength (k_txt K) <=? off1) with true by (symmetry; apply Z.leb_le; lia). cbn [u8_post].
          eapply (str_eof184 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem]. }
      replace (zlength (k_txt K) <=? off1) with false by (symmetry; apply Z.leb_gt; lia).
      rdcharA0 K m0 ENV KP SH MU WM rdck_10b038 off1. txtld_s K m0 ENV SH MU off1.
      stepA. zstepA. if_cases K5; zify_cond K5; contk K5 (znth (k_txt K) off1).   (* [comment removed for export] *)
      { cbn [u8_post]. fin_str. }
      cbn [u8_post]. stepA. stepA. stepA. eapply (str_err290 K m0); first [exact ENV| exact KP| exact SH| fin_lexmem| lia].   (* [comment removed for export] *)
Qed.
End S.
End RC__1.
