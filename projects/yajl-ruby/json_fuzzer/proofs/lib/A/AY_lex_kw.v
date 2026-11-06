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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_kw RY_lex_string_u8.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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

(* [comment removed for export] *)
Definition kw_post (tokc e start : Z) (r : wres) : machine_state -> Prop :=
  match r with
  | W_ok o => alex_at K m0 J_TOK (wz tokc) e o start
  | W_eof o => fun ms' => exists s7v, alex_at K m0 J_EOF s7v e o start ms'
  | W_bad o => alex_at K m0 J_TOK (wz 4) 6 o start
  end.

Ltac pols :=
  polu KP kp_imgsh PIMGSH; polu KP kp_img PIMG; polu KP kp_T PT; polu KP kp_Ls PLS; polu KP kp_L PL;
  polu KP kp_Hs PHS; polu KP kp_H PH; polu KP kp_stk PSTK.

(* [comment removed for export] *)
Lemma want_ull_loop : forall (rest pre : list Z) (rav s2v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  want_ull = pre ++ rest -> rest <> [] ->
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> 0 <= start < 2^32 -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (kw_post 7 e start (ylex_want rest (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz A_ULL) (wz (k_L K + 24)) (wz (k_L K + 28)) (wz (Z.of_nat (length pre))) s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x84c68) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction rest as [|w rest IH]; intros until start; intros HW NE (MU & WM & MI & ST & FR & OFF & LX & BC) BO SR ER; [congruence|].
  lex_prep ENV BC. unfold A_ULL in *.
  assert (LW : (length pre + length (w :: rest) = 3)%nat).
  { apply (f_equal (@length Z)) in HW. rewrite length_app in HW. exact (eq_sym HW). }
  cbn [length] in LW. cbn [ylex_want].
  pols.
  eofchkA K m0 ENV SH MU WM K0.
  - (* [comment removed for export] *)
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [kw_post]. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdcharA0 K m0 ENV KP SH MU WM rdck_10b7e8 off.
    zstepA.                                                                  (* [comment removed for export] *)
    zstepA. shadow_addr. zstepA.                                              (* [comment removed for export] *)
    shld (rd_shull K m0 _ ENV SH MU WM (Z.of_nat (length pre)) ltac:(lia)).  (* [comment removed for export] *)
    txtld K m0 ENV SH MU WM off.                                              (* [comment removed for export] *)
    zstepA. try if_true.                                                      (* [comment removed for export] *)
    zstepA. zstepA. rewrite sext8_lo by lia.                               (* [comment removed for export] *)
    zstepA. if_cases KS; zify_cond KS; [| kill KS].                           (* [comment removed for export] *)
    clear KS.
    assert (NTH : nth_error want_ull (length pre) = Some w).
    { rewrite HW. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    assert (WR : 0 <= w < 256).
    { apply (proj1 (Forall_forall _ _) ((fun H => proj2 (proj2 H)) want_bytes_range)). eapply nth_error_In. exact NTH. }
    pose proof (u8ro_read asegs _ 136608 (zbytes want_ull) (Z.of_nat (length pre)) (Z_to_bv 8 w) _ (ull_bytes _ MI)
                  ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
    zstepA. cbn beta. rewrite (u8_val w) by lia. clear RD.                    (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2.                                        (* [comment removed for export] *)
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? w) with false by (symmetry; apply Z.eqb_neq; lia). cbn [kw_post].
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.  (* [comment removed for export] *)
      zstepA. rewrite ?ysx32_small by lia.                                    (* [comment removed for export] *)
      zstepA. if_cases KU; zify_cond KU; [kill KU| clear KU].                 (* [comment removed for export] *)
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.  (* [comment removed for export] *)
      zstepA. zstoreA ENV.                                                    (* [comment removed for export] *)
      replace (off + 1 + -1) with off by lia.
      stepA.                                                                  (* [comment removed for export] *)
      zstepA. zstepA. zstepA. shadow_addr. zstepA.                            (* [comment removed for export] *)
      shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. try if_true.    (* [comment removed for export] *)
      stepA. zstoreA ENV. stepA.                                              (* [comment removed for export] *)
      fin_at.
    + replace (znth (k_txt K) off =? w) with true by (symmetry; apply Z.eqb_eq; lia).
      zstepA. stepA. zstepA. if_cases K3; zify_cond K3.                       (* [comment removed for export] *)
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [cbn [length] in LW; lia|].
        replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [w]))) by (rewrite length_app; cbn [length]; lia).
        eapply (IH (pre ++ [w])); [rewrite HW, <- app_assoc; reflexivity| discriminate| | lia| lia| lia].
        fin_lexmem.
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [| cbn [length] in LW; lia].
        stepA. stepA. stepA.                                                  (* [comment removed for export] *)
        cbn [ylex_want kw_post]. fin_at.
Qed.

(* [comment removed for export] *)
Lemma lex_kw_ull : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> 0 <= start < 2^32 -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (kw_post 7 e start (ylex_want want_ull (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x84c40) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start. intros LM BO SR ER. pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC).
  lex_prep ENV BC. pols.
  stepA. stepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.   (* [comment removed for export] *)
  zstoreA ENV.                                                            (* [comment removed for export] *)
  change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat (@length Z []))) at 1.
  eapply (want_ull_loop want_ull []); [reflexivity| discriminate| fin_lexmem| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma want_rue_loop : forall (rest pre : list Z) (rav s2v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  want_rue = pre ++ rest -> rest <> [] ->
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> 0 <= start < 2^32 -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (kw_post 0 e start (ylex_want rest (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz A_RUE) (wz (k_L K + 24)) (wz (k_L K + 28)) (wz (Z.of_nat (length pre))) s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x838ac) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction rest as [|w rest IH]; intros until start; intros HW NE (MU & WM & MI & ST & FR & OFF & LX & BC) BO SR ER; [congruence|].
  lex_prep ENV BC. unfold A_RUE in *.
  assert (LW : (length pre + length (w :: rest) = 3)%nat).
  { apply (f_equal (@length Z)) in HW. rewrite length_app in HW. exact (eq_sym HW). }
  cbn [length] in LW. cbn [ylex_want].
  pols.
  eofchkA K m0 ENV SH MU WM K0.
  2:{ (* [comment removed for export] *)
    stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [kw_post]. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdcharA0 K m0 ENV KP SH MU WM rdck_10a430 off.
  zstepA.                                                                  (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                                              (* [comment removed for export] *)
  shld (rd_shrue K m0 _ ENV SH MU WM (Z.of_nat (length pre)) ltac:(lia)).   (* [comment removed for export] *)
  txtld K m0 ENV SH MU WM off.                                              (* [comment removed for export] *)
  zstepA. try if_true.                                                      (* [comment removed for export] *)
  zstepA. zstepA. rewrite sext8_lo by lia.                                  (* [comment removed for export] *)
  zstepA. if_cases KS; zify_cond KS; [| kill KS].                           (* [comment removed for export] *)
  clear KS.
  assert (NTH : nth_error want_rue (length pre) = Some w).
  { rewrite HW. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
  assert (WR : 0 <= w < 256).
  { apply (proj1 (Forall_forall _ _) (proj1 want_bytes_range)). eapply nth_error_In. exact NTH. }
  pose proof (u8ro_read asegs _ 136544 (zbytes want_rue) (Z.of_nat (length pre)) (Z_to_bv 8 w) _ (rue_bytes _ MI)
                ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
  zstepA. cbn beta. rewrite (u8_val w) by lia. clear RD.                    (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2.                                        (* [comment removed for export] *)
  - replace (znth (k_txt K) off =? w) with true by (symmetry; apply Z.eqb_eq; lia).
    zstepA. stepA. zstepA. if_cases K3; zify_cond K3.                       (* [comment removed for export] *)
    + (* [comment removed for export] *)
      destruct rest as [|w2 rest2]; [cbn [length] in LW; lia|].
      replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [w]))) by (rewrite length_app; cbn [length]; lia).
      eapply (IH (pre ++ [w])); [rewrite HW, <- app_assoc; reflexivity| discriminate| | lia| lia| lia].
      fin_lexmem.
    + (* [comment removed for export] *)
      destruct rest as [|w2 rest2]; [| cbn [length] in LW; lia].
      stepA. stepA. stepA.                                                  (* [comment removed for export] *)
      cbn [ylex_want kw_post]. fin_at.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? w) with false by (symmetry; apply Z.eqb_neq; lia). cbn [kw_post].
    stepA.                                                                  (* [comment removed for export] *)
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.  (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia.                                    (* [comment removed for export] *)
    zstepA. if_cases KU; zify_cond KU; [kill KU| clear KU].                 (* [comment removed for export] *)
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.  (* [comment removed for export] *)
    zstepA. zstoreA ENV.                                                    (* [comment removed for export] *)
    replace (off + 1 + -1) with off by lia.
    stepA.                                                                  (* [comment removed for export] *)
    zstepA. zstepA. zstepA. shadow_addr. zstepA.                            (* [comment removed for export] *)
    shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. try if_true.    (* [comment removed for export] *)
    stepA. zstoreA ENV. stepA.                                              (* [comment removed for export] *)
    fin_at.
Qed.

(* [comment removed for export] *)
Lemma lex_kw_rue : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> 0 <= start < 2^32 -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (kw_post 0 e start (ylex_want want_rue (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83884) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start. intros LM BO SR ER. pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC).
  lex_prep ENV BC. pols.
  stepA. stepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.   (* [comment removed for export] *)
  zstoreA ENV.                                                            (* [comment removed for export] *)
  change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat (@length Z []))) at 1.
  eapply (want_rue_loop want_rue []); [reflexivity| discriminate| fin_lexmem| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma want_alse_loop : forall (rest pre : list Z) (rav s2v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  want_alse = pre ++ rest -> rest <> [] ->
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> 0 <= start < 2^32 -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (kw_post 0 e start (ylex_want rest (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz A_ALSE) (wz (k_L K + 24)) (wz (k_L K + 28)) (wz (Z.of_nat (length pre))) s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83c14) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction rest as [|w rest IH]; intros until start; intros HW NE (MU & WM & MI & ST & FR & OFF & LX & BC) BO SR ER; [congruence|].
  lex_prep ENV BC. unfold A_ALSE in *.
  assert (LW : (length pre + length (w :: rest) = 4)%nat).
  { apply (f_equal (@length Z)) in HW. rewrite length_app in HW. exact (eq_sym HW). }
  cbn [length] in LW. cbn [ylex_want].
  pols.
  eofchkA K m0 ENV SH MU WM K0.
  2:{ (* [comment removed for export] *)
    stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [kw_post]. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdcharA0 K m0 ENV KP SH MU WM rdck_10a798 off.
  zstepA.                                                                  (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                                              (* [comment removed for export] *)
  shld (rd_shalse K m0 _ ENV SH MU WM (Z.of_nat (length pre)) ltac:(lia)).  (* [comment removed for export] *)
  txtld K m0 ENV SH MU WM off.                                              (* [comment removed for export] *)
  zstepA. try if_true.                                                      (* [comment removed for export] *)
  zstepA. zstepA. rewrite sext8_lo by lia.                                  (* [comment removed for export] *)
  zstepA. if_cases KS; zify_cond KS; [| kill KS].                           (* [comment removed for export] *)
  clear KS.
  assert (NTH : nth_error want_alse (length pre) = Some w).
  { rewrite HW. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
  assert (WR : 0 <= w < 256).
  { apply (proj1 (Forall_forall _ _) (proj1 (proj2 want_bytes_range))). eapply nth_error_In. exact NTH. }
  pose proof (u8ro_read asegs _ 136576 (zbytes want_alse) (Z.of_nat (length pre)) (Z_to_bv 8 w) _ (alse_bytes _ MI)
                ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
  zstepA. cbn beta. rewrite (u8_val w) by lia. clear RD.                    (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2.                                        (* [comment removed for export] *)
  - replace (znth (k_txt K) off =? w) with true by (symmetry; apply Z.eqb_eq; lia).
    zstepA. stepA. zstepA. if_cases K3; zify_cond K3.                       (* [comment removed for export] *)
    + (* [comment removed for export] *)
      destruct rest as [|w2 rest2]; [cbn [length] in LW; lia|].
      replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [w]))) by (rewrite length_app; cbn [length]; lia).
      eapply (IH (pre ++ [w])); [rewrite HW, <- app_assoc; reflexivity| discriminate| | lia| lia| lia].
      fin_lexmem.
    + (* [comment removed for export] *)
      destruct rest as [|w2 rest2]; [| cbn [length] in LW; lia].
      stepA. stepA. stepA.                                                  (* [comment removed for export] *)
      cbn [ylex_want kw_post]. fin_at.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? w) with false by (symmetry; apply Z.eqb_neq; lia). cbn [kw_post].
    stepA.                                                                  (* [comment removed for export] *)
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.  (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia.                                    (* [comment removed for export] *)
    zstepA. if_cases KU; zify_cond KU; [kill KU| clear KU].                 (* [comment removed for export] *)
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.  (* [comment removed for export] *)
    zstepA. zstoreA ENV.                                                    (* [comment removed for export] *)
    replace (off + 1 + -1) with off by lia.
    stepA.                                                                  (* [comment removed for export] *)
    zstepA. zstepA. zstepA. shadow_addr. zstepA.                            (* [comment removed for export] *)
    shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. try if_false.   (* [comment removed for export] *)
    stepA. zstoreA ENV. stepA.                                              (* [comment removed for export] *)
    fin_at.
Qed.

(* [comment removed for export] *)
Lemma lex_kw_alse : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> 0 <= start < 2^32 -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (kw_post 0 e start (ylex_want want_alse (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83bec) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start. intros LM BO SR ER. pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC).
  lex_prep ENV BC. pols.
  stepA. stepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.   (* [comment removed for export] *)
  zstoreA ENV.                                                            (* [comment removed for export] *)
  change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat (@length Z []))) at 1.
  eapply (want_alse_loop want_alse []); [reflexivity| discriminate| fin_lexmem| lia| lia| lia].
Qed.
End S.
End RC__1.
