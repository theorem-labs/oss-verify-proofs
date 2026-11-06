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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex.
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
Definition kw_post (m0 : mem) (tokc e start : Z) (r : wres) : machine_state -> Prop :=
  match r with
  | W_ok o => lex_at K m0 J_TOK (wz tokc) e o start
  | W_eof o => fun ms' => exists s0v, lex_at K m0 J_EOF s0v e o start ms'
  | W_bad o => lex_at K m0 J_TOK (wz 4) 6 o start
  end.

(* [comment removed for export] *)
Lemma want_ull_loop : forall (rest pre : list Z) (rav s1v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  want_ull = pre ++ rest -> rest <> [] ->
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (kw_post m0 7 e start (ylex_want rest (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (A_ULL + Z.of_nat (length pre))) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) (wz (Z.of_nat (length rest))) s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x149a4) (k_fc K) None m (seg_rom rsegs)).
Proof.
  induction rest as [|w rest IH]; intros until start; intros HW NE TX0 (MU & WM & MI & STK & FR & OFF & LX & BC) BO; [congruence|].
  lex_prep ENV BC. unfold A_ULL in *.
  assert (LW : (length pre + length (w :: rest) = 3)%nat).
  { apply (f_equal (@length Z)) in HW. rewrite length_app in HW. exact (eq_sym HW). }
  cbn [length] in LW. cbn [ylex_want].
  replace (Z.of_nat (length (w :: rest))) with (Z.of_nat (length rest) + 1) by (cbn [length]; lia).
  eofchk K0.
  - (* [comment removed for export] *)
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [kw_post]. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    assert (NTH : nth_error want_ull (length pre) = Some w).
    { rewrite HW. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    assert (WR : 0 <= w < 256).
    { apply (proj1 (Forall_forall _ _) ((fun H => proj2 (proj2 H)) want_bytes_range)). eapply nth_error_In. exact NTH. }
    pose proof (u8ro_read rsegs _ 67193 (zbytes want_ull) (Z.of_nat (length pre)) (Z_to_bv 8 w) _ (ull_bytes _ MI)
                  ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
    zstep. cbn beta. rewrite (u8_val w) by lia. clear RD.
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? w) with false by (symmetry; apply Z.eqb_neq; lia). cbn [kw_post].
      unread. zstep. zstep. zstep. zstep. zstep.
      replace (off + 1 + -1) with off by lia. fin_at.
    + replace (znth (k_txt K) off =? w) with true by (symmetry; apply Z.eqb_eq; lia).
      zstep. zstep. zstep. if_cases K3; zify_cond K3.
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [cbn [length] in K3; lia|].
        replace (67193 + Z.of_nat (length pre) + 1) with (67193 + Z.of_nat (length (pre ++ [w]))) by (rewrite length_app; cbn [length]; lia).
        replace (Z.of_nat (length (w2 :: rest2)) + 1 + -1) with (Z.of_nat (length (w2 :: rest2))) by lia.
        eapply (IH (pre ++ [w])); [rewrite HW, <- app_assoc; reflexivity| discriminate| exact TX0| | lia].
        fin_lexmem.
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [| cbn [length] in K3; lia].
        zstep. zstep.
        cbn [ylex_want kw_post]. fin_at.
Qed.

(* [comment removed for export] *)
Lemma lex_kw_ull : forall (rav s0v s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (kw_post m0 7 e start (ylex_want want_ull (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14998) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC).
  lex_prep ENV BC.
  zstep. zstep. zstep.
  change (Z_to_bv 64 67193) with (Z_to_bv 64 (A_ULL + Z.of_nat (@length Z []))).
  change (Z_to_bv 64 3) with (Z_to_bv 64 (Z.of_nat (length want_ull))).
  eapply (want_ull_loop want_ull []); [reflexivity| discriminate| exact TX0| exact LM| exact BO].
Qed.

(* [comment removed for export] *)
Lemma want_rue_loop : forall (rest pre : list Z) (rav s1v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  want_rue = pre ++ rest -> rest <> [] ->
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (kw_post m0 0 e start (ylex_want rest (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (A_RUE + Z.of_nat (length pre))) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) (wz (Z.of_nat (length rest))) s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14214) (k_fc K) None m (seg_rom rsegs)).
Proof.
  induction rest as [|w rest IH]; intros until start; intros HW NE TX0 (MU & WM & MI & STK & FR & OFF & LX & BC) BO; [congruence|].
  lex_prep ENV BC. unfold A_RUE in *.
  assert (LW : (length pre + length (w :: rest) = 3)%nat).
  { apply (f_equal (@length Z)) in HW. rewrite length_app in HW. exact (eq_sym HW). }
  cbn [length] in LW. cbn [ylex_want].
  replace (Z.of_nat (length (w :: rest))) with (Z.of_nat (length rest) + 1) by (cbn [length]; lia).
  eofchk K0.
  - (* [comment removed for export] *)
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [kw_post]. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    assert (NTH : nth_error want_rue (length pre) = Some w).
    { rewrite HW. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    assert (WR : 0 <= w < 256).
    { apply (proj1 (Forall_forall _ _) ((fun H => proj1 H) want_bytes_range)). eapply nth_error_In. exact NTH. }
    pose proof (u8ro_read rsegs _ 67021 (zbytes want_rue) (Z.of_nat (length pre)) (Z_to_bv 8 w) _ (rue_bytes _ MI)
                  ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
    zstep. cbn beta. rewrite (u8_val w) by lia. clear RD.
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? w) with false by (symmetry; apply Z.eqb_neq; lia). cbn [kw_post].
      unread. zstep. zstep. zstep. zstep. zstep.
      replace (off + 1 + -1) with off by lia. fin_at.
    + replace (znth (k_txt K) off =? w) with true by (symmetry; apply Z.eqb_eq; lia).
      zstep. zstep. zstep. if_cases K3; zify_cond K3.
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [cbn [length] in K3; lia|].
        replace (67021 + Z.of_nat (length pre) + 1) with (67021 + Z.of_nat (length (pre ++ [w]))) by (rewrite length_app; cbn [length]; lia).
        replace (Z.of_nat (length (w2 :: rest2)) + 1 + -1) with (Z.of_nat (length (w2 :: rest2))) by lia.
        eapply (IH (pre ++ [w])); [rewrite HW, <- app_assoc; reflexivity| discriminate| exact TX0| | lia].
        fin_lexmem.
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [| cbn [length] in K3; lia].
        zstep. zstep. zstep.
        cbn [ylex_want kw_post]. fin_at.
Qed.

(* [comment removed for export] *)
Lemma lex_kw_rue : forall (rav s0v s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (kw_post m0 0 e start (ylex_want want_rue (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14208) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC).
  lex_prep ENV BC.
  zstep. zstep. zstep.
  change (Z_to_bv 64 67021) with (Z_to_bv 64 (A_RUE + Z.of_nat (@length Z []))).
  change (Z_to_bv 64 3) with (Z_to_bv 64 (Z.of_nat (length want_rue))).
  eapply (want_rue_loop want_rue []); [reflexivity| discriminate| exact TX0| exact LM| exact BO].
Qed.

(* [comment removed for export] *)
Lemma want_alse_loop : forall (rest pre : list Z) (rav s1v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  want_alse = pre ++ rest -> rest <> [] ->
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (kw_post m0 0 e start (ylex_want rest (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (A_ALSE + Z.of_nat (length pre))) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) (wz (Z.of_nat (length rest))) s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14370) (k_fc K) None m (seg_rom rsegs)).
Proof.
  induction rest as [|w rest IH]; intros until start; intros HW NE TX0 (MU & WM & MI & STK & FR & OFF & LX & BC) BO; [congruence|].
  lex_prep ENV BC. unfold A_ALSE in *.
  assert (LW : (length pre + length (w :: rest) = 4)%nat).
  { apply (f_equal (@length Z)) in HW. rewrite length_app in HW. exact (eq_sym HW). }
  cbn [length] in LW. cbn [ylex_want].
  replace (Z.of_nat (length (w :: rest))) with (Z.of_nat (length rest) + 1) by (cbn [length]; lia).
  eofchk K0.
  - (* [comment removed for export] *)
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [kw_post]. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    assert (NTH : nth_error want_alse (length pre) = Some w).
    { rewrite HW. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    assert (WR : 0 <= w < 256).
    { apply (proj1 (Forall_forall _ _) ((fun H => proj1 (proj2 H)) want_bytes_range)). eapply nth_error_In. exact NTH. }
    pose proof (u8ro_read rsegs _ 67062 (zbytes want_alse) (Z.of_nat (length pre)) (Z_to_bv 8 w) _ (alse_bytes _ MI)
                  ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
    zstep. cbn beta. rewrite (u8_val w) by lia. clear RD.
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? w) with false by (symmetry; apply Z.eqb_neq; lia). cbn [kw_post].
      unread. zstep. zstep. zstep. zstep. zstep.
      replace (off + 1 + -1) with off by lia. fin_at.
    + replace (znth (k_txt K) off =? w) with true by (symmetry; apply Z.eqb_eq; lia).
      zstep. zstep. zstep. if_cases K3; zify_cond K3.
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [cbn [length] in K3; lia|].
        replace (67062 + Z.of_nat (length pre) + 1) with (67062 + Z.of_nat (length (pre ++ [w]))) by (rewrite length_app; cbn [length]; lia).
        replace (Z.of_nat (length (w2 :: rest2)) + 1 + -1) with (Z.of_nat (length (w2 :: rest2))) by lia.
        eapply (IH (pre ++ [w])); [rewrite HW, <- app_assoc; reflexivity| discriminate| exact TX0| | lia].
        fin_lexmem.
      * (* [comment removed for export] *)
        destruct rest as [|w2 rest2]; [| cbn [length] in K3; lia].
        zstep. zstep.
        cbn [ylex_want kw_post]. fin_at.
Qed.

(* [comment removed for export] *)
Lemma lex_kw_alse : forall (rav s0v s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off -> 0 <= off <= zlength (k_txt K) ->
  evt rsegs (kw_post m0 0 e start (ylex_want want_alse (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14364) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC).
  lex_prep ENV BC.
  zstep. zstep. zstep.
  change (Z_to_bv 64 67062) with (Z_to_bv 64 (A_ALSE + Z.of_nat (@length Z []))).
  change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat (length want_alse))).
  eapply (want_alse_loop want_alse []); [reflexivity| discriminate| exact TX0| exact LM| exact BO].
Qed.

End S.
End RC__1.
