(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy F_strspn ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep ECH_LibState ECH_LibFrame ECH_Rostr ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_dup ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4 ECH_C6_stmt ECH_C7_stmt ECH_C8_blockA ECH_C13_stmt ECH_C14_stmt ECH_KitSeg ECH_LibMid ECH_UbKit ECH_C14_bio2buf ECH_C14_ladder ECH_C14_ladloop ECH_C14_tail ECH_C14_b2b.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FM_PC0 : Z := 0x2b2f94.      (* [comment removed for export] *)
Definition FM_R603_1 : Z := 0x2b3094.   (* [comment removed for export] *)
Definition FM_R603_2 : Z := 0x2b30b0.   (* [comment removed for export] *)
Definition FM_RDUP : Z := 0x2b3008.     (* [comment removed for export] *)
Definition FM_RMAL : Z := 0x2b3034.     (* [comment removed for export] *)
Definition FM_RCPY : Z := 0x2b3048.     (* [comment removed for export] *)
Definition FM_RSPN : Z := 0x2b306c.     (* [comment removed for export] *)
Definition FM_RFRE : Z := 0x2b3088.     (* [comment removed for export] *)
Definition FM_DEC : Z := 0x2b319c.      (* [comment removed for export] *)
Definition FM_B64 : Z := 0x2b3114.      (* [comment removed for export] *)
Definition A_B64_ALPHABET : Z := 0x72224.   (* [comment removed for export] *)
Definition S_b64_alphabet : list byte := Eval vm_compute in img_cstr A_B64_ALPHABET 80.
Definition K_b64_alphabet : list byte := Eval vm_compute in img_slack A_B64_ALPHABET (length S_b64_alphabet).

(* [comment removed for export] *)
Definition is_bin_fmt (ds : list byte) (L : Z) : bool :=
  match ds with
  | b0 :: b1 :: b2 :: b3 :: _ => (256 * bv_unsigned b0 + bv_unsigned b1 + 2 =? L) && (bv_unsigned b2 =? 254) && (bv_unsigned b3 =? 13)
  | _ => false
  end.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma R_b64_alphabet : ROSTR A_B64_ALPHABET S_b64_alphabet K_b64_alphabet.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rp_g603a : rp_glue FM_R603_1 FM_R603_2 P_ERR_set_debug A_ECHS_FILE_RP 603 A_ECHS_FUNC_RP.
  Proof.
    unfold rp_glue, FM_R603_2, P_ERR_set_debug, A_ECHS_FILE_RP, A_ECHS_FUNC_RP. intros.
    replace (ret_pc (Z_to_bv 64 FM_R603_1)) with (Z_to_bv 64 FM_R603_1) by (symmetry; apply ret_pc_even; [unfold FM_R603_1; lia| reflexivity]).
    unfold FM_R603_1. do 7 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma rp_g603b : rp_glue FM_R603_2 RP_ERRL0 P_ERR_set_error ERR_LIB_SSL R_PASSED_INVALID_ARGUMENT 0.
  Proof.
    unfold rp_glue, RP_ERRL0, P_ERR_set_error, ERR_LIB_SSL, R_PASSED_INVALID_ARGUMENT. intros.
    replace (ret_pc (Z_to_bv 64 FM_R603_2)) with (Z_to_bv 64 FM_R603_2) by (symmetry; apply ret_pc_even; [unfold FM_R603_2; lia| reflexivity]).
    unfold FM_R603_2. do 6 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fm_seg1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : Z),
      0 <= L < 5 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FM_R603_1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 5) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 L) s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 L) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FM_PC0) fc None m (seg_rom usegs)).
  Proof.
    intros until L. intros LR MI. unfold FM_PC0, FM_R603_1, P_ERR_new.
    step. step. try (if_cases K2; zify_cond K2; [| kill K2]; clear K2). step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fm_seg2 :
    forall (rax sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A L n K : Z) (ds : list byte),
      5 <= L < 2^20 -> n + K = L -> 0 <= K < 2^20 -> 0 <= n -> 0 < A -> A + L < 2^63 ->
      bytes_at usegs m A ds -> zlength ds = L -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0,
          ms' = if is_bin_fmt ds L
                then MS (mkR (Z_to_bv 64 FM_RDUP) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 607) a4 a5 a6 a7
                             s2 s3 s4 s5 s6 (Z_to_bv 64 L) (Z_to_bv 64 n) (Z_to_bv 64 (- K)) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom usegs)
                else MS (mkR (Z_to_bv 64 FM_RMAL) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (L + 1)) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 166) u0 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 (Z_to_bv 64 L) (Z_to_bv 64 n) (Z_to_bv 64 (- K)) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 L) (Z_to_bv 64 n) (Z_to_bv 64 (- K)) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FM_PC0) fc None m (seg_rom usegs)).
  Proof.
    intros until ds. intros LR NK KR NR AP AH DS DSL MI. unfold FM_PC0, FM_RDUP, FM_RMAL, P_CRYPTO_memdup, P_CRYPTO_malloc, A_ECHS_FILE_RP.
    unfold zlength in DSL.
    destruct ds as [|b0 [|b1 [|b2 [|b3 ds4]]]]; try (cbn in DSL; exfalso; lia).
    pose proof (byte_range b0) as B0. pose proof (byte_range b1) as B1. pose proof (byte_range b2) as B2. pose proof (byte_range b3) as B3.
    pose proof (rd_raw _ _ _ 0 b0 DS eq_refl ltac:(lia)) as RD0. replace (A + 0) with A in RD0 by lia.
    pose proof (rd_raw _ _ _ 1 b1 DS eq_refl ltac:(lia)) as RD1.
    pose proof (rd_raw _ _ _ 2 b2 DS eq_refl ltac:(lia)) as RD2.
    pose proof (rd_raw _ _ _ 3 b3 DS eq_refl ltac:(lia)) as RD3.
    step. step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2).
    (* [comment removed for export] *)
    step. step. ub_dead_by (clear - AP AH LR).
    step. unfold zxb. step. unfold zxb. step. step.
    rewrite (unsigned_lit (bv_unsigned b1)) by lia. rewrite (unsigned_lit (bv_unsigned b0)) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned b0 * 2 ^ 8)) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia).
    rewrite (lor_add_disjoint _ _ 8) by lia. change (2 ^ 8) with 256.
    step. replace (n + K) with L by (clear - NK; lia). step. rewrite (unsigned_lit (bv_unsigned b1 + bv_unsigned b0 * 256)) by (clear - B0 B1; lia). step. step.
    cbn [is_bin_fmt].
    destruct (Z.eqb_spec (256 * bv_unsigned b0 + bv_unsigned b1 + 2) L) as [E1|NE1].
    - replace (Z_to_bv 64 (L + - (bv_unsigned b1 + bv_unsigned b0 * 256))) with (Z_to_bv 64 2 : word) by (f_equal; clear - E1; lia).
      if_cases K2; zify_cond K2; [exfalso; apply K2; reflexivity|]. clear K2.
      (* [comment removed for export] *)
      step. step. ub_dead_by (clear - AP AH LR).
      step. unfold zxb. step.
      destruct (Z.eqb_spec (bv_unsigned b2) 254) as [E2|NE2].
      + rewrite E2. step. if_lit.
        (* [comment removed for export] *)
        step. step. ub_dead_by (clear - AP AH LR).
        step. unfold zxb. step.
        destruct (Z.eqb_spec (bv_unsigned b3) 13) as [E3|NE3].
        * rewrite E3. step. if_lit. do 7 step.
          cbn [andb]. apply evt_done. exists a3. reflexivity.
        * step. if_cases K2; zify_cond K2; [| kill K2]. clear K2.
          cbn [andb].
          step. replace (n + K) with L by (clear - NK; lia). do 6 step. apply evt_done. eexists. reflexivity.
      + step. if_cases K2; zify_cond K2; [| kill K2]. clear K2.
        cbn [andb].
        step. replace (n + K) with L by (clear - NK; lia). do 6 step. apply evt_done. eexists. reflexivity.
    - if_cases K2; zify_cond K2.
      2: { exfalso. clear - K2 NE1 LR B0 B1. change 18446744073709551615 with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia. Z.div_mod_to_equations. lia. }
      clear K2. cbn [andb].
      step. replace (n + K) with L by (clear - NK; lia). do 6 step. apply evt_done. eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fm_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb : Z),
      0 < Bb < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FM_RDUP) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Bb) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3 s4 s5 (Z_to_bv 64 Bb) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 FM_DEC) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FM_RDUP) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Bb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FM_RDUP)) fc None m (seg_rom usegs)).
  Proof.
    intros until Bb. intros BR MI.
    replace (ret_pc (Z_to_bv 64 FM_RDUP)) with (Z_to_bv 64 FM_RDUP) by (symmetry; apply ret_pc_even; [unfold FM_RDUP; lia| reflexivity]).
    unfold FM_RDUP, FM_DEC. step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2). step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fm_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Cp : Z),
      0 < Cp < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FM_RCPY) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Cp) s1 s7 a3 a4 a5 a6 a7 (Z_to_bv 64 Cp) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x2c04f0) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FM_RMAL) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Cp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FM_RMAL)) fc None m (seg_rom usegs)).
  Proof.
    intros until Cp. intros CR MI.
    replace (ret_pc (Z_to_bv 64 FM_RMAL)) with (Z_to_bv 64 FM_RMAL) by (symmetry; apply ret_pc_even; [unfold FM_RMAL; lia| reflexivity]).
    unfold FM_RMAL, FM_RCPY. step. try (if_cases K2; zify_cond K2; [kill K2|]; clear K2). do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fm_seg5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Cp n K L : Z) (cp : list byte) (jb : byte),
      0 < Cp -> Cp + L + 1 < 2^63 -> n + K = L -> 0 <= n -> 0 <= K -> 0 <= L -> length cp = Z.to_nat L ->
      rw_cells usegs m Cp [CB (Z.to_nat L) cp; CB 1 [jb]] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 FM_RSPN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Cp) (Z_to_bv 64 A_B64_ALPHABET) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Cp) s3 s4 s5 s6 (Z_to_bv 64 L) (Z_to_bv 64 n) (Z_to_bv 64 (- K)) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x2c122c) fc None m1 (seg_rom usegs)
          /\ munch [(Cp + L, Cp + L + 1)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 Cp [CB (Z.to_nat L) cp; CB 1 [Z_to_bv 8 0]])
        (MS (mkR (Z_to_bv 64 FM_RCPY) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Cp) s3 s4 s5 s6 (Z_to_bv 64 L) (Z_to_bv 64 n) (Z_to_bv 64 (- K)) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FM_RCPY)) fc None m (seg_rom usegs)).
  Proof.
    intros until jb. intros CP CH NK NR KR LR CPL CELLS MI.
    replace (ret_pc (Z_to_bv 64 FM_RCPY)) with (Z_to_bv 64 FM_RCPY) by (symmetry; apply ret_pc_even; [unfold FM_RCPY; lia| reflexivity]).
    unfold FM_RCPY, FM_RSPN, A_B64_ALPHABET.
    pose proof (munch_refl [(Cp + L, Cp + L + 1)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    apply (proj1 (rw_cells_app usegs m Cp [CB (Z.to_nat L) cp] [CB 1 [jb]])) in CELLS. destruct CELLS as [CPa CPb].
    cbn [cells_size csize Nat.add] in CPb. replace (Cp + Z.of_nat (Z.to_nat L + 0)) with (Cp + L) in CPb by lia.
    apply (rw_cells_recut _ _ _ [C1 jb]) in CPb; [| cbn; split; exact I| reflexivity].
    (* [comment removed for export] *)
    step. ubnot. step. ub_dead_by (clear - CP CH LR).
    step. step. replace (Cp + n + K) with (Cp + L) by lia.
    set (Q := Cp + L) in *. st1. subst Q.
    do 4 step. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    apply (proj2 (rw_cells_app usegs _ Cp [CB (Z.to_nat L) cp] [CB 1 [Z_to_bv 8 0]])). split; [exact CPa|].
    cbn [cells_size csize Nat.add]. replace (Cp + Z.of_nat (Z.to_nat L + 0)) with (Cp + L) by lia.
    eapply (rw_cells_recut _ _ [C1 (Z_to_bv 8 0)]); [exact CPb| cbn; split; [reflexivity| exact I]| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fm_seg6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (span : Z),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FM_RFRE) sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 172) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 span) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FM_RSPN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 span) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FM_RSPN)) fc None m (seg_rom usegs)).
  Proof.
    intros until span. intros MI.
    replace (ret_pc (Z_to_bv 64 FM_RSPN)) with (Z_to_bv 64 FM_RSPN) by (symmetry; apply ret_pc_even; [unfold FM_RSPN; lia| reflexivity]).
    unfold FM_RSPN, FM_RFRE, P_CRYPTO_free, A_ECHS_FILE_RP. do 7 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fm_seg7 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (span L : Z),
      0 <= span < 2^63 -> 0 <= L < 2^63 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (if span <? L then Z_to_bv 64 FM_R603_1 else Z_to_bv 64 FM_RFRE) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 span) (Z_to_bv 64 L) s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 (if span <? L then P_ERR_new else FM_B64)) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FM_RFRE) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 span) (Z_to_bv 64 L) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FM_RFRE)) fc None m (seg_rom usegs)).
  Proof.
    intros until L. intros SR LR MI.
    replace (ret_pc (Z_to_bv 64 FM_RFRE)) with (Z_to_bv 64 FM_RFRE) by (symmetry; apply ret_pc_even; [unfold FM_RFRE; lia| reflexivity]).
    unfold FM_RFRE, FM_R603_1, FM_B64, P_ERR_new.
    destruct (Z.ltb_spec span L) as [LT|GE].
    - step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. step. step. apply evt_done. reflexivity.
    - step. if_cases K2; zify_cond K2; [| kill K2]. clear K2. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section K2.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma nul_split : forall (ds : list byte), exists str rest,
    ds ++ [Z_to_bv 8 0] = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str /\ (length str <= length ds)%nat /\ (length str = length ds -> str = ds).
  Proof.
    induction ds as [|b ds IH].
    - exists [], []. cbn. repeat split; auto. 
    - destruct IH as (str & rest & E & NI & LE & EQ).
      destruct (Z.eq_dec (bv_unsigned b) 0) as [Z0|NZ].
      + assert (Hb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Z0; reflexivity).
        exists [], (ds ++ [Z_to_bv 8 0]). subst b. cbn. repeat split; [tauto| lia| intros K; exfalso; lia].
      + exists (b :: str), rest. cbn. rewrite E. repeat split.
        * intros [K|K]; [| exact (NI K)]. apply NZ. rewrite K. reflexivity.
        * lia.
        * intros K. f_equal. apply EQ. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_stack_fmt_gen : forall cph eph,
       CMEMDUP_STACK + 2368 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 512 + Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) RREALLOC_STACK
    /\ CMALLOC_STACK + 2368 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 512 + Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) RREALLOC_STACK
    /\ CFREE_STACK + 2368 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 512 + Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) RREALLOC_STACK.
  Proof. clear. intros [|?] [|?]; repeat split; vm_compute; discriminate. Qed.
  Lemma rc_stack_fmt : forall M, CMEMDUP_STACK + 2368 <= READCFG_STACK M /\ CMALLOC_STACK + 2368 <= READCFG_STACK M /\ CFREE_STACK + 2368 <= READCFG_STACK M.
  Proof. intros M. unfold READCFG_STACK, mid_stack. apply rc_stack_fmt_gen. Qed.

  Lemma S_b64_alphabet_len : length S_b64_alphabet = 66%nat.
  Proof. reflexivity. Qed.
End K2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis CERTO3 : egs_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let HRE : realloc_sr_stmt H := proj1 (proj2 HX).
  Let STATICS : statics_of_RHEAP H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word).
  Hypotheses (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo)
             (MBO : MEMBIO LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (DS : bytes_at usegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : hs_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : hs_KREL H s mo)
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H)
             (BUDG : lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H)
             (AUX : hs_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk usegs m lo (bv_unsigned sp)) (CEIL : hceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M)
             (ERR : rw_cells usegs m (errno_addr tp) [C4 errv]) (MI : mem_inv usegs m) (TP : tp = Z_to_bv 64 RATP) (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Local Notation L0c := (L0 LB M).
  Local Notation SPc := (SP' sp).
  Local Notation RBPc := (RBP sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation RCFACTS := (rc_facts H HX ra sp tp a0 a1 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).

  Local Ltac img_static := unfold RERRNO, A_malloc_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Definition fwk (Lx : list block) (p : bptr) (A nA : Z) (R' : membio) (j0 j2 : list byte) (rb : word) (m' : mem) (mo' : Model) (s' : PState) : Prop :=
       hs_RHEAP H s' (Lx ++ (p, A, nA) :: L0c) m' /\ hs_KREL H s' mo' /\ hs_MPRES H mo mo'
    /\ MEMBIO LB m' mb R' /\ mb_static R R' /\ mb_pos R' = mb_len R /\ 1 <= mb_len R <= nA /\ nA <= 512 * 3     (* [comment removed for export] *)
    /\ bytes_at usegs m' (mb_buf R) ds /\ bytes_at usegs m' A ds
    /\ rw_cells usegs m' SPc [CB 48 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st)]
    /\ rw_cells usegs m' RBPc [C8 rb] /\ rw_cells usegs m' (bv_unsigned sp + -2288) (CB 2184 j2 :: SAVESc)
    /\ (exists errv', rw_cells usegs m' RERRNO [C4 errv']) /\ LIBMID LIB m' M
    /\ mem_inv usegs m' /\ stk usegs m' lo SPc /\ hs_rauxv_ok H m' B
    /\ xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m'.

  (* [comment removed for export] *)
  Definition rp_decK0 : Prop :=
    forall (p : bptr) (A nA : Z) (R' : membio) (j0 j2 : list byte) (rb : word) (m' : mem) (mo' : Model) (s' : PState) (pbin : bptr) (Bb : Z)
           (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s3w s4w s5w s8w s9w s10w s11w u3 u4 u5 u6 : word),
      5 <= mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      fwk [(pbin, Bb, mb_len R)] p A nA R' j0 j2 rb m' mo' s' ->
      rw_cells usegs m' Bb [CB (Z.to_nat (mb_len R)) ds] ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) a0w b1 b2 b3 b4 b5 b6 b7
                                    (Z_to_bv 64 0) s3w s4w s5w (Z_to_bv 64 Bb) (Z_to_bv 64 (mb_len R)) s8w s9w s10w s11w u3 u4 u5 u6)
                               F (Z_to_bv 64 FM_DEC) fc None m' (seg_rom usegs)) mo').

  (* [comment removed for export] *)
  Definition rp_b64K : Prop :=
    forall (k n : Z) (p : bptr) (A : Z) (R' : membio) (j0 j2 : list byte) (m' : mem) (mo' : Model) (s' : PState)
           (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s10w s11w u3 u4 u5 u6 : word),
      0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 -> 5 <= mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      fwk [] p A (512 * (k + 1)) R' j0 j2 (wz n) m' mo' s' ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) a0w b1 b2 b3 b4 b5 b6 b7
                                    s2w s3w s4w s5w s6w (Z_to_bv 64 (mb_len R)) (Z_to_bv 64 n) (Z_to_bv 64 (- (512 * k))) s10w s11w u3 u4 u5 u6)
                               F (Z_to_bv 64 FM_B64) fc None m' (seg_rom usegs)) mo').

  (* [comment removed for export] *)
  Lemma fwk_lib : forall Lx p A nA R' j0 j2 rb m' mo' s', fwk Lx p A nA R' j0 j2 rb m' mo' s' -> MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Proof using MF1.
    intros until s'. intros FW. pose proof FW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LM1 & _).
    pose proof LM1 as (IM & MF & _ & _ & _ & _ & _ & _ & GM & _). rewrite MF1 in MF. split; [exact MF| split; [exact IM| exact GM]].
  Qed.

  (* [comment removed for export] *)
  Lemma mb_blocks_LB : forall R', mb_static R R' -> forall b, In b (blocks_MEMBIO mb R') -> In b LB.
  Proof using MBO.
    intros R' MST b Hb. rewrite (mb_static_blocks mb R R' MST) in Hb.
    destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fwk_x : forall Lx Lx' p A nA R' j0 j2 rb m1 mo1 s1' m2 mo2 s2',
    fwk Lx p A nA R' j0 j2 rb m1 mo1 s1' ->
    xpres ((p, A, nA) :: L0c) SPc [] m1 m2 ->
    hs_RHEAP H s2' (Lx' ++ (p, A, nA) :: L0c) m2 -> hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 ->
    (exists errv', rw_cells usegs m2 RERRNO [C4 errv']) -> mem_inv usegs m2 -> stk usegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    fwk Lx' p A nA R' j0 j2 rb m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX.
    intros until s2'. intros FW XP HP2 KREL2 MP2 ERR2 MI2 ST2 AUX2.
    pose proof FW as (HP1 & KREL1 & MP1 & MBO1 & MST & POS & LR & NAR & DSm1 & DSA1 & FRlo1 & RB1 & FRhi1 & ERR1 & LM1 & MI1 & ST1 & AUX1 & XA1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in DSL.
    assert (SUB1 : forall b, In b LB -> In b ((p, A, nA) :: L0c)) by (intros b Hb; right; exact (SUB0 _ Hb)).
    assert (XPL : xpres LB SPc [] m1 m2) by (eapply xpres_weaken; [exact XP| clear; lia| exact SUB1| intros q Hq; exact Hq]).
    unfold fwk. repeat match goal with |- _ /\ _ => split end; try assumption; try (clear - LR; lia).
    - eapply (MEMBIO_frame0 LB LB SPc); [exact MBO1| exact (mb_blocks_LB R' MST)| exact XPL].
    - destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN _]].
      eapply xpres_bytes_at'; [exact XPL| exact DSm1| right; right; exists (pD, mb_buf R, mb_len R); split; [exact PIN| cbn; rewrite DSL; clear; lia]| apply Forall_nil].
    - eapply xpres_bytes_at'; [exact XP| exact DSA1| right; right; exists (p, A, nA); split; [left; reflexivity| cbn; rewrite DSL; clear - LR; lia]| apply Forall_nil].
    - eapply xpres_rw_cells'; [exact XP| exact FRlo1| left; clear; lia| apply Forall_nil].
    - eapply xpres_rw_cells'; [exact XP| exact RB1| left; unfold SP', RBP; clear; lia| apply Forall_nil].
    - eapply xpres_rw_cells'; [exact XP| exact FRhi1| left; unfold SP'; clear; lia| apply Forall_nil].
    - eapply (LIBMID_xpres0 LIB ((p, A, nA) :: L0c) SPc); [exact LM1| exact XP| intros b Hb; right; exact (SUB0 _ (SUBL _ Hb))].
    - eapply xpres_trans; [exact XA1|]. eapply xpres_weaken; [exact XPL| unfold SP'; clear; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq].
  Qed.

  (* [comment removed for export] *)
  Lemma fwk_w : forall pc Ac nc p A nA R' j0 j2 rb m1 mo1 s1' m2 W,
    fwk [(pc, Ac, nc)] p A nA R' j0 j2 rb m1 mo1 s1' ->
    munch W m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 -> stk usegs m2 lo SPc ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= SPc) \/ (Ac <= fst iv /\ snd iv <= Ac + nc)) W ->
    fwk [(pc, Ac, nc)] p A nA R' j0 j2 rb m2 mo1 s1'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX.
    intros until W. intros FW MU WM MI2 ST2 FWW.
    pose proof FW as (HP1 & KREL1 & MP1 & MBO1 & MST & POS & LR & NAR & DSm1 & DSA1 & FRlo1 & RB1 & FRhi1 & [errv1 ERR1] & LM1 & MI1 & ST1 & AUX1 & XA1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in DSL.
    cbn [app] in HP1.
    destruct (lad_head_facts H HX ((p, A, nA) :: L0c) _ _ _ _ _ HP1) as (BRc & BHc & NIPc & DISJc & BELc).
    pose proof BRc as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
    assert (SUB1 : forall b, In b LB -> In b ((p, A, nA) :: L0c)) by (intros b Hb; right; exact (SUB0 _ Hb)).
    assert (XP : xpres ((p, A, nA) :: L0c) SPc [] m1 m2).
    { eapply (xpres_of_munch_fresh H HH); [exact HP1| unfold SP'; clear - CEIL LO STK0; lia| exact MU| exact WM|].
      eapply Forall_impl; [| exact FWW]. cbn beta. intros iv [[K1 K2]|[K1 K2]]; [left; split; [clear - K1 CEIL; lia| exact K2]| right; left; split; assumption]. }
    assert (XPL : xpres LB SPc [] m1 m2) by (eapply xpres_weaken; [exact XP| clear; lia| exact SUB1| intros q Hq; exact Hq]).
    assert (DJ : forall a n, a + n <= hceil -> (a + n <= Ac \/ Ac + nc <= a) -> disjoint_from W a n).
    { intros a n Hh Hb. clear - FWW Hh Hb CEIL. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FWW) as K. cbn in K.
      split; [lia| apply IH; eapply Forall_inv_tail; exact FWW]. }
    assert (DJS : forall a n, SPc <= a -> disjoint_from W a n).
    { intros a n Ha. clear - FWW Ha BHc CEIL LO STK0. unfold SP' in *. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FWW) as K. cbn in K.
      split; [lia| apply IH; eapply Forall_inv_tail; exact FWW]. }
    unfold fwk. repeat match goal with |- _ /\ _ => split end; try assumption; try (clear - LR; lia).
    - cbn [app]. eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta.
      intros iv [[K1 K2]|[K1 K2]]; [left; clear - K1 CEIL; lia| right; right; exists (pc, Ac, nc); split; [left; reflexivity| cbn; split; assumption]].
    - eapply (MEMBIO_frame0 LB LB SPc); [exact MBO1| exact (mb_blocks_LB R' MST)| exact XPL].
    - destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN _]].
      pose proof (DISJc _ (SUB1 _ PIN)) as D. pose proof (BELc _ (SUB1 _ PIN)) as E. cbn [blk_addr blk_size fst snd] in D, E.
      eapply bytes_at_transport; [exact DSm1| exact MU| apply DJ; rewrite DSL; [clear - E; lia| clear - D; lia]].
    - pose proof (DISJc _ (or_introl eq_refl)) as D. pose proof (BELc _ (or_introl eq_refl)) as E. cbn [blk_addr blk_size fst snd] in D, E.
      eapply bytes_at_transport; [exact DSA1| exact MU| apply DJ; rewrite DSL; [clear - E LR; lia| clear - D LR; lia]].
    - eapply rw_cells_transport; [exact FRlo1| exact MU| exact WM| apply DJS; clear; lia].
    - eapply rw_cells_transport; [exact RB1| exact MU| exact WM| apply DJS; unfold RBP, SP'; clear; lia].
    - eapply rw_cells_transport; [exact FRhi1| exact MU| exact WM| apply DJS; unfold SP'; clear; lia].
    - exists errv1. eapply rw_cells_transport; [exact ERR1| exact MU| exact WM| apply DJ; [clear - HCEILB; img_static| unfold RERRNO; cbn; clear - Bc5; lia]].
    - eapply (LIBMID_xpres0 LIB ((p, A, nA) :: L0c) SPc); [exact LM1| exact XP| intros b Hb; right; exact (SUB0 _ (SUBL _ Hb))].
    - eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta.
      intros iv [[K1 K2]|[K1 K2]]; unfold RAUXV_CELL, SP' in *; [clear - K1 K2 CEIL HCEILB SPB LO STK0; lia| clear - K1 K2 Bc4 Bc5 CEIL HCEILB SPB LO STK0; cbn in *; lia].
    - eapply xpres_trans; [exact XA1|]. eapply xpres_weaken; [exact XPL| unfold SP'; clear; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq].
  Qed.

  Local Notation FAIL_LBUF := (rp_fail_lbuf H HX CERTO3 ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M x st mb lo B S R ds errv
                                A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).

  (* [comment removed for export] *)
  Lemma rp_fail603 : forall p A nA R' j0 j2 rb m' mo' s' (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6 : word),
    fwk [] p A nA R' j0 j2 rb m' mo' s' ->
    hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 FM_R603_1) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6)
                             F (Z_to_bv 64 P_ERR_new) fc None m' (seg_rom usegs)) mo').
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HRE HX CERTO3 PERM STATICS.
    intros until u6. intros FW.
    pose proof FW as (HP1 & KREL1 & MP1 & MBO1 & MST & POS & LR & NAR & DSm1 & DSA1 & FRlo1 & RB1 & FRhi1 & ERR1 & LM1 & MI1 & ST1 & AUX1 & XA1).
    destruct (fwk_lib _ _ _ _ _ _ _ _ _ _ _ FW) as (MF_1 & IM1 & GM1). cbn [app] in HP1.
    assert (CLO : rw_cells usegs m' SPc [CB 48 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 rb]).
    { apply (proj2 (rw_cells_app usegs m' SPc [CB 48 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st)] [C8 rb])). split; [exact FRlo1|].
      cbn [cells_size csize Nat.add]. replace (SPc + Z.of_nat (72 + 0)) with RBPc by (unfold SP', RBP; clear; lia). exact RB1. }
    eapply (FAIL_LBUF 603 R_PASSED_INVALID_ARGUMENT FM_R603_1 FM_R603_2) with (p := p) (nA := nA) (s1' := s') (R' := R') (j2 := j2)
      (clo := [CB 48 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 rb]); [clear; lia| unfold R_PASSED_INVALID_ARGUMENT; clear; lia| unfold FM_R603_1; clear; lia| reflexivity
      | unfold FM_R603_2; clear; lia| reflexivity| exact rp_g603a| exact rp_g603b| clear - LR NAR; lia
      | exact HP1| exact KREL1| exact MP1| exact MBO1| exact MST| exact DSm1| reflexivity| exact CLO| exact FRhi1| exact ERR1| exact MF_1| exact IM1| exact GM1| exact MI1| exact ST1| exact AUX1| exact XA1].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_fmt : rp_decK0 -> rp_b64K -> rp_okK H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HRE HX CERTO3 PERM STATICS.
    intros KDEC KB64. unfold rp_okK.
    intros k n m1 mo1 s1' p A R' junk j0 j2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 KR NEQ NR GOK HP1 KREL1 MP1 MBO1 MST POS DSm1 DSA1 JK1 FRlo1 RB1 FRhi1 [errv1 ERR1] MF_1 LM1 MI1 ST1 AUX1 XA1.
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (rc_stack_fmt M) as (STKD & STKM & STKF).
    hcb. pose proof (word_range sp) as SPR. pose proof DSL as DSL1. unfold zlength in DSL1.
    pose proof (errph_nonneg (mid_err M)) as (EN1 & EN2 & EN3). pose proof (ctxph_nonneg3 (mid_ctx M)) as (CN1 & CN2 & CN3).
    pose proof LM1 as (IM1 & _ & _ & _ & _ & _ & _ & _ & GM1 & _).
    destruct (lad_head_facts H HX L0c _ _ _ _ _ HP1) as (BR & BH & NIP & DISJ & BEL). pose proof BR as (Ba1 & Ba2 & Ba3 & Ba4 & Ba5).
    (* [comment removed for export] *)
    assert (FW1 : fwk [] p A (512 * (k + 1)) R' j0 j2 (wz n) m1 mo1 s1').
    { unfold fwk. cbn [app]. repeat match goal with |- _ /\ _ => split end; try assumption.
      - clear - NEQ NR KR; lia.
      - clear - NEQ NR KR; lia.
      - unfold OSSL_ECH_MAX_ECHCONFIG_LEN in GOK; clear - KR NEQ NR GOK; lia.
      - exists errv1; exact ERR1. }
    destruct (Z_lt_ge_dec (mb_len R) 5) as [L5|L5].
    - (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL1| eapply fm_seg1; [clear - L5 NR NEQ KR; lia| exact MI1]|]. intros ms2 ->.
      eapply rp_fail603. exact FW1.
    - (* [comment removed for export] *)
      assert (GOK5 : 5 <= mb_len R < 1500) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN in GOK; clear - L5 GOK; lia).
      eapply (sr_evt_krel H HH); [exact KREL1| eapply fm_seg2 with (A := A) (L := mb_len R) (n := n) (K := 512 * k) (ds := ds)|].
      { clear - GOK5; lia. }
      { clear - NEQ; lia. } { clear - KR; lia. } { clear - NR; lia. } { exact Ba1. } { clear - BH HCEILB NEQ NR KR; lia. } { exact DSA1. } { exact DSL. } { exact MI1. }
      intros ms2 [a3x PO]. destruct (is_bin_fmt ds (mb_len R)) eqn:FMT; subst ms2.
      + (* [comment removed for export] *)
        pose proof (cmemdup_spec H HH) as MD. unfold cmemdup_stmt in MD.
        eapply (sr_seq H HH).
        { eapply MD with (D := A) (bs := ds) (lo := lo) (B := B) (LB := (p, A, 512 * (k + 1)) :: L0c) (s := s1') (v := 1) (errv := errv1); clear MD; try reflexivity.
          all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact IM1| exact GM1| exact MF_1| exact CEIL| exact DSA1].
          all: lazymatch goal with
               | |- Z_to_bv 64 _ = Z_to_bv 64 _ => rewrite DSL; reflexivity
               | |- 1 <= zlength ds < _ => rewrite DSL; clear - GOK5; lia
               | |- xclient_range _ _ _ _ _ => split; [right; right; exists (p, A, 512 * (k + 1)); split; [left; reflexivity| cbn; rewrite DSL; clear - NEQ NR KR; lia]
                                                     | unfold memflag_foot; apply Forall_cons; [cbn; unfold A_mem_inited; rewrite DSL; clear - Ba5 NEQ NR KR; lia| apply Forall_nil]]
               | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_cons; cbn [blk_size snd]; unfold L0; unfold mid_bytes, DECODE_BYTES, ERRSTR_BYTES in BUD; rewrite DSL;
                                           clear - BUD EN1 CN1 KR GOK5; lia
               | |- Z.of_nat _ + _ <= _ => cbn [length]; rewrite Nat2Z.inj_succ; unfold L0; unfold mid_cnt, DECODE_CNT, ERRSTR_CNT in BUDC; clear - BUDC EN2 CN2; lia
               | |- lb_big _ + _ <= _ => rewrite lb_big_cons; cbn [blk_size snd]; unfold L0; unfold mid_big, DECODE_BIG in BUDG; pose proof (big1_range (512 * (k + 1))) as G1;
                                         rewrite (big1_small (zlength ds)) by (rewrite DSL; unfold BIGB; clear - GOK5; lia); clear - BUDG EN3 CN3 G1; lia
               | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
               | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
               | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKD; lia
               | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
               | |- _ => idtac
               end. 
          }
        clear MD. intros [ms3 mo3] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & Bb & pbin & s2' & -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BRB & HP2 & CELLS2 & MF2 & IM2 & GM2).
        unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR2.
        change (bv_unsigned sp + -2368) with SPc in ST2, XP2.
        rewrite DSL in BRB, HP2.
        pose proof BRB as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5).
        (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL2| eapply fm_seg3; [clear - Bb1 Bb4 HCEILB GOK5; lia| exact MI2]|]. intros ms4 ->.
        eapply (KDEC p A (512 * (k + 1)) R' j0 j2 (wz n) m2 mo3 s2' pbin Bb); [exact GOK5| | rewrite <- DSL1, Nat2Z.id; exact CELLS2].
        eapply (fwk_x [] [(pbin, Bb, mb_len R)]); [exact FW1| eapply xpres_drop_memflag; [exact XP2| exact MF_1| exact MF2]| cbn [app]; exact HP2| exact KREL2
          | eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; exact ERR2| exact MI2| exact ST2| exact AUX2].
      + (* [comment removed for export] *)
        pose proof (cmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
        eapply (sr_seq H HH).
        { eapply CM with (n := mb_len R + 1) (lo := lo) (B := B) (LB := (p, A, 512 * (k + 1)) :: L0c) (s := s1') (v := 1) (errv := errv1); clear CM; try reflexivity.
          all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact IM1| exact GM1| exact MF_1| exact CEIL].
          all: lazymatch goal with
               | |- 1 <= _ < _ => clear - GOK5; lia
               | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_cons; cbn [blk_size snd]; unfold L0; unfold mid_bytes, DECODE_BYTES, ERRSTR_BYTES in BUD;
                                           clear - BUD EN1 CN1 KR GOK5; lia
               | |- Z.of_nat _ + _ <= _ => cbn [length]; rewrite Nat2Z.inj_succ; unfold L0; unfold mid_cnt, DECODE_CNT, ERRSTR_CNT in BUDC; clear - BUDC EN2 CN2; lia
               | |- lb_big _ + _ <= _ => rewrite lb_big_cons; cbn [blk_size snd]; unfold L0; unfold mid_big, DECODE_BIG in BUDG; pose proof (big1_range (512 * (k + 1))) as G1;
                                         rewrite (big1_small (mb_len R + 1)) by (unfold BIGB; clear - GOK5; lia); clear - BUDG EN3 CN3 G1; lia
               | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
               | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
               | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKM; lia
               | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
               | |- _ => idtac
               end. }
        clear CM. intros [ms3 mo3] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & Cp & junk2 & pc & s2' & -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BRC & HP2 & CELLS2 & MF2 & IM2 & GM2).
        unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR2.
        change (bv_unsigned sp + -2368) with SPc in ST2, XP2.
        pose proof BRC as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
        assert (FW2 : fwk [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' j0 j2 (wz n) m2 mo3 s2').
        { eapply (fwk_x [] [(pc, Cp, mb_len R + 1)]); [exact FW1| eapply xpres_drop_memflag; [exact XP2| exact MF_1| exact MF2]| cbn [app]; exact HP2| exact KREL2
            | eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; exact ERR2| exact MI2| exact ST2| exact AUX2]. }
        destruct (lad_head_facts H HX ((p, A, 512 * (k + 1)) :: L0c) _ _ _ _ _ HP2) as (_ & BHc & NIPc & DISJc & BELc).
        pose proof (DISJc _ (or_introl eq_refl)) as DAC. cbn [blk_addr blk_size fst snd] in DAC.
        clear HP1 KREL1 MBO1 DSm1 DSA1 JK1 FRlo1 RB1 FRhi1 ERR1 MF_1 LM1 MI1 ST1 AUX1 XA1 IM1 GM1 XP2.
        pose proof FW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & DSA2 & _).
        (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL2| eapply fm_seg4; [clear - Bc1 Bc4 HCEILB GOK5; lia| exact MI2]|]. intros ms4 ->.
        destruct (rw_cells_CB_split usegs m2 Cp (Z.to_nat (mb_len R + 1)) (Z.to_nat (mb_len R)) junk2 CELLS2 ltac:(clear - GOK5; lia)) as [CPa CPb].
        replace (Z.to_nat (mb_len R + 1) - Z.to_nat (mb_len R))%nat with 1%nat in CPb by (clear - GOK5; lia). rewrite Z2Nat.id in CPb by (clear - GOK5; lia).
        eapply (sr_evt_krel H HH); [exact KREL2| eapply memcpy_spec with (src := ds) (junk := firstn (Z.to_nat (mb_len R)) junk2); rewrite ?unsigned_lit by (clear - Bc1 Bc4 Ba1 BH HCEILB GOK5 KR; lia);
          [exact DSA2| clear - DSL1; lia| exact CPa| clear - DAC GOK5 NEQ NR KR; lia| exact MI2]|].
        intros ms5 PO. unfold memcpy_post in PO.
        destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & CP3 & _).
        rewrite !unsigned_lit in MU3, CP3 by (clear - Bc1 Bc4 Ba1 BH HCEILB GOK5 KR; lia).
        assert (ST3 : stk usegs m3 lo SPc) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; unfold SP'; clear - Bc4 CEIL LO STK0; lia]).
        assert (FW3 : fwk [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' j0 j2 (wz n) m3 mo3 s2').
        { eapply fwk_w; [exact FW2| exact MU3| exact WM3| exact MI3| exact ST3|]. apply Forall_cons; [right; cbn; clear - GOK5; lia| apply Forall_nil]. }
        apply (rw_cells_transport usegs _ m2 m3 _ _ CPb) in MU3 as CPb3; [| exact WM3| cbn; clear; lia].
        (* [comment removed for export] *)
        pose proof CPb3 as [[JW _] _]. cbn in JW. destruct (skipn (Z.to_nat (mb_len R)) junk2) as [|jb [|jx jl]]; cbn in JW; try (exfalso; clear - JW; lia).
        assert (CPJ : rw_cells usegs m3 Cp [CB (Z.to_nat (mb_len R)) ds; CB 1 [jb]]).
        { apply (proj2 (rw_cells_app usegs m3 Cp [CB (Z.to_nat (mb_len R)) ds] [CB 1 [jb]])). split; [exact CP3|]. cbn [cells_size csize Nat.add].
          rewrite Nat.add_0_r, Z2Nat.id by (clear - GOK5; lia). exact CPb3. }
        eapply (sr_evt_krel H HH); [exact KREL2| eapply fm_seg5 with (Cp := Cp) (n := n) (K := 512 * k) (L := mb_len R) (cp := ds) (jb := jb);
          [exact Bc1| clear - Bc4 HCEILB; lia| clear - NEQ; lia| clear - NR; lia| clear - KR; lia| clear - GOK5; lia| clear - DSL1; lia| exact CPJ| exact MI3]|].
        intros ms6 (m4 & -> & MU4 & WM4 & MI4 & CP4).
        assert (ST4 : stk usegs m4 lo SPc) by (eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4| cbn; unfold SP'; clear - Bc4 CEIL LO STK0; lia]).
        assert (FW4 : fwk [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' j0 j2 (wz n) m4 mo3 s2').
        { eapply fwk_w; [exact FW3| exact MU4| exact WM4| exact MI4| exact ST4|]. apply Forall_cons; [right; cbn; clear - GOK5; lia| apply Forall_nil]. }
        clear FW2 FW3 CPa CPb CP3 CPb3 CPJ MU3 WM3 MI3 ST3 MU4 WM4 DSA2 CELLS2 MI2 ST2.
        pose proof FW4 as (HP4 & _). cbn [app] in HP4.
        destruct (STATICS _ _ _ HP4) as (_ & CG4 & CANR & CC4).
        pose proof (proj2 (proj2 R_b64_alphabet) m4 MI4) as (AB4 & AN4 & _).
        destruct (nul_split ds) as (str & rest & SPLIT & SNN & SLE & SEQ').
        assert (CSTR4 : bytes_at usegs m4 Cp (str ++ Z_to_bv 8 0 :: rest)).
        { rewrite <- SPLIT. pose proof CP4 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite ?app_nil_r in BY. exact BY. }
        assert (SL1 : length (str ++ Z_to_bv 8 0 :: rest) = (length ds + 1)%nat) by (rewrite <- SPLIT, length_app; cbn [length]; clear; lia).
        eapply (sr_evt_krel H HH); [exact KREL2|..].
        { eapply strspn_spec with (str := str) (sslack := rest) (acc := S_b64_alphabet) (aslack := K_b64_alphabet) (lo := lo) (can := hs_canary H).
          all: lazymatch goal with
               | |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 A_B64_ALPHABET)) _ => unfold A_B64_ALPHABET; rewrite unsigned_lit by (clear; lia); exact AB4
               | |- bytes_at _ _ _ _ => rewrite unsigned_lit by (clear - Bc1 Bc4 HCEILB GOK5; lia); exact CSTR4
               | |- ~ In _ S_b64_alphabet => exact AN4
               | |- ~ In _ _ => exact SNN
               | |- (2 <= length S_b64_alphabet)%nat => rewrite S_b64_alphabet_len; clear; lia
               | |- rw_cells _ _ _ [C8 _] => first [exact CG4| exact CC4]
               | |- 0 <= hs_canary H < _ => exact CANR
               | |- _ + 8 <= 2 ^ 64 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPR LO STK0 LO0; lia
               | |- bv_unsigned (Z_to_bv 64 A_B64_ALPHABET) + _ <= _ => unfold A_B64_ALPHABET, SP'; rewrite !unsigned_lit by (clear - SPR LO STK0 LO0; lia); rewrite length_app, S_b64_alphabet_len; cbn; clear - LO STK0 CEIL HCEILB; lia
               | |- bv_unsigned _ + _ <= _ => unfold SP'; rewrite !unsigned_lit by (clear - Bc1 Bc4 HCEILB GOK5 SPR LO STK0 LO0; lia); rewrite SL1; clear - DSL1 Bc4 CEIL LO STK0; lia
               | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST4
               | |- 3506176 <= lo => clear - CEIL HCEILB; lia
               | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STK0; lia
               | |- mem_inv _ _ => exact MI4
               end. }
        cbv beta. intros ms7 (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & -> & MU5 & WM5 & MI5 & ST5).
        unfold SP' in MU5, ST5. rewrite !unsigned_lit in MU5, ST5 by (clear - SPR LO STK0 LO0; lia). change (bv_unsigned sp + -2368) with SPc in MU5, ST5.
        set (span := Z.of_nat (spn str S_b64_alphabet)) in *.
        assert (SPANR : 0 <= span <= mb_len R) by (subst span; pose proof (spn_le str S_b64_alphabet) as K; clear - K SLE DSL1; lia).
        assert (FW5 : fwk [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' j0 j2 (wz n) m5 mo3 s2').
        { eapply fwk_w; [exact FW4| exact MU5| exact WM5| exact MI5| exact ST5|]. apply Forall_cons; [left; cbn; unfold SP'; clear - LO STK0; lia| apply Forall_nil]. }
        clear FW4 HP4 CG4 CC4 AB4 AN4 CSTR4 MU5 WM5 MI4 ST4 CP4.
        (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL2| eapply fm_seg6; exact MI5|]. intros ms8 ->.
        pose proof FW5 as (HP5 & _ & MP5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv5 ERR5] & LM5 & _ & _ & AUX5 & _). cbn [app] in HP5.
        destruct (fwk_lib _ _ _ _ _ _ _ _ _ _ _ FW5) as (MF5 & IM5 & GM5).
        pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
        eapply (sr_seq H HH).
        { eapply CF with (lo := lo) (B := B) (LB := (pc, Cp, mb_len R + 1) :: (p, A, 512 * (k + 1)) :: L0c) (s := s2') (p := pc) (A := Cp) (n := mb_len R + 1) (errv := errv5); clear CF; try reflexivity.
          all: try first [exact HP5| exact KREL2| exact AUX5| exact MI5| exact IM5| exact GM5| exact CEIL].
          all: lazymatch goal with
               | |- In _ _ => left; reflexivity
               | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
               | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST5
               | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKF; lia
               | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR5
               end. }
        clear CF. intros [ms9 mo9] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m6 & s6' & -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & XP6 & HP6 & IM6 & GM6).
        rewrite (proj1 (HH_lb_remove H HH)) in XP6, HP6 by exact NIPc.
        unfold SP' in ST6, XP6. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in ST6, XP6 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR6.
        change (bv_unsigned sp + -2368) with SPc in ST6, XP6.
        assert (FW6 : fwk [] p A (512 * (k + 1)) R' j0 j2 (wz n) m6 mo9 s6').
        { eapply (fwk_x [(pc, Cp, mb_len R + 1)] []); [exact FW5| exact XP6| cbn [app]; exact HP6| exact KREL6
            | eapply (mpres_trans H HH); [exact MP5| exact MP6]| exists errv5; exact ERR6| exact MI6| exact ST6| exact AUX6]. }
        clear FW5 HP5 MP5 ERR5 LM5 AUX5 MF5 IM5 GM5 XP6 HP6 MI5 ST5.
        (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL6| eapply fm_seg7 with (span := span) (L := mb_len R); [clear - SPANR GOK5; lia| clear - GOK5; lia| exact MI6]|]. intros ms10 ->.
        destruct (span <? mb_len R) eqn:SL.
        * (* [comment removed for export] *)
          eapply rp_fail603. exact FW6.
        * (* [comment removed for export] *)
          eapply (KB64 k n p A R' j0 j2 m6 mo9 s6'); [exact KR| exact NEQ| exact NR| exact GOK5| exact FW6].
  Qed.
End RC.
