(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_Rostr ECH_UbKit ECH_C1_stmt ECH_C4_stmt ECH_C5_stmt ECH_C8_blockA ECH_C13_stmt ECH_C14_stmt F_time ECH_C14_bio2buf ECH_C14_tail ECH_C14_b2b
     ECH_C14_decK ECH_C14_dec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition DF_R_TIME : Z := 0x2b3718.   Definition DF_R_FCC : Z := 0x2b3724.   Definition DF_R_SKNEW : Z := 0x2b3754.
Definition DF_R_SET1 : Z := 0x2b376c.   Definition DF_R_SET2 : Z := 0x2b3780.  Definition DF_R_SET3 : Z := 0x2b3794.
Definition DF_PUSH : Z := 0x2b37a8.     Definition DF_R_PUSH : Z := 0x2b37b4.  Definition DF_R_DONE : Z := 0x2b37d8.
Definition DF_TA_R1 : Z := 0x2b381c.    Definition DF_TA_R2 : Z := 0x2b3838.   (* [comment removed for export] *)
Definition DF_TZ_R : Z := 0x2b3854.     (* [comment removed for export] *)
Definition DF_TY_R1 : Z := 0x2b386c.    Definition DF_TY_R2 : Z := 0x2b3888.   (* [comment removed for export] *)
Definition DF_TX_R0 : Z := 0x2b38a4.    (* [comment removed for export] *)
Definition DF_TX_R1 : Z := 0x2b38ac.    Definition DF_TX_R2 : Z := 0x2b38c8.   Definition DF_TX_R3 : Z := 0x2b38e0.   (* [comment removed for export] *)
Definition DF_TRAP : Z := 0x2b38f0.     (* [comment removed for export] *)
Definition A_THUNK1 : Z := 0x2b3974.   Definition A_THUNK2 : Z := 0x2b39a0.    Definition A_THUNK3 : Z := 0x2b394c.
(* [comment removed for export] *)
Definition S_echs_func_d1 : list byte := Eval vm_compute in img_cstr A_ECHS_FUNC_D1 64.
Definition K_echs_func_d1 : list byte := Eval vm_compute in img_slack A_ECHS_FUNC_D1 (length S_echs_func_d1).
Definition S_echs_func_df : list byte := Eval vm_compute in img_cstr A_ECHS_FUNC_DF 64.
Definition K_echs_func_df : list byte := Eval vm_compute in img_slack A_ECHS_FUNC_DF (length S_echs_func_df).

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [unfold RA; lia| reflexivity]).
  (* [comment removed for export] *)
  Local Ltac slot := match goal with |- context [bv_unsigned ?s - 4096] => replace (bv_unsigned s - 4096) with (bv_unsigned s + -2368 + -1728) by lia end.

  Lemma R_echs_func_d1 : ROSTR A_ECHS_FUNC_D1 S_echs_func_d1 K_echs_func_d1.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_echs_func_df : ROSTR A_ECHS_FUNC_DF S_echs_func_df K_echs_func_df.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma S_echs_func_lens : Z.of_nat (length S_echs_func_d1) = 20 /\ Z.of_nat (length S_echs_func_df) = 22.
  Proof. vm_compute. split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fs_dec :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (T : Z),
      0 <= T < 2^31 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists a0' a1',
          ms' = if (32 <=? T) && (T <? 1500)
                then MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 T) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 DF_HDR) fc None m (seg_rom usegs)
                else MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 509) (Z_to_bv 64 R_PASSED_NULL_PARAMETER) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 DF_TY) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 T) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DF_DEC) fc None m (seg_rom usegs)).
  Proof.
    intros until T. intros TR MI. unfold DF_DEC, DF_HDR, DF_TY, R_PASSED_NULL_PARAMETER.
    step. step.
    destruct (andb (32 <=? T) (T <? 1500)) eqn:G.
    - apply andb_prop in G. destruct G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
      step. if_cases K2; zify_cond K2.
      2: { exfalso. change 18446744073709551615 with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. revert K2. clear - G1 G2 TR. Z.div_mod_to_equations. lia. }
      clear K2. apply evt_done. do 2 eexists. reflexivity.
    - step. if_cases K2; zify_cond K2.
      { exfalso. apply Bool.andb_false_iff in G. rewrite Z.leb_gt, Z.ltb_ge in G. change 18446744073709551615 with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia.
        revert K2. clear - G TR. Z.div_mod_to_equations. lia. }
      clear K2. do 5 step. apply evt_done. do 2 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition olen_of (bs : list byte) : Z := match bs with b0 :: b1 :: _ => 256 * bv_unsigned b0 + bv_unsigned b1 | _ => 0 end.

  (* [comment removed for export] *)
  Lemma fs_hdr :
    forall (rax gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp : word) (T Bb st : Z) (bs : list byte) (w0 w1 w2 w3 w4 w5 w6 w7 : word),
      32 <= T < 1500 -> zlength bs = T -> bytes_at usegs m Bb bs -> 0 < Bb -> Bb + T < 2^63 -> 2368 <= bv_unsigned sp ->
      0 <= st < 2^64 -> st mod 8 = 0 ->
      rw_cells usegs m (bv_unsigned sp + -2368) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 (Z_to_bv 64 st)] ->
      mem_inv usegs m ->
      evt usegs (fun ms' => exists a0' a1' a2' a3',
           (T - 2 < olen_of bs /\
              ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 (Z_to_bv 64 514) (Z_to_bv 64 R_INTERNAL_ERROR) s5 (Z_to_bv 64 Bb) (Z_to_bv 64 0) (Z_to_bv 64 (olen_of bs)) s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 DF_TY) fc None m (seg_rom usegs))
        \/ (olen_of bs = 0 /\
              ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 Bb) (Z_to_bv 64 (T - 2)) (Z_to_bv 64 0) s9 (Z_to_bv 64 (Bb + 2)) s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 DF_DONE) fc None m (seg_rom usegs))
        \/ (1 <= olen_of bs <= T - 2 /\ exists m1,
              ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 (Z_to_bv 64 R_INTERNAL_ERROR) s5 (Z_to_bv 64 Bb) (Z_to_bv 64 (T - 2)) (Z_to_bv 64 (olen_of bs)) s9 (Z_to_bv 64 (Bb + 2)) s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 DF_LOOP) fc None m1 (seg_rom usegs)
              /\ munch [(bv_unsigned sp + -2344, bv_unsigned sp + -2320)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
              /\ rw_cells usegs m1 (bv_unsigned sp + -2368)
                   [C8 w0; C8 w1; C8 w2; C8 (Z_to_bv 64 0); C8 (wz ECH_VERSION); C8 (wz A_ECHS_FILE_RP); C8 w6; C8 w7; C8 (Z_to_bv 64 st)]))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 Bb) (Z_to_bv 64 T) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DF_HDR) fc None m (seg_rom usegs)).
  Proof.
    intros until w7. intros TR BSL BS BP BH SPL STR SAL FR MI. unfold DF_HDR, DF_TY, DF_DONE, DF_LOOP, R_INTERNAL_ERROR.
    pose proof (word_range sp) as SPR. unfold zlength in BSL.
    pose proof (munch_refl [(bv_unsigned sp + -2344, bv_unsigned sp + -2320)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct bs as [|b0 [|b1 bs2]]; try (cbn in BSL; exfalso; lia).
    pose proof (byte_range b0) as B0. pose proof (byte_range b1) as B1.
    pose proof (rd_raw _ _ _ 0 b0 BS eq_refl ltac:(lia)) as RD0. replace (Bb + 0) with Bb in RD0 by lia.
    pose proof (rd_raw _ _ _ 1 b1 BS eq_refl ltac:(lia)) as RD1.
    cbn [olen_of].
    (* [comment removed for export] *)
    step. step. step. br. step. step. br.
    step. unfold zxb. step. unfold zxb. step. step.
    rewrite (unsigned_lit (bv_unsigned b1)) by lia. rewrite (unsigned_lit (bv_unsigned b0)) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned b0 * 2 ^ 8)) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia).
    rewrite (Z.lor_comm (bv_unsigned b0 * 2 ^ 8) (bv_unsigned b1)). rewrite (lor_add_disjoint _ _ 8) by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b1 + bv_unsigned b0 * 256) with (256 * bv_unsigned b0 + bv_unsigned b1) by lia.
    set (olen := 256 * bv_unsigned b0 + bv_unsigned b1). assert (OR : 0 <= olen < 65536) by (subst olen; lia).
    step.
    destruct (Z_lt_ge_dec (T - 2) olen) as [LT|GE].
    - step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
      (* [comment removed for export] *)
      do 5 step. replace (T + -2) with (T - 2) by lia.
      apply evt_done. do 4 eexists. left. split; [exact LT| reflexivity].
    - step. if_cases K2; zify_cond K2; [| kill K2]. clear K2.
      (* [comment removed for export] *)
      step. step. ubnot. step. br.
      destruct (Z.eq_dec olen 0) as [Z0|NZ].
      + rewrite Z0. step. if_lit. apply evt_done. do 4 eexists. right; left. split; [reflexivity|]. replace (T + -2) with (T - 2) by lia. reflexivity.
      + step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
        (* [comment removed for export] *)
        do 2 step. slot. step. step. rewrite (unsigned_lit st) by lia. rewrite (al8 st) by exact SAL.
        do 2 step. slot. st1.
        (* [comment removed for export] *)
        do 4 step. do 2 step. slot. st1.
        step. do 2 step. slot. st1.
        step.
        apply evt_done. do 4 eexists. right; right. split; [lia|]. eexists. split; [replace (T + -2) with (T - 2) by lia; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. unfold ECH_VERSION, A_ECHS_FILE_RP, wz. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_adv :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (cur rem elen : Z),
      0 <= elen -> 4 + elen <= rem -> rem < 2^31 -> 0 <= cur -> cur + rem < 2^63 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (cur + 4 + elen)) s4 (Z_to_bv 64 (rem - 4)) s6 s7 (Z_to_bv 64 (rem - 4 - elen)) (Z_to_bv 64 elen)
                         (Z_to_bv 64 (cur + 4 + elen)) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (if rem - 4 - elen =? 0 then DF_DONE else DF_LOOP)) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (cur + 4 + elen)) s4 (Z_to_bv 64 (rem - 4)) s6 s7 s8 (Z_to_bv 64 elen) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DF_ADV) fc None m (seg_rom usegs)).
  Proof.
    intros until elen. intros ER EL RR CR CH MI. unfold DF_ADV, DF_DONE, DF_LOOP in *.
    step. rewrite (unsigned_lit elen) by lia. replace (rem - 4 + - elen) with (rem - 4 - elen) by lia.
    step.
    destruct (Z.eqb_spec (rem - 4 - elen) 0) as [E0|NE].
    - rewrite E0. step. if_lit. apply evt_done. reflexivity.
    - step. if_cases K2; zify_cond K2; [| kill K2]. clear K2. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_ok1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_R_TIME) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_time) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DF_OK) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. unfold DF_OK, DF_R_TIME, P_time. step. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fs_ok2 :
    forall (sp gp tp t0 t1 t2 s0 s1 tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (ee : Z) (E : entrep) (pad1 pad2 pad3 pad4 : list byte),
      0 < ee -> ee + ENTRY_SIZE < 2^63 -> rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 DF_R_FCC) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ech_final_config_checks) fc None m1 (seg_rom usegs)
          /\ munch [(ee + O_EN_LOADTIME, ee + 72)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                                               (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (bv_unsigned tv) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E))
                                  pad1 pad2 pad3 pad4))
        (MS (mkR (Z_to_bv 64 DF_R_TIME) sp gp tp t0 t1 t2 s0 s1 tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_TIME)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EP EH EC MI. retpc DF_R_TIME. unfold DF_R_TIME, DF_R_FCC, P_ech_final_config_checks, O_EN_LOADTIME, entry_cells in *.
    pose proof (munch_refl [(ee + 64, ee + 72)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. step. step. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    cbn [en_version en_pname en_publen en_pub en_nsuites en_suites en_maxname en_cfgid en_exts en_loadtime en_forretry en_enclen en_encoded].
    unfold wz. rewrite Z_to_bv_bv_unsigned. exact EC.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_ok3 :
    forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp : word) (rv st ents : Z) (w0 w1 w2 w4 w5 w6 w7 : word),
      (rv = 0 \/ rv = 1) -> 0 <= ents < 2^64 -> 0 < st -> st + STORE_SIZE < 2^63 -> 2368 <= bv_unsigned sp ->
      rw_cells usegs m (bv_unsigned sp + -2368) [C8 w0; C8 w1; C8 w2; C8 (Z_to_bv 64 0); C8 w4; C8 w5; C8 w6; C8 w7; C8 (Z_to_bv 64 st)] ->
      rw_cells usegs m st [C8 (wz ents); C8 (wz 0); C8 (wz 0)] -> mem_inv usegs m ->
      evt usegs (fun ms' =>
           (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 DF_R_FCC) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 DF_TX) fc None m (seg_rom usegs))
        \/ (rv = 1 /\ ents <> 0 /\ ms' = MS (mkR (Z_to_bv 64 DF_R_FCC) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ents) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 DF_PUSH) fc None m (seg_rom usegs))
        \/ (rv = 1 /\ ents = 0 /\ ms' = MS (mkR (Z_to_bv 64 DF_R_SKNEW) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 DF_R_FCC) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_FCC)) fc None m (seg_rom usegs)).
  Proof.
    intros until w7. intros RV ER SP0 SH SPL FR SC MI. retpc DF_R_FCC. unfold DF_R_FCC, DF_TX, DF_PUSH, DF_R_SKNEW, P_OPENSSL_sk_new_null in *.
    pose proof (word_range sp) as SPR.
    destruct RV as [->| ->].
    - step. if_lit. apply evt_done. left. split; reflexivity.
    - step. if_lit.
      (* [comment removed for export] *)
      do 2 step. slot. step. step. if_lit.
      do 2 step. slot. step. unfold wz in SC. step.
      destruct (Z.eq_dec ents 0) as [->|NE].
      + step. if_lit. step. step. apply evt_done. right; right. split; [reflexivity|]. split; reflexivity.
      + step. if_cases K2; zify_cond K2; [| kill K2]. clear K2. apply evt_done. right; left. split; [reflexivity|]. split; [exact NE| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fs_ok4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_R_SET1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 A_THUNK1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 a) s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_OPENSSL_sk_set_cmp_thunks) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_R_SKNEW) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_SKNEW)) fc None m (seg_rom usegs)).
  Proof. intros until a. intros MI. retpc DF_R_SKNEW. unfold DF_R_SKNEW, DF_R_SET1, P_OPENSSL_sk_set_cmp_thunks, A_THUNK1. do 6 step. apply evt_done. reflexivity. Qed.
  Lemma fs_ok5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_R_SET2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 A_THUNK2) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 a) s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_OPENSSL_sk_set_copy_thunks) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_R_SET1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 a) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_SET1)) fc None m (seg_rom usegs)).
  Proof. intros until a. intros MI. retpc DF_R_SET1. unfold DF_R_SET1, DF_R_SET2, P_OPENSSL_sk_set_copy_thunks, A_THUNK2. do 5 step. apply evt_done. reflexivity. Qed.
  Lemma fs_ok6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_R_SET3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 A_THUNK3) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 a) s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_R_SET2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 a) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_SET2)) fc None m (seg_rom usegs)).
  Proof. intros until a. intros MI. retpc DF_R_SET2. unfold DF_R_SET2, DF_R_SET3, P_OPENSSL_sk_set_thunks, A_THUNK3. do 5 step. apply evt_done. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma fs_ok7 :
    forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp : word) (a st ee : Z) (w0 w1 w2 w3 w4 w5 w6 w7 : word),
      0 < a < 2^64 -> 0 < st -> st + STORE_SIZE < 2^63 -> 2368 <= bv_unsigned sp ->
      rw_cells usegs m (bv_unsigned sp + -2368) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 (Z_to_bv 64 st)] ->
      rw_cells usegs m st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 (a1' : word),
          ms' = MS (mkR (Z_to_bv 64 DF_R_PUSH) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 a) (Z_to_bv 64 ee) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom usegs)
          /\ a1' = a1 /\ munch [(st, st + 8)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ rw_cells usegs m1 st [C8 (wz a); C8 (wz 0); C8 (wz 0)])
        (MS (mkR (Z_to_bv 64 DF_R_SET3) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_SET3)) fc None m (seg_rom usegs)).
  Proof.
    intros until w7. intros AR SP0 SH SPL FR SC MI. retpc DF_R_SET3. unfold DF_R_SET3, DF_R_PUSH, DF_PUSH, P_OPENSSL_sk_push, wz in *.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [(st, st + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 2 step. slot. step.
    st1. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. do 3 step. apply evt_done. do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma fs_ok7b :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (a ee : Z),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_R_PUSH) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 ee) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_R_FCC) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DF_PUSH) fc None m (seg_rom usegs)).
  Proof. intros until ee. intros MI. unfold DF_PUSH, DF_R_PUSH, P_OPENSSL_sk_push. do 3 step. apply evt_done. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma fs_ok8 :
    forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp : word) (rv : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 : word),
      1 <= rv < 2^32 -> 2368 <= bv_unsigned sp ->
      rw_cells usegs m (bv_unsigned sp + -2368) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists a1', ms' = MS (mkR (Z_to_bv 64 DF_R_PUSH) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1' a2 a3 a4 a5 a6 a7 s2 w2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 DF_ADV) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_R_PUSH) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_PUSH)) fc None m (seg_rom usegs)).
  Proof.
    intros until w8. intros RV SPL FR MI. retpc DF_R_PUSH. unfold DF_R_PUSH, DF_ADV in *. pose proof (word_range sp) as SPR.
    do 2 step. slot. step.
    step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. apply evt_done. eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_done :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_R_DONE) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DF_DONE) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. unfold DF_DONE, DF_R_DONE, P_ossl_echstore_entry_free. step. step. apply evt_done. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma fs_done2 :
    forall (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp : word) (w0 w1 w2 w3 w4 w5 w6 w8 : word),
      2368 <= bv_unsigned sp -> rw_cells usegs m (bv_unsigned sp + -2368) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 (Z_to_bv 64 0); C8 w8] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists a0', ms' = MS (mkR (Z_to_bv 64 DF_R_DONE) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 RP_ERRL) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_R_DONE) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_R_DONE)) fc None m (seg_rom usegs)).
  Proof.
    intros until w8. intros SPL FR MI. retpc DF_R_DONE. unfold DF_R_DONE, RP_ERRL in *. pose proof (word_range sp) as SPR.
    do 2 step. slot. step. step. if_lit. step. step. apply evt_done. eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition rglue (raA raB target : Z) (a0v a1v a2v : word) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : Prop :=
    forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv usegs m1 ->
      evt usegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 a0v a1v a2v c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma ft_a1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_TA_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DF_TA) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. unfold DF_TA, DF_TA_R1, P_ERR_new. step. step. apply evt_done. reflexivity. Qed.
  Lemma ft_a2 : forall (line : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32),
      rglue DF_TA_R1 DF_TA_R2 P_ERR_set_debug (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 line) (Z_to_bv 64 A_ECHS_FUNC_D1) sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 line) F fc.
  Proof.
    unfold rglue. intros. retpc DF_TA_R1. unfold DF_TA_R1, DF_TA_R2, P_ERR_set_debug, A_ECHS_FILE_RP, A_ECHS_FUNC_D1.
    do 7 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma ft_a3 : forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32),
      rglue DF_TA_R2 DF_TZ P_ERR_set_error (Z_to_bv 64 ERR_LIB_SSL) (Z_to_bv 64 R_ECH_DECODE_ERROR) (Z_to_bv 64 0) sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc.
  Proof.
    unfold rglue. intros. retpc DF_TA_R2. unfold DF_TA_R2, DF_TZ, P_ERR_set_error, ERR_LIB_SSL, R_ECH_DECODE_ERROR.
    do 5 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_z1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_TZ_R) sp gp tp t0 t1 t2 s0 s1 s7 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DF_TZ) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. unfold DF_TZ, DF_TZ_R, P_ossl_echstore_entry_free. step. step. apply evt_done. reflexivity. Qed.
  Lemma ft_z2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => exists a0', ms' = MS (mkR (Z_to_bv 64 DF_TY_R1) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 520) (Z_to_bv 64 R_INTERNAL_ERROR) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                                           F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_TZ_R) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 DF_TZ_R)) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. retpc DF_TZ_R. unfold DF_TZ_R, DF_TY_R1, P_ERR_new, R_INTERNAL_ERROR. do 6 step. apply evt_done. eexists. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_y1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_TY_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DF_TY) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. unfold DF_TY, DF_TY_R1, P_ERR_new. step. step. apply evt_done. reflexivity. Qed.
  Lemma ft_y2 : forall (line : Z) (sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32),
      rglue DF_TY_R1 DF_TY_R2 P_ERR_set_debug (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 line) (Z_to_bv 64 A_ECHS_FUNC_DF) sp gp tp s0 s1 s2 (Z_to_bv 64 line) s4 s5 s6 s7 s8 s9 s10 s11 F fc.
  Proof.
    unfold rglue. intros. retpc DF_TY_R1. unfold DF_TY_R1, DF_TY_R2, P_ERR_set_debug, A_ECHS_FILE_RP, A_ECHS_FUNC_DF.
    do 7 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma ft_y3 : forall (reason : Z) (sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32),
      rglue DF_TY_R2 DF_TX P_ERR_set_error (Z_to_bv 64 ERR_LIB_SSL) (Z_to_bv 64 reason) (Z_to_bv 64 0) sp gp tp s0 s1 s2 s3 (Z_to_bv 64 reason) s5 s6 s7 s8 s9 s10 s11 F fc.
  Proof.
    unfold rglue. intros. retpc DF_TY_R2. unfold DF_TY_R2, DF_TX, P_ERR_set_error, ERR_LIB_SSL.
    do 5 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ft_x1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_TX_R0) sp gp tp t0 t1 t2 s0 s1 s7 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DF_TX) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. unfold DF_TX, DF_TX_R0, P_ossl_echstore_entry_free. step. step. apply evt_done. reflexivity. Qed.
  Lemma ft_x2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_TX_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_TX_R0) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 DF_TX_R0)) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. retpc DF_TX_R0. unfold DF_TX_R0, DF_TX_R1, P_ERR_new. step. step. apply evt_done. reflexivity. Qed.
  Lemma ft_x3 : rp_glue DF_TX_R1 DF_TX_R2 P_ERR_set_debug A_ECHS_FILE_RP 637 A_ECHS_FUNC_RP.
  Proof.
    unfold rp_glue, DF_TX_R2, P_ERR_set_debug, A_ECHS_FILE_RP, A_ECHS_FUNC_RP. intros. retpc DF_TX_R1. unfold DF_TX_R1.
    do 7 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma ft_x4 : rp_glue DF_TX_R2 DF_TX_R3 P_ERR_set_error ERR_LIB_SSL R_INTERNAL_ERROR 0.
  Proof.
    unfold rp_glue, DF_TX_R3, P_ERR_set_error, ERR_LIB_SSL, R_INTERNAL_ERROR. intros. retpc DF_TX_R2. unfold DF_TX_R2.
    do 6 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma ft_x5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DF_TX_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RP_ERRL) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DF_TX_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 DF_TX_R3)) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. retpc DF_TX_R3. unfold DF_TX_R3, RP_ERRL. step. step. apply evt_done. reflexivity. Qed.
End S.
