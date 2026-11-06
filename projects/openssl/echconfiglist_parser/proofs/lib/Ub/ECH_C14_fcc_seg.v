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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep ECH_LibState ECH_C1_stmt ECH_C4_stmt ECH_C5_stmt ECH_C11_stmt ECH_C12_stmt ECH_C13_stmt ECH_C14_stmt F_strlen F_strrchr F_strspn ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lor_add_disjoint' : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy. destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.lor_0_l. lia. }
  assert (D : Z.land x (y * 2^k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [LT|GE].
    - rewrite (Z.mul_pow2_bits_low y k i) by lia. apply andb_false_r.
    - assert (LX : Z.log2 x < k) by (apply (proj1 (Z.log2_lt_pow2 x k ltac:(lia))); lia).
      rewrite (Z.bits_above_log2 x i) by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.
(* [comment removed for export] *)
Lemma lor_mid_field : forall a b c j K, 0 <= j <= K -> 0 <= a < 2^j -> 0 <= b -> b * 2^j < 2^K -> 0 <= c ->
  Z.lor (a + c * 2^K) (b * 2^j) = a + b * 2^j + c * 2^K.
Proof.
  intros a b c j K JK Ha Hb HbK Hc.
  assert (P1 : 0 < 2^j) by (apply Z.pow_pos_nonneg; lia). assert (P2 : 2^K = 2^(K-j) * 2^j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (AK : a < 2^K) by (pose proof (Z.pow_le_mono_r 2 j K ltac:(lia) ltac:(lia)); lia).
  rewrite <- (lor_add_disjoint' a c K) by lia.
  rewrite <- Z.lor_assoc. rewrite (Z.lor_comm (c * 2^K) (b * 2^j)).
  rewrite (lor_add_disjoint' (b * 2^j) c K) by lia.
  replace (b * 2^j + c * 2^K) with ((b + c * 2^(K-j)) * 2^j) by (rewrite P2; lia).
  rewrite (lor_add_disjoint' a (b + c * 2^(K-j)) j) by nia. rewrite P2. lia.
Qed.
(* [comment removed for export] *)
Lemma pack_suite_word : forall (w : word) kem kdf aead,
  0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor
      (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 48))) 48)))
      (bv_unsigned (Z_to_bv 64 kem))))) (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 kdf)) 16))))))
      (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 aead)) 32))))
  = Z_to_bv 64 (suite_word kem kdf aead (bv_unsigned w / 2^48)).
Proof.
  intros w kem kdf aead KR DR AR. pose proof (word_range w) as WR.
  set (hi := bv_unsigned w / 2^48). assert (HR : 0 <= hi < 2^16) by (subst hi; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite Z.shiftr_div_pow2 by lia. fold hi. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit hi) by lia. rewrite (unsigned_lit kem) by lia. rewrite (unsigned_lit kdf) by lia. rewrite (unsigned_lit aead) by lia.
  rewrite (unsigned_lit (hi * 2^48)) by lia.
  rewrite (Z.lor_comm (hi * 2^48) kem). rewrite (lor_add_disjoint' kem hi 48) by lia.
  rewrite (unsigned_lit (kem + hi * 2^48)) by lia. rewrite (unsigned_lit (kdf * 2^16)) by lia. rewrite (unsigned_lit (aead * 2^32)) by lia.
  rewrite (lor_mid_field kem kdf hi 16 48) by lia.
  rewrite (unsigned_lit (kem + kdf * 2^16 + hi * 2^48)) by lia.
  replace (kem + kdf * 2^16 + hi * 2^48) with ((kem + kdf * 2^16) + hi * 2^48) by lia.
  rewrite (lor_mid_field (kem + kdf * 2^16) aead hi 32 48) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition FCC_R1 : Z := 0x2b29f4.   (* [comment removed for export] *)
Definition FCC_HEAD : Z := 0x2b2a24. (* [comment removed for export] *)
Definition FCC_R2 : Z := 0x2b2a78.   (* [comment removed for export] *)
Definition FCC_RA1 : Z := 0x2b2a98.  (* [comment removed for export] *)
Definition FCC_RA2 : Z := 0x2b2ab4.  (* [comment removed for export] *)
Definition FCC_RA3 : Z := 0x2b2afc.  (* [comment removed for export] *)
Definition FCC_FAIL : Z := 0x2b2b00. (* [comment removed for export] *)
Definition FCC_R4 : Z := 0x2b2b08.   (* [comment removed for export] *)
Definition FCC_GOOD : Z := 0x2b2b3c. (* [comment removed for export] *)
Definition FCC_R5 : Z := 0x2b2b4c.   (* [comment removed for export] *)
Definition FCC_XHEAD : Z := 0x2b2b58. (* [comment removed for export] *)
Definition FCC_R6 : Z := 0x2b2b68.   (* [comment removed for export] *)
Definition FCC_NAME : Z := 0x2b2b8c. (* [comment removed for export] *)
Definition FCC_R7 : Z := 0x2b2bb0.   (* [comment removed for export] *)
Definition FCC_R8 : Z := 0x2b2be8.   (* [comment removed for export] *)
Definition FCC_R9 : Z := 0x2b2bfc.   (* [comment removed for export] *)
Definition FCC_R10 : Z := 0x2b2c0c.  (* [comment removed for export] *)
Definition FCC_R11 : Z := 0x2b2c48.  (* [comment removed for export] *)
Definition FCC_R12 : Z := 0x2b2c90.  (* [comment removed for export] *)
Definition FCC_OK : Z := 0x2b2c98.   (* [comment removed for export] *)
Definition FCC_RA4 : Z := 0x2b2ca8.  (* [comment removed for export] *)
Definition A_ECHS_FILE : Z := 0x36488.   (* [comment removed for export] *)
Definition A_FCC_FUNC : Z := 0x226af.    (* [comment removed for export] *)
Definition A_DIGITS : Z := 0x1167b.      (* [comment removed for export] *)
Definition A_HEXDIGITS : Z := 0x33a12.   (* [comment removed for export] *)
Definition ERR_LIB_SSL : Z := 20.
Definition R_PASSED_INVALID_ARGUMENT : Z := 0x80106.  (* [comment removed for export] *)
Definition R_INTERNAL_ERROR : Z := 0xc0103.           (* [comment removed for export] *)
Definition fcc_frame (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma idx6 : forall i, 0 <= i < 2^31 -> Z.shiftl i 3 + - Z.land (Z.shiftl i 1) 18446744073709551615 = 6 * i.
Proof.
  intros i Hi. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. change (2 ^ 1) with 2.
  rewrite land_ones64 by lia. lia.
Qed.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.

  Lemma fcc_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 FCC_R1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                       a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_new) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -80)
          /\ rw_cells usegs m1 (bv_unsigned sp + -80) (fcc_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ech_final_config_checks) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI.
    unfold P_ech_final_config_checks, P_X509_VERIFY_PARAM_new, FCC_R1.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. carve_frame 80%nat ST.
    do 10 st1. step. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee A : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 1 <= en_nsuites E < 2^31 ->
      0 < A < 2^64 -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> ee mod 8 = 0 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R1) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (en_nsuites E)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ee) s3 (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 65535) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_HEAD) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FCC_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R1)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC NS AR EEP EEH EAL MI.
    unfold FCC_R1, FCC_HEAD. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    replace (ret_pc (Z_to_bv 64 2828788)) with (Z_to_bv 64 2828788) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. try br.
    (* [comment removed for export] *)
    step. ubal_by EAL. step. if_lit.
    step. rewrite sx32_wz by lia. unfold wz. step. try br.
    do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_seg4n :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee i rv aead : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 1 <= en_nsuites E < 2^31 -> 0 <= i -> i + 1 < en_nsuites E ->
      (rv = 0 \/ (rv = 1 /\ aead = 65535)) -> 0 <= aead < 2^16 ->
      0 < ee -> ee + ENTRY_SIZE < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (en_nsuites E)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ee) s3 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 65535) (Z_to_bv 64 aead) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_HEAD) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 65535) (Z_to_bv 64 aead) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R2)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC NS I0 I1 RV AR EEP EEH MI.
    unfold FCC_R2, FCC_HEAD. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    replace (ret_pc (Z_to_bv 64 2828920)) with (Z_to_bv 64 2828920) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct RV as [->|[-> ->]].
    - step. try br.
      (* [comment removed for export] *)
      step. try br.
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      step. step. try br. apply evt_done. reflexivity.
    - step. if_lit.
      step. try br.
      step. try br.
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      step. step. try br. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_seg4e :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee i rv aead : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 1 <= en_nsuites E < 2^31 -> 0 <= i -> i + 1 = en_nsuites E ->
      (rv = 0 \/ (rv = 1 /\ aead = 65535)) -> 0 <= aead < 2^16 ->
      0 < ee -> ee + ENTRY_SIZE < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (en_nsuites E)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ee) s3 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 65535) (Z_to_bv 64 aead) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 65535) (Z_to_bv 64 aead) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R2)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC NS I0 I1 RV AR EEP EEH MI.
    unfold FCC_R2, FCC_RA1, P_ERR_new. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    replace (ret_pc (Z_to_bv 64 2828920)) with (Z_to_bv 64 2828920) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct RV as [->|[-> ->]].
    - step. try br.
      step. try br.
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      step. step. try br. step. step. apply evt_done. reflexivity.
    - step. if_lit.
      step. try br.
      step. try br.
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      step. step. try br. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_seg4g :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (aead : Z),
      aead <> 65535 -> 0 <= aead < 2^16 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                       s8 s3 s4 (Z_to_bv 64 1) s5 (Z_to_bv 64 65535) (Z_to_bv 64 aead) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_GOOD) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s8 s3 s4 (Z_to_bv 64 1) s5 (Z_to_bv 64 65535) (Z_to_bv 64 aead) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R2)) fc None m (seg_rom usegs)).
  Proof.
    intros until aead. intros NE AR MI.
    unfold FCC_R2, FCC_GOOD.
    replace (ret_pc (Z_to_bv 64 2828920)) with (Z_to_bv 64 2828920) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_lit.
    step. try br. apply evt_done. reflexivity.
  Qed.

  Lemma fcc_seg3 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee i kem kdf aead : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) ->
      rw_cells usegs m (en_suites E + 6 * i) [C2 (wz kem); C2 (wz kdf); C2 (wz aead)] ->
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= i < 2^31 -> 0 < ee -> ee + ENTRY_SIZE < 2^64 ->
      0 < en_suites E -> en_suites E + 6 * i + 6 < 2^64 ->
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (suite_word kem kdf aead (bv_unsigned s3 / 2^48)))
                       (Z_to_bv 64 kem) (Z_to_bv 64 (kdf * 2^16)) (Z_to_bv 64 (aead * 2^32)) a4 a5 a6 a7
                       (Z_to_bv 64 ee) (Z_to_bv 64 (suite_word kem kdf aead (bv_unsigned s3 / 2^48))) (Z_to_bv 64 i) s5 s6 s7 (Z_to_bv 64 aead) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 (Z_to_bv 64 i) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCC_HEAD) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC ROW KR DR AR IR EEP EEH SP0 SH MI.
    unfold FCC_HEAD, FCC_R2, P_OSSL_HPKE_suite_check. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. unfold wz.
    zstep. zstep. zstep. rewrite (idx6 i) by lia.
    zstep. rewrite (Z.add_comm (6 * i) (en_suites E)).
    zstep. zstep. rewrite ?land_ones64 by lia. ub_b2z. step. br. step. br.
    set (Q := en_suites E + 6 * i) in *.
    step. rewrite zx16_wz by lia. step. rewrite zx16_wz by lia. step. rewrite zx16_wz by lia. unfold wz.
    do 7 step. rewrite (pack_suite_word s3 kem kdf aead KR DR AR).
    rewrite !Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit kdf) by lia. rewrite (unsigned_lit aead) by lia.
    step. step. apply evt_done. reflexivity.
  Qed.
End S.

Section S2.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  (* [comment removed for export] *)
  Definition fcc_glue_stmt (raA raB target a0v a1v a2v : Z) : Prop :=
    forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv usegs m1 ->
      evt usegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom usegs)).
  Lemma fcc_glue275 : fcc_glue_stmt FCC_RA1 FCC_RA2 P_ERR_set_debug A_ECHS_FILE 275 A_FCC_FUNC.
  Proof.
    unfold fcc_glue_stmt. intros until m1. intros MI. unfold FCC_RA1, FCC_RA2, P_ERR_set_debug, A_ECHS_FILE, A_FCC_FUNC.
    retpc 2828952. do 7 step. finish.
  Qed.
  Lemma fcc_glue284 : fcc_glue_stmt FCC_RA4 FCC_RA2 P_ERR_set_debug A_ECHS_FILE 284 A_FCC_FUNC.
  Proof.
    unfold fcc_glue_stmt. intros until m1. intros MI. unfold FCC_RA4, FCC_RA2, P_ERR_set_debug, A_ECHS_FILE, A_FCC_FUNC.
    retpc 2829480. do 8 step. finish.
  Qed.
  Lemma fcc_glue2 : fcc_glue_stmt FCC_RA2 FCC_RA3 P_ERR_set_error ERR_LIB_SSL R_PASSED_INVALID_ARGUMENT 0.
  Proof.
    unfold fcc_glue_stmt. intros until m1. intros MI. unfold FCC_RA2, FCC_RA3, P_ERR_set_error, ERR_LIB_SSL, R_PASSED_INVALID_ARGUMENT.
    retpc 2828980. do 7 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segF0 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem), mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R4) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_RA3)) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold FCC_RA3, FCC_R4, P_X509_VERIFY_PARAM_free. retpc 2829052.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 3 step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma fcc_segF :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem), mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R4) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCC_FAIL) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold FCC_FAIL, FCC_R4, P_X509_VERIFY_PARAM_free.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 2 step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma fcc_segOK :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem), mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R4) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCC_OK) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold FCC_OK, FCC_R4, P_X509_VERIFY_PARAM_free.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segE :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (s0o s1o s2o s3o s4o s5o s6o s7o s8o : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells usegs m (bv_unsigned sp + -80) (fcc_frame s8o s7o s6o s5o s4o s3o s2o s1o s0o ra) ->
      stk usegs m lo (bv_unsigned sp + -80) -> hceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0o s1o s3 a1 a2 a3 a4 a5 a6 a7 s2o s3o s4o s5o s6o s7o s8o s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 FCC_R4) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R4)) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI. unfold FCC_R4. unfold fcc_frame in FR. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    retpc 2829064.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. do 10 st1. step. step.
    release_frame FR ST (bv_unsigned sp). apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S2.

(* [comment removed for export] *)
Definition sx16z (t : Z) : Z := if t <? 32768 then t else t + 2^64 - 65536.
Lemma sx16_wz_lit : forall t, 0 <= t < 65536 -> sx16 (wz t) = Z_to_bv 64 (sx16z t).
Proof.
  intros t Ht. unfold sx16, sx16z. rewrite wz_unsigned by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with 32768. change (bv_modulus 16) with 65536. change (bv_modulus 64) with (2^64).
  destruct (Z.ltb_spec t 32768).
  - rewrite (Z.mod_small (t + 32768) 65536) by lia. f_equal. lia.
  - assert (E1 : (t + 32768) mod 65536 = t + 32768 - 65536).
    { rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite E1.
    assert (E2 : (t + 2^64 - 65536) mod 2^64 = (t + 32768 - 65536 - 32768) mod 2^64).
    { rewrite <- (Z.mod_add (t + 2^64 - 65536) (-1)) by lia. f_equal. lia. }
    rewrite E2. reflexivity.
Qed.
Lemma sx16z_range : forall t, 0 <= t < 65536 -> 0 <= sx16z t < 2^64 /\ (2^63 <= sx16z t <-> 32768 <= t).
Proof. intros t Ht. unfold sx16z. destruct (Z.ltb_spec t 32768); lia. Qed.

Section S3.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  Lemma fcc_segX3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p j num : Z) (X : extrep) pad,
      rw_cells usegs m p (ext_cells X pad) -> 0 <= ex_type X < 2^16 -> 0 < p -> p + EXT_SIZE < 2^64 -> 0 <= j < num -> num < 2^31 ->
      p mod 8 = 0 ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      evt usegs (fun ms' => exists a0' a1',
         (32768 <= ex_type X /\
          ms' = MS (mkR (Z_to_bv 64 FCC_RA4) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 num) (Z_to_bv 64 j) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs))
      \/ (ex_type X < 32768 /\ j + 1 < num /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R6) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 num) (Z_to_bv 64 (j + 1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_XHEAD) fc None m (seg_rom usegs))
      \/ (ex_type X < 32768 /\ j + 1 = num /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R6) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 num) (Z_to_bv 64 (j + 1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_NAME) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R6) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 num) (Z_to_bv 64 j) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R6)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros XC TR PP PH JR NR PAL MI. unfold FCC_R6, FCC_RA4, FCC_XHEAD, FCC_NAME, P_ERR_new. unfold ext_cells in XC. unfold EXT_SIZE in PH.
    retpc 2829160.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (sx16z_range (ex_type X) TR) as [SR SI].
    (* [comment removed for export] *)
    step. br. step. ubal_by PAL. step. if_lit.
    step. rewrite (sx16_wz_lit (ex_type X)) by lia.
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      step. step. apply evt_done. eexists. eexists. left. split; [apply SI; revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
    - assert (TL : ex_type X < 32768) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; destruct (Z.lt_ge_cases (ex_type X) 32768) as [Hl|Hg]; [exact Hl| exfalso; pose proof (proj2 SI Hg); lia]).
      clear K0. step. rewrite (unsigned_lit j) by lia. rewrite (bv_swrap_small 32 (j + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
      (* [comment removed for export] *)
      step. br. step.
      step. if_cases K0; zify_cond K0.
      + apply evt_done. eexists. eexists. right; left. split; [exact TL|]. split; [revert K0; rewrite ?unsigned_lit, ?signed_lit by lia; lia| reflexivity].
      + apply evt_done. eexists. eexists. right; right. split; [exact TL|]. split; [revert K0; rewrite ?unsigned_lit, ?signed_lit by lia; lia| reflexivity].
  Qed.
End S3.

Section S4.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  Lemma fcc_segN1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4 (ns rest : list byte) (b0 : byte),
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 ->
      bytes_at usegs m (en_pname E) (ns ++ rest) -> nth_error ns 0 = Some b0 -> bv_unsigned b0 <> 0 -> 0 < en_pname E ->
      mem_inv usegs m ->
      evt usegs (fun ms' =>
         (bv_unsigned b0 = 46 /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 46) (Z_to_bv 64 46) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) (Z_to_bv 64 0) (Z_to_bv 64 (en_pname E)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_FAIL) fc None m (seg_rom usegs))
      \/ (bv_unsigned b0 <> 46 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R7) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 46) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) (Z_to_bv 64 0) (Z_to_bv 64 (en_pname E)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 strlen_entry) fc None m (seg_rom usegs)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCC_NAME) fc None m (seg_rom usegs)).
  Proof.
    intros until b0. intros EC EEP EEH BS NTH B0 PN MI. unfold FCC_NAME, FCC_FAIL, FCC_R7, strlen_entry. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (byte_range b0) as BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (nth_error_lt _ _ _ NTH) as NL. cbn [Z.to_nat] in NL. assert (NTH' : nth_error (ns ++ rest) (Z.to_nat 0) = Some b0) by (rewrite nth_error_app1 by exact NL; exact NTH).
    pose proof (u8ro_read usegs m (en_pname E) (ns ++ rest) 0 b0 _ BS NTH' ltac:(lia) eq_refl) as RD.
    step. unfold wz. step. try br.
    step. change (zxb b0) with (Z_to_bv 64 (bv_unsigned b0)).
    step. step. try br.
    step. step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|]. replace (bv_unsigned b0) with 46 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
    - step. step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.
End S4.

Section S5.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma fcc_segX1 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> 0 <= en_exts E < 2^64 ->
      mem_inv usegs m ->
      evt usegs (fun ms' =>
         (en_exts E = 0 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_NAME) fc None m (seg_rom usegs))
      \/ (0 < en_exts E /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R5) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (en_exts E)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_num) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCC_GOOD) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC EEP EEH XR MI. unfold FCC_GOOD, FCC_R2, FCC_R5, FCC_NAME, P_OPENSSL_sk_num. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. unfold wz. step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|].
      replace (en_exts E) with 0 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
    - step. step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segX2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num : Z),
      0 <= num < 2^31 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
         (num = 0 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R5) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_NAME) fc None m (seg_rom usegs))
      \/ (0 < num /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R5) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 num) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 num) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_XHEAD) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R5) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 num) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R5)) fc None m (seg_rom usegs)).
  Proof.
    intros until num. intros NR MI. unfold FCC_R5, FCC_NAME, FCC_XHEAD. retpc 2829132.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|].
      replace num with 0 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
    - step. step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segXH :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> 0 <= en_exts E < 2^64 ->
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCC_R6) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (en_exts E)) s4 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_value) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCC_XHEAD) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC EEP EEH XR MI. unfold FCC_XHEAD, FCC_R6, P_OPENSSL_sk_value. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. unfold wz. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segN2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name A : Z) (ns rest : list byte) (bl : byte),
      bytes_at usegs m name (ns ++ rest) -> 1 <= zlength ns <= 255 -> nth_error ns (Z.to_nat (zlength ns - 1)) = Some bl -> 0 < name ->
      mem_inv usegs m ->
      evt usegs (fun ms' =>
         (bv_unsigned bl = 46 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R7) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 46) (Z_to_bv 64 46) (Z_to_bv 64 255) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) (Z_to_bv 64 name) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_FAIL) fc None m (seg_rom usegs))
      \/ (bv_unsigned bl <> 46 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 name) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) (Z_to_bv 64 name) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_add1_host) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R7) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (zlength ns)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 name) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R7)) fc None m (seg_rom usegs)).
  Proof.
    intros until bl. intros BS LR NTH PN MI. unfold FCC_R7, FCC_R8, FCC_FAIL, P_X509_VERIFY_PARAM_add1_host. retpc 2829232.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (byte_range bl) as BR. unfold zlength in *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (nth_error_lt _ _ _ NTH) as NL.
    assert (NTH' : nth_error (ns ++ rest) (Z.to_nat (Z.of_nat (length ns) - 1)) = Some bl) by (rewrite nth_error_app1 by exact NL; exact NTH).
    pose proof (u8ro_read usegs m name (ns ++ rest) (Z.of_nat (length ns) - 1) bl _ BS NTH' ltac:(lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. step. ubnot. step. br.
    (* [comment removed for export] *)
    step. step. step. try br.
    zstep. replace (name + (Z.of_nat (length ns) + -1)) with (name + (Z.of_nat (length ns) - 1)) by lia.
    step. change (zxb bl) with (Z_to_bv 64 (bv_unsigned bl)).
    step. step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|].
      replace (bv_unsigned bl) with 46 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
    - step. step. step. step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.
End S5.

(* [comment removed for export] *)
Lemma seqz_ne46 : forall c, 0 <= c < 256 -> c <> 46 -> v_sltiu (Z_to_bv 64 (c + -46)) 1 = Z_to_bv 64 0.
Proof.
  intros c CR NE. rewrite v_sltiu_b2z. f_equal. change (bv_wrap 64 1) with 1.
  destruct (Z.lt_ge_cases c 46).
  - replace (Z_to_bv 64 (c + -46)) with (Z_to_bv 64 (c + -46 + 2^64)).
    2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
      rewrite <- (Z.mod_add (c + -46) 1) by lia. f_equal; lia. }
    rewrite unsigned_lit by lia. replace (c + -46 + 2^64 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - rewrite unsigned_lit by lia. replace (c + -46 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Section S6.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma fcc_segN3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee r : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> (r = 0 \/ r = 1) ->
      mem_inv usegs m ->
      evt usegs (fun ms' =>
         (r = 0 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_RA3) fc None m (seg_rom usegs))
      \/ (r = 1 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R9) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 46) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (en_pname E)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 strrchr_entry) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ee) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R8)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC EEP EEH RR MI. unfold FCC_R8, FCC_RA3, FCC_R9, strrchr_entry. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH. retpc 2829288.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct RR as [-> | ->].
    - step. if_lit. apply evt_done. left. split; reflexivity.
    - step. if_lit. step. unfold wz. step. step. step. apply evt_done. right. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segN4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name q : Z),
      0 <= q < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => let LL := if q =? 0 then name else q in
          ms' = MS (mkR (Z_to_bv 64 FCC_R10) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LL) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 strlen_entry) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FCC_R9) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 name) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R9)) fc None m (seg_rom usegs)).
  Proof.
    intros until q. intros QR MI. unfold FCC_R9, FCC_R10, strlen_entry. retpc 2829308.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (Z.eqb_spec q 0) as [->|NZ].
    - step. if_lit. step. step. apply evt_done. reflexivity.
    - step. try br. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segN5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LL L2 : Z) (ls rest : list byte) (c0 : byte),
      bytes_at usegs m LL (ls ++ rest) -> nth_error ls 0 = Some c0 -> 0 <= L2 < 2^32 -> 0 < LL ->
      LL + 4 <= 2^64 ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      evt usegs (fun ms' => let d := (if bv_unsigned c0 =? 46 then 1 else 0) in
         (L2 < 2 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R10) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 L2) (Z_to_bv 64 2) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_RA3) fc None m (seg_rom usegs))
      \/ (2 <= L2 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R11) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (LL + d)) (Z_to_bv 64 A_DIGITS) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (LL + d)) (Z_to_bv 64 (L2 - d)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 strspn_entry) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R10) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 L2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R10)) fc None m (seg_rom usegs)).
  Proof.
    intros until c0. intros BS NTH LR LLP LLH MI. unfold FCC_R10, FCC_RA3, FCC_R11, strspn_entry, A_DIGITS. retpc 2829324.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (byte_range c0) as BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (nth_error_lt _ _ _ NTH) as NL. cbn [Z.to_nat] in NL.
    assert (NTH' : nth_error (ls ++ rest) (Z.to_nat 0) = Some c0) by (rewrite nth_error_app1 by exact NL; exact NTH).
    pose proof (u8ro_read usegs m LL (ls ++ rest) 0 c0 _ BS NTH' ltac:(lia) eq_refl) as RD.
    step. step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
    - (* [comment removed for export] *)
      step. br. step.
      step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). step.
      destruct (Z.eqb_spec (bv_unsigned c0) 46) as [E46|N46].
      + rewrite E46. step. if_lit.
        (* [comment removed for export] *)
        step. step. br. step. zstep. replace (L2 + -1) with (L2 - 1) by lia.
        do 4 step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
      + step. br.
        do 4 step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| ].
        replace (LL + 0) with LL by lia. replace (L2 - 0) with L2 by lia. reflexivity.
  Qed.
End S6.

Section S7.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma fcc_segN6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LL L3 n1 : Z) (ls rest : list byte) (c0 c1 : byte),
      bytes_at usegs m LL (ls ++ rest) -> (3 <= L3 -> nth_error ls 0 = Some c0 /\ nth_error ls 1 = Some c1) -> 0 <= L3 < 2^32 -> 0 <= n1 < 2^32 -> 0 < LL ->
      LL + 3 <= 2^64 ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      evt usegs (fun ms' => exists a0' a1',
         (n1 = L3 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R11) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_RA3) fc None m (seg_rom usegs))
      \/ (n1 <> L3 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R11) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_OK) fc None m (seg_rom usegs))
      \/ (n1 <> L3 /\ 3 <= L3 /\ bv_unsigned c0 = 48 /\ Z.lor (bv_unsigned c1) 32 = 120 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (LL + 2)) (Z_to_bv 64 A_HEXDIGITS) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 strspn_entry) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R11) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R11)) fc None m (seg_rom usegs)).
  Proof.
    intros until c1. intros BS NTH LR NR LLP LLH MI. unfold FCC_R11, FCC_RA3, FCC_OK, FCC_R12, strspn_entry, A_HEXDIGITS. retpc 2829384.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (byte_range c0) as BR0. pose proof (byte_range c1) as BR1.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    { apply evt_done. eexists. eexists. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity]. }
    assert (NE : n1 <> L3) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    step. step. if_cases K0; zify_cond K0.
    { apply evt_done. eexists. eexists. right; left. split; [exact NE| reflexivity]. }
    assert (L3R : 3 <= L3) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    destruct (NTH L3R) as [NTH0 NTH1].
    pose proof (nth_error_lt _ _ _ NTH0) as NL0. pose proof (nth_error_lt _ _ _ NTH1) as NL1. cbn [Z.to_nat] in NL0, NL1.
    assert (NTH0' : nth_error (ls ++ rest) (Z.to_nat 0) = Some c0) by (rewrite nth_error_app1 by exact NL0; exact NTH0).
    assert (NTH1' : nth_error (ls ++ rest) (Z.to_nat 1) = Some c1) by (rewrite nth_error_app1 by exact NL1; exact NTH1).
    pose proof (u8ro_read usegs m LL (ls ++ rest) 0 c0 _ BS NTH0' ltac:(lia) eq_refl) as RD0.
    pose proof (u8ro_read usegs m LL (ls ++ rest) 1 c1 _ BS NTH1' ltac:(lia) eq_refl) as RD1.
    step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). step. step. if_cases K0; zify_cond K0.
    { apply evt_done. eexists. eexists. right; left. split; [exact NE| reflexivity]. }
    assert (C0E : bv_unsigned c0 = 48) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. br.
    step. change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)). step.
    pose proof (lor_lt_pow2 (bv_unsigned c1) 32 8 ltac:(lia) ltac:(lia)) as ORR.
    step. step. if_cases K0; zify_cond K0.
    { apply evt_done. eexists. eexists. right; left. split; [exact NE| reflexivity]. }
    assert (C1E : Z.lor (bv_unsigned c1) 32 = 120) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. br.
    do 4 step. apply evt_done. exists s4, s4. right; right. split; [exact NE|]. split; [exact L3R|]. split; [exact C0E|]. split; [exact C1E| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fcc_segN7 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L3 n2 : Z),
      3 <= L3 < 2^32 -> 0 <= n2 < 2^32 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
         (n2 = L3 - 2 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n2) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (L3 - 2)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_RA3) fc None m (seg_rom usegs))
      \/ (n2 <> L3 - 2 /\
          ms' = MS (mkR (Z_to_bv 64 FCC_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n2) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (L3 - 2)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FCC_OK) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 FCC_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n2) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FCC_R12)) fc None m (seg_rom usegs)).
  Proof.
    intros until n2. intros LR NR MI. unfold FCC_R12, FCC_RA3, FCC_OK. retpc 2829456.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. replace (L3 + -2) with (L3 - 2) by lia. step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
    - apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.
End S7.
