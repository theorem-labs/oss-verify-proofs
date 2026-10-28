(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsWalk AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C4 ECH_AStmt_C11 ECH_AKit ECH_AsKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

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
  intros w kem kdf aead KR DR AR. pose proof (aword_range w) as WR.
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
Definition FCC_R1 : Z := 0x270f3c.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CK2.
  Context {HCEIL : HeapCeil}.

  Lemma accessible_read2 : forall m a, accessible m a 2 ->
    exists v, 0 <= v < 8 /\ (v = 0 \/ a mod 8 + 2 <= v) /\ ov_read_bytes asegs m (wa (sh a)) 1 = Some [b8 v].
  Proof.
    intros m a ACC. pose proof ACC as (A0 & A1 & AC).
    destruct (accessible_read1 m a ltac:(eapply accessible_sub; [exact ACC| lia| lia| lia])) as (v & V0 & OK & RD).
    exists v. split; [exact V0|]. split; [| exact RD].
    destruct (Z.eq_dec v 0) as [->|NZ]; [left; reflexivity| right].
    destruct OK as [K|K]; [exfalso; exact (NZ K)|].
    destruct (AC (a + 1) ltac:(lia)) as (v' & V0' & RD' & OK').
    assert (SX : sh (a + 1) = sh a) by (unfold sh; Z.div_mod_to_equations; nia).
    assert (EV : v' = v).
    { apply ov_rdn1 in RD || idtac. unfold mrd in RD'. rewrite SX in RD'. rewrite ov_rdn in RD. cbn [rdn] in RD. unfold mrd in RD |- *.
      destruct (m (wa (sh a))) as [b|] eqn:E.
      - rewrite RD' in RD || (rewrite <- RD' in RD || idtac).
        assert (EB : b8 v' = b8 v) by congruence. apply (f_equal bv_unsigned) in EB. rewrite !b8_unsigned_small in EB by lia. exact EB.
      - destruct (seg_rom asegs (wa (sh a))) as [b|]; [| discriminate RD'].
        assert (EB : b8 v' = b8 v) by congruence. apply (f_equal bv_unsigned) in EB. rewrite !b8_unsigned_small in EB by lia. exact EB. }
    subst v'. destruct OK' as [K'|K']; [exfalso; exact (NZ K')|]. Z.div_mod_to_equations. lia.
  Qed.

  Lemma ck2_bge_false : forall a v, 0 <= a -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    negb (bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7 + 1)) (Z_to_bv 64 v)) = false.
  Proof.
    intros a v Ha Hv Hav. rewrite ck1_land7_of_word by exact Ha.
    unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64 / 2) with (2^63). change (2 ^ Z.of_N 64) with (2^64).
    rewrite (Z.mod_small (a mod 8 + 1 + 2^63)) by (Z.div_mod_to_equations; lia). rewrite (Z.mod_small (v + 2^63)) by lia.
    destruct (Z.ltb_spec (a mod 8 + 1 + 2 ^ 63 - 2 ^ 63) (v + 2 ^ 63 - 2 ^ 63)); [reflexivity| exfalso; Z.div_mod_to_equations; lia].
  Qed.
  Lemma ck2_blt_true : forall a v, 0 <= a -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7 + 1)) (Z_to_bv 64 v) = true.
  Proof. intros a v Ha Hv Hav. pose proof (ck2_bge_false a v Ha Hv Hav) as E. destruct (bv_lts _ _); [reflexivity| discriminate E]. Qed.
  (* [comment removed for export] *)
  Lemma ck2_bge_false' : forall a v, 0 <= a < 2^64 -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    negb (bv_lts (Z_to_bv 64 (Z.land a 7 + 1)) (Z_to_bv 64 v)) = false.
  Proof. intros a v Ha Hv Hav. rewrite <- (unsigned_lit a) at 1 by lia. apply ck2_bge_false; lia. Qed.
  Lemma ck2_blt_true' : forall a v, 0 <= a < 2^64 -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    bv_lts (Z_to_bv 64 (Z.land a 7 + 1)) (Z_to_bv 64 v) = true.
  Proof. intros a v Ha Hv Hav. rewrite <- (unsigned_lit a) at 1 by lia. apply ck2_blt_true; lia. Qed.
End CK2.

(* [comment removed for export] *)
Ltac ck2_load ACC a v V1 V2 Ha :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in let SXV := fresh "SXV" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc a 2) by (eapply accessible_sub; [exact ACC| lia| lia| lia]) end;
  assert (Ha : 0 <= a) by lia;
  destruct (accessible_read2 _ _ ACW) as (v & V1 & V2 & RD);
  rewrite <- (sh_shiftr a), ASHADOW_BASE_val in RD by exact Ha;
  replace (wa (Z.shiftr a 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW;
  assert (SXV : sxb (b8 v) = Z_to_bv 64 v) by (unfold sxb; rewrite b8_signed_small by lia; reflexivity); rewrite SXV; clear SXV.
(* [comment removed for export] *)
Ltac ck2_branch_bge a v V1 V2 Ha K :=
  let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in
  step; destruct (Z.eq_dec v 0) as [Ev|Nv];
  [ if_false_by (ck1_bnez_false v Ev); apply K
  | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
    step; zstep; step; first [if_false_by (ck2_bge_false a v Ha V1 VV)| if_false_by (ck2_bge_false' a v ltac:(lia) V1 VV)]; step; apply K ].
Ltac ck2_branch_blt a v V1 V2 Ha K :=
  let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in
  step; destruct (Z.eq_dec v 0) as [Ev|Nv];
  [ if_false_by (ck1_bnez_false v Ev); apply K
  | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
    step; zstep; step; first [if_true_by (ck2_blt_true a v Ha V1 VV)| if_true_by (ck2_blt_true' a v ltac:(lia) V1 VV)]; apply K ].

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

(* [comment removed for export] *)
Definition AFC_R1 : Z := 0x552aa0.   (* [comment removed for export] *)
Definition AFC_HEAD : Z := 0x552b0c. (* [comment removed for export] *)
Definition AFC_R2 : Z := 0x552ba0.   (* [comment removed for export] *)
Definition AFC_RA1 : Z := 0x552c08.  (* [comment removed for export] *)
Definition AFC_DBG : Z := 0x552c1c.  (* [comment removed for export] *)
Definition AFC_RA2 : Z := 0x552c24.  (* [comment removed for export] *)
Definition AFC_RA3 : Z := 0x552c3c.  (* [comment removed for export] *)
Definition AFC_RB1 : Z := 0x552c50.  (* [comment removed for export] *)
Definition AFC_RB2 : Z := 0x552c6c.  (* [comment removed for export] *)
Definition AFC_FAIL : Z := 0x552c84. (* [comment removed for export] *)
Definition AFC_TAIL : Z := 0x552c88. (* [comment removed for export] *)
Definition AFC_R4 : Z := 0x552c94.   (* [comment removed for export] *)
Definition AFC_EPI : Z := 0x552c98.
Definition AFC_GOOD : Z := 0x552cd4. (* [comment removed for export] *)
Definition AFC_R5 : Z := 0x552cfc.   (* [comment removed for export] *)
Definition AFC_XHEAD : Z := 0x552d08. (* [comment removed for export] *)
Definition AFC_R6 : Z := 0x552d20.   (* [comment removed for export] *)
Definition AFC_NAME : Z := 0x552d68. (* [comment removed for export] *)
Definition AFC_R7 : Z := 0x552dbc.   (* [comment removed for export] *)
Definition AFC_R8 : Z := 0x552e0c.   (* [comment removed for export] *)
Definition AFC_R9 : Z := 0x552e2c.   (* [comment removed for export] *)
Definition AFC_R10 : Z := 0x552e40.  (* [comment removed for export] *)
Definition AFC_R11 : Z := 0x552e90.  (* [comment removed for export] *)
Definition AFC_R12 : Z := 0x552f04.  (* [comment removed for export] *)
Definition AFC_OK : Z := 0x552f0c.   (* [comment removed for export] *)
Definition AFC_RA4 : Z := 0x552f1c.  (* [comment removed for export] *)
Definition AA_ECHS_FILE : Z := 0x11238e.   (* [comment removed for export] *)
Definition AA_FCC_FUNC : Z := 0x1123c0.    (* [comment removed for export] *)
Definition AA_DIGITS : Z := 0x112400.      (* [comment removed for export] *)
Definition AA_HEXDIGITS : Z := 0x112420.   (* [comment removed for export] *)
Definition ERR_LIB_SSL : Z := 20.
Definition R_PASSED_INVALID_ARGUMENT : Z := 0x80106.  (* [comment removed for export] *)
Definition R_INTERNAL_ERROR : Z := 0xc0103.           (* [comment removed for export] *)
Definition ASHB : Z := 0x7fff8000.
(* [comment removed for export] *)
Definition afcc_frame (ee : Z) (vpm : word) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (wz (Z.land (ee + 32) 7 + 3)); C8 vpm; C8 (wz ee); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Lemma afcc_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo ee : Z),
      a0 = Z_to_bv 64 ee ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 junk (a1' : word),
          ms' = MS (mkR (Z_to_bv 64 AFC_R1) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 ee) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_new) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -128)
          /\ rw_cells asegs m1 (bv_unsigned sp + -128) ([CB 24 junk] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ech_final_config_checks) fc None m (seg_rom asegs)).
  Proof.
    intros until ee. intros A0 GSB SHB0 ST CEIL LO MI. subst a0.
    unfold P_ech_final_config_checks, AFC_R1, ASHB, P_X509_VERIFY_PARAM_new.
    acb. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 128%nat ST.
    do 13 st1.
    step. step. step. step. step. step. step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
    cbn [app]. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_seg2 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee V : Z) (E : entrep) pad1 pad2 pad3 pad4 junk (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 1 <= en_nsuites E < 2^31 ->
      0 < V < 2^64 -> 0 <= ee -> ee mod 8 = 0 -> ee + ENTRY_SIZE <= AAPP_HI -> accessible m ee ENTRY_SIZE ->
      rw_cells asegs m (bv_unsigned sp + -128) ([CB 24 junk] ++ [C8 f11; C8 f10; C8 f9; C8 f8; C8 f7; C8 f6; C8 f5; C8 f4; C8 f3; C8 f2; C8 f1; C8 f0; C8 fra]) ->
      aceil <= bv_unsigned sp + -128 -> (ee + ENTRY_SIZE <= bv_unsigned sp + -128) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AFC_R1) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 (Z.land (ee + 32) 7 + 3)) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) (Z_to_bv 64 V) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                       (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_HEAD) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -128, bv_unsigned sp + -104)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (bv_unsigned sp + -128) (afcc_frame ee (Z_to_bv 64 V) f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra))
        (MS (mkR (Z_to_bv 64 AFC_R1) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros EC NS VR EE0 EAL EEH ACCE FR CSP EEF MI.
    unfold AFC_R1, AFC_HEAD, ASHB in *. unfold entry_cells in EC. unfold ENTRY_SIZE, AAPP_HI in *. retpc. acb.
    pose proof (aword_range sp) as SPR.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp + -104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
    (* [comment removed for export] *)
    step. step. try br. clear ACCE.
    replace (bv_unsigned sp - 112) with (bv_unsigned sp + -128 + 16) by lia. idtac.
    replace (bv_unsigned sp - 120) with (bv_unsigned sp + -128 + 8) by lia. idtac.
    (* [comment removed for export] *)
    idtac. do 2 st1. step. ubal_by EAL. step. if_lit. do 2 step. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCE : accessible mx ee 104) by (unfold id in ACCE0; eapply accessible_across; [exact ACCE0| exact MU|]; constructor; [cbn; unfold AHI_LO; clear - CSP ACEILB; lia| constructor]) end.
    ck8_check ACCE (ee + 32).
    (* [comment removed for export] *)
    step. rewrite sx32_wz by lia. unfold wz. step. try br.
    (* [comment removed for export] *)
    step. idtac. replace (bv_unsigned sp - 120) with (bv_unsigned sp + -128 + 8) by lia. idtac. idtac. idtac. do 4 step. zstep. step. zstep. step. zstep.
    replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128 + 0) by lia. st1. zstep. step.
    apply evt_done. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition afcc3_post (sp gp tp t0 t1 t2 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (ee V i kem kdf aead : Z) (w : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (a1' a2' a3' a4' a5' : word),
      ms' = MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 (suite_word kem kdf aead (bv_unsigned w / 2^48)))
                   a1' a2' a3' a4' a5' a6 a7
                   (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) (Z_to_bv 64 (suite_word kem kdf aead (bv_unsigned w / 2^48))) (Z_to_bv 64 ASHB)
                   (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
               F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs).
  Lemma afcc_seg3 :
    forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 w : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee V i kem kdf aead : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> accessible m ee ENTRY_SIZE ->
      rw_cells asegs m (en_suites E + 6 * i) [C2 (wz kem); C2 (wz kdf); C2 (wz aead)] -> accessible m (en_suites E + 6 * i) 6 ->
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= i < 2^31 -> 0 < en_suites E -> en_suites E + 6 * i + 6 <= AAPP_HI ->
      mem_inv asegs m ->
      evt asegs (afcc3_post sp gp tp t0 t1 t2 a6 a7 s2 t3 t4 t5 t6 F fc ee V i kem kdf aead w m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
            F (Z_to_bv 64 AFC_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until pad4. intros EC EE0 EEH ACCE ROW ACCR KR DR AR IR SP0 SH MI.
    unfold AFC_HEAD, AFC_R2, P_OSSL_HPKE_suite_check, ASHB in *. unfold entry_cells in EC. unfold ENTRY_SIZE, AAPP_HI in *. acb.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    ck8_check ACCE (ee + 40). go.
    replace (bv_unsigned (Z_to_bv 64 (Z.shiftl i 3)) - bv_unsigned (Z_to_bv 64 (Z.shiftl i 1)) + en_suites E) with (en_suites E + 6 * i) by (rewrite !Z.shiftl_mul_pow2 by lia; rewrite !unsigned_lit by lia; lia).
    rewrite (v_sltu_b2z (Z_to_bv 64 0)), v_sltiu_b2z. unfold wz. rewrite !(unsigned_lit 0), (unsigned_lit (en_suites E)), (unsigned_lit (en_suites E + 6 * i)) by lia. change (bv_wrap 64 1) with 1.
    rewrite (proj2 (Z.ltb_lt 0 (en_suites E))) by lia. rewrite (proj2 (Z.ltb_ge (en_suites E + 6 * i) 1)) by lia. cbn [Z.b2z]. if_lit. go.
    set (Q := en_suites E + 6 * i) in *.
    (* [comment removed for export] *)
    assert (KA : forall (v : Z) (a2v a3v : word),
      evt asegs (afcc3_post sp gp tp t0 t1 t2 a6 a7 s2 t3 t4 t5 t6 F fc ee V i kem kdf aead w m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 Q) (Z_to_bv 64 v) a2v a3v a4 a5 a6 a7 s2
                 (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + 2147450880))
                 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 0x552b48) fc None m (seg_rom asegs))).
    { intros vA a2v a3v0.
      (* [comment removed for export] *)
      zstep. zstep. zstep. ck1_load ACCR (Q + 3) vB VB1 VB2 HB.
      (* [comment removed for export] *)
      assert (KB : forall (v : Z) (a3v : word),
        evt asegs (afcc3_post sp gp tp t0 t1 t2 a6 a7 s2 t3 t4 t5 t6 F fc ee V i kem kdf aead w m)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 Q) (Z_to_bv 64 v) (Z_to_bv 64 (Q + 3)) a3v a4 a5 a6 a7 s2
                   (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + 2147450880))
                   (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + 2147450880)) t3 t4 t5 t6)
              F (Z_to_bv 64 0x552b5c) fc None m (seg_rom asegs))).
      { intros vB' a3v.
        (* [comment removed for export] *)
        zstep. zstep. zstep. ck2_load ACCR (Q + 4) vC VC1 VC2 HC.
        step. rewrite zx16_wz by lia. step. rewrite zx16_wz by lia. unfold wz.
        (* [comment removed for export] *)
        assert (KC : forall (v : Z) (a4v a5v : word),
          evt asegs (afcc3_post sp gp tp t0 t1 t2 a6 a7 s2 t3 t4 t5 t6 F fc ee V i kem kdf aead w m)
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 kdf) (Z_to_bv 64 (Q + 4)) (Z_to_bv 64 kem) (Z_to_bv 64 v) a4v a5v a6 a7 s2
                     (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + 2147450880))
                     (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + 2147450880)) t3 t4 t5 t6)
                F (Z_to_bv 64 0x552b78) fc None m (seg_rom asegs))).
        { intros vC' a4v a5v.
          (* [comment removed for export] *)
          go. unfold wz in *.
          replace (Z.shiftl kdf 16) with (Z.shiftl (bv_unsigned (Z_to_bv 64 kdf)) 16) by (rewrite (unsigned_lit kdf) by lia; reflexivity).
          rewrite (pack_suite_word w kem kdf aead KR DR AR).
          rewrite !Z.shiftl_mul_pow2 by lia. rewrite ?(unsigned_lit kdf) by lia. rewrite ?(unsigned_lit aead) by lia.
          go. step.
          unfold afcc3_post. finish. }
        cbv delta [mkR] in KC.
        pose proof (KC vC) as KCv. ck2_branch_bge (Q + 4) vC VC1 VC2 HC KCv. }
      cbv delta [mkR] in KB.
      pose proof (KB vB) as KBv. ck1_branch_bge (Q + 3) vB VB1 VB2 HB KBv. }
    cbv delta [mkR] in KA.
    (* [comment removed for export] *)
    ck1_load ACCR Q vA VA1 VA2 HA.
    pose proof (KA vA) as KAv. ck1_branch_bge Q vA VA1 VA2 HA KAv.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_seg4n :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 w t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee V i rv aead : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 1 <= en_nsuites E < 2^31 -> 0 <= i -> i + 1 < en_nsuites E ->
      (rv = 0 \/ (rv = 1 /\ aead = 65535)) -> 0 <= aead < 2^16 ->
      0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> accessible m ee ENTRY_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 (en_nsuites E)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                       (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_HEAD) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad4. intros EC NS I0 I1 RV AR EE0 EEH ACCE MI.
    unfold AFC_R2, AFC_HEAD, ASHB in *. unfold entry_cells in EC. unfold ENTRY_SIZE, AAPP_HI in *. retpc. acb.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct RV as [->|[-> ->]].
    - go.
      ck8_check ACCE (ee + 32).
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      go. try (br; go). apply evt_done. reflexivity.
    - go.
      ck8_check ACCE (ee + 32).
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      go. try (br; go). apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_seg4e :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 w t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee V i rv aead : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 1 <= en_nsuites E < 2^31 -> 0 <= i -> i + 1 = en_nsuites E ->
      (rv = 0 \/ (rv = 1 /\ aead = 65535)) -> 0 <= aead < 2^16 ->
      0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> accessible m ee ENTRY_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_RA1) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 (en_nsuites E)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                       (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 65535) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 aead) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (ee + 40)) w (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 (Z.shiftr (ee + 40) 3 + ASHB)) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad4. intros EC NS I0 I1 RV AR EE0 EEH ACCE MI.
    unfold AFC_R2, AFC_RA1, P_ERR_new, ASHB in *. unfold entry_cells in EC. unfold ENTRY_SIZE, AAPP_HI in *. retpc. acb.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct RV as [->|[-> ->]].
    - go.
      ck8_check ACCE (ee + 32).
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      go. try (br; go). step. apply evt_done. reflexivity.
    - go.
      ck8_check ACCE (ee + 32).
      step. unfold zx32. rewrite wz_unsigned by lia. rewrite Z.mod_small by lia.
      go. try (br; go). step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_seg4g :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (aead : Z),
      aead <> 65535 -> 0 <= aead < 2^16 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R2) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 65535) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 aead) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 1) s9 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_GOOD) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFC_R2) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 65535) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 aead) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 1) s9 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until aead. intros NE AR MI. unfold AFC_R2, AFC_GOOD. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. try br. go. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segX1 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4 (vpm f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> 0 <= en_exts E < 2^64 -> accessible m ee ENTRY_SIZE ->
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee vpm f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 128 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
         (en_exts E = 0 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (ee + 56)) s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_NAME) fc None m (seg_rom asegs))
      \/ (0 < en_exts E /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R5) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 (en_exts E)) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (ee + 56)) s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_num) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R2) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFC_GOOD) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros EC EE0 EEH XR ACCE FR SPL MI. unfold AFC_GOOD, AFC_R2, AFC_R5, AFC_NAME, P_OPENSSL_sk_num, ASHB in *. unfold entry_cells in EC.
    unfold afcc_frame, wz in FR. unfold ENTRY_SIZE, AAPP_HI in *. acb. pose proof (aword_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    replace (bv_unsigned sp - 120) with (bv_unsigned sp + -128 + 8) by lia. step. zstep. zstep. zstep.
    ck8_check ACCE (ee + 56). step. unfold wz. step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|].
      replace (en_exts E) with 0 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
    - step. step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segX2 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num : Z),
      0 <= num < 2^31 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
         (num = 0 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R5) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_NAME) fc None m (seg_rom asegs))
      \/ (0 < num /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R5) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 num) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 num) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_XHEAD) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R5) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 num) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R5)) fc None m (seg_rom asegs)).
  Proof.
    intros until num. intros NR MI. unfold AFC_R5, AFC_NAME, AFC_XHEAD. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|].
      replace num with 0 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
    - step. step. apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segXH :
    forall (ra sp gp tp t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> 0 <= en_exts E < 2^64 -> accessible m ee ENTRY_SIZE ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R6) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 (en_exts E)) s5 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (ee + 56)) s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_value) fc None m (seg_rom asegs))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (ee + 56)) s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFC_XHEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until pad4. intros EC EE0 EEH XR ACCE MI. unfold AFC_XHEAD, AFC_R6, P_OPENSSL_sk_value, ASHB in *. unfold entry_cells in EC. unfold ENTRY_SIZE, AAPP_HI in *. acb.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    ck8_check ACCE (ee + 56). step. unfold wz. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segX3 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p j num : Z) (X : extrep) pad,
      rw_cells asegs m p (ext_cells X pad) -> 0 <= ex_type X < 2^16 -> 0 <= p -> p + EXT_SIZE <= AAPP_HI -> accessible m p EXT_SIZE -> 0 <= j < num -> num < 2^31 ->
      0 < p -> p mod 8 = 0 ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' : word),
         (32768 <= ex_type X /\
          ms' = MS (mkR (Z_to_bv 64 AFC_RA4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 num) (Z_to_bv 64 j) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs))
      \/ (ex_type X < 32768 /\ j + 1 < num /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R6) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 num) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_XHEAD) fc None m (seg_rom asegs))
      \/ (ex_type X < 32768 /\ j + 1 = num /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R6) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 num) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_NAME) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R6) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 num) (Z_to_bv 64 j) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R6)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros XC TR PP PH ACCX JR NR PNZ PAL MI. unfold AFC_R6, AFC_RA4, AFC_XHEAD, AFC_NAME, P_ERR_new, ASHB in *. unfold ext_cells in XC. unfold EXT_SIZE, AAPP_HI in *.
    retpc. acb.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (sx16z_range (ex_type X) TR) as [SR SI].
    (* [comment removed for export] *)
    go. try br. go. try (ubal_by PAL; step; if_lit). go. ck8_check ACCX p.
    step. rewrite (sx16_wz_lit (ex_type X)) by lia.
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      step. step. apply evt_done. do 3 eexists. left. split; [apply SI; revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
    - assert (TL : ex_type X < 32768) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; destruct (Z.lt_ge_cases (ex_type X) 32768) as [Hl|Hg]; [exact Hl| exfalso; pose proof (proj2 SI Hg); lia]).
      clear K0. step. rewrite (unsigned_lit j) by lia. rewrite (bv_swrap_small 32 (j + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
      go. br. go. if_cases K0; zify_cond K0.
      + apply evt_done. do 3 eexists. right; left. split; [exact TL|]. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
      + go. apply evt_done. do 3 eexists. right; right. split; [exact TL|]. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segN1 :
    forall (ra sp gp tp t0 t1 t2 s1 s2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee nn : Z) (E : entrep) pad1 pad2 pad3 pad4 (ns rest : list byte) (b0 : byte)
           (vpm f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> accessible m ee ENTRY_SIZE ->
      bytes_at asegs m (en_pname E) (ns ++ rest) -> nth_error ns 0 = Some b0 -> bv_unsigned b0 <> 0 -> 0 < en_pname E -> en_pname E + nn <= AAPP_HI ->
      accessible m (en_pname E) nn -> 1 <= nn ->
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee vpm f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 128 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' : word),
         (bv_unsigned b0 = 46 /\
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + ASHB)) a0' a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (ee + 8)) (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 0) vpm (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_TAIL) fc None m (seg_rom asegs))
      \/ (bv_unsigned b0 <> 46 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R7) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + ASHB)) (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 46) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (ee + 8)) (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 0) vpm (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_strlen_icpt) fc None m (seg_rom asegs)))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFC_NAME) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros EC EE0 EEH ACCE BS NTH B0 PN PNH ACCN NN1 FR SPL MI. unfold AFC_NAME, AFC_TAIL, AFC_R7, P_strlen_icpt, ASHB in *. unfold entry_cells in EC.
    unfold afcc_frame, wz in FR. unfold ENTRY_SIZE, AAPP_HI in *. acb. pose proof (aword_range sp) as SPR.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (abyte_range b0) as BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (nth_error_lt _ _ _ NTH) as NL. cbn [Z.to_nat] in NL. assert (NTH' : nth_error (ns ++ rest) (Z.to_nat 0) = Some b0) by (rewrite nth_error_app1 by exact NL; exact NTH).
    pose proof (u8ro_read asegs m (en_pname E) (ns ++ rest) 0 b0 _ BS NTH' ltac:(lia) eq_refl) as RD.
    (* [comment removed for export] *)
    go. ck8_check ACCE (ee + 8). go. try br. go. unfold wz.
    (* [comment removed for export] *)
    assert (K : forall (v : Z) (a1v : word),
      evt asegs (fun ms' => exists (a0' a1' : word),
         (bv_unsigned b0 = 46 /\
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + 2147450880)) a0' a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (ee + 8)) (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 0) vpm (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x552c88) fc None m (seg_rom asegs))
      \/ (bv_unsigned b0 <> 46 /\
          ms' = MS (mkR (Z_to_bv 64 0x552dbc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + 2147450880)) (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 46) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (ee + 8)) (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 0) vpm (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 1738488) fc None m (seg_rom asegs)))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + 2147450880)) (Z_to_bv 64 v) a1v a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (ee + 8)) (Z_to_bv 64 (en_pname E)) s4 vpm (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x552d9c) fc None m (seg_rom asegs))).
    { intros v a1v.
      (* [comment removed for export] *)
      step. change (zxb b0) with (Z_to_bv 64 (bv_unsigned b0)). step. step. try br. step. step. if_cases K0; zify_cond K0.
      - apply evt_done. do 2 eexists. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|]. replace (bv_unsigned b0) with 46 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
      - step. step. step. apply evt_done. do 2 eexists. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity]. }
    cbv delta [mkR] in K.
    ck1_load ACCN (en_pname E) v V1 V2 Hk.
    pose proof (K v) as Kv. ck1_branch_blt (en_pname E) v V1 V2 Hk Kv.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segN2 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name V nn : Z) (ns rest : list byte) (bl : byte) (ee : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      bytes_at asegs m name (ns ++ rest) -> 1 <= zlength ns <= 255 -> nth_error ns (Z.to_nat (zlength ns - 1)) = Some bl -> 0 < name -> name + nn <= AAPP_HI ->
      accessible m name nn -> zlength ns <= nn ->
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee (Z_to_bv 64 V) f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 128 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists (a2' a3' : word),
         (bv_unsigned bl = 46 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R7) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 46) (Z_to_bv 64 46) a2' a3' a4 a5 a6 a7
                       s2 (Z_to_bv 64 name) (Z_to_bv 64 0) (Z_to_bv 64 V) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_TAIL) fc None m (seg_rom asegs))
      \/ (bv_unsigned bl <> 46 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) (Z_to_bv 64 name) (Z_to_bv 64 0) a3' a4 a5 a6 a7
                       s2 (Z_to_bv 64 name) (Z_to_bv 64 0) (Z_to_bv 64 V) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_add1_host) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R7) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (zlength ns)) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 name) s4 (Z_to_bv 64 V) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R7)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros BS LR NTH PN PNH ACCN NN FR SPL MI. unfold AFC_R7, AFC_R8, AFC_TAIL, P_X509_VERIFY_PARAM_add1_host, ASHB, AAPP_HI in *. retpc. acb.
    unfold afcc_frame, wz in FR. pose proof (aword_range sp) as SPR.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (abyte_range bl) as BR. unfold zlength in *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (nth_error_lt _ _ _ NTH) as NL.
    assert (NTH' : nth_error (ns ++ rest) (Z.to_nat (Z.of_nat (length ns) - 1)) = Some bl) by (rewrite nth_error_app1 by exact NL; exact NTH).
    pose proof (u8ro_read asegs m name (ns ++ rest) (Z.of_nat (length ns) - 1) bl _ BS NTH' ltac:(lia) eq_refl) as RD.
    (* [comment removed for export] *)
    step. zstep. zstep.
    assert (K : forall (v : Z) (a3v : word),
      evt asegs (fun ms' => exists (a2' a3' : word),
         (bv_unsigned bl = 46 /\
          ms' = MS (mkR (Z_to_bv 64 5582268) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 46) (Z_to_bv 64 46) a2' a3' a4 a5 a6 a7
                       s2 (Z_to_bv 64 name) (Z_to_bv 64 0) (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x552c88) fc None m (seg_rom asegs))
      \/ (bv_unsigned bl <> 46 /\
          ms' = MS (mkR (Z_to_bv 64 0x552e0c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) (Z_to_bv 64 name) (Z_to_bv 64 0) a3' a4 a5 a6 a7
                       s2 (Z_to_bv 64 name) (Z_to_bv 64 0) (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 4400496) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 5582268) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (Z.of_nat (length ns))) (Z_to_bv 64 (name + Z.of_nat (length ns) + -1)) (Z_to_bv 64 v) a3v a4 a5 a6 a7
                 s2 (Z_to_bv 64 name) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x552ddc) fc None m (seg_rom asegs))).
    { intros v a3v.
      (* [comment removed for export] *)
      go. try br. go.
      change (zxb bl) with (Z_to_bv 64 (bv_unsigned bl)). if_cases K0; zify_cond K0.
      - apply evt_done. do 2 eexists. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia|].
        replace (bv_unsigned bl) with 46 by (revert K0; rewrite ?unsigned_lit by lia; lia). reflexivity.
      - go. step. apply evt_done. do 2 eexists. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity]. }
    cbv delta [mkR] in K.
    go. rewrite zb_lxor_ones by lia. try br. go. replace (name + (Z.of_nat (length ns) + -1)) with (name + Z.of_nat (length ns) + -1) by lia.
    ck1_load ACCN (name + Z.of_nat (length ns) + -1) v V1 V2 Hk.
    pose proof (K v) as Kv. ck1_branch_blt (name + Z.of_nat (length ns) + -1) v V1 V2 Hk Kv.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segN3 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee r : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 <= ee -> ee + ENTRY_SIZE <= AAPP_HI -> accessible m ee ENTRY_SIZE -> (r = 0 \/ r = 1) ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
         (r = 0 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + ASHB)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (ee + 8)) s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_FAIL) fc None m (seg_rom asegs))
      \/ (r = 1 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R9) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + ASHB)) (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 46) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (en_pname E)) s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_strrchr) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 8) 3 + ASHB)) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (ee + 8)) s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R8)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad4. intros EC EE0 EEH ACCE RR MI. unfold AFC_R8, AFC_FAIL, AFC_R9, P_strrchr, ASHB in *. unfold entry_cells in EC. unfold ENTRY_SIZE, AAPP_HI in *. retpc. acb.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct RR as [-> | ->].
    - step. if_lit. apply evt_done. left. split; reflexivity.
    - step. if_lit. ck8_check ACCE (ee + 8). step. unfold wz. step. step. step. step. apply evt_done. right. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segN4 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name q : Z),
      0 <= q < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => let LL := if q =? 0 then name else q in
          ms' = MS (mkR (Z_to_bv 64 AFC_R10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 LL) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_strlen_icpt) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFC_R9) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 name) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R9)) fc None m (seg_rom asegs)).
  Proof.
    intros until q. intros QR MI. unfold AFC_R9, AFC_R10, P_strlen_icpt. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (Z.eqb_spec q 0) as [->|NZ].
    - step. if_lit. step. step. step. apply evt_done. reflexivity.
    - step. try br. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segN5 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LL L2 nn : Z) (ls rest : list byte) (c0 : byte),
      bytes_at asegs m LL (ls ++ rest) -> nth_error ls 0 = Some c0 -> 0 <= L2 < 2^32 -> 0 < LL -> LL + nn <= AAPP_HI -> accessible m LL nn -> 1 <= nn ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists (a2' : word),
         (L2 < 2 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 L2) (Z_to_bv 64 2) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_FAIL) fc None m (seg_rom asegs))
      \/ (2 <= L2 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R11) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (LL + (if bv_unsigned c0 =? 46 then 1 else 0))) (Z_to_bv 64 AA_DIGITS) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 (LL + (if bv_unsigned c0 =? 46 then 1 else 0))) (Z_to_bv 64 (L2 - (if bv_unsigned c0 =? 46 then 1 else 0))) s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_strspn) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 L2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) s3 s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R10)) fc None m (seg_rom asegs)).
  Proof.
    intros until c0. intros BS NTH LR LLP LLH ACCL NN1 MI. unfold AFC_R10, AFC_FAIL, AFC_R11, P_strspn, AA_DIGITS, ASHB, AAPP_HI in *. retpc. acb.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (abyte_range c0) as BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (nth_error_lt _ _ _ NTH) as NL. cbn [Z.to_nat] in NL.
    assert (NTH' : nth_error (ls ++ rest) (Z.to_nat 0) = Some c0) by (rewrite nth_error_app1 by exact NL; exact NTH).
    pose proof (u8ro_read asegs m LL (ls ++ rest) 0 c0 _ BS NTH' ltac:(lia) eq_refl) as RD.
    (* [comment removed for export] *)
    step. step. if_cases K0; zify_cond K0.
    { apply evt_done. eexists. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity]. }
    assert (L2R : 2 <= L2) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    assert (K : forall (v : Z) (a1v a2v : word),
      evt asegs (fun ms' => exists (a2' : word),
         (L2 < 2 /\
          ms' = MS (mkR (Z_to_bv 64 5582400) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 L2) (Z_to_bv 64 2) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x552c84) fc None m (seg_rom asegs))
      \/ (2 <= L2 /\
          ms' = MS (mkR (Z_to_bv 64 0x552e90) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (LL + (if bv_unsigned c0 =? 46 then 1 else 0))) (Z_to_bv 64 1123328) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 (LL + (if bv_unsigned c0 =? 46 then 1 else 0))) (Z_to_bv 64 (L2 - (if bv_unsigned c0 =? 46 then 1 else 0))) s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 1738512) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 5582400) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 v) a1v a2v a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L2) s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x552e60) fc None m (seg_rom asegs))).
    { intros v a1v a2v.
      (* [comment removed for export] *)
      go. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)).
      destruct (Z.eqb_spec (bv_unsigned c0) 46) as [E46|N46].
      + rewrite E46. if_lit. go. step.
        apply evt_done. eexists. right. split; [exact L2R| cbn [Z.eqb Pos.eqb]; reflexivity].
      + if_cases K1; zify_cond K1; [|exfalso; revert K1; rewrite ?unsigned_lit by lia; lia]. go. step.
        apply evt_done. eexists. right. split; [exact L2R|].
        replace (bv_unsigned c0 =? 46) with false by (symmetry; apply Z.eqb_neq; exact N46). rewrite ?Z.sub_0_r, ?Z.add_0_r. reflexivity. }
    cbv delta [mkR] in K.
    go. ck1_load ACCL LL v V1 V2 Hk.
    pose proof (K v) as Kv. step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev). exact (Kv _ a2).
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|]. go.
      replace (Z.land LL 7) with (Z.land (bv_unsigned (Z_to_bv 64 LL)) 7) by (rewrite unsigned_lit by lia; reflexivity).
      if_true_by (ck1_blt_true LL v Hk V1 VV). exact (Kv _ a2).
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segN6 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LL L3 n1 nn : Z) (ls rest : list byte) (c0 c1 : byte) (ee V : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      bytes_at asegs m LL (ls ++ rest) -> nth_error ls 0 = Some c0 -> (3 <= L3 -> nth_error ls 1 = Some c1) -> 0 <= L3 < 2^32 -> 0 <= n1 < 2^32 -> 0 < LL ->
      LL + nn <= AAPP_HI -> accessible m LL nn -> 1 <= nn -> (3 <= L3 -> 2 <= nn) ->
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee (Z_to_bv 64 V) f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 128 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' : word),
         (n1 = L3 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R11) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_FAIL) fc None m (seg_rom asegs))
      \/ (n1 <> L3 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R11) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_OK) fc None m (seg_rom asegs))
      \/ (n1 <> L3 /\ 3 <= L3 /\ bv_unsigned c0 = 48 /\ Z.lor (bv_unsigned c1) 32 = 120 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R12) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 (Z_to_bv 64 (LL + 2)) (Z_to_bv 64 AA_HEXDIGITS) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_strspn) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R11) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 (Z_to_bv 64 n1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 s5 (Z_to_bv 64 ASHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R11)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros BS NTH0 NTH1 LR NR LLP LLH ACCL NN1 NN2 FR SPL MI. unfold AFC_R11, AFC_FAIL, AFC_OK, AFC_R12, P_strspn, AA_HEXDIGITS, ASHB, AAPP_HI in *. retpc. acb.
    unfold afcc_frame, wz in FR. pose proof (aword_range sp) as SPR.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. pose proof (abyte_range c0) as BR0. pose proof (abyte_range c1) as BR1.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. if_cases K0; zify_cond K0.
    { apply evt_done. do 3 eexists. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity]. }
    assert (NE : n1 <> L3) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    pose proof (nth_error_lt _ _ _ NTH0) as NL0. cbn [Z.to_nat] in NL0.
    assert (NTH0' : nth_error (ls ++ rest) (Z.to_nat 0) = Some c0) by (rewrite nth_error_app1 by exact NL0; exact NTH0).
    pose proof (u8ro_read asegs m LL (ls ++ rest) 0 c0 _ BS NTH0' ltac:(lia) eq_refl) as RD0.
    (* [comment removed for export] *)
    assert (K : forall (v : Z) (a1v : word),
      evt asegs (fun ms' => exists (a0' a1' a2' : word),
         (n1 = L3 /\
          ms' = MS (mkR (Z_to_bv 64 5582480) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x552c84) fc None m (seg_rom asegs))
      \/ (n1 <> L3 /\
          ms' = MS (mkR (Z_to_bv 64 5582480) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x552f0c) fc None m (seg_rom asegs))
      \/ (n1 <> L3 /\ 3 <= L3 /\ bv_unsigned c0 = 48 /\ Z.lor (bv_unsigned c1) 32 = 120 /\
          ms' = MS (mkR (Z_to_bv 64 0x552f04) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 (Z_to_bv 64 (LL + 2)) (Z_to_bv 64 1123360) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 1738512) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 5582480) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 (Z_to_bv 64 v) a1v a2 a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x552ea8) fc None m (seg_rom asegs))).
    { intros v a1v.
      (* [comment removed for export] *)
      step. step. if_cases K0; zify_cond K0.
      { apply evt_done. do 3 eexists. right; left. split; [exact NE| reflexivity]. }
      assert (L3R : 3 <= L3) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      pose proof (NTH1 L3R) as NTH1v. pose proof (nth_error_lt _ _ _ NTH1v) as NL1. cbn [Z.to_nat] in NL1.
      assert (NTH1' : nth_error (ls ++ rest) (Z.to_nat 1) = Some c1) by (rewrite nth_error_app1 by exact NL1; exact NTH1v).
      pose proof (u8ro_read asegs m LL (ls ++ rest) 1 c1 _ BS NTH1' ltac:(lia) eq_refl) as RD1.
      (* [comment removed for export] *)
      step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). step. step. if_cases K0; zify_cond K0.
      { apply evt_done. do 3 eexists. right; left. split; [exact NE| reflexivity]. }
      assert (C0E : bv_unsigned c0 = 48) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      zstep.
      assert (K2 : forall (v2 : Z) (a2v : word),
        evt asegs (fun ms' => exists (a0' a1' a2' : word),
           (n1 = L3 /\
            ms' = MS (mkR (Z_to_bv 64 5582480) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x552c84) fc None m (seg_rom asegs))
        \/ (n1 <> L3 /\
            ms' = MS (mkR (Z_to_bv 64 5582480) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x552f0c) fc None m (seg_rom asegs))
        \/ (n1 <> L3 /\ 3 <= L3 /\ bv_unsigned c0 = 48 /\ Z.lor (bv_unsigned c1) 32 = 120 /\
            ms' = MS (mkR (Z_to_bv 64 0x552f04) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 (Z_to_bv 64 (LL + 2)) (Z_to_bv 64 1123360) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 1738512) fc None m (seg_rom asegs)))
          (MS (mkR (Z_to_bv 64 5582480) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s3 (Z_to_bv 64 (LL + 1)) (Z_to_bv 64 v2) a2v a3 a4 a5 a6 a7 (Z_to_bv 64 LL) (Z_to_bv 64 L3) s4 (Z_to_bv 64 V) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x552ed8) fc None m (seg_rom asegs))).
      { intros v2 a2v.
        (* [comment removed for export] *)
        step. change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)). step.
        pose proof (lor_lt_pow2 (bv_unsigned c1) 32 8 ltac:(lia) ltac:(lia)) as ORR.
        step. step. if_cases K0; zify_cond K0.
        { apply evt_done. do 3 eexists. right; left. split; [exact NE| reflexivity]. }
        assert (C1E : Z.lor (bv_unsigned c1) 32 = 120) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
        go. try br. go. step. apply evt_done. do 3 eexists. right; right. split; [exact NE|]. split; [exact L3R|]. split; [exact C0E|]. split; [exact C1E| reflexivity]. }
      cbv delta [mkR] in K2.
      go. try br. go. ck1_load ACCL (LL + 1) v2 W1 W2 Hk2.
      pose proof (K2 v2) as K2v. step. destruct (Z.eq_dec v2 0) as [Ev2|Nv2].
      - if_false_by (ck1_bnez_false v2 Ev2). exact (K2v _).
      - if_true_by (ck1_bnez_true v2 W1 Nv2). destruct W2 as [VV2|VV2]; [exfalso; exact (Nv2 VV2)|]. go.
        replace (Z.land (LL + 1) 7) with (Z.land (bv_unsigned (Z_to_bv 64 (LL + 1))) 7) by (rewrite unsigned_lit by lia; reflexivity).
        if_true_by (ck1_blt_true (LL + 1) v2 Hk2 W1 VV2). exact (K2v _). }
    cbv delta [mkR] in K.
    go. ck1_load ACCL LL v V1 V2 Hk.
    pose proof (K v) as Kv. step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev). exact (Kv _).
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|]. go.
      replace (Z.land LL 7) with (Z.land (bv_unsigned (Z_to_bv 64 LL)) 7) by (rewrite unsigned_lit by lia; reflexivity).
      if_true_by (ck1_blt_true LL v Hk V1 VV). exact (Kv _).
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segN7 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L3 n2 : Z) (ee V : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      3 <= L3 < 2^32 -> 0 <= n2 < 2^32 ->
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee (Z_to_bv 64 V) f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 128 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
         (n2 = L3 - 2 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (L3 - 2)) (Z_to_bv 64 0) (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs))
      \/ (n2 <> L3 - 2 /\
          ms' = MS (mkR (Z_to_bv 64 AFC_R12) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 n2) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (L3 - 2)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFC_OK) fc None m (seg_rom asegs)))
        (MS (mkR (Z_to_bv 64 AFC_R12) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 n2) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R12)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros LR NR FR SPL MI. unfold AFC_R12, AFC_R4, P_X509_VERIFY_PARAM_free, AFC_OK. retpc.
    unfold afcc_frame, wz in FR. pose proof (aword_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. rewrite ?unsigned_lit by lia. replace (L3 + -2) with (L3 - 2) by lia. if_cases K0; zify_cond K0.
    - go. step. apply evt_done. left. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
    - apply evt_done. right. split; [revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition afcc_glue_stmt (raA raB target a0v a1v a2v : Z) : Prop :=
    forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv asegs m1 ->
      evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom asegs)).
  Lemma afcc_glue275 : afcc_glue_stmt AFC_RA1 AFC_RA2 P_ERR_set_debug AA_ECHS_FILE 275 AA_FCC_FUNC.
  Proof.
    unfold afcc_glue_stmt. intros until m1. intros MI. unfold AFC_RA1, AFC_RA2, P_ERR_set_debug, AA_ECHS_FILE, AA_FCC_FUNC. retpc.
    do 7 step. finish.
  Qed.
  Lemma afcc_glue284 : afcc_glue_stmt AFC_RA4 AFC_RA2 P_ERR_set_debug AA_ECHS_FILE 284 AA_FCC_FUNC.
  Proof.
    unfold afcc_glue_stmt. intros until m1. intros MI. unfold AFC_RA4, AFC_RA2, P_ERR_set_debug, AA_ECHS_FILE, AA_FCC_FUNC. retpc.
    do 8 step. finish.
  Qed.
  Lemma afcc_glue258 : afcc_glue_stmt AFC_RB1 AFC_RB2 P_ERR_set_debug AA_ECHS_FILE 258 AA_FCC_FUNC.
  Proof.
    unfold afcc_glue_stmt. intros until m1. intros MI. unfold AFC_RB1, AFC_RB2, P_ERR_set_debug, AA_ECHS_FILE, AA_FCC_FUNC. retpc.
    do 7 step. finish.
  Qed.
  Lemma afcc_glue2 : afcc_glue_stmt AFC_RA2 AFC_RA3 P_ERR_set_error ERR_LIB_SSL R_PASSED_INVALID_ARGUMENT 0.
  Proof.
    unfold afcc_glue_stmt. intros until m1. intros MI. unfold AFC_RA2, AFC_RA3, P_ERR_set_error, ERR_LIB_SSL, R_PASSED_INVALID_ARGUMENT. retpc.
    do 6 step. finish.
  Qed.
  Lemma afcc_glue2b : afcc_glue_stmt AFC_RB2 AFC_FAIL P_ERR_set_error ERR_LIB_SSL R_INTERNAL_ERROR 0.
  Proof.
    unfold afcc_glue_stmt. intros until m1. intros MI. unfold AFC_RB2, AFC_FAIL, P_ERR_set_error, ERR_LIB_SSL, R_INTERNAL_ERROR. retpc.
    do 6 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segRA3 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (ee V : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee (Z_to_bv 64 V) f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 128 <= bv_unsigned sp -> 0 <= V < 2^64 ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFC_RA3) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_RA3)) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros FR SPL VR MI. unfold AFC_RA3, AFC_R4, P_X509_VERIFY_PARAM_free. unfold afcc_frame, wz in FR. retpc.
    pose proof (aword_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. replace (bv_unsigned sp - 112) with (bv_unsigned sp + -128 + 16) by lia. step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segF :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (V : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFC_FAIL) fc None m (seg_rom asegs)).
  Proof.
    intros until V. intros MI. unfold AFC_FAIL, AFC_R4, P_X509_VERIFY_PARAM_free.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. step. apply evt_done. reflexivity.
  Qed.
  Lemma afcc_segFr :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (V : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFC_FAIL) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_FAIL)) fc None m (seg_rom asegs)).
  Proof. intros until V. intros MI. unfold AFC_FAIL at 2. retpc. apply afcc_segF. exact MI. Qed.

  (* [comment removed for export] *)
  Lemma afcc_segT :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (V : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFC_TAIL) fc None m (seg_rom asegs)).
  Proof.
    intros until V. intros MI. unfold AFC_TAIL, AFC_R4, P_X509_VERIFY_PARAM_free.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segOK :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (V : Z) (ee : Z) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee (Z_to_bv 64 V) f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) -> 128 <= bv_unsigned sp ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 V) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFC_OK) fc None m (seg_rom asegs)).
  Proof.
    intros until fra. intros FR SPL MI. unfold AFC_OK, AFC_R4, P_X509_VERIFY_PARAM_free. unfold afcc_frame, wz in FR. pose proof (aword_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afcc_segE :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (ee : Z) (vpm x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells asegs m (bv_unsigned sp + -128) (afcc_frame ee vpm x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 ra) ->
      stk asegs m lo (bv_unsigned sp + -128) -> aceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 x0 x1 s4 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 AFC_R4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFC_R4)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI. unfold AFC_R4. unfold afcc_frame in FR. retpc. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.
