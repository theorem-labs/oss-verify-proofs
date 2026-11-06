(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame SFModel.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_C1_stmt ECH_C4_stmt ECH_C5_stmt ECH_C10_stmt ECH_C13_stmt ECH_C14_stmt ECH_KitSeg ECH_UbKit F_memchr F_memcpy ECH_C14_decexts_seg ECH_C14_decK.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition upd_version (E : entrep) (v : Z) : entrep :=
  mkENT v (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_cfgid (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) v (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_nsuites (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) v (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_suites (E : entrep) (v : Z) (o : oblk) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) v o
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_maxname (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        v (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_enclen (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) v (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_encoded (E : entrep) (v : Z) (o : oblk) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) v o (en_id E).
Lemma upd_version_id : forall E, upd_version E (en_version E) = E.
Proof. intros E. destruct E. reflexivity. Qed.
Lemma upd_cfgid_id : forall E, upd_cfgid E (en_cfgid E) = E.
Proof. intros E. destruct E. reflexivity. Qed.
Lemma upd_nsuites_id : forall E, upd_nsuites E (en_nsuites E) = E.
Proof. intros E. destruct E. reflexivity. Qed.
(* [comment removed for export] *)
Definition bz (bs : list byte) (j : nat) : Z := match nth_error bs j with Some b => bv_unsigned b | None => 0 end.
Fixpoint srows (bs : list byte) (off : nat) (kem : Z) (n : nat) : list (Z * Z * Z) :=
  match n with
  | O => []
  | S n' => (kem, 256 * bz bs off + bz bs (S off), 256 * bz bs (S (S off)) + bz bs (S (S (S off)))) :: srows bs (4 + off) kem n'
  end.
Lemma srows_length : forall bs off kem n, length (srows bs off kem n) = n.
Proof. intros bs off kem n. revert off. induction n as [|n IH]; intros off; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma bz_range : forall bs j, 0 <= bz bs j < 256.
Proof. intros bs j. unfold bz. destruct (nth_error bs j) as [b|]; [apply byte_range| lia]. Qed.
Lemma srows_ok : forall bs off kem n, 0 <= kem < 2^16 -> Forall row_ok (srows bs off kem n).
Proof.
  intros bs off kem n KR. revert off. induction n as [|n IH]; intros off; cbn; constructor; [| apply IH].
  unfold row_ok. cbn [fst snd]. pose proof (bz_range bs off). pose proof (bz_range bs (S off)). pose proof (bz_range bs (S (S off))). pose proof (bz_range bs (S (S (S off)))). lia.
Qed.
Lemma wrap_neg : forall x, - 2^64 <= x < 0 -> bv_unsigned (Z_to_bv 64 x) = x + 2^64.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma mod64_neg : forall x, - 2^64 <= x < 0 -> x mod 2^64 = x + 2^64.
Proof. intros x Hx. rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma upd_maxname_id : forall E, upd_maxname E (en_maxname E) = E.
Proof. intros E. destruct E. reflexivity. Qed.
(* [comment removed for export] *)
Lemma add_not64 : forall r x, 0 <= x < 2^64 -> Z_to_bv 64 (r + Z.lxor x 18446744073709551615) = Z_to_bv 64 (r - x - 1).
Proof.
  intros r x Hx. rewrite lnot_mod64 by lia. unfold Z.lnot, Z.pred. apply Z_to_bv_eqm.
  rewrite Z.add_mod, Z.mod_mod, <- Z.add_mod by lia. f_equal. lia.
Qed.
Lemma upd_enclen_cells : forall E v pad1 pad2 pad3 pad4, entry_cells (upd_enclen E v) pad1 pad2 pad3 pad4 = entry_cells (upd_enclen E v) pad1 pad2 pad3 pad4.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma memchr_ok_all_u : forall A1 c n buf, Z.of_nat (length buf) = n -> memchr_ok A1 c n buf.
Proof. intros A1 c n buf L. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat n) buf)); lia. Qed.

(* [comment removed for export] *)
Lemma bytes_at_sub_u : forall m A zs i n,
  bytes_at usegs m A zs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length zs) ->
  bytes_at usegs m (A + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs))) = n.
Proof.
  intros m A zs i n BS I0 N0 LE.
  rewrite <- (firstn_skipn (Z.to_nat i) zs) in BS. apply bytes_at_app in BS. destruct BS as [_ BS].
  rewrite firstn_length_le in BS by lia. rewrite Z2Nat.id in BS by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) zs)) in BS. apply bytes_at_app in BS. destruct BS as [BS _].
  split; [exact BS|]. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
Qed.

(* [comment removed for export] *)
Lemma zbv_mod : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). exact E. Qed.
Lemma mod16_lo : forall z, (z mod 65536) mod 256 = z mod 256.
Proof. intros z. change 65536 with (256 * 256). rewrite Z.rem_mul_r, (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity. Qed.
Lemma mod16_hi : forall z, (z mod 65536) / 256 = (z / 256) mod 256.
Proof. intros z. change 65536 with (256 * 256). rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.div_add by lia. rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia. Qed.
(* [comment removed for export] *)
Lemma le2_mod16 : forall z1 z2, 0 <= z1 < 2^64 -> 0 <= z2 < 2^64 -> z1 mod 65536 = z2 mod 65536 -> le2 (Z_to_bv 64 z1) = le2 (Z_to_bv 64 z2).
Proof.
  intros z1 z2 P1 P2 E. unfold le2. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite !(Z.mod_small _ (2^64)) by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  f_equal; [| f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256.
  - rewrite <- (mod16_lo z1), <- (mod16_lo z2), E. reflexivity.
  - rewrite <- (mod16_hi z1), <- (mod16_hi z2), E. reflexivity.
Qed.
Lemma lor_add_disjoint_u : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
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
Lemma ub_byte1 : forall w, 0 <= w -> bv_unsigned (Z_to_bv 64 (Z.shiftl w 48)) / 2^56 = (w mod 65536) / 256.
Proof.
  intros w Hw. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (65536 * 2^48). rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mul_mod_distr_r by lia. change (2^56) with (256 * 2^48). rewrite Z.div_mul_cancel_r by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma ub_kdf : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  let w := b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24) in
  (w * 2^8 + (w mod 65536) / 256) mod 65536 = (256 * b0 + b1) mod 65536 /\ ((w / 2^16) * 2^8 + b3) mod 65536 = (256 * b2 + b3) mod 65536
  /\ 0 <= w < 2^32 /\ (w mod 65536) / 256 = b1 /\ w / 2^16 = b2 + 256 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3 w.
  assert (M : w mod 65536 = b0 + b1 * 256) by (subst w; replace (b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24)) with ((b0 + b1 * 256) + (b2 + 256 * b3) * 65536) by lia; rewrite Z.mod_add by lia; apply Z.mod_small; lia).
  assert (B1 : (w mod 65536) / 256 = b1) by (rewrite M; replace (b0 + b1 * 256) with (b0 + b1 * 256) by lia; rewrite Z.div_add by lia; rewrite Z.div_small by lia; lia).
  assert (D : w / 2^16 = b2 + 256 * b3) by (subst w; replace (b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24)) with ((b0 + b1 * 256) + (b2 + 256 * b3) * 2^16) by lia; rewrite Z.div_add by lia; rewrite Z.div_small by lia; lia).
  rewrite B1, D. split; [| split; [| split; [subst w; lia| split; reflexivity]]].
  - subst w. replace ((b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24)) * 2^8 + b1) with ((256 * b0 + b1) + (b1 + b2 * 256 + b3 * 65536) * 65536) by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace ((b2 + 256 * b3) * 2^8 + b3) with ((256 * b2 + b3) + b3 * 65536) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac s0slot := match goal with |- context [bv_unsigned ?sp - 4096] => replace (bv_unsigned sp - 4096) with (bv_unsigned sp + -2368 + -1728) by lia end.
  Local Ltac retpc0 := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Lemma up_get2_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P Q Bb cur ms rem lo : Z) (bs : list byte) (q0 q1 q2 : word),
      rw_cells usegs m P (pk_cells cur ms rem) -> rw_cells usegs m Q [C8 q0; C8 q1; C8 q2] -> P mod 8 = 0 -> Q mod 8 = 0 -> apart P 24 Q 24 ->
      bv_unsigned sp <= P -> bv_unsigned sp <= Q ->
      bytes_at usegs m Bb bs -> Bb <= cur -> 0 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil -> 0 <= ms < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned ra mod 2 = 0 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m' rv,
          munch [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
          /\ ( (rv = 0 /\ rw_cells usegs m' P (pk_cells cur ms rem) /\ rw_cells usegs m' Q [C8 q0; C8 q1; C8 q2])
             \/ (rv = 1 /\ exists len hi lb, 0 <= hi < 256 /\ 0 <= lb < 256 /\ len = lb + 256 * hi /\ 2 + len <= rem /\
                  nth_error bs (Z.to_nat (cur - Bb + 0)) = Some (Z_to_bv 8 hi) /\ nth_error bs (Z.to_nat (cur - Bb + 1)) = Some (Z_to_bv 8 lb) /\
                  rw_cells usegs m' P (pk_cells (cur + 2 + len) ms (rem - 2 - len)) /\ rw_cells usegs m' Q (pk_cells (cur + 2) ms len)) )
          /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) (Z_to_bv 64 Q) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 Q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UP_get2) fc None m (seg_rom usegs)).
  Proof.
    intros until q2. intros PK QC ALP ALQ APQ SPP SPQ BS BC R0 CR BP BH MSR ST CEIL LO RAE MI.
    unfold UP_get2, pk_cells, apart, wz in *. hcb. pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. pose proof (rw_cells_bound _ _ _ _ QC) as QB. cbn [cells_size csize Nat.add] in PB, QB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    step. st1. st1. step. step. step. step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (R2 : rem < 2) by (revert K0; rewrite ?unsigned_lit by lia; clear - R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
      step. step. step. step. step. step.
      apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 0.
      lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ left; split; [reflexivity| split; assumption] | reflexivity].
    - assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; clear - R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
      step. step. ub_dead. step. step. ub_dead. step. step. ub_dead.
      destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
      destruct (nth_error bs (Z.to_nat (cur - Bb + 1))) as [c1|] eqn:N1; [| apply nth_error_None in N1; lia].
      pose proof (pk_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (byte_range c0) as C0R.
      pose proof (pk_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1. pose proof (byte_range c1) as C1R.
      step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). step. change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)).
      step. step.
      rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c0)) by lia. rewrite (unsigned_lit (bv_unsigned c0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c1)) by lia.
      replace (Z.lor (bv_unsigned c0 * 2 ^ 8) (bv_unsigned c1)) with (bv_unsigned c1 + 256 * bv_unsigned c0)
        by (rewrite Z.lor_comm; replace (bv_unsigned c0 * 2 ^ 8) with (Z.shiftl (bv_unsigned c0) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned c1) (bv_unsigned c0)) by lia; lia).
      set (len := bv_unsigned c1 + 256 * bv_unsigned c0) in *. assert (LR : 0 <= len < 2^16) by (subst len; lia).
      step. step. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        assert (EN : 2 + len <= rem) by (revert K0; rewrite ?unsigned_lit by lia; clear - R2 LR R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
        step. step. ubnot. step. ub_dead. step. step. step. step. ubal_by ALQ. st1. st1. step. if_lit. step. ubal_by ALP. st1. step. if_lit. st1. st1. step.
        step. step. step. step.
        apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 1.
        lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
        repeat match goal with |- _ /\ _ => split end; try eassumption; [ | reflexivity].
        * right. split; [reflexivity|]. exists len, (bv_unsigned c0), (bv_unsigned c1).
          repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear - C0R C1R EN; subst len; lia).
          all: try (f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned).
          all: try (replace (rem + -2 - len) with (rem - 2 - len) by lia; assumption).
      + assert (EN : rem < 2 + len) by (revert K0; rewrite ?unsigned_lit by lia; clear - R2 LR R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
        step. step. step. step. step. step.
        apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 0.
        lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
        repeat match goal with |- _ /\ _ => split end; try eassumption; [ left; split; [reflexivity| split; assumption] | reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma up_get1_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P Q Bb cur ms rem lo : Z) (bs : list byte) (q0 q1 q2 : word),
      rw_cells usegs m P (pk_cells cur ms rem) -> rw_cells usegs m Q [C8 q0; C8 q1; C8 q2] -> P mod 8 = 0 -> Q mod 8 = 0 -> apart P 24 Q 24 ->
      bv_unsigned sp <= P -> bv_unsigned sp <= Q ->
      bytes_at usegs m Bb bs -> Bb <= cur -> 0 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil -> 0 <= ms < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned ra mod 2 = 0 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m' rv,
          munch [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
          /\ ( (rv = 0 /\ rw_cells usegs m' P (pk_cells cur ms rem) /\ rw_cells usegs m' Q [C8 q0; C8 q1; C8 q2])
             \/ (rv = 1 /\ exists len, 0 <= len < 256 /\ 1 + len <= rem /\ nth_error bs (Z.to_nat (cur - Bb + 0)) = Some (Z_to_bv 8 len) /\
                  rw_cells usegs m' P (pk_cells (cur + 1 + len) ms (rem - 1 - len)) /\ rw_cells usegs m' Q (pk_cells (cur + 1) ms len)) )
          /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) (Z_to_bv 64 Q) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 Q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UP_get1) fc None m (seg_rom usegs)).
  Proof.
    intros until q2. intros PK QC ALP ALQ APQ SPP SPQ BS BC R0 CR BP BH MSR ST CEIL LO RAE MI.
    unfold UP_get1, pk_cells, apart, wz in *. hcb. pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. pose proof (rw_cells_bound _ _ _ _ QC) as QB. cbn [cells_size csize Nat.add] in PB, QB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    step. st1. st1. step. step. step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (R2 : rem = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
      step. step. step. step. step. step.
      apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 0.
      lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ left; split; [reflexivity| split; assumption] | reflexivity].
    - assert (R2 : 1 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; clear - R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
      step. step. ub_dead. step. step. ub_dead.
      destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
      pose proof (pk_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (byte_range c0) as C0R.
      step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)).
      step. step. if_cases K0; zify_cond K0.
      + assert (EN : 1 + bv_unsigned c0 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; clear - R2 C0R R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
        step. step. ubnot. step. ub_dead. step. step. step. step. ubal_by ALQ. st1. st1. step. if_lit. step. ubal_by ALP. st1. step. if_lit. st1. st1. step.
        step. step. step. step.
        apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 1.
        lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
        repeat match goal with |- _ /\ _ => split end; try eassumption; [ | reflexivity].
        right. split; [reflexivity|]. exists (bv_unsigned c0).
        repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear - C0R EN; lia).
        all: try (f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned).
        all: try (replace (rem + -1 - bv_unsigned c0) with (rem - 1 - bv_unsigned c0) by lia; assumption).
      + assert (EN : rem < 1 + bv_unsigned c0) by (revert K0; rewrite ?unsigned_lit by lia; clear - R2 C0R R0 CR BB BC BH HCEILB; intros K0; lia). clear K0.
        step. step. step. step. step. step.
        apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 0.
        lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
        repeat match goal with |- _ /\ _ => split end; try eassumption; [ left; split; [reflexivity| split; assumption] | reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma up_has0_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P cur ms rem lo : Z) (buf : list byte),
      rw_cells usegs m P (pk_cells cur ms rem) -> P mod 8 = 0 -> bv_unsigned sp <= P ->
      bytes_at usegs m cur buf -> zlength buf = rem -> 0 < cur -> cur + rem <= hceil ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned ra mod 2 = 0 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
          munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
          /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if find_byte 0 buf then 1 else 0)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UP_has0) fc None m (seg_rom usegs)).
  Proof.
    intros until buf. intros PK ALP SPP BS BL CP CH ST CEIL LO RAE MI.
    unfold UP_has0, pk_cells, wz in *. hcb. pose proof (word_range sp) as SPR. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. cbn [cells_size csize Nat.add] in PB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    step. ubal_by ALP. step. if_lit. step. st1. st1. step. step. step. step. step. step.
    eapply evt_cut; [eapply memchr_spec with (buf := buf); [rewrite unsigned_lit by lia; eassumption| apply memchr_ok_all_u; rewrite unsigned_lit by lia; exact BL| eassumption]|].
    cbv beta. intros ms1 (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & mh & -> & MUh & WMh & MIh & _).
    rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit rem) by lia. rewrite (unsigned_lit cur) by lia. change (0 mod 256) with 0.
    lazymatch goal with FRx : rw_cells usegs _ (bv_unsigned sp + -16) _ |- _ =>
      apply (rw_cells_transport usegs _ _ mh _ _ FRx) in MUh as FRh; [| exact WMh| cbn; exact I] end.
    lazymatch goal with STx : stk usegs _ lo _ |- _ => pose proof MUh as MUh'; apply (stk_transport_disjoint usegs _ _ mh _ _ STx) in MUh' as STh; [| exact WMh| cbn; exact I] end.
    assert (MU2 : munch [(bv_unsigned sp + -16, bv_unsigned sp)] m mh) by (eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUh]]; intros x Hx; cbn in Hx |- *; first [lia| destruct Hx]).
    pose proof (wmono_trans usegs _ _ _ WM WMh) as WM2.
    clear MU WM MUh WMh MUh'. rename MU2 into MU. rename WM2 into WM.
    retpc0.
    step.
    rewrite v_sltu_b2z. rewrite (unsigned_lit 0) by lia.
    replace (Z_to_bv 64 (Z.b2z (0 <? bv_unsigned (Z_to_bv 64 (memchr_res cur 0 rem buf))))) with (Z_to_bv 64 (if find_byte 0 buf then 1 else 0)).
    2:{ unfold memchr_res. rewrite <- BL, Nat2Z.id, firstn_all. destruct (find_byte 0 buf) as [i|] eqn:FB.
        - pose proof (find_byte_Some _ _ _ FB) as (Hi & _). rewrite unsigned_lit by (clear - Hi CP CH HCEILB BL; lia). destruct (Z.ltb_spec 0 (cur + Z.of_nat i)); [reflexivity| exfalso; clear - H CP; lia].
        - rewrite unsigned_lit by lia. reflexivity. }
    step. step. step. step.
    apply evt_done. do 14 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end.
    lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx STh (bv_unsigned sp) end.
    repeat match goal with |- _ /\ _ => split end; try eassumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma up_copy_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P D n Bb cur ms rem lo : Z) (bs junk : list byte),
      rw_cells usegs m P (pk_cells cur ms rem) -> P mod 8 = 0 -> bv_unsigned sp <= P ->
      rw_cells usegs m D [CB (Z.to_nat n) junk] -> bv_unsigned sp <= D -> apart P 24 D n -> 1 <= n ->
      bytes_at usegs m Bb bs -> Bb <= cur -> 0 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned ra mod 2 = 0 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' rv,
          munch [(bv_unsigned sp + -32, bv_unsigned sp); (P, P + 24); (D, D + n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
          /\ ( (rv = 0 /\ rem < n /\ rw_cells usegs m' P (pk_cells cur ms rem) /\ rw_cells usegs m' D [CB (Z.to_nat n) junk])
             \/ (rv = 1 /\ n <= rem /\ rw_cells usegs m' P (pk_cells (cur + n) ms (rem - n)) /\ rw_cells usegs m' D [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat (cur - Bb)) bs))]) )
          /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UP_copy) fc None m (seg_rom usegs)).
  Proof.
    intros until junk. intros PK ALP SPP DC SPD APD N1 BS BC R0 CR BP BH ST CEIL LO RAE MI.
    unfold UP_copy, pk_cells, apart, wz in *. hcb. pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. pose proof (rw_cells_bound _ _ _ _ DC) as DB. cbn [cells_size csize Nat.add] in PB, DB. rewrite Nat.add_0_r, Z2Nat.id in DB by lia.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (P, P + 24); (D, D + n)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    step. st1. st1. st1. st1. step. step. step. ubal_by ALP. step. if_lit. step. step. step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (EN : n <= rem) by (revert K0; rewrite ?unsigned_lit by lia; clear - N1 R0 CR BB BC BH HCEILB DB SPD; intros K0; lia). clear K0.
      step. step. step. step. step.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => match goal with BSx : bytes_at usegs mx Bb bs |- _ =>
        destruct (bytes_at_sub_u mx Bb bs (cur - Bb) n BSx ltac:(clear - BC; lia) ltac:(clear - N1; lia) ltac:(clear - BC CR EN; lia)) as [BSX XBL] end end.
      replace (Bb + (cur - Bb)) with cur in BSX by lia.
      eapply evt_cut; [eapply memcpy_spec with (junk := junk); [rewrite unsigned_lit by lia; exact BSX| rewrite unsigned_lit by lia; apply Nat2Z.inj; rewrite XBL, Z2Nat.id by lia; reflexivity
                                                            | rewrite !unsigned_lit by lia; eassumption| rewrite !unsigned_lit by lia; clear - SPD CR BH BC EN HCEILB LO CEIL DB; lia| eassumption]|].
      cbv beta. intros ms1 (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & mh & -> & MUh & WMh & MIh & DSTh & SRCh).
      rewrite (unsigned_lit D) in MUh, DSTh by lia. rewrite (unsigned_lit n) in MUh, DSTh by lia. rewrite (unsigned_lit cur) in SRCh by lia.
      lazymatch goal with FRx : rw_cells usegs _ (bv_unsigned sp + -32) _ |- _ => apply (rw_cells_transport usegs _ _ mh _ _ FRx) in MUh as FRh; [| exact WMh| cbn; clear - SPD; lia] end.
      lazymatch goal with STx : stk usegs _ lo _ |- _ => pose proof MUh as MUh'; apply (stk_transport_disjoint usegs _ _ mh _ _ STx) in MUh' as STh; [| exact WMh| cbn; clear - SPD; lia] end.
      lazymatch goal with PKx : rw_cells usegs _ P _ |- _ => pose proof MUh as MUh''; apply (rw_cells_transport usegs _ _ mh _ _ PKx) in MUh'' as PKh; [| exact WMh| cbn; clear - APD; lia] end.
      assert (MU2 : munch [(bv_unsigned sp + -32, bv_unsigned sp); (P, P + 24); (D, D + n)] m mh) by (eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUh]]; intros x Hx; cbn in Hx |- *; first [lia| destruct Hx]).
      pose proof (wmono_trans usegs _ _ _ WM WMh) as WM2.
      clear MU WM MUh WMh MUh' MUh''. rename MU2 into MU. rename WM2 into WM.
      retpc0.
      step. step. step. ub_dead. step. ub_dead. step. ub_dead. step. step. st1. st1. step.
      step. step. step. step. step. step.
      apply evt_done. do 14 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 1.
      lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -32) _ |- _ => release_frame FRx STh (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ | reflexivity].
      right. split; [reflexivity|]. split; [exact EN|]. replace (cur + n) with (n + cur) by lia. replace (rem - n) with (rem + - n) by lia.
      split; assumption.
    - assert (EN : rem < n) by (revert K0; rewrite ?unsigned_lit by lia; clear - N1 R0 CR BB BC BH HCEILB DB SPD; intros K0; lia). clear K0.
      step. step. step. step. step. step. step. step.
      apply evt_done. do 14 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists 0.
      lazymatch goal with FRx : rw_cells usegs ?mx (bv_unsigned sp + -32) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ left; split; [reflexivity| split; [exact EN| split; assumption]] | reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.


  (* [comment removed for export] *)
  Lemma ude_seg1 :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (w0 w1 w2 w3 w4 w6 w7 w8 : word) pad mxb (x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      rw_cells usegs m (bv_unsigned sp + -2368) (UFRM w0 w1 w2 w3 w4 (Z_to_bv 64 UA_ECHS_FILE) w6 w7 w8) ->
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1) ->
      2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          munch [(bv_unsigned sp + -120, bv_unsigned sp + -112)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 (Z_to_bv 64 0) tp1)
          /\ ms' = MS (mkR (Z_to_bv 64 UDE_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 104) (Z_to_bv 64 UA_ECHS_FILE) (Z_to_bv 64 360) a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UDF_LOOP) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros FR F3 SPL MI. unfold UDF_LOOP, UDE_R1, P_CRYPTO_zalloc, UA_ECHS_FILE in *. unfold UFRM in FR. unfold UF3 in F3 |- *.
    pose proof (word_range sp) as SPR.
    pose proof (munch_refl [(bv_unsigned sp + -120, bv_unsigned sp + -112)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. step. step. step. step. s0slot. step. step. step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. reflexivity.
  Qed.


  (* [comment removed for export] *)
  Lemma ude_seg2 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur rem ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w6 w7 w8 : word) pad mxb (x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      rw_cells usegs m (bv_unsigned sp + -2368) (UFRM w0 w1 w2 w3 (Z_to_bv 64 UECH_VERSION) (Z_to_bv 64 UA_ECHS_FILE) w6 w7 w8) ->
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1) ->
      bytes_at usegs m Bb bs -> Bb <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil ->
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> ee mod 8 = 0 -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a0' a1' a2' a3' a4' s3' s5' s8' s9' : word) m1 (w2' c0' c1' c2' : word) v,
          munch [(bv_unsigned sp + -2352, bv_unsigned sp + -2344); (ee, ee + 2); (bv_unsigned sp + -144, bv_unsigned sp + -120)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 (bv_unsigned sp + -2368) (UFRM w0 w1 w2' w3 (Z_to_bv 64 UECH_VERSION) (Z_to_bv 64 UA_ECHS_FILE) w6 w7 w8)
          /\ rw_cells usegs m1 (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0' c1' c2' tp0 tp1)
          /\ rw_cells usegs m1 ee (entry_cells (upd_version E v) pad1 pad2 pad3 pad4) /\ (v = en_version E \/ 0 <= v < 2^16) /\
         (  (exists line, (line = 367 \/ line = 374 \/ line = 400) /\
             ms' = MS (mkR (Z_to_bv 64 UDE_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3' a4' a5 a6 a7
                           s2 s3' s4 s5' (Z_to_bv 64 Bb) (Z_to_bv 64 ee) s8' s9' (Z_to_bv 64 cur) (Z_to_bv 64 line) t3 t4 t5 t6)
                      F (Z_to_bv 64 UDF_TA) fc None m1 (seg_rom usegs))
         \/ (exists elen, 0 <= elen /\ 4 + elen <= rem /\ c0' = Z_to_bv 64 (cur + 4) /\ c1' = Z_to_bv 64 Bb /\ c2' = Z_to_bv 64 elen /\
             (  (v <> UECH_VERSION /\ w2' = w2 /\
                 ms' = MS (mkR (Z_to_bv 64 UDE_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 v) (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 UECH_VERSION) (Z_to_bv 64 2) (Z_to_bv 64 2) a5 a6 a7
                               s2 (Z_to_bv 64 (cur + 4 + elen)) s4 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 Bb) (Z_to_bv 64 ee) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) (Z_to_bv 64 cur) (Z_to_bv 64 374) t3 t4 t5 t6)
                          F (Z_to_bv 64 UDE_SKIP) fc None m1 (seg_rom usegs))
             \/ (v = UECH_VERSION /\ 1 <= elen /\ w2' = Z_to_bv 64 (cur + 4 + elen) /\
                 ms' = MS (mkR (Z_to_bv 64 UDE_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp - 4096)) (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 UECH_VERSION) (Z_to_bv 64 2) (Z_to_bv 64 2) a5 a6 a7
                               s2 (Z_to_bv 64 (cur + 4 + elen)) s4 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 Bb) (Z_to_bv 64 ee) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
                          F (Z_to_bv 64 UDE_J1) fc None m1 (seg_rom usegs))))))
        (MS (mkR (Z_to_bv 64 UDE_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 Bb) s7 (Z_to_bv 64 rem) s9 (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R1)) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros FR F3 BS BC R1 CR BP BH EC EEP EEH ALE EBA HSP MI.
    unfold UDE_R1, UDE_SKIP, UDE_J1, UDF_TA, UDF_TZ, UDE_A367 in *. unfold UFRM in FR |- *. unfold UF3 in F3 |- *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA. retpc0.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2368 <= bv_unsigned sp) by lia. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (munch_refl [(bv_unsigned sp + -2352, bv_unsigned sp + -2344); (ee, ee + 2); (bv_unsigned sp + -144, bv_unsigned sp + -120)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. br. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R1' : rem = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step.
      apply evt_done. do 9 eexists. exists m, w2, c0, c1, c2, (en_version E).
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_version_id; exact EC).
      - left. reflexivity.
      - left. exists 367. split; [left; reflexivity| reflexivity]. }
    assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    step. step. ub_dead. step. step. ub_dead. step. ubal_by ALE. step. if_lit.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [b0|] eqn:N0; [| apply nth_error_None in N0; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 1))) as [b1|] eqn:N1; [| apply nth_error_None in N1; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (pk_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
    pose proof (byte_range b0) as C0R. pose proof (byte_range b1) as C1R.
    step. change (zxb b0) with (Z_to_bv 64 (bv_unsigned b0)). step. change (zxb b1) with (Z_to_bv 64 (bv_unsigned b1)).
    step. step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned b0)) by lia. rewrite (unsigned_lit (bv_unsigned b0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned b1)) by lia.
    replace (Z.lor (bv_unsigned b0 * 2 ^ 8) (bv_unsigned b1)) with (bv_unsigned b1 + 256 * bv_unsigned b0)
      by (rewrite Z.lor_comm; replace (bv_unsigned b0 * 2 ^ 8) with (Z.shiftl (bv_unsigned b0) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned b1) (bv_unsigned b0)) by lia; lia).
    set (v := bv_unsigned b1 + 256 * bv_unsigned b0) in *. assert (VR : 0 <= v < 2^16) by (subst v; lia).
    st1. step. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R23 : rem <= 3) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_even_mask, land_W64, land_1, Z.mod_small by lia; clear - R2; intros K0; lia). clear K0.
      apply evt_done. do 9 eexists. exists m0, w2, c0, c1, c2, v.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - right. exact VR.
      - left. exists 374. split; [right; left; reflexivity| reflexivity]. }
    assert (R4 : 4 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_even_mask, land_W64, land_1, Z.mod_small by lia; clear - R2; intros K0; lia). clear K0.
    step. step. step. step. ub_dead. step. step. ub_dead.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 2))) as [b2|] eqn:N2; [| apply nth_error_None in N2; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 3))) as [b3|] eqn:N3; [| apply nth_error_None in N3; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N2 ltac:(lia) ltac:(lia)) as RD2. pose proof (pk_byte _ _ _ _ _ _ BS N3 ltac:(lia) ltac:(lia)) as RD3.
    pose proof (byte_range b2) as C2R. pose proof (byte_range b3) as C3R.
    step. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)). step. change (zxb b3) with (Z_to_bv 64 (bv_unsigned b3)).
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned b2)) by lia. rewrite (unsigned_lit (bv_unsigned b2 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned b3)) by lia.
    replace (Z.lor (bv_unsigned b2 * 2 ^ 8) (bv_unsigned b3)) with (bv_unsigned b3 + 256 * bv_unsigned b2)
      by (rewrite Z.lor_comm; replace (bv_unsigned b2 * 2 ^ 8) with (Z.shiftl (bv_unsigned b2) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned b3) (bv_unsigned b2)) by lia; lia).
    set (elen := bv_unsigned b3 + 256 * bv_unsigned b2) in *. assert (ELR : 0 <= elen < 2^16) by (subst elen; lia).
    step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (RL : rem - 4 < elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
      apply evt_done. do 9 eexists. exists m0, w2, c0, c1, c2, v.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - right. exact VR.
      - left. exists 374. split; [right; left; reflexivity| reflexivity]. }
    assert (RL : elen <= rem - 4) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
    step. step. ubnot. step. ub_dead. step. step. st1. st1. st1. step. step. s0slot. step. unfold UECH_VERSION. step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (NV : v <> 65037) by (revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). clear K0.
      apply evt_done. do 9 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists w2, (Z_to_bv 64 (cur + 4)), (Z_to_bv 64 Bb), (Z_to_bv 64 elen), v.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      + right. exact VR.
      + right. exists elen. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. left. split; [exact NV|]. split; [reflexivity|].
        replace (rem + -4) with (rem - 4) by lia. reflexivity.
    - assert (EV : v = 65037) by (revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). clear K0.
      step. step. s0slot. st1. step. step. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        assert (E0 : elen = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - ELR; intros K0; lia). clear K0.
        apply evt_done. do 9 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists (Z_to_bv 64 (cur + 4 + elen)), (Z_to_bv 64 (cur + 4)), (Z_to_bv 64 Bb), (Z_to_bv 64 elen), v.
        repeat match goal with |- _ /\ _ => split end; try assumption.
        * right. exact VR.
        * left. exists 400. split; [right; right; reflexivity| reflexivity].
      + assert (E1 : 1 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - ELR; intros K0; lia). clear K0.
        apply evt_done. do 9 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists (Z_to_bv 64 (cur + 4 + elen)), (Z_to_bv 64 (cur + 4)), (Z_to_bv 64 Bb), (Z_to_bv 64 elen), v.
        repeat match goal with |- _ /\ _ => split end; try assumption.
        * right. exact VR.
        * right. exists elen. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. right. split; [exact EV|]. split; [exact E1|]. split; [reflexivity|].
          replace (rem + -4) with (rem - 4) by lia. reflexivity.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg3 :
    forall (sp gp tp t0 t1 t2 s1 a0 a5 a6 a7 s2 s4 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur rem ee elen : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w5 w6 w7 w8 : word) pad mxb (x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c1 tp0 tp1 : word),
      rw_cells usegs m (bv_unsigned sp + -2368) (UFRM w0 w1 w2 w3 w4 w5 w6 w7 w8) ->
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 (Z_to_bv 64 (cur + 4)) c1 (Z_to_bv 64 elen) tp0 tp1) ->
      bytes_at usegs m Bb bs -> Bb <= cur -> 1 <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil ->
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a0' a1' a2' a3' s3' s8' : word) m1 (w0' w1' p0' p1' p2' c0' c2' : word) c,
          munch [(bv_unsigned sp + -2368, bv_unsigned sp + -2352); (ee + 49, ee + 50); (bv_unsigned sp + -168, bv_unsigned sp + -120)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 (bv_unsigned sp + -2368) (UFRM w0' w1' w2 w3 w4 w5 w6 w7 w8)
          /\ rw_cells usegs m1 (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0' p1' p2' c0' c1 c2' tp0 tp1)
          /\ rw_cells usegs m1 ee (entry_cells (upd_cfgid E c) pad1 pad2 pad3 pad4) /\ 0 <= c < 256 /\
         (  ms' = MS (mkR (Z_to_bv 64 UDE_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3' (Z_to_bv 64 2) a5 a6 a7
                      s2 s3' s4 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 Bb) (Z_to_bv 64 ee) s8' (Z_to_bv 64 elen) (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
                  F (Z_to_bv 64 UDF_TA) fc None m1 (seg_rom usegs)
         \/ (exists publen kemhi kemlo, 5 <= elen /\ 0 <= publen /\ 5 + publen <= elen /\ 0 <= kemhi < 256 /\ 0 <= kemlo < 256 /\
             nth_error bs (Z.to_nat (cur - Bb + 4)) = Some (Z_to_bv 8 c) /\
             nth_error bs (Z.to_nat (cur - Bb + 5)) = Some (Z_to_bv 8 kemhi) /\ nth_error bs (Z.to_nat (cur - Bb + 6)) = Some (Z_to_bv 8 kemlo) /\
             w0' = Z_to_bv 64 (ee + 24) /\ w1' = Z_to_bv 64 (ee + 16) /\ p0' = Z_to_bv 64 (cur + 9) /\ p1' = Z_to_bv 64 Bb /\ p2' = Z_to_bv 64 publen /\
             c0' = Z_to_bv 64 (cur + 9 + publen) /\ c2' = Z_to_bv 64 (elen - 5 - publen) /\
             ms' = MS (mkR (Z_to_bv 64 UDE_R3) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1
                           (Z_to_bv 64 (bv_unsigned sp + -168)) (Z_to_bv 64 (ee + 24)) (Z_to_bv 64 (ee + 16)) (Z_to_bv 64 (bv_unsigned sp - 4096)) (Z_to_bv 64 2) a5 a6 a7
                           s2 (Z_to_bv 64 kemhi) s4 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 Bb) (Z_to_bv 64 ee) (Z_to_bv 64 kemlo) (Z_to_bv 64 elen) (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_PACKET_memdup) fc None m1 (seg_rom usegs))))
        (MS (mkR (Z_to_bv 64 UDE_R1) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 UECH_VERSION) (Z_to_bv 64 2) (Z_to_bv 64 2) a5 a6 a7
                 s2 (Z_to_bv 64 (cur + 4 + elen)) s4 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 Bb) (Z_to_bv 64 ee) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
            F (Z_to_bv 64 UDE_J1) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros FR F3 BS BC EL1 ER CR BP BH EC EEP EEH EBA HSP MI.
    unfold UDE_R1, UDE_R3, UDE_J1, UDF_TA, P_PACKET_memdup in *. unfold UFRM in FR |- *. unfold UF3 in F3 |- *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2368 <= bv_unsigned sp) by lia. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (munch_refl [(bv_unsigned sp + -2368, bv_unsigned sp + -2352); (ee + 49, ee + 50); (bv_unsigned sp + -168, bv_unsigned sp + -120)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 4))) as [c4|] eqn:N4; [| apply nth_error_None in N4; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N4 ltac:(lia) ltac:(lia)) as RD4. pose proof (byte_range c4) as C4R.
    replace (cur + 4) with (cur + 4 + 0) by lia. step. replace (cur + 4 + 0) with (cur + 4) in * by lia. change (zxb c4) with (Z_to_bv 64 (bv_unsigned c4)).
    st1. rewrite (Z.mod_small (bv_unsigned c4) 256) in * by lia.
    step. step. ub_dead. step. step. st1. st1. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (E3 : elen < 3) by (revert K0; rewrite ?unsigned_lit by lia; clear - EL1 ER CR BB BC; intros K0; lia). clear K0.
      apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists w0, w1, p0, p1, p2, (Z_to_bv 64 (cur + 5)), (Z_to_bv 64 (elen - 1)), (bv_unsigned c4).
      repeat match goal with |- _ /\ _ => split end; try eassumption; try (clear - C4R; lia). all: try (left; reflexivity).
      all: try (replace (elen - 1) with (elen + -1) by lia; assumption). }
    assert (E3 : 3 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - EL1 ER CR BB BC; intros K0; lia). clear K0.
    step. step. step. ub_dead2 || ub_dead. step. step. ub_dead.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 5))) as [c5|] eqn:N5; [| apply nth_error_None in N5; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 6))) as [c6|] eqn:N6; [| apply nth_error_None in N6; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N5 ltac:(lia) ltac:(lia)) as RD5. pose proof (byte_range c5) as C5R.
    pose proof (pk_byte _ _ _ _ _ _ BS N6 ltac:(lia) ltac:(lia)) as RD6. pose proof (byte_range c6) as C6R.
    step. change (zxb c5) with (Z_to_bv 64 (bv_unsigned c5)). step. change (zxb c6) with (Z_to_bv 64 (bv_unsigned c6)).
    step. step. st1. st1. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (E5 : elen < 5) by (revert K0; rewrite ?unsigned_lit by lia; clear - E3 EL1 ER CR BB BC; intros K0; lia). clear K0.
      apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists w0, w1, p0, p1, p2, (Z_to_bv 64 (cur + 7)), (Z_to_bv 64 (elen - 3)), (bv_unsigned c4).
      repeat match goal with |- _ /\ _ => split end; try eassumption; try (clear - C4R; lia). all: try (left; reflexivity).
      all: try (replace (elen - 3) with (elen + -3) by lia; assumption). }
    assert (E5 : 5 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - E3 EL1 ER CR BB BC; intros K0; lia). clear K0.
    step. step. ub_dead. step. step. ub_dead.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 7))) as [c7|] eqn:N7; [| apply nth_error_None in N7; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 8))) as [c8|] eqn:N8; [| apply nth_error_None in N8; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N7 ltac:(lia) ltac:(lia)) as RD7. pose proof (byte_range c7) as C7R.
    pose proof (pk_byte _ _ _ _ _ _ BS N8 ltac:(lia) ltac:(lia)) as RD8. pose proof (byte_range c8) as C8R.
    step. change (zxb c7) with (Z_to_bv 64 (bv_unsigned c7)). step. change (zxb c8) with (Z_to_bv 64 (bv_unsigned c8)).
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c7)) by lia. rewrite (unsigned_lit (bv_unsigned c7 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c8)) by lia.
    replace (Z.lor (bv_unsigned c7 * 2 ^ 8) (bv_unsigned c8)) with (bv_unsigned c8 + 256 * bv_unsigned c7)
      by (rewrite Z.lor_comm; replace (bv_unsigned c7 * 2 ^ 8) with (Z.shiftl (bv_unsigned c7) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned c8) (bv_unsigned c7)) by lia; lia).
    set (publen := bv_unsigned c8 + 256 * bv_unsigned c7) in *. assert (PLR : 0 <= publen < 2^16) by (subst publen; lia).
    step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (EP : elen - 5 < publen) by (revert K0; rewrite ?unsigned_lit by lia; clear - E5 PLR ER CR BB BC; intros K0; lia). clear K0.
      apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists w0, w1, p0, p1, p2, (Z_to_bv 64 (cur + 7)), (Z_to_bv 64 (elen - 3)), (bv_unsigned c4).
      repeat match goal with |- _ /\ _ => split end; try eassumption; try (clear - C4R; lia). all: try (left; reflexivity).
      all: try (replace (elen - 3) with (elen + -3) by lia; assumption). }
    assert (EP : 5 + publen <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - E5 PLR ER CR BB BC; intros K0; lia). clear K0.
    step. step. ubnot. step. ub_dead. step. step. st1. st1. st1. step. st1. st1. step. step. step. step. s0slot. st1. step. step. s0slot. st1. step.
    apply evt_done. do 6 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end.
    exists (Z_to_bv 64 (ee + 24)), (Z_to_bv 64 (ee + 16)), (Z_to_bv 64 (cur + 9)), (Z_to_bv 64 Bb), (Z_to_bv 64 publen), (Z_to_bv 64 (cur + 9 + publen)), (Z_to_bv 64 (elen - 5 - publen)), (bv_unsigned c4).
    repeat match goal with |- _ /\ _ => split end; try eassumption; try (clear - C4R; lia).
    all: try (right; exists publen, (bv_unsigned c5), (bv_unsigned c6); repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity; f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned).
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg4a :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv : Z),
      (rv = 0 \/ rv = 1) -> 2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
            (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R3) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_TA) fc None m (seg_rom usegs))
         \/ (rv = 1 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R4a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp + -144)) (Z_to_bv 64 (bv_unsigned sp + -192)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UP_get2) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 UDE_R3) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R3)) fc None m (seg_rom usegs)).
  Proof.
    intros until rv. intros RV SPL MI. unfold UDE_R3, UDE_R4a, UDF_TA, UP_get2 in *. retpc0. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. apply evt_done. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. step. step. step. apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg4b :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv ee so : Z) (E : entrep) pad1 pad2 pad3 pad4
           pad mxb (x0 x1 x2 n0 n1 n2 u0 u1 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      (rv = 0 \/ rv = 1) -> 0 <= so < 2^16 ->
      (rv = 1 -> rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 (Z_to_bv 64 so) p0 p1 p2 c0 c1 c2 tp0 tp1)) ->
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a0' a1' a2' : word) m1 ns,
          munch [(ee + 32, ee + 36)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (upd_nsuites E ns) pad1 pad2 pad3 pad4) /\ (ns = en_nsuites E \/ 0 <= ns < 2^16) /\
         (  ms' = MS (mkR (Z_to_bv 64 UDE_R4a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 UDF_TA) fc None m1 (seg_rom usegs)
         \/ (rv = 1 /\ 2 <= so /\ so mod 2 = 0 /\ ns = so / 4 /\
             ms' = MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ns) (Z_to_bv 64 6) (Z_to_bv 64 UA_ECHS_FILE) (Z_to_bv 64 405) a4 a5 a6 a7
                           s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m1 (seg_rom usegs))))
        (MS (mkR (Z_to_bv 64 UDE_R4a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R4a)) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros RV SOR F3 EC EEP EEH HSP MI. unfold UDE_R4a, UDE_R4, UDF_TA, P_CRYPTO_malloc_array, UA_ECHS_FILE in *. unfold UF3 in F3. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH. retpc0.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2368 <= bv_unsigned sp) by lia.
    pose proof (munch_refl [(ee + 32, ee + 36)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    { assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0.
      apply evt_done. do 3 eexists. exists m, (en_nsuites E). repeat match goal with |- _ /\ _ => split end; try eassumption; try (rewrite upd_nsuites_id; exact EC). all: try (left; reflexivity). }
    assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0.
    specialize (F3 R1).
    step. step. step. step. step. step.
    rewrite (zbv_mod (so + 316912650057057350356995932160) (so + 18446744056529682432)) by (clear - SOR; change (2^64) with 18446744073709551616; lia).
    rewrite (zbv_mod 316912650057057350356995932161 18446744056529682433) by reflexivity.
    if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 3 eexists. exists m, (en_nsuites E). repeat match goal with |- _ /\ _ => split end; try eassumption; try (rewrite upd_nsuites_id; exact EC). all: try (left; reflexivity). }
    assert (S1 : 1 <= so) by (revert K0; rewrite ?unsigned_lit by lia; clear - SOR; intros K0; lia). clear K0.
    step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 3 eexists. exists m, (en_nsuites E). repeat match goal with |- _ /\ _ => split end; try eassumption; try (rewrite upd_nsuites_id; exact EC). all: try (left; reflexivity). }
    assert (EVN : so mod 2 = 0) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_1; clear - SOR; intros K0; lia). clear K0.
    step. rewrite (unsigned_lit so) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
    assert (NS0 : 0 <= so / 4) by (apply Z.div_pos; clear - S1; lia). assert (NSR : so / 4 < 2^16) by (apply Z.div_lt_upper_bound; [lia|]; clear - SOR; lia).
    st1. do 6 step.
    apply evt_done. do 3 eexists. match goal with MIx : mem_inv usegs ?mx |- _ => exists mx end. exists (so / 4).
    repeat match goal with |- _ /\ _ => split end; try eassumption.
    - right. split; [exact NS0| exact NSR].
    - right. split; [exact R1|]. split; [clear - S1 EVN; lia|]. split; [exact EVN|]. split; [reflexivity| reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg5 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee so sq kemhi kemlo SA : Z) (E : entrep) (o : oblk) pad1 pad2 pad3 pad4
           pad mxb (x0 x1 x2 n0 n1 n2 u1 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil ->
      0 <= SA < 2^64 -> SA mod 2 = 0 -> 0 <= kemhi < 256 -> 0 <= kemlo < 256 -> 0 <= so < 2^16 -> 0 <= sq < 2^64 ->
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 (Z_to_bv 64 sq) u1 (Z_to_bv 64 so) p0 p1 p2 c0 c1 c2 tp0 tp1) ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          munch [(ee + 40, ee + 48)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (upd_suites E SA o) pad1 pad2 pad3 pad4) /\
         (  (SA = 0 /\
             ms' = MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7
                           s2 (Z_to_bv 64 kemhi) s4 s5 s6 (Z_to_bv 64 ee) (Z_to_bv 64 kemlo) s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 UDF_TZ) fc None m1 (seg_rom usegs))
         \/ (0 < SA /\
             ms' = MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp (Z_to_bv 64 SA) (Z_to_bv 64 so) t2 sp s1
                           (Z_to_bv 64 SA) (Z_to_bv 64 0) (Z_to_bv 64 so) (Z_to_bv 64 sq) (Z_to_bv 64 (256 * kemhi + kemlo)) (Z_to_bv 64 0) (Z_to_bv 64 (SA + 4)) (Z_to_bv 64 (-1))
                           s2 (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 ee) (Z_to_bv 64 (-4)) s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 UDE_LH) fc None m1 (seg_rom usegs))))
        (MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 kemhi) s4 s5 s6 (Z_to_bv 64 ee) (Z_to_bv 64 kemlo) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R4)) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros EC EEP EEH SAR SAE KH KL SOR SQR F3 HSP MI.
    unfold UDE_R4, UDE_LH, UDF_TZ in *. unfold UF3 in F3. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH. retpc0.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2368 <= bv_unsigned sp) by lia.
    pose proof (munch_refl [(ee + 40, ee + 48)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. step. if_cases K0; zify_cond K0.
    - assert (Z0 : SA = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - SAR; intros K0; lia). clear K0.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [exact Z0| reflexivity].
    - assert (Z1 : 0 < SA) by (revert K0; rewrite ?unsigned_lit by lia; clear - SAR; intros K0; lia). clear K0.
      step. step. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit kemhi) by lia. step. step. step.
      rewrite (unsigned_lit (kemhi * 2 ^ 8)) by lia. rewrite (unsigned_lit kemlo) by lia.
      replace (Z.lor (kemhi * 2 ^ 8) kemlo) with (256 * kemhi + kemlo)
        by (rewrite Z.lor_comm; replace (kemhi * 2 ^ 8) with (Z.shiftl kemhi 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add kemlo kemhi) by lia; lia).
      step. rewrite (unsigned_lit SA) by lia. rewrite (al2 SA SAE). step. step. step. step. step. step.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact Z1|]. reflexivity.
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma ude_loop : forall (k : nat) (i : Z) (sp gp tp t2 s1 s2 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb ee so sq ns kem SA : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4 junk
           pad mxb (x0 x1 x2 n0 n1 n2 u1 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      Z.of_nat k = ns - i -> 0 <= i <= ns -> en_nsuites E = ns -> 0 <= ns -> 4 * ns <= so <= 4 * ns + 3 -> so < 2^16 -> 0 <= kem < 2^16 ->
      rw_cells usegs m (SA + 6 * i) [CB (Z.to_nat (6 * (ns - i))) junk] -> 0 < SA -> SA + 6 * ns <= hceil -> SA mod 2 = 0 ->
      bytes_at usegs m Bb bs -> 0 < Bb -> Bb <= sq -> sq + so <= Bb + zlength bs -> Bb + zlength bs <= hceil -> (SA + 6 * ns <= Bb \/ Bb + zlength bs <= SA) ->
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> (SA + 6 * ns <= ee \/ ee + ENTRY_SIZE <= SA) ->
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 (Z_to_bv 64 (sq + 4 * i)) u1 (Z_to_bv 64 (so - 4 * i)) p0 p1 p2 c0 c1 c2 tp0 tp1) ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (t0' t2' a6' a7' t3' t4' t5' t6' : word) m1 junk',
          munch [(SA + 6 * i, SA + 6 * ns); (bv_unsigned sp + -192, bv_unsigned sp + -168)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 (SA + 6 * i) (suite_cells (srows bs (Z.to_nat (sq - Bb + 4 * i)) kem k) ++ [CB 0 junk'])
          /\ bytes_at usegs m1 Bb bs /\ rw_cells usegs m1 ee (entry_cells E pad1 pad2 pad3 pad4)
          /\ rw_cells usegs m1 (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 (Z_to_bv 64 (sq + 4 * ns)) u1 (Z_to_bv 64 (so - 4 * ns)) p0 p1 p2 c0 c1 c2 tp0 tp1)
          /\ ms' = MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0' (Z_to_bv 64 (so - 4 * ns)) t2' sp s1
                        (Z_to_bv 64 SA) (Z_to_bv 64 (4 * ns)) (Z_to_bv 64 so) (Z_to_bv 64 sq) (Z_to_bv 64 kem) (Z_to_bv 64 0) a6' a7'
                        s2 (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 ee) (Z_to_bv 64 (-4)) s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 UDE_J2) fc None m1 (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp (Z_to_bv 64 (SA + 6 * i)) (Z_to_bv 64 (so - 4 * i)) t2 sp s1
                 (Z_to_bv 64 SA) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 so) (Z_to_bv 64 sq) (Z_to_bv 64 kem) (Z_to_bv 64 0) (Z_to_bv 64 (SA + 4 + 6 * i)) (Z_to_bv 64 (i - 1))
                 s2 (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 ee) (Z_to_bv 64 (-4)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UDE_LH) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until tp1; intros HK IR NSE NS0 SOB SOR KR SC SAP SAH SAE BS BP SQB QB BH SBA EC EEP EEH SEA F3 HSP MI.
    - (* [comment removed for export] *)
      unfold UDE_LH, UDE_J2 in *. unfold UF3 in F3 |- *. hcb. pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
      assert (IE : i = ns) by lia. subst i.
      pose proof (munch_refl [(SA + 6 * ns, SA + 6 * ns); (bv_unsigned sp + -192, bv_unsigned sp + -168)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. clear - SOB. intros K0. lia. }
      clear K0.
      apply evt_done. do 8 eexists. exists m, junk.
      repeat match goal with |- _ /\ _ => split end; try assumption. cbn [srows suite_cells app]. rewrite Z.sub_diag in SC. exact SC. reflexivity.
    - (* [comment removed for export] *)
      unfold UDE_LH, UDE_J2 in *. unfold UF3 in F3 |- *. hcb. pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *. unfold entry_cells in EC. unfold ENTRY_SIZE in *.
      assert (IL : i < ns) by lia.
      pose proof (munch_refl [(SA + 6 * i, SA + 6 * ns); (bv_unsigned sp + -192, bv_unsigned sp + -168)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      step. if_cases K0; zify_cond K0.
      { exfalso. revert K0. rewrite ?unsigned_lit by lia. clear - IL IR SOB. intros K0. lia. }
      clear K0.
      destruct (nth_error bs (Z.to_nat (sq - Bb + 4 * i + 0))) as [e0|] eqn:M0; [| apply nth_error_None in M0; lia].
      destruct (nth_error bs (Z.to_nat (sq - Bb + 4 * i + 1))) as [e1|] eqn:M1; [| apply nth_error_None in M1; lia].
      destruct (nth_error bs (Z.to_nat (sq - Bb + 4 * i + 2))) as [e2|] eqn:M2; [| apply nth_error_None in M2; lia].
      destruct (nth_error bs (Z.to_nat (sq - Bb + 4 * i + 3))) as [e3|] eqn:M3; [| apply nth_error_None in M3; lia].
      pose proof (pk_byte m Bb bs (sq + 4 * i) 0 e0 BS ltac:(replace (sq + 4 * i - Bb + 0) with (sq - Bb + 4 * i + 0) by lia; exact M0) ltac:(lia) ltac:(lia)) as RD0.
      pose proof (pk_byte m Bb bs (sq + 4 * i) 1 e1 BS ltac:(replace (sq + 4 * i - Bb + 1) with (sq - Bb + 4 * i + 1) by lia; exact M1) ltac:(lia) ltac:(lia)) as RD1.
      pose proof (pk_byte m Bb bs (sq + 4 * i) 2 e2 BS ltac:(replace (sq + 4 * i - Bb + 2) with (sq - Bb + 4 * i + 2) by lia; exact M2) ltac:(lia) ltac:(lia)) as RD2.
      pose proof (pk_byte m Bb bs (sq + 4 * i) 3 e3 BS ltac:(replace (sq + 4 * i - Bb + 3) with (sq - Bb + 4 * i + 3) by lia; exact M3) ltac:(lia) ltac:(lia)) as RD3.
      pose proof (byte_range e0) as E0R. pose proof (byte_range e1) as E1R. pose proof (byte_range e2) as E2R. pose proof (byte_range e3) as E3R.
      step. step. ub_dead.
      step. change (zxb e0) with (Z_to_bv 64 (bv_unsigned e0)). step. change (zxb e1) with (Z_to_bv 64 (bv_unsigned e1)).
      step. change (zxb e2) with (Z_to_bv 64 (bv_unsigned e2)). step. change (zxb e3) with (Z_to_bv 64 (bv_unsigned e3)).
      step. step. st1. st1. step. ub_dead. step. if_lit.
      (* [comment removed for export] *)
      replace (SA + 4 + 6 * i) with (SA + 6 * i + 4) by lia.
      match goal with SCx : rw_cells usegs ?mx (SA + 6 * i) [CB _ junk] |- _ =>
        pose proof (rw_cells_split_CB usegs mx (SA + 6 * i) [] (Z.to_nat (6 * (ns - i))) junk [] [6%nat; Z.to_nat (6 * (ns - (i + 1)))] SCx ltac:(cbn [sum_nat]; lia)) as SC2;
        clear SCx; cbn [mk_CB_cells app] in SC2 end.
      set (Q := SA + 6 * i) in *.
      st1. step. ub_dead.
      pose proof (ub_kdf (bv_unsigned e0) (bv_unsigned e1) (bv_unsigned e2) (bv_unsigned e3) E0R E1R E2R E3R) as (KV1 & KV2 & WR & KB1 & KD). cbv zeta in KV1, KV2, WR, KB1, KD.
      set (w := bv_unsigned e0 + bv_unsigned e1 * 2^8 + (bv_unsigned e2 * 2^16 + bv_unsigned e3 * 2^24)) in *.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit (bv_unsigned e1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. rewrite (unsigned_lit (bv_unsigned e2)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. rewrite (unsigned_lit (bv_unsigned e1 * 2 ^ 8)), (unsigned_lit (bv_unsigned e0)) by lia. rewrite (Z.lor_comm (bv_unsigned e1 * 2 ^ 8)), (lor_add_disjoint_u (bv_unsigned e0) (bv_unsigned e1) 8) by lia.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit (bv_unsigned e3)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. rewrite (unsigned_lit (bv_unsigned e3 * 2 ^ 24)), (unsigned_lit (bv_unsigned e2 * 2 ^ 16)) by lia.
      rewrite (Z.lor_comm (bv_unsigned e3 * 2 ^ 24)), (lor_add_disjoint_u (bv_unsigned e2 * 2 ^ 16) (bv_unsigned e3) 24) by lia.
      step. rewrite (unsigned_lit (bv_unsigned e2 * 2 ^ 16 + bv_unsigned e3 * 2 ^ 24)), (unsigned_lit (bv_unsigned e0 + bv_unsigned e1 * 2 ^ 8)) by lia.
      rewrite (Z.lor_comm (bv_unsigned e2 * 2 ^ 16 + bv_unsigned e3 * 2 ^ 24)).
      replace (bv_unsigned e2 * 2 ^ 16 + bv_unsigned e3 * 2 ^ 24) with ((bv_unsigned e2 + bv_unsigned e3 * 2 ^ 8) * 2 ^ 16) by lia.
      rewrite (lor_add_disjoint_u (bv_unsigned e0 + bv_unsigned e1 * 2 ^ 8) (bv_unsigned e2 + bv_unsigned e3 * 2 ^ 8) 16) by lia.
      replace (bv_unsigned e0 + bv_unsigned e1 * 2 ^ 8 + (bv_unsigned e2 + bv_unsigned e3 * 2 ^ 8) * 2 ^ 16) with w by (subst w; lia).
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit w) by lia. rewrite (Z.shiftl_mul_pow2 w 8) by lia.
      step. rewrite (unsigned_lit w) by lia. step. rewrite (Z.shiftr_div_pow2 _ 56) by lia. rewrite (ub_byte1 w) by lia. rewrite KB1.
      step. rewrite (unsigned_lit (w * 2 ^ 8)), (unsigned_lit (bv_unsigned e1)) by lia. rewrite (Z.lor_comm (w * 2 ^ 8)), (lor_add_disjoint_u (bv_unsigned e1) w 8) by lia.
      (* [comment removed for export] *)
      step. rewrite NSE. unfold zx32. rewrite wz_unsigned by lia. rewrite (Z.mod_small ns) by lia.
      step. replace (i - 1 + 1) with i by lia. step.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit w) by lia. rewrite (Z.shiftr_div_pow2 w 16) by lia. rewrite KD.
      step. rewrite (unsigned_lit (bv_unsigned e2 + 256 * bv_unsigned e3)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. rewrite (unsigned_lit ((bv_unsigned e2 + 256 * bv_unsigned e3) * 2 ^ 8)), (unsigned_lit (bv_unsigned e3)) by lia.
      rewrite (Z.lor_comm ((bv_unsigned e2 + 256 * bv_unsigned e3) * 2 ^ 8)), (lor_add_disjoint_u (bv_unsigned e3) (bv_unsigned e2 + 256 * bv_unsigned e3) 8) by lia.
      st1. st1. step. step. step. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; clear - IL; lia]. clear K0.
      (* [comment removed for export] *)
      match goal with SCx : rw_cells usegs ?mx Q ?cs |- _ =>
        assert (SC3' : rw_cells usegs mx Q ([C2 (Z_to_bv 64 kem); C2 (Z_to_bv 64 (256 * bv_unsigned e0 + bv_unsigned e1)); C2 (Z_to_bv 64 (256 * bv_unsigned e2 + bv_unsigned e3))]
                                          ++ [CB (Z.to_nat (6 * (ns - (i + 1)))) (firstn (Z.to_nat (6 * (ns - (i + 1)))) (skipn 6 junk))]));
        [ eapply rw_cells_recut; [exact SCx| exact (proj1 (proj1 SCx))|];
          cbn [cells_bytes cbytes app]; rewrite (le2_mod16 (256 * bv_unsigned e0 + bv_unsigned e1) (bv_unsigned e1 + w * 2 ^ 8)) by (clear - KV1 E0R E1R WR; lia);
          rewrite (le2_mod16 (256 * bv_unsigned e2 + bv_unsigned e3) (bv_unsigned e3 + (bv_unsigned e2 + 256 * bv_unsigned e3) * 2 ^ 8)) by (clear - KV2 E2R E3R; lia); reflexivity
        | clear SCx ] end.
      pose proof (proj1 (rw_cells_app usegs _ Q _ _) SC3') as [SC3 SC4]. clear SC3'.
      cbn [cells_size csize Nat.add] in SC4. subst Q. replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) in SC4 by lia.
      replace (SA + 6 * i + 6) with (SA + 6 * (i + 1)) by lia. replace (SA + 6 * i + 10) with (SA + 4 + 6 * (i + 1)) by lia.
      replace (so - 4 * i + -4) with (so - 4 * (i + 1)) in * by lia. replace (sq + 4 * i + 4) with (sq + 4 * (i + 1)) in * by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia.
      replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + 1 - 1)) by (f_equal; lia).
      eapply evt_mono.
      { eapply (IH (i + 1)); try eassumption; try (unfold entry_cells; eassumption); rewrite ?Nat2Z.inj_succ in HK; clear - HK IL IR; lia. }
      cbv beta. intros ms' (t0' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk' & MU1 & WM1 & MI1 & SC5 & BS1 & EC1 & F31 & ->).
      exists t0', t2', a6', a7', t3', t4', t5', t6', m1, junk'. repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia.
      + eapply wmono_trans; [exact WM| exact WM1].
      + cbn [srows suite_cells app]. replace (Z.to_nat (sq - Bb + 4 * (i + 1))) with (4 + Z.to_nat (sq - Bb + 4 * i))%nat in SC5 by lia.
        unfold bz. replace (Z.to_nat (sq - Bb + 4 * i)) with (Z.to_nat (sq - Bb + 4 * i + 0)) by lia. rewrite M0.
        replace (S (Z.to_nat (sq - Bb + 4 * i + 0))) with (Z.to_nat (sq - Bb + 4 * i + 1)) by lia. rewrite M1.
        replace (S (Z.to_nat (sq - Bb + 4 * i + 1))) with (Z.to_nat (sq - Bb + 4 * i + 2)) by lia. rewrite M2.
        replace (S (Z.to_nat (sq - Bb + 4 * i + 2))) with (Z.to_nat (sq - Bb + 4 * i + 3)) by lia. rewrite M3.
        apply (proj2 (rw_cells_app usegs m1 (SA + 6 * i) [C2 (wz kem); C2 (wz (256 * bv_unsigned e0 + bv_unsigned e1)); C2 (wz (256 * bv_unsigned e2 + bv_unsigned e3))] _)). split.
        * eapply rw_cells_transport; [exact SC3| exact MU1| exact WM1| cbn; lia].
        * cbn [cells_size csize Nat.add]. replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) by lia. fold bz in SC5.
          replace (S (S (S (S (Z.to_nat (sq - Bb + 4 * i + 0)))))) with (4 + Z.to_nat (sq - Bb + 4 * i))%nat by lia. exact SC5.
      + reflexivity.
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg7a :
    forall (sp gp tp t0 t1 t2 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (so cnt : Z),
      0 <= so < 2^16 -> 0 <= cnt < 2^16 -> 2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
            (so <> cnt /\ ms' = MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 (Z_to_bv 64 cnt) (Z_to_bv 64 so) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 4) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 420) t3 t4 t5 t6)
                                      F (Z_to_bv 64 UDF_TA) fc None m (seg_rom usegs))
         \/ (so = cnt /\ ms' = MS (mkR (Z_to_bv 64 UDE_R5a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp + -144)) (Z_to_bv 64 (bv_unsigned sp + -241)) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 4) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 420) t3 t4 t5 t6)
                                      F (Z_to_bv 64 UP_copy) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 UDE_R4) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 (Z_to_bv 64 cnt) (Z_to_bv 64 so) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UDE_J2) fc None m (seg_rom usegs)).
  Proof.
    intros until cnt. intros SOR CNR SPL MI. unfold UDE_R4, UDE_J2, UDE_R5a, UDF_TA, UP_copy in *. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. step. if_cases K0; zify_cond K0.
    - assert (NE : so <> cnt) by (revert K0; rewrite ?unsigned_lit by lia; clear - SOR CNR; intros K0; lia). clear K0. apply evt_done. left. split; [exact NE| reflexivity].
    - assert (EQ : so = cnt) by (revert K0; rewrite ?unsigned_lit by lia; clear - SOR CNR; intros K0; lia). clear K0. step. step. step. step. apply evt_done. right. split; [exact EQ| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg7b :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv ee mx : Z) (E : entrep) pad1 pad2 pad3 pad4
           pad (x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      (rv = 0 \/ rv = 1) -> 0 <= mx < 256 ->
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad (Z_to_bv 8 mx) x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1) ->
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a0' a1' : word) m1 mx',
          munch [(ee + 48, ee + 49)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (upd_maxname E mx') pad1 pad2 pad3 pad4) /\ (mx' = en_maxname E \/ mx' = mx) /\
         (  (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R5a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_TA) fc None m1 (seg_rom usegs))
         \/ (rv = 1 /\ mx' = mx /\ ms' = MS (mkR (Z_to_bv 64 UDE_R5b) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp + -144)) (Z_to_bv 64 (bv_unsigned sp + -216)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UP_get1) fc None m1 (seg_rom usegs))))
        (MS (mkR (Z_to_bv 64 UDE_R5a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R5a)) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros RV MXR F3 EC EEP EEH HSP MI. unfold UDE_R5a, UDE_R5b, UDF_TA, UP_get1 in *. unfold UF3 in F3. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH. retpc0.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2368 <= bv_unsigned sp) by lia.
    pose proof (munch_refl [(ee + 48, ee + 49)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0.
      apply evt_done. do 2 eexists. exists m, (en_maxname E). repeat match goal with |- _ /\ _ => split end; try eassumption; try (rewrite upd_maxname_id; exact EC). left; reflexivity. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0.
      step. change (zxb (Z_to_bv 8 mx)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 mx))). rewrite (Z_to_bv_unsigned 8 mx). unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small mx 256) by lia.
      st1. rewrite (Z.mod_small mx 256) in * by lia. step. step. step.
      apply evt_done. do 2 eexists. match goal with MIx : mem_inv usegs ?mx0 |- _ => exists mx0 end. exists mx. repeat match goal with |- _ /\ _ => split end; try eassumption. right; reflexivity. right. split; [exact R1|]. split; [reflexivity| reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg7c :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv : Z),
      (rv = 0 \/ rv = 1) -> 2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
            (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R5b) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 425) t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_TA) fc None m (seg_rom usegs))
         \/ (rv = 1 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R5) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp + -216)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UP_has0) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 UDE_R5b) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R5b)) fc None m (seg_rom usegs)).
  Proof.
    intros until rv. intros RV SPL MI. unfold UDE_R5b, UDE_R5, UDF_TA, UDE_A425, UP_has0 in *. retpc0. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. step. step. apply evt_done. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. step. step. apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg8 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (z ee nl : Z)
           pad mxb (x0 x1 x2 n0 n1 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      (z = 0 \/ z = 1) -> 0 <= nl < 256 -> 0 <= ee < 2^64 ->
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 (Z_to_bv 64 nl) u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1) ->
      2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a0' a1' : word),
            ((z <> 0 \/ nl < 4) /\ ms' = MS (mkR (Z_to_bv 64 UDE_R5) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 (Z_to_bv 64 431) t3 t4 t5 t6)
                                      F (Z_to_bv 64 UDF_TA) fc None m (seg_rom usegs))
         \/ (z = 0 /\ 4 <= nl /\ ms' = MS (mkR (Z_to_bv 64 UDE_R6) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp + -216)) (Z_to_bv 64 (ee + 8)) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 (Z_to_bv 64 431) t3 t4 t5 t6)
                                      F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 UDE_R5) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 z) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R5)) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros ZR NLR EER F3 SPL MI. unfold UDE_R5, UDE_R6, UDF_TA, P_PACKET_strndup in *. unfold UF3 in F3. retpc0. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. if_cases K0; zify_cond K0.
    { apply evt_done. do 2 eexists. left. split; [left; revert K0; rewrite ?unsigned_lit by lia; clear - ZR; intros K0; lia| reflexivity]. }
    assert (Z0 : z = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - ZR; intros K0; lia). clear K0.
    step. step. if_cases K0; zify_cond K0.
    { apply evt_done. do 2 eexists. left. split; [right; revert K0; rewrite ?unsigned_lit by lia; clear - NLR; intros K0; lia| reflexivity]. }
    assert (N4 : 4 <= nl) by (revert K0; rewrite ?unsigned_lit by lia; clear - NLR; intros K0; lia). clear K0.
    step. step. step. apply evt_done. do 2 eexists. right. split; [exact Z0|]. split; [exact N4| reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg9a :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv : Z),
      (rv = 0 \/ rv = 1) -> 2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
            (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R6) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_TA) fc None m (seg_rom usegs))
         \/ (rv = 1 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R6a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp + -144)) (Z_to_bv 64 (bv_unsigned sp + -240)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UP_get2) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 UDE_R6) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R6)) fc None m (seg_rom usegs)).
  Proof.
    intros until rv. intros RV SPL MI. unfold UDE_R6, UDE_R6a, UDF_TA, UP_get2 in *. retpc0. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. apply evt_done. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. step. step. step. apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg9b :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv ee xl : Z)
           pad mxb (x0 x1 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      (rv = 0 \/ rv = 1) -> 0 <= xl < 2^16 -> 0 <= ee < 2^64 ->
      (rv = 1 -> rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 (Z_to_bv 64 xl) n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1)) ->
      2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
            (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R6a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 (Z_to_bv 64 442) t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_TA) fc None m (seg_rom usegs))
         \/ (rv = 1 /\ xl = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R6a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 xl) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDE_J3) fc None m (seg_rom usegs))
         \/ (rv = 1 /\ 1 <= xl /\ ms' = MS (mkR (Z_to_bv 64 UDE_R7) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ee) (Z_to_bv 64 (bv_unsigned sp + -240)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 UDE_R6a) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R6a)) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros RV XLR EER F3 SPL MI. unfold UDE_R6a, UDE_R7, UDE_J3, UDF_TA, UDE_A442, P_ech_decode_echconfig_exts in *. unfold UF3 in F3. retpc0. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    { assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. step. step. apply evt_done. left. split; [exact R0| reflexivity]. }
    assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0.
    specialize (F3 R1).
    step. step. if_cases K0; zify_cond K0.
    - assert (X0 : xl = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - XLR; intros K0; lia). clear K0. apply evt_done. right; left. split; [exact R1|]. split; [exact X0| reflexivity].
    - assert (X1 : 1 <= xl) by (revert K0; rewrite ?unsigned_lit by lia; clear - XLR; intros K0; lia). clear K0. step. step. step. apply evt_done. right; right. split; [exact R1|]. split; [exact X1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg10 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv : Z),
      (rv = 0 \/ rv = 1) -> mem_inv usegs m ->
      evt usegs (fun ms' =>
            (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R7) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 447) t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_TA) fc None m (seg_rom usegs))
         \/ (rv = 1 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R7) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDE_J3) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 UDE_R7) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R7)) fc None m (seg_rom usegs)).
  Proof.
    intros until rv. intros RV MI. unfold UDE_R7, UDE_J3, UDF_TA, UDE_A447 in *. retpc0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. step. step. apply evt_done. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg11 :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (cur ee endp : Z) (E : entrep) pad1 pad2 pad3 pad4
           pad mxb (x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c1 c2 tp0 tp1 : word),
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 (Z_to_bv 64 endp) c1 c2 tp0 tp1) ->
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> cur <= endp -> 0 < cur -> endp <= hceil ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          munch [(ee + 88, ee + 96)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (upd_enclen E (endp - cur)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 UDE_R8) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1
                        (Z_to_bv 64 cur) (Z_to_bv 64 (endp - cur)) (Z_to_bv 64 UA_ECHS_FILE) (Z_to_bv 64 453) a4 a5 a6 a7
                        s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m1 (seg_rom usegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UDE_J3) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros F3 EC EEP EEH XC CP XH HSP MI. unfold UDE_R8, UDE_J3, P_CRYPTO_memdup, UA_ECHS_FILE in *. unfold UF3 in F3. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2368 <= bv_unsigned sp) by lia.
    pose proof (munch_refl [(ee + 88, ee + 96)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. rewrite ?unsigned_lit by lia. rewrite ?land_W64, ?Z.mod_small by lia. st1. do 6 step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ude_seg12 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee EA : Z) (E : entrep) (o : oblk) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w5 w6 w8 : word),
      rw_cells usegs m (bv_unsigned sp + -2368) (UFRM w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 0) w8) ->
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> 0 <= EA < 2^64 ->
      hceil <= bv_unsigned sp + -2368 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (a0' : word) m1,
          munch [(ee + 96, ee + 104)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (upd_encoded E EA o) pad1 pad2 pad3 pad4) /\
         (  (EA = 0 /\ ms' = MS (mkR (Z_to_bv 64 UDE_R8) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_TZ) fc None m1 (seg_rom usegs))
         \/ (0 < EA /\ ms' = MS (mkR (Z_to_bv 64 UDE_R8) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 UDF_OK) fc None m1 (seg_rom usegs))))
        (MS (mkR (Z_to_bv 64 UDE_R8) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 EA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 UDE_R8)) fc None m (seg_rom usegs)).
  Proof.
    intros until w8. intros FR EC EEP EEH EAR HSP MI. unfold UDE_R8, UDF_TZ, UDF_OK in *. unfold UFRM in FR. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH. retpc0.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2368 <= bv_unsigned sp) by lia.
    pose proof (munch_refl [(ee + 96, ee + 104)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. step. if_cases K0; zify_cond K0.
    - assert (Z0 : EA = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - EAR; intros K0; lia). clear K0.
      apply evt_done. do 2 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [exact Z0| reflexivity].
    - assert (Z1 : 0 < EA) by (revert K0; rewrite ?unsigned_lit by lia; clear - EAR; intros K0; lia). clear K0.
      step. step. s0slot. step. step. if_lit.
      apply evt_done. do 2 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact Z1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ude_skip :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee endp : Z)
           pad mxb (x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1 : word),
      rw_cells usegs m (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1) ->
      0 <= endp < 2^64 -> 0 <= ee < 2^64 -> 2368 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          munch [(bv_unsigned sp + -144, bv_unsigned sp + -120)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 (bv_unsigned sp + -248) (UF3 pad mxb x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 (Z_to_bv 64 endp) c1 (Z_to_bv 64 0) tp0 tp1)
          /\ ms' = MS (mkR (Z_to_bv 64 UDE_R2) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 endp) s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m1 (seg_rom usegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 endp) s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UDE_SKIP) fc None m (seg_rom usegs)).
  Proof.
    intros until tp1. intros F3 ER EER SPL MI. unfold UDE_SKIP, UDE_R2, P_ossl_echstore_entry_free in *. unfold UF3 in F3 |- *. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -120)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. st1. step. step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ude_skipret :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 UDE_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 UDF_ADV) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 UDE_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 UDE_R2)) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold UDE_R2, UDF_ADV. retpc0. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. apply evt_done. reflexivity.
  Qed.
End S.
