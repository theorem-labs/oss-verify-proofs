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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_C1_stmt ECH_C4_stmt ECH_C5_stmt ECH_C10_stmt ECH_C13_stmt ECH_C14_stmt ECH_C14_bio2buf ECH_C14_decexts_seg ECH_C14_dec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition DE_R1 : Z := 0x26cb04.   (* [comment removed for export] *)
Definition DE_J1 : Z := 0x26cb7c.   (* [comment removed for export] *)
Definition DE_SKIP : Z := 0x26cd10. (* [comment removed for export] *)
Definition DE_R2 : Z := 0x26cd18.   (* [comment removed for export] *)
Definition DE_R3 : Z := 0x26cc28.   (* [comment removed for export] *)
Definition DE_R4 : Z := 0x26cc90.   (* [comment removed for export] *)
Definition DE_LH : Z := 0x26ccc4.   (* [comment removed for export] *)
Definition DE_J2 : Z := 0x26cd1c.   (* [comment removed for export] *)
Definition DE_R5 : Z := 0x26cd88.   (* [comment removed for export] *)
Definition DE_R6 : Z := 0x26cda4.   (* [comment removed for export] *)
Definition DE_R7 : Z := 0x26cdf4.   (* [comment removed for export] *)
Definition DE_J3 : Z := 0x26cdf8.   (* [comment removed for export] *)
Definition DE_R8 : Z := 0x26ce1c.   (* [comment removed for export] *)
Definition DE_A367 : Z := 0x26d0c4. Definition DE_A447 : Z := 0x26d0d4. Definition DE_A414 : Z := 0x26cfec.
(* [comment removed for export] *)
Definition FRM (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) : list cell :=
  [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13].
Definition F3W (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : word) : list cell :=
  [C8 v0; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10].
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
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  Local Ltac s0slot := match goal with |- context [bv_unsigned ?sp - 4096] => replace (bv_unsigned sp - 4096) with (bv_unsigned sp + -2352 + -1744) by lia end.

  (* [comment removed for export] *)
  Lemma de_seg1 :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (w0 w1 w2 w3 w4 w5 w6 w7 w9 w10 w11 w12 w13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : word),
      rw_cells rsegs m (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 A_ECHS_FILE_RP) w9 w10 w11 w12 w13) ->
      rw_cells rsegs m (bv_unsigned sp + -192) (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) ->
      2352 <= bv_unsigned sp -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          munch [(bv_unsigned sp + -120, bv_unsigned sp + -112)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (bv_unsigned sp + -192) (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 (Z_to_bv 64 0) v10)
          /\ ms' = MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 104) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 360) a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom rsegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DF_LOOP) fc None m (seg_rom rsegs)).
  Proof.
    intros until v10. intros FR F3 SPL MI. unfold DF_LOOP, DE_R1, P_CRYPTO_zalloc, A_ECHS_FILE_RP in *. unfold FRM in FR. unfold F3W, O_F3 in F3 |- *.
    pose proof (word_range sp) as SPR.
    pose proof (munch_refl [(bv_unsigned sp + -120, bv_unsigned sp + -112)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    st1. do 3 step. step. replace (bv_unsigned sp - 4096) with (bv_unsigned sp + -2352 + -1744) by lia. step. step. step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg2 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur rem ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 : word),
      rw_cells rsegs m (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 ECH_VERSION) w8 w9 w10 w11 w12 w13) ->
      bytes_at rsegs m Bb bs -> Bb <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil ->
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists (a0' a1' a2' s4' : word) m1 (w9' w10' : word) v,
          munch [(bv_unsigned sp + -2280, bv_unsigned sp + -2264); (ee, ee + 2)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 ECH_VERSION) w8 w9' w10' w11 w12 w13)
          /\ rw_cells rsegs m1 ee (entry_cells (upd_version E v) pad1 pad2 pad3 pad4) /\ (v = en_version E \/ 0 <= v < 2^16) /\
         (  (exists line, (line = 367 \/ line = 374) /\
             ms' = MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3 a4 a5 a6 a7
                           s2 (Z_to_bv 64 Bb) s4' s5 s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) (Z_to_bv 64 line) t3 t4 t5 t6)
                      F (Z_to_bv 64 DF_TA) fc None m1 (seg_rom rsegs))
         \/ (exists elen, 0 <= elen /\ 4 + elen <= rem /\ w9' = Z_to_bv 64 (rem - 4) /\ w10' = Z_to_bv 64 elen /\
             (  (v <> ECH_VERSION /\
                 ms' = MS (mkR (Z_to_bv 64 DE_R2) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ee) (Z_to_bv 64 ECH_VERSION) a2' a3 a4 a5 a6 a7
                               s2 (Z_to_bv 64 Bb) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 (cur + 4)) s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) (Z_to_bv 64 374) t3 t4 t5 t6)
                          F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m1 (seg_rom rsegs))
             \/ (v = ECH_VERSION /\
                 ms' = MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 v) (Z_to_bv 64 ECH_VERSION) a2' a3 a4 a5 a6 a7
                               s2 (Z_to_bv 64 Bb) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 (cur + 4)) s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) (Z_to_bv 64 374) t3 t4 t5 t6)
                          F (Z_to_bv 64 DE_J1) fc None m1 (seg_rom rsegs))))))
        (MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 Bb) (Z_to_bv 64 rem) s5 s6 s7 s8 s9 (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DE_R1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until w13. intros FR BS BC R1 CR BP BH EC EEP EEH EBA HSP MI.
    unfold DE_R1, DE_R2, DE_J1, DF_TA, P_ossl_echstore_entry_free in *. unfold FRM in FR |- *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA. retpc.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2352 <= bv_unsigned sp) by lia. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (munch_refl [(bv_unsigned sp + -2280, bv_unsigned sp + -2264); (ee, ee + 2)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. step. br. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R1' : rem = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step.
      apply evt_done. exists (Z_to_bv 64 1), a1, a2, (Z_to_bv 64 rem), m, w9, w10, (en_version E).
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_version_id; exact EC).
      - left. reflexivity.
      - left. exists 367. split; [left; reflexivity| reflexivity]. }
    assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 1))) as [c1|] eqn:N1; [| apply nth_error_None in N1; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (pk_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
    pose proof (byte_range c0) as C0R. pose proof (byte_range c1) as C1R.
    step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). step. change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)).
    step. step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c0)) by lia. rewrite (unsigned_lit (bv_unsigned c0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c1)) by lia.
    replace (Z.lor (bv_unsigned c0 * 2 ^ 8) (bv_unsigned c1)) with (bv_unsigned c1 + 256 * bv_unsigned c0)
      by (rewrite Z.lor_comm; replace (bv_unsigned c0 * 2 ^ 8) with (Z.shiftl (bv_unsigned c0) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned c1) (bv_unsigned c0)) by lia; lia).
    set (v := bv_unsigned c1 + 256 * bv_unsigned c0) in *. assert (VR : 0 <= v < 2^16) by (subst v; lia).
    st1. step. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R23 : rem <= 3) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_even_mask, land_W64, land_1, Z.mod_small by lia; clear - R2; intros K0; lia). clear K0.
      apply evt_done. exists (Z_to_bv 64 v), (Z_to_bv 64 2), (Z_to_bv 64 (Z.land rem 18446744073709551614)), (Z_to_bv 64 rem), m0, w9, w10, v.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - right. exact VR.
      - left. exists 374. split; [right; reflexivity| reflexivity]. }
    assert (R4 : 4 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_even_mask, land_W64, land_1, Z.mod_small by lia; clear - R2; intros K0; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 2))) as [c2|] eqn:N2; [| apply nth_error_None in N2; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 3))) as [c3|] eqn:N3; [| apply nth_error_None in N3; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N2 ltac:(lia) ltac:(lia)) as RD2. pose proof (pk_byte _ _ _ _ _ _ BS N3 ltac:(lia) ltac:(lia)) as RD3.
    pose proof (byte_range c2) as C2R. pose proof (byte_range c3) as C3R.
    step. change (zxb c2) with (Z_to_bv 64 (bv_unsigned c2)). step. change (zxb c3) with (Z_to_bv 64 (bv_unsigned c3)).
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c2)) by lia. rewrite (unsigned_lit (bv_unsigned c2 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c3)) by lia.
    replace (Z.lor (bv_unsigned c2 * 2 ^ 8) (bv_unsigned c3)) with (bv_unsigned c3 + 256 * bv_unsigned c2)
      by (rewrite Z.lor_comm; replace (bv_unsigned c2 * 2 ^ 8) with (Z.shiftl (bv_unsigned c2) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned c3) (bv_unsigned c2)) by lia; lia).
    set (elen := bv_unsigned c3 + 256 * bv_unsigned c2) in *. assert (ELR : 0 <= elen < 2^16) by (subst elen; lia).
    step. step. step. s0slot. st1. step. step. s0slot. st1.
    step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (RL : rem - 4 < elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
      apply evt_done. exists (Z_to_bv 64 v), (Z_to_bv 64 elen), (Z_to_bv 64 (bv_unsigned sp - 4096)), (Z_to_bv 64 (rem + -4)), m2, (Z_to_bv 64 (rem + -4)), (Z_to_bv 64 elen), v.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - right. exact VR.
      - left. exists 374. split; [right; reflexivity| reflexivity]. }
    assert (RL : elen <= rem - 4) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
    step. step. step. s0slot. step. unfold ECH_VERSION. step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (NV : v <> 65037) by (revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). clear K0.
      step. step.
      apply evt_done. exists (Z_to_bv 64 v), (Z_to_bv 64 elen), (Z_to_bv 64 (bv_unsigned sp - 4096)), (Z_to_bv 64 (rem + -4)), m2, (Z_to_bv 64 (rem + -4)), (Z_to_bv 64 elen), v.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      + right. exact VR.
      + right. exists elen. split; [lia|]. split; [lia|]. split; [f_equal; lia|]. split; [reflexivity|]. left. split; [exact NV| reflexivity].
    - assert (EV : v = 65037) by (revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). clear K0.
      apply evt_done. exists (Z_to_bv 64 v), (Z_to_bv 64 elen), (Z_to_bv 64 (bv_unsigned sp - 4096)), (Z_to_bv 64 (rem + -4)), m2, (Z_to_bv 64 (rem + -4)), (Z_to_bv 64 elen), v.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      + right. exact VR.
      + right. exists elen. split; [lia|]. split; [lia|]. split; [f_equal; lia|]. split; [reflexivity|]. right. split; [exact EV| rewrite EV; reflexivity].
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg3 :
    forall (sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur rem ee elen v : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w5 w6 w8 w11 w12 w13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : word),
      rw_cells rsegs m (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 ECH_VERSION) w8 (Z_to_bv 64 (rem + -4)) (Z_to_bv 64 elen) w11 w12 w13) ->
      rw_cells rsegs m (bv_unsigned sp + -192) (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) ->
      bytes_at rsegs m Bb bs -> Bb <= cur -> 0 <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil ->
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists (a0' a1' s4' s5' : word) m1 (w1' w3' w4' w6' f6 f7 f8 : word) c,
          munch [(bv_unsigned sp + -2344, bv_unsigned sp + -2336); (bv_unsigned sp + -2328, bv_unsigned sp + -2312);
                 (bv_unsigned sp + -2304, bv_unsigned sp + -2296); (ee + 49, ee + 50); (bv_unsigned sp + -144, bv_unsigned sp + -120)] m m1
          /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (bv_unsigned sp + -2352) (FRM w0 w1' w2 w3' w4' w5 w6' (Z_to_bv 64 ECH_VERSION) w8 (Z_to_bv 64 (rem + -4)) (Z_to_bv 64 elen) w11 w12 w13)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -192) (F3W v0 v1 v2 v3 v4 v5 f6 f7 f8 v9 v10)
          /\ rw_cells rsegs m1 ee (entry_cells (upd_cfgid E c) pad1 pad2 pad3 pad4) /\ (c = en_cfgid E \/ 0 <= c < 256) /\
         (  ms' = MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0' a1' a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 Bb) s4' s5' s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
                  F (Z_to_bv 64 DF_TA) fc None m1 (seg_rom rsegs)
         \/ (exists publen kemhi kemlo, 5 <= elen /\ 0 <= publen /\ 5 + publen <= elen /\ 0 <= kemhi < 256 /\ 0 <= kemlo < 256 /\ 0 <= c < 256 /\
             nth_error bs (Z.to_nat (cur - Bb + 4)) = Some (Z_to_bv 8 c) /\
             nth_error bs (Z.to_nat (cur - Bb + 5)) = Some (Z_to_bv 8 kemhi) /\ nth_error bs (Z.to_nat (cur - Bb + 6)) = Some (Z_to_bv 8 kemlo) /\
             w4' = Z_to_bv 64 (cur + 4) /\ w6' = Z_to_bv 64 kemlo /\ f6 = Z_to_bv 64 (cur + 9) /\ f7 = Z_to_bv 64 Bb /\ f8 = Z_to_bv 64 publen /\
             ms' = MS (mkR (Z_to_bv 64 DE_R3) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1
                           (Z_to_bv 64 (bv_unsigned sp + -144)) (Z_to_bv 64 (ee + 24)) (Z_to_bv 64 (ee + 16)) (Z_to_bv 64 (bv_unsigned sp - 4096)) a4 a5 a6 a7
                           s2 (Z_to_bv 64 Bb) (Z_to_bv 64 (elen - 5)) (Z_to_bv 64 publen) (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ee) s8 (Z_to_bv 64 kemhi) (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_PACKET_memdup) fc None m1 (seg_rom rsegs))))
        (MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 v) (Z_to_bv 64 ECH_VERSION) a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 Bb) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 (cur + 4)) s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) (Z_to_bv 64 374) t3 t4 t5 t6)
            F (Z_to_bv 64 DE_J1) fc None m (seg_rom rsegs)).
  Proof.
    intros until v10. intros FR F3 BS BC EL0 ER CR BP BH EC EEP EEH EBA HSP MI.
    unfold DE_R1, DE_R3, DE_J1, DF_TA, P_PACKET_memdup in *. unfold FRM in FR |- *. unfold F3W in F3 |- *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2352 <= bv_unsigned sp) by lia. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (munch_refl [(bv_unsigned sp + -2344, bv_unsigned sp + -2336); (bv_unsigned sp + -2328, bv_unsigned sp + -2312);
                 (bv_unsigned sp + -2304, bv_unsigned sp + -2296); (ee + 49, ee + 50); (bv_unsigned sp + -144, bv_unsigned sp + -120)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. step. step. s0slot. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (E0 : elen = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - EL0 ER CR BB BC; intros K0; lia). clear K0.
      apply evt_done. do 4 eexists. exists m, w1, w3, w4, w6, v6, v7, v8, (en_cfgid E).
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_cfgid_id; exact EC).
      - left. reflexivity.
      - left. reflexivity. }
    assert (E1 : 1 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - EL0 ER CR BB BC; intros K0; lia). clear K0.
    step. step. s0slot. st1.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 4))) as [c4|] eqn:N4; [| apply nth_error_None in N4; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N4 ltac:(lia) ltac:(lia)) as RD4. pose proof (byte_range c4) as C4R.
    replace (cur + 4) with (cur + 4 + 0) by lia. step. replace (cur + 4 + 0) with (cur + 4) by lia. change (zxb c4) with (Z_to_bv 64 (bv_unsigned c4)).
    st1. rewrite (Z.mod_small (bv_unsigned c4) 256) in EC by lia. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 4 eexists. exists m1, w1, w3, (Z_to_bv 64 (cur + 4)), w6, v6, v7, v8, (bv_unsigned c4).
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - right. exact C4R.
      - left. reflexivity. }
    assert (E3 : 3 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - EL0 ER CR BB BC; intros K0; lia). clear K0.
    step. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 4 eexists. exists m1, w1, w3, (Z_to_bv 64 (cur + 4)), w6, v6, v7, v8, (bv_unsigned c4).
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - right. exact C4R.
      - left. reflexivity. }
    assert (E5 : 5 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - EL0 ER CR BB BC E3; intros K0; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 7))) as [c7|] eqn:N7; [| apply nth_error_None in N7; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 8))) as [c8|] eqn:N8; [| apply nth_error_None in N8; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 5))) as [c5|] eqn:N5; [| apply nth_error_None in N5; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 6))) as [c6|] eqn:N6; [| apply nth_error_None in N6; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N7 ltac:(lia) ltac:(lia)) as RD7. pose proof (byte_range c7) as C7R.
    pose proof (pk_byte _ _ _ _ _ _ BS N8 ltac:(lia) ltac:(lia)) as RD8. pose proof (byte_range c8) as C8R.
    pose proof (pk_byte _ _ _ _ _ _ BS N5 ltac:(lia) ltac:(lia)) as RD5. pose proof (byte_range c5) as C5R.
    pose proof (pk_byte _ _ _ _ _ _ BS N6 ltac:(lia) ltac:(lia)) as RD6. pose proof (byte_range c6) as C6R.
    step. change (zxb c7) with (Z_to_bv 64 (bv_unsigned c7)). step. change (zxb c8) with (Z_to_bv 64 (bv_unsigned c8)).
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c7)) by lia. rewrite (unsigned_lit (bv_unsigned c7 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c8)) by lia.
    replace (Z.lor (bv_unsigned c7 * 2 ^ 8) (bv_unsigned c8)) with (bv_unsigned c8 + 256 * bv_unsigned c7)
      by (rewrite Z.lor_comm; replace (bv_unsigned c7 * 2 ^ 8) with (Z.shiftl (bv_unsigned c7) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned c8) (bv_unsigned c7)) by lia; lia).
    set (publen := bv_unsigned c8 + 256 * bv_unsigned c7) in *. assert (PLR : 0 <= publen < 2^16) by (subst publen; lia).
    step. step. s0slot. step. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 4 eexists. exists m1, w1, w3, (Z_to_bv 64 (cur + 4)), w6, v6, v7, v8, (bv_unsigned c4).
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - right. exact C4R.
      - left. reflexivity. }
    assert (EP : 5 + publen <= elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - E5 PLR ER CR BB BC; intros K0; lia). clear K0.
    step. change (zxb c5) with (Z_to_bv 64 (bv_unsigned c5)). step. change (zxb c6) with (Z_to_bv 64 (bv_unsigned c6)).
    step. step. s0slot. st1.
    step. st1. st1. st1. step. step. step. step. step. s0slot. st1. step. step. s0slot. st1. step.
    apply evt_done. do 4 eexists. match goal with MIx : mem_inv rsegs ?mx |- _ => exists mx end. exists (Z_to_bv 64 (ee + 24)), (Z_to_bv 64 (ee + 16)), (Z_to_bv 64 (cur + 4)), (Z_to_bv 64 (bv_unsigned c6)), (Z_to_bv 64 (cur + 9)), (Z_to_bv 64 Bb), (Z_to_bv 64 publen), (bv_unsigned c4).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - right. exact C4R.
    - right. exists publen, (bv_unsigned c5), (bv_unsigned c6). repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
      all: f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg4 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur rem ee elen publen : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
      rw_cells rsegs m (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) ->
      bytes_at rsegs m Bb bs -> Bb <= cur -> 0 <= publen -> 5 + publen <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil ->
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists (a0' a1' s4' s5' s6' : word) m1 (w5' : word) ns,
          munch [(bv_unsigned sp + -2312, bv_unsigned sp + -2304); (ee + 32, ee + 36)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5' w6 w7 w8 w9 w10 w11 w12 w13)
          /\ rw_cells rsegs m1 ee (entry_cells (upd_nsuites E ns) pad1 pad2 pad3 pad4) /\ (ns = en_nsuites E \/ 0 <= ns < 2^16) /\
         (  ms' = MS (mkR (Z_to_bv 64 DE_R3) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0' a1' a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 Bb) s4' s5' s6' (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
                  F (Z_to_bv 64 DF_TA) fc None m1 (seg_rom rsegs)
         \/ (exists so sohi solo, 0 <= solo < 256 /\ 0 <= sohi < 256 /\ so = solo + 256 * sohi /\ 2 <= so /\ so mod 2 = 0 /\ 5 + publen + 2 + so <= elen /\
             ns = so / 4 /\ 0 <= ns /\ w5' = Z_to_bv 64 (elen - 5 - publen - 2) /\
             nth_error bs (Z.to_nat (cur - Bb + (9 + publen))) = Some (Z_to_bv 8 sohi) /\ nth_error bs (Z.to_nat (cur - Bb + (10 + publen))) = Some (Z_to_bv 8 solo) /\
             ms' = MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1
                           (Z_to_bv 64 ns) (Z_to_bv 64 6) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 405) a4 a5 a6 a7
                           s2 (Z_to_bv 64 Bb) (Z_to_bv 64 so) (Z_to_bv 64 (cur + 9 + publen)) (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 ns) s9 (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m1 (seg_rom rsegs))))
        (MS (mkR (Z_to_bv 64 DE_R3) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 Bb) (Z_to_bv 64 (elen - 5)) (Z_to_bv 64 publen) (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) (Z_to_bv 64 400) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DE_R3)) fc None m (seg_rom rsegs)).
  Proof.
    intros until w13. intros FR BS BC PL0 EP ER CR BP BH EC EEP EEH EBA HSP MI.
    unfold DE_R3, DE_R4, DF_TA, P_CRYPTO_malloc_array, A_ECHS_FILE_RP in *. unfold FRM in FR |- *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA. retpc.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2352 <= bv_unsigned sp) by lia. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (munch_refl [(bv_unsigned sp + -2312, bv_unsigned sp + -2304); (ee + 32, ee + 36)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. br. step. step. step. if_cases K0; zify_cond K0.
    { apply evt_done. do 5 eexists. exists m, w5, (en_nsuites E).
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_nsuites_id; exact EC). all: try (left; reflexivity). }
    assert (E7 : 2 <= elen - 5 - publen) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_W64, Z.mod_small by lia; clear - PL0 EP ER CR BB BC; intros K0; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + (9 + publen)))) as [d0|] eqn:N9; [| apply nth_error_None in N9; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + (10 + publen)))) as [d1|] eqn:N10; [| apply nth_error_None in N10; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N9 ltac:(lia) ltac:(lia)) as RD9. pose proof (byte_range d0) as D0R.
    pose proof (pk_byte _ _ _ _ _ _ BS N10 ltac:(lia) ltac:(lia)) as RD10. pose proof (byte_range d1) as D1R.
    step. replace (cur + 9 + publen) with (cur + (9 + publen) + 0) by lia.
    step. change (zxb d0) with (Z_to_bv 64 (bv_unsigned d0)). replace (cur + (9 + publen) + 0 + 1) with (cur + (10 + publen)) by lia.
    step. change (zxb d1) with (Z_to_bv 64 (bv_unsigned d1)). replace (cur + (9 + publen) + 0) with (cur + 9 + publen) by lia.
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned d0)) by lia. rewrite (unsigned_lit (bv_unsigned d0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned d1)) by lia.
    replace (Z.lor (bv_unsigned d0 * 2 ^ 8) (bv_unsigned d1)) with (bv_unsigned d1 + 256 * bv_unsigned d0)
      by (rewrite Z.lor_comm; replace (bv_unsigned d0 * 2 ^ 8) with (Z.shiftl (bv_unsigned d0) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned d1) (bv_unsigned d0)) by lia; lia).
    set (so := bv_unsigned d1 + 256 * bv_unsigned d0) in *. assert (SOR : 0 <= so < 2^16) by (subst so; lia).
    step. step. step. s0slot. st1. rewrite (unsigned_lit publen) in FR by lia. try rewrite (unsigned_lit publen) by lia.
    step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 5 eexists. exists m0, (Z_to_bv 64 (elen - 5 + - publen + -2)), (en_nsuites E).
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_nsuites_id; exact EC). all: try (left; reflexivity). }
    assert (E9 : so <= elen - 5 - publen - 2) by (revert K0; rewrite ?unsigned_lit by lia; rewrite ?land_W64, ?Z.mod_small by lia; clear - PL0 EP ER CR BB BC E7 SOR; intros K0; lia). clear K0.
    step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 5 eexists. exists m0, (Z_to_bv 64 (elen - 5 + - publen + -2)), (en_nsuites E).
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_nsuites_id; exact EC). all: try (left; reflexivity). }
    assert (S1 : 1 <= so) by (revert K0; rewrite ?unsigned_lit by lia; clear - SOR; intros K0; lia). clear K0.
    step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 5 eexists. exists m0, (Z_to_bv 64 (elen - 5 + - publen + -2)), (en_nsuites E).
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_nsuites_id; exact EC). all: try (left; reflexivity). }
    assert (EVN : so mod 2 = 0).
    { revert K0. rewrite ?unsigned_lit by lia. rewrite land_1. subst so. clear - D0R D1R. intros K0.
      rewrite Z.add_mod by lia. replace (256 * bv_unsigned d0) with (128 * bv_unsigned d0 * 2) by lia. rewrite Z.mod_mul by lia. rewrite Z.add_0_r, Z.mod_mod by lia. lia. }
    clear K0.
    step. rewrite (unsigned_lit so) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
    assert (NS0 : 0 <= so / 4) by (apply Z.div_pos; clear - S1; lia).
    assert (NSR : so / 4 < 2^16) by (apply Z.div_lt_upper_bound; [lia|]; clear - SOR; lia).
    st1. do 7 step. replace (cur + (9 + publen)) with (cur + 9 + publen) by lia.
    apply evt_done. do 5 eexists. exists m1, (Z_to_bv 64 (elen - 5 + - publen + -2)), (so / 4).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - right. split; [exact NS0| exact NSR].
    - right. exists so, (bv_unsigned d0), (bv_unsigned d1). repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear - S1 EVN SOR E9 NS0 D0R D1R; lia).
      all: f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg5 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur ee so q solo ns kemhi kemlo SA : Z) (lenbs : Z) (E : entrep) (o : oblk) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w11 w12 w13 : word),
      rw_cells rsegs m (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5 (Z_to_bv 64 kemlo) w7 w8 w9 w10 w11 w12 w13) ->
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil ->
      0 <= SA -> SA + 6 * ns <= hceil -> 0 <= kemhi < 256 -> 0 <= kemlo < 256 -> 0 <= ns < 2^16 -> 0 <= so < 2^16 -> 0 < Bb -> q + so <= lenbs -> Bb + lenbs <= hceil ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          munch [(ee + 40, ee + 48)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 ee (entry_cells (upd_suites E SA o) pad1 pad2 pad3 pad4) /\
         (  (SA = 0 /\
             ms' = MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7
                           s2 (Z_to_bv 64 Bb) (Z_to_bv 64 so) (Z_to_bv 64 (Bb + q)) (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 ns) (Z_to_bv 64 kemhi) (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 DF_TZ) fc None m1 (seg_rom rsegs))
         \/ (0 < SA /\
             ms' = MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 (Z_to_bv 64 (-1)) t2 sp s1
                           (Z_to_bv 64 (SA + 4)) (Z_to_bv 64 (Bb + q + 2)) (Z_to_bv 64 (- ns)) (Z_to_bv 64 (256 * kemhi + kemlo)) (Z_to_bv 64 (-1)) a5 a6 a7
                           s2 (Z_to_bv 64 Bb) (Z_to_bv 64 so) (Z_to_bv 64 (Bb + q)) (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 (Bb + q + 2 + so)) (Z_to_bv 64 (kemhi * 2^8)) (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 DE_LH) fc None m1 (seg_rom rsegs))))
        (MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 Bb) (Z_to_bv 64 so) (Z_to_bv 64 (Bb + q)) (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 ns) (Z_to_bv 64 kemhi) (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DE_R4)) fc None m (seg_rom rsegs)).
  Proof.
    intros until w13. intros FR EC EEP EEH SA0 SAH KH KL NS0 SOR BP QB BH HSP MI.
    unfold DE_R4, DE_LH, DF_TZ in *. unfold FRM in FR |- *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH. retpc.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2352 <= bv_unsigned sp) by lia.
    pose proof (munch_refl [(ee + 40, ee + 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    st1. step. if_cases K0; zify_cond K0.
    - assert (Z0 : SA = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - SA0 SAH HCEILB; intros K0; lia). clear K0.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [exact Z0| reflexivity].
    - assert (Z1 : 0 < SA) by (revert K0; rewrite ?unsigned_lit by lia; clear - SA0 SAH HCEILB; intros K0; lia). clear K0.
      step. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit kemhi) by lia. step. step. step. rewrite (unsigned_lit ns) by lia. replace (0 + - ns) with (- ns) by lia.
      step. step. s0slot. step. unfold wz. step.
      rewrite (unsigned_lit (kemhi * 2 ^ 8)) by lia. rewrite (unsigned_lit kemlo) by lia.
      replace (Z.lor (kemhi * 2 ^ 8) kemlo) with (256 * kemhi + kemlo)
        by (rewrite Z.lor_comm; replace (kemhi * 2 ^ 8) with (Z.shiftl kemhi 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add kemlo kemhi) by lia; lia).
      step. step. step.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact Z1|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma de_loop : forall (k : nat) (i : Z) (sp gp tp t0 t2 s1 a5 a6 a7 s2 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur ee so q solo ns kem kh SA : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4 junk,
      Z.of_nat k = ns - i -> 0 <= i <= ns -> en_nsuites E = ns -> 0 <= ns < 2^16 -> 0 <= kem < 2^16 ->
      rw_cells rsegs m (SA + 6 * i) [CB (Z.to_nat (6 * (ns - i))) junk] -> 0 < SA -> SA + 6 * ns <= hceil ->
      bytes_at rsegs m Bb bs -> 0 < Bb -> 0 <= q -> q + 2 + 4 * ns <= zlength bs -> Bb + zlength bs <= hceil -> (SA + 6 * ns <= Bb \/ Bb + zlength bs <= SA) ->
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> (SA + 6 * ns <= ee \/ ee + ENTRY_SIZE <= SA) ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists (t0' a5' a6' a7' : word) m1 junk',
          munch [(SA + 6 * i, SA + 6 * ns)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (SA + 6 * i) (suite_cells (srows bs (Z.to_nat (q + 2 + 4 * i)) kem k) ++ [CB 0 junk'])
          /\ bytes_at rsegs m1 Bb bs /\ rw_cells rsegs m1 ee (entry_cells E pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0' (Z_to_bv 64 (-1)) t2 sp s1
                        (Z_to_bv 64 (SA + 4 + 6 * ns)) (Z_to_bv 64 (Bb + q + 2 + 4 * ns)) (Z_to_bv 64 (- ns)) (Z_to_bv 64 kem) (Z_to_bv 64 (ns - 1)) a5' a6' a7'
                        s2 (Z_to_bv 64 Bb) (Z_to_bv 64 so) (Z_to_bv 64 (Bb + q)) (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 (Bb + q + 2 + so)) (Z_to_bv 64 kh) (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 DE_J2) fc None m1 (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 (Z_to_bv 64 (-1)) t2 sp s1
                 (Z_to_bv 64 (SA + 4 + 6 * i)) (Z_to_bv 64 (Bb + q + 2 + 4 * i)) (Z_to_bv 64 (- ns)) (Z_to_bv 64 kem) (Z_to_bv 64 (i - 1)) a5 a6 a7
                 s2 (Z_to_bv 64 Bb) (Z_to_bv 64 so) (Z_to_bv 64 (Bb + q)) (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 (Bb + q + 2 + so)) (Z_to_bv 64 kh) (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DE_LH) fc None m (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros until junk; intros HK IR NSE NSR KR SC SAP SAH BS BP Q0 QB BH SBA EC EEP EEH SEA HSP MI.
    - (* [comment removed for export] *)
      unfold DE_LH, DE_J2 in *. hcb. pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
      assert (IE : i = ns) by lia. subst i.
      pose proof (munch_refl [(SA + 6 * ns, SA + 6 * ns)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      step. step. if_cases K0; zify_cond K0. 2: { exfalso. revert K0. rewrite land_W64. replace (- ns + (ns - 1)) with (-1) by lia. intros K0. apply K0. reflexivity. }
      apply evt_done. exists t0, (Z_to_bv 64 (- ns + (ns - 1))), a6, a7, m, junk.
      repeat match goal with |- _ /\ _ => split end; try assumption. cbn [srows suite_cells app]. rewrite Z.sub_diag in SC. exact SC. reflexivity.
    - (* [comment removed for export] *)
      unfold DE_LH, DE_J2 in *. hcb. pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *. unfold entry_cells in EC. unfold ENTRY_SIZE in *.
      assert (IL : i < ns) by lia.
      pose proof (munch_refl [(SA + 6 * i, SA + 6 * ns)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      step. step. if_cases K0; zify_cond K0.
      { exfalso. revert K0. rewrite land_W64. rewrite mod64_neg by lia. clear - IL IR NSR. lia. }
      clear K0.
      destruct (nth_error bs (Z.to_nat (q + 2 + 4 * i + 0))) as [e0|] eqn:M0; [| apply nth_error_None in M0; lia].
      destruct (nth_error bs (Z.to_nat (q + 2 + 4 * i + 1))) as [e1|] eqn:M1; [| apply nth_error_None in M1; lia].
      destruct (nth_error bs (Z.to_nat (q + 2 + 4 * i + 2))) as [e2|] eqn:M2; [| apply nth_error_None in M2; lia].
      destruct (nth_error bs (Z.to_nat (q + 2 + 4 * i + 3))) as [e3|] eqn:M3; [| apply nth_error_None in M3; lia].
      pose proof (pk_byte m Bb bs (Bb + q + 2 + 4 * i) 0 e0 BS ltac:(replace (Bb + q + 2 + 4 * i - Bb + 0) with (q + 2 + 4 * i + 0) by lia; exact M0) ltac:(lia) ltac:(lia)) as RD0.
      pose proof (pk_byte m Bb bs (Bb + q + 2 + 4 * i) 1 e1 BS ltac:(replace (Bb + q + 2 + 4 * i - Bb + 1) with (q + 2 + 4 * i + 1) by lia; exact M1) ltac:(lia) ltac:(lia)) as RD1.
      pose proof (pk_byte m Bb bs (Bb + q + 2 + 4 * i) 2 e2 BS ltac:(replace (Bb + q + 2 + 4 * i - Bb + 2) with (q + 2 + 4 * i + 2) by lia; exact M2) ltac:(lia) ltac:(lia)) as RD2.
      pose proof (pk_byte m Bb bs (Bb + q + 2 + 4 * i) 3 e3 BS ltac:(replace (Bb + q + 2 + 4 * i - Bb + 3) with (q + 2 + 4 * i + 3) by lia; exact M3) ltac:(lia) ltac:(lia)) as RD3.
      pose proof (byte_range e0) as E0R. pose proof (byte_range e1) as E1R. pose proof (byte_range e2) as E2R. pose proof (byte_range e3) as E3R.
      step. change (zxb e0) with (Z_to_bv 64 (bv_unsigned e0)). step. change (zxb e1) with (Z_to_bv 64 (bv_unsigned e1)).
      step. change (zxb e2) with (Z_to_bv 64 (bv_unsigned e2)). step. change (zxb e3) with (Z_to_bv 64 (bv_unsigned e3)).
      step. step.
      rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned e0)) by lia. rewrite (unsigned_lit (bv_unsigned e0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned e1)) by lia.
      replace (Z.lor (bv_unsigned e0 * 2 ^ 8) (bv_unsigned e1)) with (256 * bv_unsigned e0 + bv_unsigned e1)
        by (rewrite Z.lor_comm; replace (bv_unsigned e0 * 2 ^ 8) with (Z.shiftl (bv_unsigned e0) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned e1) (bv_unsigned e0)) by lia; lia).
      step. rewrite NSE. unfold zx32. rewrite wz_unsigned by lia. rewrite (Z.mod_small ns) by lia.
      step. replace (i - 1 + 1) with i by lia.
      step. step.
      rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned e2)) by lia. rewrite (unsigned_lit (bv_unsigned e2 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned e3)) by lia.
      replace (Z.lor (bv_unsigned e2 * 2 ^ 8) (bv_unsigned e3)) with (256 * bv_unsigned e2 + bv_unsigned e3)
        by (rewrite Z.lor_comm; replace (bv_unsigned e2 * 2 ^ 8) with (Z.shiftl (bv_unsigned e2) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned e3) (bv_unsigned e2)) by lia; lia).
      replace (SA + 4 + 6 * i) with (SA + 6 * i + 4) by lia.
      match goal with SCx : rw_cells rsegs ?mx (SA + 6 * i) [CB _ junk] |- _ =>
        pose proof (rw_cells_split_CB rsegs mx (SA + 6 * i) [] (Z.to_nat (6 * (ns - i))) junk [] [6%nat; Z.to_nat (6 * (ns - (i + 1)))] SCx ltac:(cbn [sum_nat]; lia)) as SC2;
        clear SCx; cbn [mk_CB_cells app] in SC2 end.
      set (Q := SA + 6 * i) in *.
      st1. st1. st1. subst Q. step. step. step. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; clear - IL; lia]. clear K0.
      replace (SA + 6 * i + 10) with (SA + 4 + 6 * (i + 1)) by lia. replace (Bb + q + 2 + 4 * i + 4) with (Bb + q + 2 + 4 * (i + 1)) by lia.
      replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + 1 - 1)) by (f_equal; lia).
      pose proof (proj1 (rw_cells_app rsegs m0 (SA + 6 * i) [C2 (Z_to_bv 64 kem); C2 (Z_to_bv 64 (256 * bv_unsigned e0 + bv_unsigned e1)); C2 (Z_to_bv 64 (256 * bv_unsigned e2 + bv_unsigned e3))] _) SC2) as [SC3 SC4].
      cbn [cells_size csize Nat.add] in SC4. replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) in SC4 by lia.
      eapply evt_mono.
      { eapply (IH (i + 1)); try eassumption; try (unfold entry_cells; eassumption); rewrite ?Nat2Z.inj_succ in HK; clear - HK IL IR; lia. }
      cbv beta. intros ms' (t0' & a5' & a6' & a7' & m1 & junk' & MU1 & WM1 & MI1 & SC5 & BS1 & EC1 & ->).
      exists t0', a5', a6', a7', m1, junk'. repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia.
      + eapply wmono_trans; [exact WM| exact WM1].
      + cbn [srows suite_cells app]. replace (Z.to_nat (q + 2 + 4 * (i + 1))) with (4 + Z.to_nat (q + 2 + 4 * i))%nat in SC5 by lia.
        unfold bz. replace (Z.to_nat (q + 2 + 4 * i)) with (Z.to_nat (q + 2 + 4 * i + 0)) by lia. rewrite M0.
        replace (S (Z.to_nat (q + 2 + 4 * i + 0))) with (Z.to_nat (q + 2 + 4 * i + 1)) by lia. rewrite M1.
        replace (S (Z.to_nat (q + 2 + 4 * i + 1))) with (Z.to_nat (q + 2 + 4 * i + 2)) by lia. rewrite M2.
        replace (S (Z.to_nat (q + 2 + 4 * i + 2))) with (Z.to_nat (q + 2 + 4 * i + 3)) by lia. rewrite M3.
        apply (proj2 (rw_cells_app rsegs m1 (SA + 6 * i) [C2 (wz kem); C2 (wz (256 * bv_unsigned e0 + bv_unsigned e1)); C2 (wz (256 * bv_unsigned e2 + bv_unsigned e3))] _)). split.
        * eapply rw_cells_transport; [exact SC3| exact MU1| exact WM1| cbn; lia].
        * cbn [cells_size csize Nat.add]. replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) by lia. fold bz in SC5.
          replace (S (S (S (S (Z.to_nat (q + 2 + 4 * i + 0)))))) with (4 + Z.to_nat (q + 2 + 4 * i))%nat by lia. exact SC5.
      + reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg7 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur ee so q solo r2 : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : word),
      rw_cells rsegs m (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 (Z_to_bv 64 r2) w6 w7 w8 w9 w10 w11 w12 w13) ->
      rw_cells rsegs m (bv_unsigned sp + -192) (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) ->
      bytes_at rsegs m Bb bs -> 0 <= q -> 0 <= so -> so <= r2 -> q + 2 + r2 <= zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil ->
      so = solo mod 256 + 256 * (so / 256) -> 0 <= solo < 256 -> so mod 2 = 0 ->
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists (a0' a1' a2' s4' s8' s9' : word) m1 (f3 f4 f5 : word) mx line,
          munch [(ee + 48, ee + 49); (bv_unsigned sp + -168, bv_unsigned sp + -144)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (bv_unsigned sp + -192) (F3W v0 v1 v2 f3 f4 f5 v6 v7 v8 v9 v10)
          /\ rw_cells rsegs m1 ee (entry_cells (upd_maxname E mx) pad1 pad2 pad3 pad4) /\ (mx = en_maxname E \/ 0 <= mx < 256) /\
         (  ((line = 420 \/ line = 425) /\
             ms' = MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3 a4 a5 a6 a7
                           s2 (Z_to_bv 64 Bb) s4' s5 (Z_to_bv 64 solo) (Z_to_bv 64 ee) s8' s9' (Z_to_bv 64 cur) (Z_to_bv 64 line) t3 t4 t5 t6)
                      F (Z_to_bv 64 DF_TA) fc None m1 (seg_rom rsegs))
         \/ (exists nl, so + 2 <= r2 /\ 0 <= nl < 256 /\ so + 2 + nl <= r2 /\ 0 <= mx < 256 /\
             nth_error bs (Z.to_nat (q + 2 + so)) = Some (Z_to_bv 8 mx) /\ nth_error bs (Z.to_nat (q + 2 + so + 1)) = Some (Z_to_bv 8 nl) /\
             f3 = Z_to_bv 64 (Bb + q + 2 + so + 2) /\ f4 = Z_to_bv 64 Bb /\ f5 = Z_to_bv 64 nl /\
             ms' = MS (mkR (Z_to_bv 64 DE_R5) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1
                           (Z_to_bv 64 (Bb + q + 2 + so + 2)) (Z_to_bv 64 0) (Z_to_bv 64 nl) a3 a4 a5 a6 a7
                           s2 (Z_to_bv 64 Bb) (Z_to_bv 64 (r2 - so - 2)) s5 (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 (Bb + q + 2 + so + 2)) (Z_to_bv 64 nl) (Z_to_bv 64 cur) (Z_to_bv 64 425) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_memchr) fc None m1 (seg_rom rsegs))))
        (MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 Bb) (Z_to_bv 64 so) s5 (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 (Bb + q + 2 + so)) s9 (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DE_J2) fc None m (seg_rom rsegs)).
  Proof.
    intros until v10. intros FR F3 BS Q0 S0 SR QB BP BH SOLO SOL EVN EC EEP EEH EBA HSP MI.
    unfold DE_R4, DE_R5, DE_J2, DF_TA, P_memchr in *. unfold FRM in FR. unfold F3W in F3 |- *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2352 <= bv_unsigned sp) by lia. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (munch_refl [(ee + 48, ee + 49); (bv_unsigned sp + -168, bv_unsigned sp + -144)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. step. step. s0slot. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 6 eexists. exists m, v3, v4, v5, (en_maxname E), 420.
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_maxname_id; exact EC). all: try (left; reflexivity).
      left. split; [left; reflexivity| reflexivity]. }
    assert (NE : r2 <> so) by (revert K0; rewrite ?unsigned_lit by lia; clear - S0 SR QB BB; intros K0; lia). clear K0.
    step. step. if_cases K0; zify_cond K0.
    { apply evt_done. do 6 eexists. exists m, v3, v4, v5, (en_maxname E), 420.
      repeat match goal with |- _ /\ _ => split end; try assumption; try (rewrite upd_maxname_id; exact EC). all: try (left; reflexivity).
      left. split; [left; reflexivity| reflexivity]. }
    clear K0. assert (SR2 : so + 1 <= r2) by (clear - SR NE; lia).
    destruct (nth_error bs (Z.to_nat (q + 2 + so))) as [g0|] eqn:G0; [| apply nth_error_None in G0; lia].
    pose proof (pk_byte m Bb bs (Bb + q + 2 + so) 0 g0 BS ltac:(replace (Bb + q + 2 + so - Bb + 0) with (q + 2 + so) by lia; exact G0) ltac:(lia) ltac:(lia)) as RG0.
    pose proof (byte_range g0) as G0R.
    step. change (zxb g0) with (Z_to_bv 64 (bv_unsigned g0)).
    step. step. step. s0slot. step. step. rewrite (unsigned_lit so) by lia. rewrite add_not64 by lia.
    st1. rewrite (Z.mod_small (bv_unsigned g0) 256) in EC by lia.
    step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 6 eexists. exists m0, v3, v4, v5, (bv_unsigned g0), 425.
      repeat match goal with |- _ /\ _ => split end; try assumption. all: try (right; exact G0R).
      left. split; [right; reflexivity| reflexivity]. }
    assert (SR3 : so + 2 <= r2) by (revert K0; rewrite ?unsigned_lit by lia; clear - SR2 QB BB S0; intros K0; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (q + 2 + so + 1))) as [g1|] eqn:G1; [| apply nth_error_None in G1; lia].
    pose proof (pk_byte m0 Bb bs (Bb + q + 2 + so) 1 g1 BS ltac:(replace (Bb + q + 2 + so - Bb + 1) with (q + 2 + so + 1) by lia; exact G1) ltac:(lia) ltac:(lia)) as RG1.
    pose proof (byte_range g1) as G1R.
    step. change (zxb g1) with (Z_to_bv 64 (bv_unsigned g1)). step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      apply evt_done. do 6 eexists. exists m0, v3, v4, v5, (bv_unsigned g0), 425.
      repeat match goal with |- _ /\ _ => split end; try assumption. all: try (right; exact G0R).
      left. split; [right; reflexivity| reflexivity]. }
    assert (SR4 : so + 2 + bv_unsigned g1 <= r2) by (revert K0; rewrite ?unsigned_lit by lia; clear - SR3 QB BB S0 G1R; intros K0; lia). clear K0.
    step. st1. st1. st1. step. step. step. step. replace (r2 - so - 1 + -1) with (r2 - so - 2) by lia.
    apply evt_done. do 6 eexists. match goal with MIx : mem_inv rsegs ?mx |- _ => exists mx end. exists (Z_to_bv 64 (Bb + q + 2 + so + 2)), (Z_to_bv 64 Bb), (Z_to_bv 64 (bv_unsigned g1)), (bv_unsigned g0), 425.
    repeat match goal with |- _ /\ _ => split end; try assumption. all: try (right; exact G0R).
    right. exists (bv_unsigned g1). repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear - SR4 G1R G0R; lia).
    all: try (f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned).
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg8 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee nl res : Z),
      0 <= res < 2^64 -> 0 <= nl < 256 -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
            ((nl < 4 \/ res <> 0) /\
             ms' = MS (mkR (Z_to_bv 64 DE_R5) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 res) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 (Z_to_bv 64 nl) s10 (Z_to_bv 64 431) t3 t4 t5 t6)
                      F (Z_to_bv 64 DF_TA) fc None m (seg_rom rsegs))
         \/ (4 <= nl /\ res = 0 /\
             ms' = MS (mkR (Z_to_bv 64 DE_R6) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (bv_unsigned sp + -168)) (Z_to_bv 64 (ee + 8)) a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 (Z_to_bv 64 nl) s10 (Z_to_bv 64 431) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom rsegs)))
        (MS (mkR (Z_to_bv 64 DE_R5) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 (Z_to_bv 64 nl) s10 (Z_to_bv 64 425) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DE_R5)) fc None m (seg_rom rsegs)).
  Proof.
    intros until res. intros RR NL EEP EEH HSP MI. unfold DE_R5, DE_R6, DF_TA, P_PACKET_strndup in *. unfold ENTRY_SIZE in EEH. retpc.
    hcb. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. step. step. if_cases K0; zify_cond K0.
    { apply evt_done. left. split; [left; revert K0; rewrite ?unsigned_lit by lia; clear; lia| reflexivity]. }
    assert (N4 : 4 <= nl) by (revert K0; rewrite ?unsigned_lit by lia; clear; lia). clear K0.
    step. if_cases K0; zify_cond K0.
    { apply evt_done. left. split; [right; revert K0; rewrite ?unsigned_lit by lia; clear; lia| reflexivity]. }
    assert (R0 : res = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear; lia). clear K0.
    step. step. step. apply evt_done. right. split; [exact N4|]. split; [exact R0|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg9 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb cur ee np nl left : Z) (bs : list byte)
           (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : word),
      rw_cells rsegs m (bv_unsigned sp + -192) (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) ->
      bytes_at rsegs m Bb bs -> Bb <= np -> 0 <= nl -> nl <= left -> np + left <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= hceil -> 0 <= left < 2^16 ->
      0 < ee -> ee + ENTRY_SIZE <= hceil -> hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists (a0' a1' a2' s4' s5' : word) m1 (f0 f1 f2 : word),
          munch [(bv_unsigned sp + -192, bv_unsigned sp + -168)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (bv_unsigned sp + -192) (F3W f0 f1 f2 v3 v4 v5 v6 v7 v8 v9 v10) /\
         (  ms' = MS (mkR (Z_to_bv 64 DE_R6) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0' a1' a2' a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 Bb) s4' s5' s6 (Z_to_bv 64 ee) (Z_to_bv 64 np) (Z_to_bv 64 nl) (Z_to_bv 64 cur) (Z_to_bv 64 442) t3 t4 t5 t6)
                  F (Z_to_bv 64 DF_TA) fc None m1 (seg_rom rsegs)
         \/ (exists xl, 0 <= xl /\ nl + 2 + xl <= left /\ f0 = Z_to_bv 64 (np + nl + 2) /\ f1 = Z_to_bv 64 Bb /\ f2 = Z_to_bv 64 xl /\
             (  (xl = 0 /\
                 ms' = MS (mkR (Z_to_bv 64 DE_R6) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (left - nl - 2)) a1' a2' a3 a4 a5 a6 a7
                               s2 (Z_to_bv 64 Bb) (Z_to_bv 64 xl) (Z_to_bv 64 (np + nl + 2)) s6 (Z_to_bv 64 ee) (Z_to_bv 64 np) (Z_to_bv 64 nl) (Z_to_bv 64 cur) (Z_to_bv 64 442) t3 t4 t5 t6)
                          F (Z_to_bv 64 DE_J3) fc None m1 (seg_rom rsegs))
             \/ (1 <= xl /\
                 ms' = MS (mkR (Z_to_bv 64 DE_R7) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 ee) (Z_to_bv 64 (bv_unsigned sp + -192)) a2' a3 a4 a5 a6 a7
                               s2 (Z_to_bv 64 Bb) (Z_to_bv 64 xl) (Z_to_bv 64 (np + nl + 2)) s6 (Z_to_bv 64 ee) (Z_to_bv 64 np) (Z_to_bv 64 nl) (Z_to_bv 64 cur) (Z_to_bv 64 442) t3 t4 t5 t6)
                          F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m1 (seg_rom rsegs))))))
        (MS (mkR (Z_to_bv 64 DE_R6) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 Bb) (Z_to_bv 64 left) s5 s6 (Z_to_bv 64 ee) (Z_to_bv 64 np) (Z_to_bv 64 nl) (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DE_R6)) fc None m (seg_rom rsegs)).
  Proof.
    intros until v10. intros F3 BS BN NL0 NLL NB BP BH LR EEP EEH HSP MI.
    unfold DE_R6, DE_R7, DE_J3, DF_TA, P_ech_decode_echconfig_exts in *. unfold F3W in F3 |- *. unfold ENTRY_SIZE in EEH. retpc.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2352 <= bv_unsigned sp) by lia. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp + -168)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. br. step. step. step. step. if_cases K0; zify_cond K0.
    { apply evt_done. do 5 eexists. exists m, v0, v1, v2. repeat match goal with |- _ /\ _ => split end; try assumption. left. reflexivity. }
    assert (L2 : 2 <= left - nl) by (revert K0; rewrite ?unsigned_lit by lia; rewrite ?land_W64, ?Z.mod_small by lia; clear - NL0 NLL LR; intros K0; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (np + nl - Bb + 0))) as [h0|] eqn:H0; [| apply nth_error_None in H0; lia].
    destruct (nth_error bs (Z.to_nat (np + nl - Bb + 1))) as [h1|] eqn:H1; [| apply nth_error_None in H1; lia].
    pose proof (pk_byte m Bb bs (np + nl) 0 h0 BS H0 ltac:(lia) ltac:(lia)) as RH0. pose proof (byte_range h0) as H0R.
    pose proof (pk_byte m Bb bs (np + nl) 1 h1 BS H1 ltac:(lia) ltac:(lia)) as RH1. pose proof (byte_range h1) as H1R.
    step. step. change (zxb h0) with (Z_to_bv 64 (bv_unsigned h0)). step. change (zxb h1) with (Z_to_bv 64 (bv_unsigned h1)).
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned h0)) by lia. rewrite (unsigned_lit (bv_unsigned h0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned h1)) by lia.
    replace (Z.lor (bv_unsigned h0 * 2 ^ 8) (bv_unsigned h1)) with (bv_unsigned h1 + 256 * bv_unsigned h0)
      by (rewrite Z.lor_comm; replace (bv_unsigned h0 * 2 ^ 8) with (Z.shiftl (bv_unsigned h0) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned h1) (bv_unsigned h0)) by lia; lia).
    set (xl := bv_unsigned h1 + 256 * bv_unsigned h0) in *. assert (XLR : 0 <= xl < 2^16) by (subst xl; lia).
    step. step. if_cases K0; zify_cond K0.
    { apply evt_done. do 5 eexists. exists m, v0, v1, v2. repeat match goal with |- _ /\ _ => split end; try assumption. left. reflexivity. }
    assert (L3 : xl <= left - nl - 2) by (revert K0; rewrite ?unsigned_lit by lia; rewrite ?land_W64, ?Z.mod_small by lia; clear - NL0 NLL LR L2 XLR; intros K0; lia). clear K0.
    step. st1. st1. st1. replace (np + nl + 0 + 2) with (np + nl + 2) by lia. step. if_cases K0; zify_cond K0.
    - assert (X0 : xl = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - XLR; intros K0; lia). clear K0.
      apply evt_done. do 5 eexists. match goal with MIx : mem_inv rsegs ?mx |- _ => exists mx end. exists (Z_to_bv 64 (np + nl + 2)), (Z_to_bv 64 Bb), (Z_to_bv 64 xl). repeat match goal with |- _ /\ _ => split end; try assumption.
      right. exists xl. repeat match goal with |- _ /\ _ => split end; try reflexivity; try (clear - L3 X0 XLR; lia). left. split; [exact X0|].
      replace (left - nl + -2) with (left - nl - 2) by lia. reflexivity.
    - assert (X1 : 1 <= xl) by (revert K0; rewrite ?unsigned_lit by lia; clear - XLR; intros K0; lia). clear K0.
      step. step. step.
      apply evt_done. do 5 eexists. match goal with MIx : mem_inv rsegs ?mx |- _ => exists mx end. exists (Z_to_bv 64 (np + nl + 2)), (Z_to_bv 64 Bb), (Z_to_bv 64 xl). repeat match goal with |- _ /\ _ => split end; try assumption.
      right. exists xl. repeat match goal with |- _ /\ _ => split end; try reflexivity; try (clear - L3 X1 XLR; lia). right. split; [exact X1| reflexivity].
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg10 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv : Z),
      (rv = 0 \/ rv = 1) -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
            (rv = 0 /\ ms' = MS (mkR (Z_to_bv 64 DE_R7) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 447) t3 t4 t5 t6)
                                    F (Z_to_bv 64 DF_TA) fc None m (seg_rom rsegs))
         \/ (rv = 1 /\ ms' = MS (mkR (Z_to_bv 64 DE_R7) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 DE_J3) fc None m (seg_rom rsegs)))
        (MS (mkR (Z_to_bv 64 DE_R7) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DE_R7)) fc None m (seg_rom rsegs)).
  Proof.
    intros until rv. intros RV MI. unfold DE_R7, DE_J3, DF_TA in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. step. step. apply evt_done. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; clear - RV; intros K0; lia). clear K0. apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg11 :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s8 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (cur ee xp xl : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> cur <= xp + xl -> 0 < cur -> xp + xl <= hceil ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          munch [(ee + 88, ee + 96)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 ee (entry_cells (upd_enclen E (xp + xl - cur)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 DE_R8) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1
                        (Z_to_bv 64 cur) (Z_to_bv 64 (xp + xl - cur)) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 453) a4 a5 a6 a7
                        s2 s3 (Z_to_bv 64 (xp + xl)) (Z_to_bv 64 xp) s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m1 (seg_rom rsegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 xl) (Z_to_bv 64 xp) s6 (Z_to_bv 64 ee) s8 s9 (Z_to_bv 64 cur) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DE_J3) fc None m (seg_rom rsegs)).
  Proof.
    intros until pad4. intros EC EEP EEH XC CP XH HSP MI. unfold DE_R8, DE_J3, P_CRYPTO_memdup, A_ECHS_FILE_RP in *. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH.
    hcb. pose proof (word_range sp) as SPR.
    pose proof (munch_refl [(ee + 88, ee + 96)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. step. rewrite ?unsigned_lit by lia. rewrite ?land_W64, ?Z.mod_small by lia. st1. do 6 step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma de_seg12 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee EA : Z) (E : entrep) (o : oblk) pad1 pad2 pad3 pad4
           (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
      rw_cells rsegs m (bv_unsigned sp + -2352) (FRM w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 0)) ->
      rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= hceil -> 0 <= EA < 2^64 ->
      hceil <= bv_unsigned sp + -2352 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists (a0' : word) m1,
          munch [(ee + 96, ee + 104)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 ee (entry_cells (upd_encoded E EA o) pad1 pad2 pad3 pad4) /\
         (  (EA = 0 /\ ms' = MS (mkR (Z_to_bv 64 DE_R8) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 DF_TZ) fc None m1 (seg_rom rsegs))
         \/ (0 < EA /\ ms' = MS (mkR (Z_to_bv 64 DE_R8) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 DF_OK) fc None m1 (seg_rom rsegs))))
        (MS (mkR (Z_to_bv 64 DE_R8) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 EA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ee) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DE_R8)) fc None m (seg_rom rsegs)).
  Proof.
    intros until w12. intros FR EC EEP EEH EAR HSP MI. unfold DE_R8, DF_TZ, DF_OK in *. unfold FRM in FR. unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH. retpc.
    hcb. pose proof (word_range sp) as SPR. assert (SPL : 2352 <= bv_unsigned sp) by lia.
    pose proof (munch_refl [(ee + 96, ee + 104)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    st1. step. if_cases K0; zify_cond K0.
    - assert (Z0 : EA = 0) by (revert K0; rewrite ?unsigned_lit by lia; clear - EAR; intros K0; lia). clear K0.
      apply evt_done. do 2 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [exact Z0| reflexivity].
    - assert (Z1 : 0 < EA) by (revert K0; rewrite ?unsigned_lit by lia; clear - EAR; intros K0; lia). clear K0.
      step. step. s0slot. step. step. if_lit.
      apply evt_done. do 2 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact Z1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma de_skipret :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 DE_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DF_ADV) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 DE_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 DE_R2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI. unfold DE_R2, DF_ADV. retpc. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. apply evt_done. reflexivity.
  Qed.
End S.
