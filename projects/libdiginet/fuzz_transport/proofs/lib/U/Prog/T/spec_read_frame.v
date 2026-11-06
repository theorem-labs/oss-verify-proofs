From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract spec_read_frame_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the frame buffer: one byte of fr read through the machine ---- *)

Lemma srf_firstn1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma srf_byte_at : forall (fr : list byte) i, 0 <= i < Z.of_nat (length fr) ->
  byte_at (zs fr) i = bv_unsigned (nth (Z.to_nat i) fr (Z_to_bv 8 0)).
Proof.
  intros fr i Hi. unfold byte_at, zs.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  apply map_nth.
Qed.

Lemma srf_byte_all : forall (fr : list byte) k, 0 <= byte_at (zs fr) k < 256.
Proof.
  intros fr k. unfold byte_at, zs.
  destruct (Nat.lt_ge_cases (Z.to_nat k) (length fr)) as [L|L].
  - rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact L).
    rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) fr (Z_to_bv 8 0))) as R.
    unfold bv_modulus in R. exact R.
  - rewrite nth_overflow by (rewrite length_map; exact L). lia.
Qed.

Lemma srf_rd1 : forall m p (fr : list byte) i, bytes_at rsegs m p fr -> 0 <= i < Z.of_nat (length fr) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (p + i)) 1 = Some [Z_to_bv 8 (byte_at (zs fr) i)].
Proof.
  intros m p fr i B Hi.
  pose proof (bytes_at_read rsegs m p fr i 1 B ltac:(lia) ltac:(lia)) as R. unfold wa in R. rewrite R.
  rewrite (srf_firstn1 fr (Z.to_nat i) (Z_to_bv 8 0)) by lia.
  rewrite srf_byte_at by exact Hi. f_equal. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small; [reflexivity | apply bv_unsigned_in_range].
Qed.

Lemma srf_uz8 : forall x, 0 <= x < 256 -> bv_unsigned (zxb (Z_to_bv 8 x)) = x.
Proof.
  intros x Hx. unfold zxb.
  assert (E : bv_unsigned (Z_to_bv 8 x) = x) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; exact Hx).
  rewrite E. apply unsigned_lit. lia.
Qed.

Lemma srf_land7 : forall fp, fp mod 8 = 0 -> Z.land fp 7 = 0.
Proof. intros fp H. change 7 with (2 ^ 3 - 1). rewrite zb_land_mask by lia. exact H. Qed.

(* sb of a zero-extended loaded byte stores that byte *)
Lemma srf_le1_zxb : forall b : byte, le1 (zxb b) = [b].
Proof.
  intros b. unfold le1, zxb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  rewrite unsigned_lit by lia.
  cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(* ---- bit arithmetic of the byte assembly ---- *)

Lemma srf_lor_add : forall a b k, 0 <= k -> 0 <= b < 2 ^ k -> a mod 2 ^ k = 0 -> Z.lor a b = a + b.
Proof.
  intros a b k Hk Hb Ha.
  assert (L : Z.land a b = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [N|N].
    - rewrite <- (Z.mod_pow2_bits_low a k n N), Ha, Z.bits_0. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ k)) by lia. rewrite (Z.mod_pow2_bits_high b k n) by lia.
      apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite (Z.add_nocarry_lxor a b L). reflexivity.
Qed.

Lemma srf_lor_lo8 : forall a b, 0 <= b < 256 -> a mod 256 = 0 -> Z.lor a b = a + b.
Proof. intros a b H1 H2. apply (srf_lor_add a b 8); [lia | exact H1 | exact H2]. Qed.
Lemma srf_lor_lo16 : forall a b, 0 <= b < 65536 -> a mod 65536 = 0 -> Z.lor a b = a + b.
Proof. intros a b H1 H2. apply (srf_lor_add a b 16); [lia | exact H1 | exact H2]. Qed.
Lemma srf_lor_lo24 : forall a b, 0 <= b < 16777216 -> a mod 16777216 = 0 -> Z.lor a b = a + b.
Proof. intros a b H1 H2. apply (srf_lor_add a b 24); [lia | exact H1 | exact H2]. Qed.
Lemma srf_lor_hi8 : forall a b, 0 <= a < 256 -> b mod 256 = 0 -> Z.lor a b = a + b.
Proof. intros a b H1 H2. rewrite Z.lor_comm, Z.add_comm. apply srf_lor_lo8; assumption. Qed.
Lemma srf_lor_hi16 : forall a b, 0 <= a < 65536 -> b mod 65536 = 0 -> Z.lor a b = a + b.
Proof. intros a b H1 H2. rewrite Z.lor_comm, Z.add_comm. apply srf_lor_lo16; assumption. Qed.
Lemma srf_lor_hi24 : forall a b, 0 <= a < 16777216 -> b mod 16777216 = 0 -> Z.lor a b = a + b.
Proof. intros a b H1 H2. rewrite Z.lor_comm, Z.add_comm. apply srf_lor_lo24; assumption. Qed.

Lemma srf_lxor_ones : forall x, 0 <= x < 18446744073709551616 ->
  Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx.
  assert (E : Z.lxor x (Z.ones 64) = Z.lnot x mod 2 ^ 64).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec. destruct (Z.lt_ge_cases n 64) as [L|L].
    - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. rewrite Z.ones_spec_low by lia.
      destruct (Z.testbit x n); reflexivity.
    - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.ones_spec_high by lia. rewrite xorb_false_r.
      rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
  change 18446744073709551615 with (Z.ones 64) at 1. rewrite E. unfold Z.lnot.
  change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma srf_be16 : forall b i, 0 <= byte_at b i < 256 -> 0 <= byte_at b (i + 1) < 256 ->
  spec_be16 b i = byte_at b i * 256 + byte_at b (i + 1).
Proof.
  intros b i H1 H2. unfold spec_be16, u16. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite srf_lor_lo8 by (Z.div_mod_to_equations; lia). apply Z.mod_small. lia.
Qed.

Lemma srf_be32 : forall b i, 0 <= byte_at b i < 256 -> 0 <= byte_at b (i + 1) < 256 ->
  0 <= byte_at b (i + 2) < 256 -> 0 <= byte_at b (i + 3) < 256 ->
  spec_be32 b i = byte_at b i * 16777216 + byte_at b (i + 1) * 65536 + byte_at b (i + 2) * 256 + byte_at b (i + 3).
Proof.
  intros b i H1 H2 H3 H4. unfold spec_be32, u32. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  change (2 ^ 32) with 4294967296.
  rewrite (Z.mod_small (byte_at b i * 16777216)) by lia.
  rewrite (Z.mod_small (byte_at b (i + 1) * 65536)) by lia.
  rewrite (Z.mod_small (byte_at b (i + 2) * 256)) by lia.
  rewrite (srf_lor_lo8 (byte_at b (i + 2) * 256)) by (Z.div_mod_to_equations; lia).
  rewrite (srf_lor_lo16 (byte_at b (i + 1) * 65536)) by (Z.div_mod_to_equations; lia).
  rewrite (srf_lor_lo24 (byte_at b i * 16777216)) by (Z.div_mod_to_equations; lia).
  lia.
Qed.

(* ---- the body sum: the machine's running total, and spec_sum_at ---- *)

Fixpoint psum (b : list Z) (q : Z) (n : nat) : Z :=
  match n with O => 0 | S n' => psum b q n' + byte_at b (q + Z.of_nat n') end.

Lemma psum_S : forall b q n, psum b q (S n) = psum b q n + byte_at b (q + Z.of_nat n).
Proof. reflexivity. Qed.

Lemma psum_first : forall b q n, psum b q (S n) = byte_at b q + psum b (q + 1) n.
Proof.
  intros b q n. revert q. induction n as [|n IH]; intros q.
  - cbn [psum Z.of_nat]. rewrite Z.add_0_r. lia.
  - rewrite psum_S, IH, psum_S. replace (q + 1 + Z.of_nat n) with (q + Z.of_nat (S n)) by lia. lia.
Qed.

Lemma psum_range : forall (fr : list byte) q n, 0 <= psum (zs fr) q n <= 255 * Z.of_nat n.
Proof.
  intros fr q n. induction n as [|n IH]; [cbn; lia|].
  rewrite psum_S. pose proof (srf_byte_all fr (q + Z.of_nat n)). lia.
Qed.

Lemma srf_sum_loop : forall b q f s i, 0 <= s < 65536 ->
  spec_sum_loop b q s i f = (s + psum b (q + i) f) mod 65536.
Proof.
  intros b q f. induction f as [|f IH]; intros s i Hs.
  - cbn [spec_sum_loop psum]. rewrite Z.add_0_r, Z.mod_small by lia. reflexivity.
  - cbn [spec_sum_loop]. rewrite psum_first.
    assert (E : Z.land (s + byte_at b (q + i)) 65535 = (s + byte_at b (q + i)) mod 65536)
      by (change 65535 with (2 ^ 16 - 1); rewrite zb_land_mask by lia; reflexivity).
    rewrite E. rewrite IH by (apply Z.mod_pos_bound; lia).
    rewrite Zplus_mod_idemp_l. f_equal. replace (q + (i + 1)) with (q + i + 1) by lia. lia.
Qed.

Lemma srf_sum_at : forall b q n, spec_sum_at b q n = psum b q (Z.to_nat n) mod 65536.
Proof.
  intros b q n. unfold spec_sum_at, u16. rewrite srf_sum_loop by lia.
  rewrite Z.add_0_l, Z.add_0_r. apply Z.mod_mod. lia.
Qed.

Lemma srf_put2_mod : forall x, put 2 (x mod 65536) = put 2 x.
Proof. intros x. unfold put. change 65536 with (2 ^ 16). apply Z_to_le_bytes_mod. lia. Qed.

(* ---- the four outcomes of the model ---- *)

Lemma srf_m_short : forall b len, len < 30 ->
  spec_read_frame b len = SpecFrame SPEC_E_SHORT 0 0 0 0 0 0 0 0 0 0 0 0 0 0.
Proof.
  intros b len H. unfold spec_read_frame.
  replace (len <? SPEC_BODY_AT) with true by (symmetry; apply Z.ltb_lt; unfold SPEC_BODY_AT; lia).
  reflexivity.
Qed.

Lemma srf_m_et : forall b len, 30 <= len -> spec_be16 b 12 <> 34911 ->
  spec_read_frame b len = SpecFrame SPEC_E_ETHERTYPE 0 0 (spec_be16 b 12) 0 0 0 0 0 0 0 0 0 0 0.
Proof.
  intros b len H1 H2. unfold spec_read_frame.
  replace (len <? SPEC_BODY_AT) with false by (symmetry; apply Z.ltb_ge; unfold SPEC_BODY_AT; lia).
  replace (spec_be16 b 12 =? SPEC_ETHERTYPE) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_ETHERTYPE; lia).
  reflexivity.
Qed.

Lemma srf_m_len : forall b len, 30 <= len -> spec_be16 b 12 = 34911 ->
  spec_be16 b 14 < 16 \/ len - 14 < spec_be16 b 14 ->
  spec_read_frame b len = SpecFrame SPEC_E_LENGTH 0 0 (spec_be16 b 12) (spec_be16 b 14) 0 0 0 0 0 0 0 0 0 0.
Proof.
  intros b len H1 H2 H3. unfold spec_read_frame.
  replace (len <? SPEC_BODY_AT) with false by (symmetry; apply Z.ltb_ge; unfold SPEC_BODY_AT; lia).
  replace (spec_be16 b 12 =? SPEC_ETHERTYPE) with true by (symmetry; apply Z.eqb_eq; unfold SPEC_ETHERTYPE; lia).
  cbn [negb].
  destruct H3 as [H3|H3].
  - replace (spec_be16 b SPEC_AT_NUMBYTES <? SPEC_HDR) with true
      by (symmetry; apply Z.ltb_lt; unfold SPEC_HDR, SPEC_AT_NUMBYTES; lia).
    reflexivity.
  - replace (len - SPEC_ETH_HDR <? spec_be16 b SPEC_AT_NUMBYTES) with true
      by (symmetry; apply Z.ltb_lt; unfold SPEC_ETH_HDR, SPEC_AT_NUMBYTES; lia).
    rewrite orb_true_r. reflexivity.
Qed.

Lemma srf_m_ok : forall b len, 30 <= len -> spec_be16 b 12 = 34911 ->
  16 <= spec_be16 b 14 -> spec_be16 b 14 <= len - 14 ->
  spec_read_frame b len =
  SpecFrame SPEC_OK 0 SPEC_MAC (spec_be16 b 12) (spec_be16 b 14) (spec_be16 b 16) (spec_be16 b 26)
    (spec_be32 b 18) (spec_be32 b 22) (byte_at b 28) (byte_at b 29) SPEC_BODY_AT (spec_be16 b 14 - 16)
    (len - 30 - (spec_be16 b 14 - 16)) (spec_sum_at b 30 (spec_be16 b 14 - 16)).
Proof.
  intros b len H1 H2 H3 H4. unfold spec_read_frame.
  replace (len <? SPEC_BODY_AT) with false by (symmetry; apply Z.ltb_ge; unfold SPEC_BODY_AT; lia).
  replace (spec_be16 b 12 =? SPEC_ETHERTYPE) with true by (symmetry; apply Z.eqb_eq; unfold SPEC_ETHERTYPE; lia).
  replace (spec_be16 b SPEC_AT_NUMBYTES <? SPEC_HDR) with false
    by (symmetry; apply Z.ltb_ge; unfold SPEC_HDR, SPEC_AT_NUMBYTES; lia).
  replace (len - SPEC_ETH_HDR <? spec_be16 b SPEC_AT_NUMBYTES) with false
    by (symmetry; apply Z.ltb_ge; unfold SPEC_ETH_HDR, SPEC_AT_NUMBYTES; lia).
  reflexivity.
Qed.

(* ---- the struct cell ---- *)

Lemma srf_rwc80 : forall m A cs S, rw_cells rsegs m A cs -> cells_size cs = 80%nat -> cells_bytes cs = S ->
  rw_cells rsegs m A [CB 80 S].
Proof.
  intros m A cs S H L E. pose proof (rw_cells_merge rsegs m A [] cs []) as M.
  rewrite app_nil_r in M. cbn [app] in M. rewrite <- L, <- E. apply M. exact H.
Qed.

(* ---- tactics ---- *)

Ltac srf_unlit :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.

Ltac srf_cond_solve :=
  unfold bv_eqb, bv_ltu;
  repeat match goal with H : Z.land ?x 7 = 0 |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
           rewrite (unsigned_lit x) by lia end;
  repeat match goal with H : Z.land ?x 7 = 0 |- context [Z.land ?x 7] => rewrite H end;
  fold_lit_ux; srf_unlit; fold_lit_ux; solve_cond_rec.

Ltac srf_br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false by (symmetry; srf_cond_solve)
            | replace c with true by (symmetry; srf_cond_solve) ]; cbv iota
  end.

Ltac st := step; try srf_br.

Ltac ld1 H i :=
  let R := fresh "RB" in let RD := fresh "RD" in
  lazymatch type of H with bytes_at _ _ _ ?fr => pose proof (srf_byte_all fr i) as R end;
  pose proof (srf_rd1 _ _ _ i H ltac:(lia)) as RD; st; clear RD.

Ltac srf_sb := step; rewrite srf_le1_zxb; mem_after_store_opt.

Ltac srf_lia := first [ lia | (Z.div_mod_to_equations; lia) ].

Ltac srf_lor :=
  match goal with
  | |- context [Z.lor ?a ?b] =>
      first [ rewrite (srf_lor_lo8 a b) by srf_lia | rewrite (srf_lor_lo16 a b) by srf_lia
            | rewrite (srf_lor_lo24 a b) by srf_lia | rewrite (srf_lor_hi8 a b) by srf_lia
            | rewrite (srf_lor_hi16 a b) by srf_lia | rewrite (srf_lor_hi24 a b) by srf_lia ]
  end.

Ltac srf_zclean :=
  repeat match goal with |- context [bv_unsigned (zxb (Z_to_bv 8 ?b))] => rewrite (srf_uz8 b) by lia end;
  repeat match goal with |- context [Z.shiftl ?a ?k] => rewrite (Z.shiftl_mul_pow2 a k) by lia end;
  repeat match goal with |- context [2 ^ ?k] =>
           let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end;
  repeat (first [ progress srf_unlit | srf_lor ]).

(* replace the register value assembled from frame bytes by v *)
Ltac srf_fix v :=
  match goal with
  | |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
      replace (Z_to_bv 64 (Z.lor x y)) with (Z_to_bv 64 v) by (f_equal; srf_zclean; lia)
  end.

(* jump to the common exit with the struct merged into one 80-byte cell; every premise named, never searched *)
Ltac srf_epi EPI RWc FR ST MU WMO MI WM :=
  eapply EPI; [ apply (srf_rwc80 _ _ _ _ RWc); reflexivity | exact FR | exact ST | exact MU | exact WMO
              | exact MI | exact WM | | ].

(* 145 of the 146 instructions at 0x15004..0x15264 are stepped. The one never reached is the trap unimp at 0x15248:
   every branch to it (0x15040, 0x1504c..0x15080, 0x1508c..0x151e8, 0x151fc) is decided not taken from 0 < p,
   fp mod 8 = 0, p + length fr <= 2^64 (bytes_at), len <= length fr and p + len < 2^64. *)
Theorem spec_read_frame_holds : memset_contract -> spec_read_frame_contract.
Proof.
  intros HMS. unfold memset_contract in HMS.
  unfold spec_read_frame_contract, spec_read_frame_ENTRY, spec_read_frame_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B p len fp fr junk -> -> -> Hp HFR Hlen HPL Hfp8 Hspfp RWF DIS OW S16 ST LO WOS MI WM.
  unfold off_window in OW. unfold w_off_stack in WOS.
  pose proof (bytes_at_bound rsegs m p fr HFR) as PB.
  pose proof (rw_cells_bound rsegs m fp _ RWF) as FB. cbn [cells_size csize] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  change (2 ^ 64) with 18446744073709551616 in PB, FB, Rsp, HPL.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (fp, fp + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  wk_facts. pose proof (srf_land7 fp Hfp8) as FP7.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 32%nat ST.
  do 12 step.
  rename m into m0.
  lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -32) _ |- _ => rename mm into m1; rename H into FR end.
  (* memset (f, 0, 80) *)
  eapply evt_cut.
  { eapply HMS with (m := m1) (junk := junk).
    - rewrite !unsigned_lit by lia. exact RWF.
    - exact MI. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 &
                  E & MUc & WMc & MIc & RWc).
  subst ms'. rewrite !unsigned_lit in MUc, RWc by lia.
  change (Z.to_nat 80) with 80%nat in RWc.
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (b8 0) in RWc by reflexivity.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI. clear m1.
  rewrite (ret_pc_even 86068) by (first [lia | reflexivity]).
  (* the common exit at 0x1521c: sw a0,0(s0); restore; ret *)
  assert (EPI : forall (m3 : word -> option byte) (code : Z) (S : list byte)
                  (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    rw_cells rsegs m3 fp [CB 80 S] ->
    rw_cells rsegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m3 lo (bv_unsigned sp + -32) ->
    munch [(bv_unsigned sp + -32, bv_unsigned sp); (fp, fp + 80)] m0 m3 ->
    wmono rsegs m0 m3 -> mem_inv rsegs m3 -> wmem rsegs m3 B ->
    code = sf_code (spec_read_frame (zs fr) len) ->
    put 4 code ++ skipn 4 S = sf_bytes p (spec_read_frame (zs fr) len) ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7 (Z_to_bv 64 fp) y9
                          (Z_to_bv 64 code) y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          y28 y29 y30 y31)
                     F (Z_to_bv 64 86556) fc None m3 (seg_rom rsegs))).
  { intros m3 code S y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      RW3 FR3 ST3 MU3 WMO3 MI3 WM3 HC HS.
    st.
    st. st. st. st. st.
    release_frame FR3 ST3 (bv_unsigned sp).
    st.
    apply evt_done. unfold QQ. subst code.
    do 14 eexists. eexists. split; [reflexivity|].
    split; [replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; exact MU3|].
    split; [exact WMO3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact WM3|].
    apply (srf_rwc80 _ _ _ _ RW3); [reflexivity|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r, le4_put. exact HS. }
  st. st.
  rewrite bv_ltu_Z, !unsigned_lit by lia.
  destruct (Z.ltb_spec 29 len) as [L30|L30]; cbv iota.
  2: {
    (* len < 30: SPEC_E_SHORT *)
    st. st. st. st.
    srf_epi EPI RWc FR ST MU WMO MIc WM.
    - rewrite srf_m_short by lia. reflexivity.
    - rewrite srf_m_short by lia. reflexivity. }
  (* len >= 30: the NULL / overflow / alignment checks of the UBSan build all pass *)
  st. st. st. st. st. st. st.
  ld1 HFR 12. ld1 HFR 13. st. st.
  assert (ET : spec_be16 (zs fr) 12 = byte_at (zs fr) 12 * 256 + byte_at (zs fr) 13)
    by (rewrite srf_be16 by apply srf_byte_all; reflexivity).
  srf_fix (spec_be16 (zs fr) 12).
  st. st. st. st.
  destruct (Z.eqb_spec (spec_be16 (zs fr) 12) 34911) as [EET|EET]; srf_br.
  2: {
    (* SPEC_E_ETHERTYPE *)
    st.
    srf_epi EPI RWc FR ST MU WMO MIc WM.
    - rewrite srf_m_et by lia. reflexivity.
    - rewrite srf_m_et by lia. cbn [cells_bytes cbytes]. rewrite ?le2_put. reflexivity. }
  st. st. st.
  ld1 HFR 14. ld1 HFR 15. st. st. st.
  assert (NB : spec_be16 (zs fr) 14 = byte_at (zs fr) 14 * 256 + byte_at (zs fr) 15)
    by (rewrite srf_be16 by apply srf_byte_all; reflexivity).
  srf_fix (spec_be16 (zs fr) 14).
  st. st. st.
  destruct (Z.ltb_spec (spec_be16 (zs fr) 14) 16) as [NB16|NB16]; srf_br.
  1: {
    (* SPEC_E_LENGTH: numbytes < 16 *)
    srf_epi EPI RWc FR ST MU WMO MIc WM.
    - rewrite srf_m_len by lia. reflexivity.
    - rewrite srf_m_len by lia. cbn [cells_bytes cbytes]. rewrite ?le2_put. reflexivity. }
  st. st.
  destruct (Z.ltb_spec (len - 14) (spec_be16 (zs fr) 14)) as [NBL|NBL]; srf_br.
  1: {
    (* SPEC_E_LENGTH: numbytes > len - 14 *)
    srf_epi EPI RWc FR ST MU WMO MIc WM.
    - rewrite srf_m_len by lia. reflexivity.
    - rewrite srf_m_len by lia. cbn [cells_bytes cbytes]. rewrite ?le2_put. reflexivity. }
  (* SPEC_OK: dst, src, sum, send, ack, retry, cmd, ncmds *)
  st. st. st. st. st. st. st. st.
  ld1 HFR 16. ld1 HFR 17. st. st.
  assert (SM : spec_be16 (zs fr) 16 = byte_at (zs fr) 16 * 256 + byte_at (zs fr) 17)
    by (rewrite srf_be16 by apply srf_byte_all; reflexivity).
  srf_fix (spec_be16 (zs fr) 16).
  st. st. st. st. st. st. st. st. st.
  ld1 HFR 19. ld1 HFR 18. ld1 HFR 20. ld1 HFR 21.
  st. st. st. st. st. st.
  assert (SD : spec_be32 (zs fr) 18 = byte_at (zs fr) 18 * 16777216 + byte_at (zs fr) 19 * 65536 +
                                      byte_at (zs fr) 20 * 256 + byte_at (zs fr) 21)
    by (rewrite srf_be32 by apply srf_byte_all; reflexivity).
  srf_fix (spec_be32 (zs fr) 18).
  st. st. st. st. st. st. st. st. st.
  ld1 HFR 23. ld1 HFR 22. ld1 HFR 24. ld1 HFR 25.
  st. st. st. st. st. st.
  assert (AK : spec_be32 (zs fr) 22 = byte_at (zs fr) 22 * 16777216 + byte_at (zs fr) 23 * 65536 +
                                      byte_at (zs fr) 24 * 256 + byte_at (zs fr) 25)
    by (rewrite srf_be32 by apply srf_byte_all; reflexivity).
  srf_fix (spec_be32 (zs fr) 22).
  st. st. st. st.
  ld1 HFR 26. ld1 HFR 27. st. st.
  assert (RT : spec_be16 (zs fr) 26 = byte_at (zs fr) 26 * 256 + byte_at (zs fr) 27)
    by (rewrite srf_be16 by apply srf_byte_all; reflexivity).
  srf_fix (spec_be16 (zs fr) 26).
  st. st. st.
  ld1 HFR 28. st. srf_sb. st.
  ld1 HFR 29. st. srf_sb. st.
  (* body, body_len, pad_len *)
  st. st.
  replace (Z_to_bv 64 (spec_be16 (zs fr) 14 + -16)) with (Z_to_bv 64 (spec_be16 (zs fr) 14 - 16))
    by (f_equal; lia).
  st. st.
  match goal with |- context [Z_to_bv 64 (?x - ?y + -14)] =>
    replace (Z_to_bv 64 (x - y + -14)) with (Z_to_bv 64 (len - 30 - (spec_be16 (zs fr) 14 - 16)))
      by (f_equal; srf_unlit; lia) end.
  st. st. st.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mK end.
  (* 0x1523c: li a0,0; sh a1,72(s0); j 0x1521c *)
  assert (TAIL : forall (sum : Z) (y12 y13 y14 : word),
    sum = psum (zs fr) 30 (Z.to_nat (spec_be16 (zs fr) 14 - 16)) ->
    evt rsegs QQ (MS (mkR (Z_to_bv 64 86068) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 fp)
                          (Z_to_bv 64 (len - 30 - (spec_be16 (zs fr) 14 - 16)))
                          (Z_to_bv 64 (spec_be16 (zs fr) 14 - 16)) (Z_to_bv 64 sum) y12 y13 y14 x15 x16 x17
                          (Z_to_bv 64 (p + 30)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 86588) fc None mK (seg_rom rsegs))).
  { intros sum y12 y13 y14 HSUM.
    st. st. st.
    srf_epi EPI RWc FR ST MU WMO MIc WM.
    - rewrite srf_m_ok by lia. reflexivity.
    - rewrite srf_m_ok by lia. unfold sf_bytes, sf_ptr.
      cbn [sf_code sf_dst sf_src sf_ethertype sf_numbytes sf_sum sf_retry sf_send sf_ack sf_cmd sf_ncmds
           sf_body sf_body_len sf_pad_len sf_body_sum].
      rewrite Z.eqb_refl. cbv iota. rewrite Z.add_0_r.
      rewrite srf_sum_at, srf_put2_mod.
      cbn [cells_bytes cbytes]. rewrite ?le8_put, ?le4_put, ?le2_put. subst sum.
      reflexivity. }
  (* the body-sum loop at 0x151fc *)
  assert (LOOP : forall k i (y14 : word), Z.of_nat k = spec_be16 (zs fr) 14 - 16 - i ->
    0 <= i < spec_be16 (zs fr) 14 - 16 ->
    evt rsegs QQ (MS (mkR (Z_to_bv 64 86068) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 fp)
                          (Z_to_bv 64 (len - 30 - (spec_be16 (zs fr) 14 - 16)))
                          (Z_to_bv 64 (spec_be16 (zs fr) 14 - 16)) (Z_to_bv 64 (psum (zs fr) 30 (Z.to_nat i)))
                          (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - (p + 30))) y14 x15 x16 x17
                          (Z_to_bv 64 (p + 30)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 86524) fc None mK (seg_rom rsegs))).
  { induction k as [|k IH]; intros i y14 Hk Hi; [lia|].
    st. st.
    ld1 HFR (30 + i).
    st. st.
    match goal with |- context [Z_to_bv 64 (psum (zs fr) 30 (Z.to_nat i) + ?x)] =>
      replace (Z_to_bv 64 (psum (zs fr) 30 (Z.to_nat i) + x))
        with (Z_to_bv 64 (psum (zs fr) 30 (Z.to_nat (i + 1))))
        by (f_equal; rewrite srf_uz8 by lia; replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia;
            rewrite psum_S, Z2Nat.id by lia; reflexivity) end.
    st.
    destruct (Z.eqb_spec (i + 1) (spec_be16 (zs fr) 14 - 16)) as [EI|EI]; srf_br.
    - st. eapply TAIL. rewrite EI. reflexivity.
    - apply (IH (i + 1)); lia. }
  st.
  destruct (Z.eqb_spec (spec_be16 (zs fr) 14 - 16) 0) as [BL0|BL0]; srf_br.
  1: { st. eapply TAIL. rewrite BL0. reflexivity. }
  st. st. st.
  match goal with |- context [Z_to_bv 64 (Z.lxor ?x ?y)] =>
    replace (Z_to_bv 64 (Z.lxor x y)) with (Z_to_bv 64 (18446744073709551615 - (p + 30)))
      by (f_equal; srf_unlit; try (replace y with 18446744073709551615 by reflexivity);
          rewrite srf_lxor_ones by lia; reflexivity) end.
  eapply (LOOP (Z.to_nat (spec_be16 (zs fr) 14 - 16)) 0); lia.
Qed.
