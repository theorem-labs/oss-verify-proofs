(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeTile SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit.
Import ListNotations.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import CxMemo.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import CxLiaT0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition S2_ENTRY : Z := 0xb6bec.
Definition S2_EXIT : Z := 0xcd488.
Definition S2_LEN_MAX : Z := 1048512.

Notation SHA x := (Z.shiftr x 3 + 2147450880)%Z (only parsing).

Definition T_SOWN : Z := 0x24120.
Definition T_DIG : Z := 0x24260.
Definition T_P10 : Z := 0x253a0.
Definition T_P5 : Z := 0x25480.
Definition T_ESC : Z := 0x28ae0.

Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition padded_bytes (bs : list Z) : list byte := zbytes bs ++ repeat (Z_to_bv 8 0) 64.

Lemma zbytes_length : forall l, length (zbytes l) = length l.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma padded_bytes_length : forall bs, length (padded_bytes bs) = (length bs + 64)%nat.
Proof. intros. unfold padded_bytes. rewrite length_app, zbytes_length, repeat_length. reflexivity. Qed.
Lemma padded_bytes_blen : forall bs, Z.of_nat (length (padded_bytes bs)) = (blen bs + 64)%Z.
Proof. intros. rewrite padded_bytes_length. unfold blen. lia. Qed.

Lemma nth_error_zbytes : forall l i, (i < length l)%nat -> nth_error (zbytes l) i = Some (Z_to_bv 8 (nth i l 0%Z)).
Proof. intros l i H. unfold zbytes. rewrite nth_error_map. rewrite (nth_error_nth' l 0%Z H). reflexivity. Qed.

Lemma nth_error_padded : forall bs i, (0 <= i < blen bs + 64)%Z ->
  nth_error (padded_bytes bs) (Z.to_nat i) = Some (Z_to_bv 8 (B bs i)).
Proof.
  intros bs i H. unfold padded_bytes, B, blen in *.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [L|L].
  - rewrite nth_error_app1 by (rewrite zbytes_length; exact L). apply nth_error_zbytes. exact L.
  - rewrite nth_error_app2 by (rewrite zbytes_length; exact L). rewrite zbytes_length.
    rewrite (nth_overflow bs 0%Z L). rewrite nth_error_repeat by lia. reflexivity.
Qed.

Lemma buf_read : forall (m : mem) A bs i,
  bytes_at bsegs m A (padded_bytes bs) -> (0 <= i < blen bs + 64)%Z ->
  ov_read_bytes bsegs m (wa (A + i)) 1 = Some [Z_to_bv 8 (B bs i)].
Proof.
  intros m A bs i H Hi.
  eapply (u8ro_read bsegs m A (padded_bytes bs) i); [exact H| apply nth_error_padded; exact Hi | lia | reflexivity].
Qed.

Lemma zxb_small : forall x, (0 <= x < 256)%Z -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma zxb_B_hook : forall bs i, bytes_ok bs -> zxb (Z_to_bv 8 (B bs i)) = Z_to_bv 64 (B bs i).
Proof. intros bs i H. apply zxb_small. apply B_range. exact H. Qed.

Lemma u8_small : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma u64_small : forall c, (0 <= c < 2^64)%Z -> bv_unsigned (Z_to_bv 64 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma zx32_small : forall x, (0 <= x < 2^32)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. f_equal. rewrite u64_small by lia. apply Z.mod_small. lia. Qed.

Lemma swrap32_small : forall x, (-2147483648 <= x < 2147483648)%Z -> bv_swrap 32 x = x.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx32_small : forall x, (0 <= x < 2^31)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold sx32. f_equal. rewrite u64_small by lia. apply swrap32_small. lia. Qed.

Lemma shl32_shr29 : forall x, (0 <= x < 2^32)%Z -> (Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 29 = 8 * x)%Z.
Proof.
  intros x H. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (x * 2 ^ 32)%Z with (8 * x * 2 ^ 29)%Z by lia. apply Z.div_mul. lia.
Qed.
Lemma shl32_shr30 : forall x, (0 <= x < 2^32)%Z -> (Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = 4 * x)%Z.
Proof.
  intros x H. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (x * 2 ^ 32)%Z with (4 * x * 2 ^ 30)%Z by lia. apply Z.div_mul. lia.
Qed.
Lemma shl32_shr32 : forall x, (0 <= x < 2^32)%Z -> (Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x)%Z.
Proof.
  intros x H. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma shl3 : forall x, Z.shiftl x 3 = (8 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma shl2 : forall x, Z.shiftl x 2 = (4 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma sub_shr3 : forall a w, Z.shiftr (a + 8 * w - a) 3 = w.
Proof. intros. replace (a + 8 * w - a)%Z with (w * 2 ^ 3)%Z by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. Qed.

Ltac s2norm :=
  cbv beta;
  repeat match goal with
  | |- context [zxb (Z_to_bv 8 (B ?bs ?i))] => rewrite (zxb_B_hook bs i) by assumption
  | |- context [zxb (Z_to_bv 8 ?c)] => cx_memo c (rewrite (zxb_small c) by lia)
  | |- context [bv_unsigned (Z_to_bv 8 ?c)] => cx_memo c (rewrite (u8_small c) by lia)
  | |- context [zx32 (Z_to_bv 64 ?c)] => cx_memo c (rewrite (zx32_small c) by lia)
  | |- context [sx32 (Z_to_bv 64 ?c)] => cx_memo c (rewrite (sx32_small c) by lia)
  | |- context [bv_swrap 32 ?x] => cx_memo x (rewrite (swrap32_small x) by lia)
  | |- context [Z.modulo ?x 4294967296] => cx_memo x (rewrite (Z.mod_small x 4294967296) by lia)
  | |- context [Z.shiftr (Z.modulo (Z.shiftl ?x 32) 18446744073709551616) 29] => rewrite (shl32_shr29 x) by lia
  | |- context [Z.shiftr (Z.modulo (Z.shiftl ?x 32) 18446744073709551616) 30] => rewrite (shl32_shr30 x) by lia
  | |- context [Z.shiftr (Z.modulo (Z.shiftl ?x 32) 18446744073709551616) 32] => rewrite (shl32_shr32 x) by lia
  | |- context [Z.shiftr (?a + 8 * ?w - ?a) 3] => rewrite (sub_shr3 a w)
  | |- context [Z.shiftl ?x 3] => rewrite (shl3 x)
  | |- context [Z.shiftl ?x 2] => rewrite (shl2 x)
  end.

Definition oc_rel (sc : list (bool * Z)) (ocs : list word) : Prop :=
  forall j s, nth_error (rev sc) j = Some s -> nth_error ocs (2 * (j + 1)) = Some (wz (snd s)).
Definition ia_rel (sc : list (bool * Z)) (ias : list byte) : Prop :=
  forall j s, nth_error (rev sc) j = Some s -> nth_error ias (j + 1) = Some (Z_to_bv 8 (if fst s then 1 else 0)%Z).

Lemma oc_rel_nil : forall ocs, oc_rel [] ocs.
Proof. intros ocs j s H. destruct j; discriminate. Qed.
Lemma ia_rel_nil : forall ias, ia_rel [] ias.
Proof. intros ias j s H. destruct j; discriminate. Qed.

Lemma nth_error_Some_lt : forall {X} (l : list X) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros X l i x H. apply nth_error_Some. congruence. Qed.

Lemma nth_error_upd_same' : forall {X} (l : list X) i x, (i < length l)%nat -> nth_error (upd l i x) i = Some x.
Proof. intros. apply nth_error_upd_same. assumption. Qed.

Lemma oc_rel_upd_other : forall sc ocs i v, oc_rel sc ocs ->
  (forall j, (j < length sc)%nat -> i <> (2 * (j + 1))%nat) -> oc_rel sc (upd ocs i v).
Proof.
  intros sc ocs i v H Hi j s Hj. rewrite nth_error_upd_other.
  - apply H. exact Hj.
  - apply Hi. apply nth_error_Some_lt in Hj. rewrite length_rev in Hj. exact Hj.
Qed.

Lemma oc_rel_push : forall sc ocs b ti, oc_rel sc ocs -> (2 * (length sc + 1) < length ocs)%nat ->
  oc_rel ((b, ti) :: sc) (upd ocs (2 * (length sc + 1)) (wz ti)).
Proof.
  intros sc ocs b ti H HL j s Hj. cbn [rev] in Hj.
  destruct (Nat.lt_ge_cases j (length sc)) as [L|L].
  - rewrite nth_error_app1 in Hj by (rewrite length_rev; exact L).
    rewrite nth_error_upd_other by lia. apply H. exact Hj.
  - rewrite nth_error_app2 in Hj by (rewrite length_rev; exact L). rewrite length_rev in Hj.
    destruct (j - length sc)%nat as [|q] eqn:Eq; [|destruct q; discriminate].
    cbn in Hj. inversion Hj; subst s. cbn [snd].
    replace j with (length sc) by lia. apply nth_error_upd_same. exact HL.
Qed.

Lemma oc_rel_pop : forall s sc ocs, oc_rel (s :: sc) ocs -> oc_rel sc ocs.
Proof.
  intros s sc ocs H j x Hj. apply H. cbn [rev]. rewrite nth_error_app1; [exact Hj|].
  apply nth_error_Some_lt in Hj. exact Hj.
Qed.

Lemma oc_rel_top : forall b ti sc ocs, oc_rel ((b, ti) :: sc) ocs -> nth_error ocs (2 * (length sc + 1)) = Some (wz ti).
Proof.
  intros b ti sc ocs H. apply (H (length sc) (b, ti)). cbn [rev].
  rewrite nth_error_app2 by (rewrite length_rev; lia). rewrite length_rev, Nat.sub_diag. reflexivity.
Qed.

Lemma ia_rel_push : forall sc ias b ti, ia_rel sc ias -> (length sc + 1 < length ias)%nat ->
  ia_rel ((b, ti) :: sc) (upd ias (length sc + 1) (Z_to_bv 8 (if b then 1 else 0)%Z)).
Proof.
  intros sc ias b ti H HL j s Hj. cbn [rev] in Hj.
  destruct (Nat.lt_ge_cases j (length sc)) as [L|L].
  - rewrite nth_error_app1 in Hj by (rewrite length_rev; exact L).
    rewrite nth_error_upd_other by lia. apply H. exact Hj.
  - rewrite nth_error_app2 in Hj by (rewrite length_rev; exact L). rewrite length_rev in Hj.
    destruct (j - length sc)%nat as [|q] eqn:Eq; [|destruct q; discriminate].
    cbn in Hj. inversion Hj; subst s. cbn [fst].
    replace j with (length sc) by lia. apply nth_error_upd_same. exact HL.
Qed.

Lemma ia_rel_pop : forall s sc ias, ia_rel (s :: sc) ias -> ia_rel sc ias.
Proof.
  intros s sc ias H j x Hj. apply H. cbn [rev]. rewrite nth_error_app1; [exact Hj|].
  apply nth_error_Some_lt in Hj. exact Hj.
Qed.

Lemma ia_rel_top : forall b ti sc ias, ia_rel ((b, ti) :: sc) ias ->
  nth_error ias (length sc + 1) = Some (Z_to_bv 8 (if b then 1 else 0)%Z).
Proof.
  intros b ti sc ias H. apply (H (length sc) (b, ti)). cbn [rev].
  rewrite nth_error_app2 by (rewrite length_rev; lia). rewrite length_rev, Nat.sub_diag. reflexivity.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Record s2env : Type := mkS2Env {
  e_ra : word; e_sp : word; e_gp : word; e_tp : word;
  e_s0 : word; e_s1 : word; e_s2 : word; e_s3 : word; e_s4 : word; e_s5 : word;
  e_s6 : word; e_s7 : word; e_s8 : word; e_s9 : word; e_s10 : word; e_s11 : word;
  e_lo : Z; e_spa : Z; e_FF : Z; e_THIS : Z; e_DOC : Z; e_IDX : Z; e_BUF : Z; e_TAPE : Z; e_SBUF : Z; e_OC : Z; e_IA : Z;
  e_bs : list Z; e_idxs : list Z; e_iws : list word;
  e_tcap : Z; e_scap : Z;
  e_vptr : word; e_p12 : list byte; e_nxt0 : word; e_p28 : list byte; e_capv : word; e_p50 : list byte; e_dcap : word;
  e_j0 : list byte; e_j256 : list byte;
  e_m0 : mem;
  e_tws : list Z; e_sbs : list Z
}.

Notation e_len E := (blen (e_bs E)).
Notation e_n E := (n (e_idxs E)).
Notation e_off E := (off (e_bs E) (e_idxs E)).
Notation e_tok E := (tok (e_bs E) (e_idxs E)).
Notation e_SP E := (e_spa E).

Record env_ok (E : s2env) : Prop := mkEnvOk {
  ok_s1 : S1OUT (e_bs E) (e_idxs E);
  ok_bytes : bytes_ok (e_bs E);
  ok_len : (e_len E <= S2_LEN_MAX)%Z;
  ok_tcap : (e_len E + 3 <= e_tcap E /\ e_tcap E <= 2^40)%Z;
  ok_scap : (5 * e_len E + 5 <= 3 * e_scap E /\ e_scap E <= 2^40)%Z;
  ok_iws : firstn (length (e_idxs E) + 3) (e_iws E) = map (Z_to_bv 64) (ext (e_bs E) (e_idxs E));
  ok_iwl : (e_len E + 4 <= Z.of_nat (length (e_iws E)) /\ Z.of_nat (length (e_iws E)) < 2^40)%Z;
  ok_glo : (0x645000 <= e_lo E)%Z;
  ok_spa : (e_lo E <= e_spa E /\ bv_unsigned (e_sp E) - 432 <= e_spa E /\ e_spa E <= bv_unsigned (e_sp E) - 416)%Z;
  ok_sptop : (bv_unsigned (e_sp E) <= 2^47)%Z;
  ok_ff : (0 < e_FF E /\ e_FF E + 2048 <= e_lo E)%Z;
  ok_this : (0 < e_THIS E /\ e_THIS E + 96 <= e_lo E)%Z;
  ok_doc : (0 < e_DOC E /\ e_DOC E + 24 <= e_lo E)%Z;
  ok_idx : (0 < e_IDX E /\ e_IDX E + 4 * Z.of_nat (length (e_iws E)) <= e_lo E)%Z;
  ok_buf : (0 < e_BUF E /\ e_BUF E + e_len E + 64 <= e_lo E)%Z;
  ok_tape : (0 < e_TAPE E /\ e_TAPE E + 8 * e_tcap E <= e_lo E)%Z;
  ok_sbuf : (0 < e_SBUF E /\ e_SBUF E + e_scap E <= e_lo E)%Z;
  ok_oc : (0 < e_OC E /\ e_OC E + 8192 <= e_lo E)%Z;
  ok_ia : (0 < e_IA E /\ e_IA E + 1024 <= e_lo E)%Z;

  ok_al_spa : (e_spa E mod 32 = 0)%Z;
  ok_al_ff : (e_FF E mod 64 = 0)%Z;
  ok_al_this : (e_THIS E mod 8 = 0)%Z;
  ok_al_doc : (e_DOC E mod 8 = 0)%Z;
  ok_al_idx : (e_IDX E mod 8 = 0)%Z;
  ok_al_tape : (e_TAPE E mod 8 = 0)%Z;
  ok_al_sbuf : (e_SBUF E mod 8 = 0)%Z;
  ok_al_oc : (e_OC E mod 8 = 0)%Z;
  ok_al_ia : (e_IA E mod 8 = 0)%Z;

  ok_d_this_idx : (e_THIS E + 96 <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (length (e_iws E)) <= e_THIS E)%Z;
  ok_d_this_buf : (e_THIS E + 96 <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_THIS E)%Z;
  ok_d_this_tape : (e_THIS E + 96 <= e_TAPE E \/ e_TAPE E + 8 * e_tcap E <= e_THIS E)%Z;
  ok_d_this_sbuf : (e_THIS E + 96 <= e_SBUF E \/ e_SBUF E + e_scap E <= e_THIS E)%Z;
  ok_d_this_oc : (e_THIS E + 96 <= e_OC E \/ e_OC E + 8192 <= e_THIS E)%Z;
  ok_d_this_ia : (e_THIS E + 96 <= e_IA E \/ e_IA E + 1024 <= e_THIS E)%Z;
  ok_d_tape_idx : (e_TAPE E + 8 * e_tcap E <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (length (e_iws E)) <= e_TAPE E)%Z;
  ok_d_tape_buf : (e_TAPE E + 8 * e_tcap E <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_TAPE E)%Z;
  ok_d_tape_sbuf : (e_TAPE E + 8 * e_tcap E <= e_SBUF E \/ e_SBUF E + e_scap E <= e_TAPE E)%Z;
  ok_d_tape_oc : (e_TAPE E + 8 * e_tcap E <= e_OC E \/ e_OC E + 8192 <= e_TAPE E)%Z;
  ok_d_tape_ia : (e_TAPE E + 8 * e_tcap E <= e_IA E \/ e_IA E + 1024 <= e_TAPE E)%Z;
  ok_d_sbuf_idx : (e_SBUF E + e_scap E <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (length (e_iws E)) <= e_SBUF E)%Z;
  ok_d_sbuf_buf : (e_SBUF E + e_scap E <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_SBUF E)%Z;
  ok_d_sbuf_oc : (e_SBUF E + e_scap E <= e_OC E \/ e_OC E + 8192 <= e_SBUF E)%Z;
  ok_d_sbuf_ia : (e_SBUF E + e_scap E <= e_IA E \/ e_IA E + 1024 <= e_SBUF E)%Z;
  ok_d_oc_idx : (e_OC E + 8192 <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (length (e_iws E)) <= e_OC E)%Z;
  ok_d_oc_buf : (e_OC E + 8192 <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_OC E)%Z;
  ok_d_oc_ia : (e_OC E + 8192 <= e_IA E \/ e_IA E + 1024 <= e_OC E)%Z;
  ok_d_ia_idx : (e_IA E + 1024 <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (length (e_iws E)) <= e_IA E)%Z;
  ok_d_ia_buf : (e_IA E + 1024 <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_IA E)%Z;

  ok_d_doc_this : (e_DOC E + 24 <= e_THIS E \/ e_THIS E + 96 <= e_DOC E)%Z;
  ok_d_doc_tape : (e_DOC E + 24 <= e_TAPE E \/ e_TAPE E + 8 * e_tcap E <= e_DOC E)%Z;
  ok_d_doc_sbuf : (e_DOC E + 24 <= e_SBUF E \/ e_SBUF E + e_scap E <= e_DOC E)%Z;
  ok_d_doc_oc : (e_DOC E + 24 <= e_OC E \/ e_OC E + 8192 <= e_DOC E)%Z;
  ok_d_doc_ia : (e_DOC E + 24 <= e_IA E \/ e_IA E + 1024 <= e_DOC E)%Z;

  ok_d_ff_this : (e_FF E + 8 <= e_THIS E \/ e_THIS E + 96 <= e_FF E)%Z;
  ok_d_ff_doc : (e_FF E + 8 <= e_DOC E \/ e_DOC E + 24 <= e_FF E)%Z;
  ok_d_ff_idx : (e_FF E + 8 <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (length (e_iws E)) <= e_FF E)%Z;
  ok_d_ff_buf : (e_FF E + 8 <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_FF E)%Z;
  ok_d_ff_tape : (e_FF E + 8 <= e_TAPE E \/ e_TAPE E + 8 * e_tcap E <= e_FF E)%Z;
  ok_d_ff_sbuf : (e_FF E + 8 <= e_SBUF E \/ e_SBUF E + e_scap E <= e_FF E)%Z;
  ok_d_ff_oc : (e_FF E + 8 <= e_OC E \/ e_OC E + 8192 <= e_FF E)%Z;
  ok_d_ff_ia : (e_FF E + 8 <= e_IA E \/ e_IA E + 1024 <= e_FF E)%Z
}.

Definition s2_W (E : s2env) : list ivl :=
  [ (e_lo E, bv_unsigned (e_sp E));
    (e_THIS E, e_THIS E + 96);
    (e_TAPE E, e_TAPE E + 8 * e_tcap E);
    (e_SBUF E, e_SBUF E + e_scap E);
    (e_OC E, e_OC E + 8192);
    (e_IA E, e_IA E + 1024);
    (e_FF E, e_FF E + 8) ]%Z.

Definition impl_cells (E : s2env) (nxt : word) : list cell :=
  [C8 (e_vptr E); C4 (wz (e_n E)); CB 4 (e_p12 E); C8 (wz (e_IDX E)); C4 nxt; CB 4 (e_p28 E); C8 (e_capv E); C8 (wz 1024);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (e_p50 E); C8 (wz (e_OC E)); C8 (wz (e_IA E)); C8 (wz (e_BUF E));
   C8 (wz (e_len E)); C8 (wz (e_DOC E))].
Definition doc_cells (E : s2env) : list cell := [C8 (wz (e_TAPE E)); C8 (wz (e_SBUF E)); C8 (e_dcap E)].

Definition fr_cells (E : s2env) (sl : list cell) : list cell :=
  match sl with
  | [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; c304] =>
      [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200;
       C8 (wz (e_THIS E + 16)); C8 (wz (e_THIS E + 8)); C8 (wz (SHA (e_THIS E + 16))); C8 (wz (SHA (e_THIS E + 8))); C8 (wz (SHA (e_THIS E + 88)));
       C8 (wz (e_THIS E + 88)); C8 (wz (e_THIS E)); C8 (wz (e_FF E)); c272; C8 (wz 2147450880); c288; C8 (wz (e_FF E)); c304]
  | _ => []
  end.

Definition saved_cells (E : s2env) : list cell :=
  [C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E);
   C8 (e_s4 E); C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition s2_ghost (E : s2env) (tws sbs : list Z) : s2env :=
  mkS2Env (e_ra E) (e_sp E) (e_gp E) (e_tp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E)
          (e_s9 E) (e_s10 E) (e_s11 E) (e_lo E) (e_spa E) (e_FF E) (e_THIS E) (e_DOC E) (e_IDX E) (e_BUF E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E)
          (e_bs E) (e_idxs E) (e_iws E) (e_tcap E) (e_scap E) (e_vptr E) (e_p12 E) (e_nxt0 E) (e_p28 E) (e_capv E) (e_p50 E)
          (e_dcap E) (e_j0 E) (e_j256 E) (e_m0 E) tws sbs.
Definition gapp (E : s2env) (ws ss : list Z) : s2env := s2_ghost E (e_tws E ++ ws) (e_sbs E ++ ss).
Definition gpatch (E : s2env) (i v : Z) : s2env := s2_ghost E (zupd (e_tws E) (Z.to_nat i) v) (e_sbs E).

Lemma env_ok_ghost : forall E tws sbs, env_ok E -> env_ok (s2_ghost E tws sbs).
Proof. intros E tws sbs []. constructor; assumption. Qed.
Lemma env_ok_gapp : forall E ws ss, env_ok E -> env_ok (gapp E ws ss).
Proof. intros. apply env_ok_ghost. assumption. Qed.
Lemma env_ok_gpatch : forall E i v, env_ok E -> env_ok (gpatch E i v).
Proof. intros. apply env_ok_ghost. assumption. Qed.

Definition twords (l : list Z) : list byte := u64s (map (Z_to_bv 64) l).

Lemma twords_length : forall l, Z.of_nat (length (twords l)) = (8 * Z.of_nat (length l))%Z.
Proof. intros l. unfold twords. rewrite u64s_length, length_map. lia. Qed.
Lemma twords_app : forall a b, twords (a ++ b) = twords a ++ twords b.
Proof. intros. unfold twords. rewrite map_app, u64s_app. reflexivity. Qed.
Lemma twords_of_words : forall ws : list word, twords (map bv_unsigned ws) = u64s ws.
Proof.
  intros ws. unfold twords. f_equal. rewrite map_map. rewrite <- (map_id ws) at 2. apply map_ext. intros w. apply Z_to_bv_bv_unsigned.
Qed.
Lemma zbytes_of_bytes : forall bb : list byte, zbytes (map bv_unsigned bb) = bb.
Proof.
  intros bb. unfold zbytes. rewrite map_map. rewrite <- (map_id bb) at 2. apply map_ext. intros w.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma zbytes_app : forall a b, zbytes (a ++ b) = zbytes a ++ zbytes b.
Proof. intros. unfold zbytes. apply map_app. Qed.
Lemma map_zupd_upd : forall (l : list Z) i v, map (Z_to_bv 64) (zupd l i v) = upd (map (Z_to_bv 64) l) i (Z_to_bv 64 v).
Proof. induction l as [|y l IH]; intros [|i] v; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Definition tape_img (E : s2env) (tws sbs : list Z) (m1 : mem) : Prop :=
  bytes_at bsegs m1 (e_TAPE E) (twords tws) /\ bytes_at bsegs m1 (e_SBUF E) (zbytes sbs) /\
  (Z.of_nat (length tws) <= e_tcap E)%Z /\ (Z.of_nat (length sbs) <= e_scap E)%Z /\
  stk bsegs m1 (e_TAPE E) (e_TAPE E + 8 * e_tcap E) /\ stk bsegs m1 (e_SBUF E) (e_SBUF E + e_scap E) /\
  bytes_ok sbs                                  .

Lemma tape_img_write : forall E tws sbs (m1 : mem) a bs n, Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z -> tape_img E tws sbs m1 ->
  (e_TAPE E + 8 * Z.of_nat (length tws) <= a \/ a + n <= e_TAPE E)%Z ->
  (e_SBUF E + Z.of_nat (length sbs) <= a \/ a + n <= e_SBUF E)%Z ->
  tape_img E tws sbs (write_to_mem m1 (wa a) bs).
Proof.
  intros E tws sbs m1 a bs n Hn Ha Hl (T1 & T2 & T3 & T4 & S1 & S2 & SB) D1 D2.
  split; [|split; [|split; [exact T3|split; [exact T4|split; [|split; [|exact SB]]]]]].
  - apply (bytes_at_write_other_n bsegs m1 a bs _ _ n Hn Ha Hl T1). rewrite twords_length. lia.
  - apply (bytes_at_write_other_n bsegs m1 a bs _ _ n Hn Ha Hl T2). rewrite zbytes_length. lia.
  - apply stk_write; [exact S1 | exact Ha | lia].
  - apply stk_write; [exact S2 | exact Ha | lia].
Qed.

Section TimgRegions.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (tws sbs : list Z) (m1 : mem) (a : Z) (bs : list byte) (n : Z).
  Hypothesis Hn : Z.of_nat (length bs) = n.
  Hypothesis Ha : (0 <= a)%Z.
  Hypothesis Hl : (a + n <= 2^64)%Z.
  Hypothesis TI : tape_img E tws sbs m1.

  Lemma tape_img_write_stack : (e_lo E <= a)%Z -> tape_img E tws sbs (write_to_mem m1 (wa a) bs).
  Proof using OK Hn Ha Hl TI.
    intros H. pose proof TI as (_ & _ & T3 & T4 & _). pose proof (ok_tape _ OK). pose proof (ok_sbuf _ OK).
    apply (tape_img_write E tws sbs m1 a bs n Hn Ha Hl TI); lia.
  Qed.
  Lemma tape_img_write_this : (e_THIS E <= a /\ a + n <= e_THIS E + 96)%Z -> tape_img E tws sbs (write_to_mem m1 (wa a) bs).
  Proof using OK Hn Ha Hl TI.
    intros H. pose proof TI as (_ & _ & T3 & T4 & _). pose proof (ok_d_this_tape _ OK). pose proof (ok_d_this_sbuf _ OK).
    pose proof (Zle_0_nat (length bs)).
    apply (tape_img_write E tws sbs m1 a bs n Hn Ha Hl TI); lia.
  Qed.
  Lemma tape_img_write_oc : (e_OC E <= a /\ a + n <= e_OC E + 8192)%Z -> tape_img E tws sbs (write_to_mem m1 (wa a) bs).
  Proof using OK Hn Ha Hl TI.
    intros H. pose proof TI as (_ & _ & T3 & T4 & _). pose proof (ok_d_tape_oc _ OK). pose proof (ok_d_sbuf_oc _ OK).
    pose proof (Zle_0_nat (length bs)).
    apply (tape_img_write E tws sbs m1 a bs n Hn Ha Hl TI); lia.
  Qed.
  Lemma tape_img_write_ia : (e_IA E <= a /\ a + n <= e_IA E + 1024)%Z -> tape_img E tws sbs (write_to_mem m1 (wa a) bs).
  Proof using OK Hn Ha Hl TI.
    intros H. pose proof TI as (_ & _ & T3 & T4 & _). pose proof (ok_d_tape_ia _ OK). pose proof (ok_d_sbuf_ia _ OK).
    pose proof (Zle_0_nat (length bs)).
    apply (tape_img_write E tws sbs m1 a bs n Hn Ha Hl TI); lia.
  Qed.
  Lemma tape_img_write_ff : (e_FF E <= a /\ a + n <= e_FF E + 8)%Z -> tape_img E tws sbs (write_to_mem m1 (wa a) bs).
  Proof using OK Hn Ha Hl TI.
    intros H. pose proof TI as (_ & _ & T3 & T4 & _). pose proof (ok_d_ff_tape _ OK). pose proof (ok_d_ff_sbuf _ OK).
    pose proof (Zle_0_nat (length bs)). pose proof (Zle_0_nat (length tws)). pose proof (Zle_0_nat (length sbs)).
    apply (tape_img_write E tws sbs m1 a bs n Hn Ha Hl TI); lia.
  Qed.

  Lemma tape_img_write_tape : (e_TAPE E + 8 * Z.of_nat (length tws) <= a /\ a + n <= e_TAPE E + 8 * e_tcap E)%Z ->
    tape_img E tws sbs (write_to_mem m1 (wa a) bs).
  Proof using OK Hn Ha Hl TI.
    intros H. pose proof TI as (_ & _ & T3 & T4 & _). pose proof (ok_d_tape_sbuf _ OK). pose proof (Zle_0_nat (length bs)).
    apply (tape_img_write E tws sbs m1 a bs n Hn Ha Hl TI); lia.
  Qed.
  Lemma tape_img_write_sbuf : (e_SBUF E + Z.of_nat (length sbs) <= a /\ a + n <= e_SBUF E + e_scap E)%Z ->
    tape_img E tws sbs (write_to_mem m1 (wa a) bs).
  Proof using OK Hn Ha Hl TI.
    intros H. pose proof TI as (_ & _ & T3 & T4 & _). pose proof (ok_d_tape_sbuf _ OK). pose proof (Zle_0_nat (length bs)).
    apply (tape_img_write E tws sbs m1 a bs n Hn Ha Hl TI); lia.
  Qed.
End TimgRegions.

Lemma timg_bytes_at_nil : forall (m1 : mem) A, (0 <= A <= 2^64)%Z -> bytes_at bsegs m1 A [].
Proof. intros m1 A H. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma tape_img_app : forall E tws sbs (m1 : mem) (ws : list word) (bb : list byte), tape_img E tws sbs m1 ->
  bytes_at bsegs m1 (e_TAPE E + 8 * Z.of_nat (length tws)) (u64s ws) ->
  bytes_at bsegs m1 (e_SBUF E + Z.of_nat (length sbs)) bb ->
  (Z.of_nat (length tws) + Z.of_nat (length ws) <= e_tcap E)%Z ->
  (Z.of_nat (length sbs) + Z.of_nat (length bb) <= e_scap E)%Z ->
  tape_img E (tws ++ map bv_unsigned ws) (sbs ++ map bv_unsigned bb) m1.
Proof.
  intros E tws sbs m1 ws bb (T1 & T2 & T3 & T4 & S1 & S2 & SB) B1 B2 L1 L2. unfold tape_img.
  rewrite twords_app, zbytes_app, twords_of_words, zbytes_of_bytes, !length_app, !length_map.
  split; [|split; [|split; [lia|split; [lia|split; [exact S1 | split; [exact S2 | apply Forall_app; split; [exact SB | apply bytes_ok_map]]]]]]].
  - apply bytes_at_app. split; [exact T1|]. rewrite twords_length. exact B1.
  - apply bytes_at_app. split; [exact T2|]. rewrite zbytes_length. exact B2.
Qed.

Lemma tape_img_patch : forall E tws sbs (m1 : mem) i (v : word), tape_img E tws sbs m1 -> (0 <= i < Z.of_nat (length tws))%Z ->
  env_ok E ->
  tape_img E (zupd tws (Z.to_nat i) (bv_unsigned v)) sbs (write_to_mem m1 (wa (e_TAPE E + 8 * i)) (le8 v)).
Proof.
  intros E tws sbs m1 i v (T1 & T2 & T3 & T4 & S1 & S2 & SB) Hi OK. unfold tape_img.
  pose proof (ok_tape _ OK) as OT. pose proof (ok_spa _ OK) as OR.
  pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  rewrite zupd_length. split; [|split; [|split; [exact T3|split; [exact T4|split; [|split; [|exact SB]]]]]].
  - unfold twords in *. rewrite map_zupd_upd, Z_to_bv_bv_unsigned.
    set (ws := map (Z_to_bv 64) tws) in *.
    assert (HL : length ws = length tws) by (subst ws; apply length_map).
    destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & Ew & Hlen & Hupd).
    eapply bytes_at_ext.
    { apply (bytes_at_write_inside bsegs m1 (e_TAPE E) (u64s ws) (8 * i) (le8 v) T1); [lia|].
      rewrite length_le8, u64s_length. lia. }
    rewrite Hupd, Ew, !u64s_app. cbn [u64s].
    replace (Z.to_nat (8 * i)) with (length (u64s pre)) by (rewrite u64s_length; lia).
    apply upd_bytes_mid. rewrite !length_le8. reflexivity.
  - pose proof (ok_d_tape_sbuf _ OK).
    apply bytes_at_write_other; [exact T2 | lia | rewrite length_le8; lia |]. rewrite length_le8, zbytes_length. lia.
  - apply stk_write; [exact S1 | lia | rewrite length_le8; lia].
  - apply stk_write; [exact S2 | lia | rewrite length_le8; lia].
Qed.

Lemma Z_to_le_bytes_le_val : forall zs, bytes_ok zs -> Z_to_le_bytes (length zs) (le_val zs) = map (Z_to_bv 8) zs.
Proof.
  induction zs as [|z zs IH]; intros H; [reflexivity|]. inversion H as [|? ? Hz Hzs]; subst.
  cbn [length Z_to_le_bytes le_val map]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    replace (z + 256 * le_val zs)%Z with (z + le_val zs * 256)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
    replace ((z + 256 * le_val zs) / 256)%Z with (le_val zs); [apply IH; exact Hzs|].
    replace (z + 256 * le_val zs)%Z with (z + le_val zs * 256)%Z by lia. rewrite Z.div_add by lia. rewrite (Z.div_small z) by lia. lia.
Qed.

Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists v : word, le8 v = bs.
Proof.
  intros bs HL. set (zs := map bv_unsigned bs). assert (BO : bytes_ok zs) by apply bytes_ok_map.
  pose proof (le_val_range zs BO) as R. assert (LZ : length zs = 8%nat) by (subst zs; rewrite length_map; exact HL).
  rewrite LZ in R. change (256 ^ Z.of_nat 8)%Z with (2 ^ 64)%Z in R.
  exists (Z_to_bv 64 (le_val zs)). unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z; lia).
  rewrite <- LZ at 1. rewrite (Z_to_le_bytes_le_val zs BO). subst zs. apply zbytes_of_bytes.
Qed.

Lemma timg_hole8 : forall E tws sbs (m1 : mem) i, tape_img E tws sbs m1 -> (0 <= i < e_tcap E)%Z ->
  exists v : word, bytes_at bsegs m1 (e_TAPE E + 8 * i) (le8 v).
Proof.
  intros E tws sbs m1 i (_ & _ & _ & _ & S1 & _) Hi.
  destruct (stk_split bsegs m1 _ (e_TAPE E + 8 * i) _ S1 ltac:(lia)) as [_ S2].
  destruct (stk_split bsegs m1 _ (e_TAPE E + 8 * i + 8) _ S2 ltac:(lia)) as [S3 _].
  destruct (stk_bytes bsegs m1 _ _ S3 ltac:(lia)) as (bs & HL & HB).
  destruct (le8_surj bs ltac:(lia)) as (v & <-). exists v. exact HB.
Qed.

Lemma timg_sbytes : forall E tws sbs (m1 : mem) o d, tape_img E tws sbs m1 -> (0 <= o)%Z -> (0 <= d)%Z -> (o + d <= e_scap E)%Z ->
  exists cb : list byte, Z.of_nat (length cb) = d /\ bytes_at bsegs m1 (e_SBUF E + o) cb.
Proof.
  intros E tws sbs m1 o d (_ & _ & _ & _ & _ & S1 & _) Ho Hd Hod.
  destruct (stk_split bsegs m1 _ (e_SBUF E + o) _ S1 ltac:(lia)) as [_ S2].
  destruct (stk_split bsegs m1 _ (e_SBUF E + o + d) _ S2 ltac:(lia)) as [S3 _].
  destruct (stk_bytes bsegs m1 _ _ S3 ltac:(lia)) as (bs & HL & HB). exists bs. split; [lia|exact HB].
Qed.

Lemma tape_img_patchZ : forall E tws sbs (m1 : mem) i v, env_ok E -> tape_img E tws sbs m1 -> (0 <= i < Z.of_nat (length tws))%Z -> (0 <= v < 2^64)%Z ->
  tape_img E (zupd tws (Z.to_nat i) v) sbs (write_to_mem m1 (wa (e_TAPE E + 8 * i)) (le8 (Z_to_bv 64 v))).
Proof.
  intros E tws sbs m1 i v OK TI Hi Hv. pose proof (tape_img_patch E tws sbs m1 i (Z_to_bv 64 v) TI Hi OK) as P.
  rewrite u64_small in P by lia. exact P.
Qed.

Lemma tape_img_app1 : forall E tws sbs (m1 : mem) z A, env_ok E -> tape_img E tws sbs m1 -> bytes_at bsegs m1 A (le8 (Z_to_bv 64 z)) ->
  A = (e_TAPE E + 8 * Z.of_nat (length tws))%Z -> (Z.of_nat (length tws) + 1 <= e_tcap E)%Z -> (0 <= z < 2^64)%Z ->
  tape_img E (tws ++ [z]) (sbs ++ []) m1.
Proof.
  intros E tws sbs m1 z A OK TI B -> L Hz. pose proof TI as (_ & T2 & _ & T4 & _ & S2 & _). pose proof (ok_sbuf _ OK) as OS.
  pose proof (ok_spa _ OK) as OR. pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (tape_img_app E tws sbs m1 [Z_to_bv 64 z] [] TI) as P. cbn [u64s map length] in P. rewrite app_nil_r, u64_small in P by lia.
  apply P; [exact B | apply timg_bytes_at_nil; lia | cbn; lia | cbn; lia].
Qed.

Lemma tape_img_app2 : forall E tws sbs (m1 : mem) z1 z2 A1 A2, env_ok E -> tape_img E tws sbs m1 ->
  bytes_at bsegs m1 A1 (le8 (Z_to_bv 64 z1)) -> bytes_at bsegs m1 A2 (le8 (Z_to_bv 64 z2)) ->
  A1 = (e_TAPE E + 8 * Z.of_nat (length tws))%Z -> A2 = (A1 + 8)%Z ->
  (Z.of_nat (length tws) + 2 <= e_tcap E)%Z -> (0 <= z1 < 2^64)%Z -> (0 <= z2 < 2^64)%Z ->
  tape_img E (tws ++ [z1; z2]) (sbs ++ []) m1.
Proof.
  intros E tws sbs m1 z1 z2 A1 A2 OK TI B1 B2 -> -> L Hz1 Hz2. pose proof TI as (_ & T2 & _ & T4 & _ & S2 & _). pose proof (ok_sbuf _ OK) as OS.
  pose proof (ok_spa _ OK) as OR. pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (tape_img_app E tws sbs m1 [Z_to_bv 64 z1; Z_to_bv 64 z2] [] TI) as P. cbn [u64s map length] in P.
  rewrite app_nil_r, !u64_small in P by lia.
  apply P; [ | apply timg_bytes_at_nil; lia | cbn; lia | cbn; lia].
  apply bytes_at_app. split; [exact B1|]. rewrite length_le8. exact B2.
Qed.

Lemma tape_img_ghost : forall E t0 s0 tws sbs (m1 : mem), tape_img E tws sbs m1 -> tape_img (s2_ghost E t0 s0) tws sbs m1.
Proof. intros E t0 s0 tws sbs m1 H. exact H. Qed.

Lemma le1_unsigned : forall v : word, map bv_unsigned (le1 v) = [(bv_unsigned v mod 256)%Z].
Proof.
  intros v. unfold le1. cbn [Z_to_le_bytes map]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8)%Z with 256%Z. reflexivity.
Qed.

Lemma tape_img_app_str : forall E tws sbs (m1 : mem) d (cb : list byte) (v0 v1 v2 v3 : word) A, tape_img E tws sbs m1 ->
  A = (e_SBUF E + Z.of_nat (length sbs))%Z ->
  bytes_at bsegs m1 A (le1 v0) -> bytes_at bsegs m1 (A + 1) (le1 v1) -> bytes_at bsegs m1 (A + 2) (le1 v2) -> bytes_at bsegs m1 (A + 3) (le1 v3) ->
  bytes_at bsegs m1 (A + 4) cb -> Z.of_nat (length cb) = d -> bytes_at bsegs m1 (A + 4 + d) (le1 (Z_to_bv 64 0)) ->
  (bv_unsigned v0 mod 256 = d mod 256)%Z -> (bv_unsigned v1 mod 256 = (d / 256) mod 256)%Z ->
  (bv_unsigned v2 mod 256 = (d / 65536) mod 256)%Z -> (bv_unsigned v3 mod 256 = (d / 16777216) mod 256)%Z ->
  (Z.of_nat (length sbs) + d + 5 <= e_scap E)%Z -> (0 <= e_TAPE E)%Z -> (e_TAPE E + 8 * e_tcap E <= 2^64)%Z ->
  tape_img E (tws ++ []) (sbs ++ srec d (map bv_unsigned cb)) m1.
Proof.
  intros E tws sbs m1 d cb v0 v1 v2 v3 A TI -> B0 B1 B2 B3 BC HL BN E0 E1 E2 E3 HCAP HT0 HT1.
  pose proof TI as (_ & _ & T3 & _).
  pose proof (tape_img_app E tws sbs m1 [] (le1 v0 ++ le1 v1 ++ le1 v2 ++ le1 v3 ++ cb ++ le1 (Z_to_bv 64 0)) TI) as P.
  cbn [map] in P. rewrite !map_app, !le1_unsigned, E0, E1, E2, E3 in P.
  change (bv_unsigned (Z_to_bv 64 0) mod 256)%Z with 0%Z in P.
  apply P; clear P.
  - apply timg_bytes_at_nil. lia.
  - apply bytes_at_app. split; [exact B0|]. rewrite length_le1.
    apply bytes_at_app. split; [exact B1|]. rewrite length_le1.
    apply bytes_at_app. split; [replace (e_SBUF E + Z.of_nat (length sbs) + Z.of_nat 1 + Z.of_nat 1)%Z with (e_SBUF E + Z.of_nat (length sbs) + 2)%Z by lia; exact B2|].
    rewrite length_le1.
    apply bytes_at_app. split; [replace (e_SBUF E + Z.of_nat (length sbs) + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z with (e_SBUF E + Z.of_nat (length sbs) + 3)%Z by lia; exact B3|].
    rewrite length_le1.
    apply bytes_at_app. split.
    + replace (e_SBUF E + Z.of_nat (length sbs) + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z with (e_SBUF E + Z.of_nat (length sbs) + 4)%Z by lia. exact BC.
    + replace (e_SBUF E + Z.of_nat (length sbs) + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat (length cb))%Z with (e_SBUF E + Z.of_nat (length sbs) + 4 + d)%Z by lia.
      exact BN.
  - cbn [length]. lia.
  - rewrite !length_app, !length_le1. lia.
Qed.

Lemma str_byte_k : forall d kk, (0 <= d < 2^31)%Z -> (0 <= kk)%Z ->
  (bv_unsigned (Z_to_bv 64 (Z.shiftr (d mod 18446744073709551616) kk)) mod 256 = (d / 2^kk) mod 256)%Z.
Proof.
  intros d kk Hd Hk. rewrite (Z.mod_small d) by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (HP : (1 <= 2^kk)%Z) by (pose proof (Z.pow_pos_nonneg 2 kk); lia).
  assert (0 <= d / 2^kk <= d)%Z.
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|].
    replace d with (1 * d)%Z at 1 by lia. apply Z.mul_le_mono_nonneg_r; lia. }
  rewrite u64_small by lia. reflexivity.
Qed.

Lemma str_word_machine : forall A sbv, (0 <= sbv < 2^56)%Z -> Z.lor (A + sbv - A) 2449958197289549824 = tword t_str sbv.
Proof.
  intros A sbv H. replace (A + sbv - A)%Z with sbv by lia. change 2449958197289549824%Z with (Z.shiftl 34 56). apply tword_lor'. exact H.
Qed.

Lemma empty_word_machine : forall Wv oc, (0 <= Wv + 2 < 2^32)%Z ->
  Z.lor (Z.shiftr ((Wv + 2) * 4294967296) 32) (oc * 72057594037927936) = cword oc (Wv + 2) 0.
Proof.
  intros Wv oc HW. rewrite Z.shiftr_div_pow2 by lia. change (2^32)%Z with 4294967296%Z. rewrite Z.div_mul by lia.
  unfold cword. rewrite Z.lor_comm. change 72057594037927936%Z with (2^56)%Z. rewrite <- (Z.shiftl_mul_pow2 oc 56) by lia.
  rewrite tword_lor by lia. f_equal. lia.
Qed.

Lemma close_word_machine : forall A Wv t, (0 <= Wv < 2^32)%Z ->
  Z.lor (Z.shiftr (Z.shiftl (A + 8 * Wv - A) 29 mod 18446744073709551616) 32) (t * 72057594037927936) = tword t Wv.
Proof.
  intros A Wv t HW. replace (A + 8 * Wv - A)%Z with (Wv * 2^3)%Z by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. change (3 + 29)%Z with 32%Z.
  rewrite (Z.mod_small (Wv * 2^32)) by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia.
  rewrite Z.lor_comm. change 72057594037927936%Z with (2^56)%Z. rewrite <- (Z.shiftl_mul_pow2 t 56) by lia. apply tword_lor. lia.
Qed.
Lemma next2_machine : forall A Wv, (0 <= Wv)%Z -> (Wv + 2 < 2^32)%Z ->
  Z.shiftl ((Z.shiftr (A + 8 * Wv - A) 3 + 2) mod 18446744073709551616) 32 = ((Wv + 2) * 2^32)%Z.
Proof.
  intros A Wv H0 HW. replace (A + 8 * Wv - A)%Z with (Wv * 2^3)%Z by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia.
  rewrite Z.mod_small by lia. apply Z.shiftl_mul_pow2. lia.
Qed.

Definition empty_env (E : s2env) (oc Wv : Z) : s2env := gapp E [cword oc (Wv + 2) 0; tword (oc + 2) Wv] [].

Definition endc_env (E : s2env) (oc ti Wv cv : Z) : s2env := gapp (gpatch E ti (cword oc (Wv + 1) cv)) [tword (oc + 2) ti] [].

Ltac s2_gproj0 :=
  cbn [e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
       e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0 e_tws e_sbs s2_ghost gapp gpatch empty_env endc_env].

Definition tape_ok (tws sbs : list Z) : Prop :=
  tape_wfS (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any (Z.of_nat (length tws)).
Definition s2_fail (x : word) : Prop := (1 <= bv_unsigned x < 64)%Z.

Definition s2_errok (E : s2env) (err : Z) : Prop := (1 <= err < 64)%Z \/ (err = 0%Z /\ tape_ok (e_tws E) (e_sbs E)).
Lemma s2_errok_range : forall E err, s2_errok E err -> (0 <= err < 64)%Z.
Proof. intros E err [H|[-> _]]; lia. Qed.

Ltac s2_timg_assumption :=
  lazymatch goal with
  | |- tape_img _ _ _ ?m =>
      first [ eassumption
            | match goal with TI : tape_img _ _ _ m |- _ => first [ exact TI | rewrite ?app_nil_r in TI; exact TI | rewrite ?app_nil_r; exact TI ] end
            | fail 100 "s2_close_mem: no tape image of the current memory matches the goal's (ghost) environment" ]
  end.

Definition MEMI (E : s2env) (nxt : word) (sl : list cell) (sc : list (bool * Z)) (fc : bv 32) (m1 : mem) : Prop :=
  frm0 fc /\
  rw_cells bsegs m1 (e_spa E) (fr_cells E sl) /\
  rw_cells bsegs m1 (bv_unsigned (e_sp E) + -104) (saved_cells E) /\
  stk bsegs m1 (e_spa E + 312) (bv_unsigned (e_sp E) + -104) /\
  wr_at bsegs m1 (e_FF E) 8 /\
  rw_cells bsegs m1 (e_THIS E) (impl_cells E nxt) /\
  rw_cells bsegs m1 (e_DOC E) (doc_cells E) /\
  u32arr bsegs m1 (e_IDX E) (e_iws E) /\
  bytes_at bsegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
  wr_at bsegs m1 (e_TAPE E) (8 * e_tcap E) /\
  wr_at bsegs m1 (e_SBUF E) (e_scap E) /\
  (exists ocs, u32arr bsegs m1 (e_OC E) ocs /\ length ocs = 2048%nat /\ oc_rel sc ocs) /\
  (exists ias, u8arr bsegs m1 (e_IA E) ias /\ length ias = 1024%nat /\ ia_rel sc ias) /\
  mem_inv bsegs m1 /\ munch (s2_W E) (e_m0 E) m1 /\ wmono bsegs (e_m0 E) m1 /\
  stk bsegs m1 (e_lo E) (e_spa E) /\
  tape_img E (e_tws E) (e_sbs E) m1.

Definition shz_all (E : s2env) (m1 : mem) : Prop :=
  shz m1 (e_THIS E) 96 /\ shz m1 (e_DOC E) 24 /\ shz m1 (e_IDX E) (4 * (e_len E + 3)) /\ shz m1 (e_BUF E) (e_len E + 56) /\
  shz m1 (e_TAPE E) (8 * e_tcap E) /\ shz m1 (e_SBUF E) (e_scap E) /\ shz m1 (e_OC E) 8192 /\ shz m1 (e_IA E) 1024 /\
  shz m1 T_SOWN 256 /\ shz m1 T_DIG 3544 /\ shz m1 T_P10 184 /\ shz m1 T_P5 10416 /\ shz m1 T_ESC 256.

Definition a_shz (E : s2env) : Prop :=
  forall m', munch (s2_W E) (e_m0 E) m' -> wmono bsegs (e_m0 E) m' -> shz_all E m'.

Definition MEMX (E : s2env) (err : Z) (fc : bv 32) (m1 : mem) : Prop :=
  exists nxt sc j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j288 j304,
    MEMI E nxt [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; C8 (wz err); CB 8 j288; CB 8 j304] sc fc m1.

Ltac s2_open_mem H :=
  let ocs := fresh "ocs" in let ias := fresh "ias" in
  destruct H as (FRM & FR & SAV & GAP & FFW & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & (ocs & OCA & OCL & OCR) & (ias & IAA & IAL & IAR) & MI & MU & WM & ST & TIMG);
  unfold fr_cells in FR; unfold saved_cells in SAV; unfold impl_cells in IMPL; unfold doc_cells in DOCC; unfold s2_W in MU;
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac s2_open_memx H :=
  let nxt := fresh "nxt" in let sc := fresh "sc" in
  destruct H as (nxt & sc & H);
  do 28 (let j := fresh "j" in destruct H as (j & H));
  s2_open_mem H.

Inductive forgets : list cell -> list cell -> Prop :=
| fg_nil : forgets [] []
| fg_keep : forall c l l', forgets l l' -> forgets (c :: l) (c :: l')
| fg_drop : forall c l l', forgets l l' -> forgets (c :: l) (CB (csize c) (cbytes c) :: l').

Lemma rw_cells_forgets : forall segs m sl sl', forgets sl sl' -> forall A,
  rw_cells segs m A sl -> rw_cells segs m A sl'.
Proof.
  intros segs m sl sl' H. induction H as [|c l l' H IH|c l l' H IH]; intros A HR; [exact HR| |].
  - change (c :: l) with ([c] ++ l) in HR. apply rw_cells_app in HR. destruct HR as [H1 H2].
    change (c :: l') with ([c] ++ l'). apply rw_cells_app. split; [exact H1|]. apply IH. exact H2.
  - change (c :: l) with ([c] ++ l) in HR. apply rw_cells_app in HR. destruct HR as [H1 H2].
    change (CB (csize c) (cbytes c) :: l') with ([CB (csize c) (cbytes c)] ++ l'). apply rw_cells_app. split.
    + pose proof (rw_cells_merge segs m A [] [c] []) as M. cbn [app cells_size cells_bytes Nat.add] in M.
      rewrite Nat.add_0_r, app_nil_r in M. apply M. exact H1.
    + cbn [cells_size csize Nat.add] in *. rewrite Nat.add_0_r in *. apply IH. exact H2.
Qed.

Lemma MEMI_of_cells : forall E nxt cs sl sc fc m1,
  frm0 fc -> rw_cells bsegs m1 (e_spa E) cs -> forgets cs (fr_cells E sl) ->
  rw_cells bsegs m1 (bv_unsigned (e_sp E) + -104) (saved_cells E) ->
  stk bsegs m1 (e_spa E + 312) (bv_unsigned (e_sp E) + -104) ->
  wr_at bsegs m1 (e_FF E) 8 ->
  rw_cells bsegs m1 (e_THIS E) (impl_cells E nxt) ->
  rw_cells bsegs m1 (e_DOC E) (doc_cells E) ->
  u32arr bsegs m1 (e_IDX E) (e_iws E) ->
  bytes_at bsegs m1 (e_BUF E) (padded_bytes (e_bs E)) ->
  wr_at bsegs m1 (e_TAPE E) (8 * e_tcap E) ->
  wr_at bsegs m1 (e_SBUF E) (e_scap E) ->
  (exists ocs, u32arr bsegs m1 (e_OC E) ocs /\ length ocs = 2048%nat /\ oc_rel sc ocs) ->
  (exists ias, u8arr bsegs m1 (e_IA E) ias /\ length ias = 1024%nat /\ ia_rel sc ias) ->
  mem_inv bsegs m1 -> munch (s2_W E) (e_m0 E) m1 -> wmono bsegs (e_m0 E) m1 -> stk bsegs m1 (e_lo E) (e_spa E) ->
  tape_img E (e_tws E) (e_sbs E) m1 ->
  MEMI E nxt sl sc fc m1.
Proof.
  intros E nxt cs sl sc fc m1 H0 H1 HF H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.
  unfold MEMI. split; [exact H0|]. split; [exact (rw_cells_forgets bsegs m1 _ _ HF _ H1)|].
  repeat (split; [assumption|]). assumption.
Qed.

Lemma fg_keep_eq : forall c c' l l', c = c' -> forgets l l' -> forgets (c :: l) (c' :: l').
Proof. intros c c' l l' <- H. apply fg_keep. exact H. Qed.
Ltac forgets_tac := s2_gproj0; repeat first [ apply fg_nil | apply fg_keep | apply fg_drop | (apply fg_keep_eq; [solve [f_equal; f_equal; lia] |]) ].

Ltac s2_close_mem :=
  lazymatch goal with
  | |- MEMI ?E _ _ _ _ ?m =>
      lazymatch goal with
      | FRh : rw_cells _ m (e_spa _) ?cs |- _ =>
          eapply (MEMI_of_cells E _ cs);
          [ eassumption | exact FRh | unfold fr_cells; forgets_tac
          | unfold saved_cells; eassumption | eassumption | eassumption | unfold impl_cells; eassumption | unfold doc_cells; eassumption
          | eassumption | eassumption | eassumption | eassumption
          | eexists; split; [eassumption| split] | eexists; split; [eassumption| split]
          | eassumption | unfold s2_W; eassumption | eassumption | eassumption
          | s2_timg_assumption ]
      end
  end.
Ltac s2_close_mem0 := s2_close_mem; eassumption.

Ltac s2_close_auto :=
  s2_close_mem;
  [ rewrite ?upd_length; eassumption
  | first [ eassumption | apply oc_rel_upd_other; [eassumption | intros jj Hjj; lia] ]
  | rewrite ?upd_length; eassumption
  | eassumption ].

Ltac s2_close_forget := s2_close_mem.
Ltac s2_close_memx :=
  unfold MEMX; do 30 eexists;
  s2_close_mem; [ rewrite ?upd_length; eassumption | apply oc_rel_nil | rewrite ?upd_length; eassumption | apply ia_rel_nil ].

Definition s2_hidden (P : Prop) : Prop := P.
Ltac s2_unhide := repeat match goal with H : s2_hidden _ |- _ => unfold s2_hidden in H end.

Ltac s2_env OK :=
  pose proof (ok_len _ OK) as EK_len; pose proof (ok_tcap _ OK) as EK_tcap; pose proof (ok_scap _ OK) as EK_scap;
  pose proof (ok_iwl _ OK) as EK_iwl; pose proof (n_le_len _ _ (ok_s1 _ OK)) as EK_nlen;
  pose proof (ok_glo _ OK) as EK_glo; pose proof (ok_spa _ OK) as EK_spa; pose proof (ok_sptop _ OK) as EK_sptop;
  pose proof (ok_ff _ OK) as EK_ff; pose proof (ok_this _ OK) as EK_this;
  pose proof (ok_doc _ OK) as EK_doc; pose proof (ok_idx _ OK) as EK_idx; pose proof (ok_buf _ OK) as EK_buf;
  pose proof (ok_tape _ OK) as EK_tape; pose proof (ok_sbuf _ OK) as EK_sbuf; pose proof (ok_oc _ OK) as EK_oc;
  pose proof (ok_ia _ OK) as EK_ia;
  pose proof (ok_al_spa _ OK : s2_hidden _) as EK_al_spa; pose proof (ok_al_this _ OK : s2_hidden _) as EK_al_this;
  pose proof (ok_al_idx _ OK : s2_hidden _) as EK_al_idx; pose proof (ok_al_tape _ OK : s2_hidden _) as EK_al_tape;
  pose proof (ok_al_oc _ OK : s2_hidden _) as EK_al_oc; pose proof (ok_al_doc _ OK : s2_hidden _) as EK_al_doc;
  unfold S2_LEN_MAX in *.

Definition env_at (E : s2env) (m : mem) : s2env :=
  mkS2Env (e_ra E) (e_sp E) (e_gp E) (e_tp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E)
          (e_lo E) (e_spa E) (e_FF E) (e_THIS E) (e_DOC E) (e_IDX E) (e_BUF E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E)
          (e_bs E) (e_idxs E) (e_iws E) (e_tcap E) (e_scap E)
          (e_vptr E) (e_p12 E) (e_nxt0 E) (e_p28 E) (e_capv E) (e_p50 E) (e_dcap E) (e_j0 E) (e_j256 E) m (e_tws E) (e_sbs E).
Lemma env_at_ok : forall E m, env_ok E -> env_ok (env_at E m).
Proof. intros E m H. destruct H. constructor; cbn [env_at e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0]; assumption. Qed.

Section Access.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Lemma n_bound : (1 <= e_n E <= 1048512)%Z.
  Proof using OK.
    pose proof (n_pos _ _ (ok_s1 _ OK)). pose proof (n_le_len _ _ (ok_s1 _ OK)). pose proof (ok_len _ OK). unfold S2_LEN_MAX in *. lia.
  Qed.

  Lemma off_bound : forall k, (0 <= k <= e_n E)%Z -> (0 <= e_off E k <= e_len E)%Z.
  Proof using OK. intros k Hk. exact (off_range _ _ (ok_s1 _ OK) k Hk). Qed.

  Lemma idx_nth : forall k, (0 <= k < e_n E + 3)%Z -> nth_error (e_iws E) (Z.to_nat k) = Some (wz (e_off E k)).
  Proof using OK.
    intros k Hk.
    assert (L : (Z.to_nat k < length (ext (e_bs E) (e_idxs E)))%nat).
    { pose proof (length_ext (e_bs E) (e_idxs E)). unfold n in *. lia. }
    rewrite <- (firstn_skipn (length (e_idxs E) + 3) (e_iws E)), (ok_iws _ OK).
    rewrite nth_error_app1 by (rewrite length_map; exact L).
    rewrite nth_error_map. unfold off. rewrite (nth_error_nth' _ 0%Z L). reflexivity.
  Qed.

  Lemma idx_read : forall (m1 : mem) k, u32arr bsegs m1 (e_IDX E) (e_iws E) -> (0 <= k < e_n E + 3)%Z ->
    ov_read_bytes bsegs m1 (wa (e_IDX E + 4 * k)) 4 = Some (le4 (wz (e_off E k))).
  Proof using OK.
    intros m1 k H Hk. eapply (u32arr_read bsegs m1 (e_IDX E) (e_iws E) k); [exact H| apply idx_nth; exact Hk| lia| reflexivity].
  Qed.

  Lemma tok_range : forall k, (0 <= e_tok E k < 256)%Z.
  Proof using OK. intros k. apply B_range. exact (ok_bytes _ OK). Qed.

  Lemma tok_read : forall (m1 : mem) k, bytes_at bsegs m1 (e_BUF E) (padded_bytes (e_bs E)) -> (0 <= k <= e_n E)%Z ->
    ov_read_bytes bsegs m1 (wa (e_BUF E + e_off E k)) 1 = Some [Z_to_bv 8 (e_tok E k)].
  Proof using OK.
    intros m1 k H Hk. pose proof (off_range _ _ (ok_s1 _ OK) k Hk). apply buf_read; [exact H| lia].
  Qed.
End Access.

Ltac lia0 :=
  first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                            | Zify.zify; xlia zchecker ]
        | Zify.zify; xlia zchecker ].

Ltac s2_pose_sep :=
  lazymatch goal with OKh : env_ok ?E |- _ =>
    let go A B L := try (lazymatch goal with |- context [A] => lazymatch goal with |- context [B] => pose proof (L _ OKh) end end) in
    go (e_THIS E) (e_IDX E) ok_d_this_idx; go (e_THIS E) (e_BUF E) ok_d_this_buf; go (e_THIS E) (e_TAPE E) ok_d_this_tape;
    go (e_THIS E) (e_SBUF E) ok_d_this_sbuf; go (e_THIS E) (e_OC E) ok_d_this_oc; go (e_THIS E) (e_IA E) ok_d_this_ia;
    go (e_TAPE E) (e_IDX E) ok_d_tape_idx; go (e_TAPE E) (e_BUF E) ok_d_tape_buf; go (e_TAPE E) (e_SBUF E) ok_d_tape_sbuf;
    go (e_TAPE E) (e_OC E) ok_d_tape_oc; go (e_TAPE E) (e_IA E) ok_d_tape_ia;
    go (e_SBUF E) (e_IDX E) ok_d_sbuf_idx; go (e_SBUF E) (e_BUF E) ok_d_sbuf_buf; go (e_SBUF E) (e_OC E) ok_d_sbuf_oc; go (e_SBUF E) (e_IA E) ok_d_sbuf_ia;
    go (e_OC E) (e_IDX E) ok_d_oc_idx; go (e_OC E) (e_BUF E) ok_d_oc_buf; go (e_OC E) (e_IA E) ok_d_oc_ia;
    go (e_IA E) (e_IDX E) ok_d_ia_idx; go (e_IA E) (e_BUF E) ok_d_ia_buf;
    go (e_DOC E) (e_THIS E) ok_d_doc_this; go (e_DOC E) (e_TAPE E) ok_d_doc_tape; go (e_DOC E) (e_SBUF E) ok_d_doc_sbuf;
    go (e_DOC E) (e_OC E) ok_d_doc_oc; go (e_DOC E) (e_IA E) ok_d_doc_ia;
    go (e_FF E) (e_THIS E) ok_d_ff_this; go (e_FF E) (e_DOC E) ok_d_ff_doc; go (e_FF E) (e_IDX E) ok_d_ff_idx; go (e_FF E) (e_BUF E) ok_d_ff_buf;
    go (e_FF E) (e_TAPE E) ok_d_ff_tape; go (e_FF E) (e_SBUF E) ok_d_ff_sbuf; go (e_FF E) (e_OC E) ok_d_ff_oc; go (e_FF E) (e_IA E) ok_d_ff_ia;
    idtac
  end.

Ltac s2lia := first [ lia0 | cx_posed_something2 s2_pose_sep; lia0 ].

Ltac cx_lia_t1 := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac word_eq_tac ::=
  first [ exact eq_refl
        | f_equal; cx_lia_t1
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | f_equal; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].

Ltac tlia0 := sf_clear_big;
             first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
                   | Zify.zify; xlia zchecker
                   | sf_unhide;
                     first [ zify_prune_neg; Zify.zify; xlia zchecker
                           | zify_prune_plain; Zify.zify; xlia zchecker
                           | Zify.zify; xlia zchecker ] ].
Ltac s2tlia := first [ tlia0 | s2_pose_sep; tlia0 ].

Lemma tape_store_ok : forall E (m1 : mem) i, wr_at bsegs m1 (e_TAPE E) (8 * e_tcap E) -> (0 <= i < e_tcap E)%Z ->
  store_ok bsegs m1 (wa (e_TAPE E + 8 * i)) 8 = true.
Proof. intros E m1 i H Hi. apply (wr_at_store_ok bsegs m1 (e_TAPE E) (8 * e_tcap E) (8 * i) 8 H); lia. Qed.

Ltac s2_cur_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => k m end.

Notation S2R E pc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m :=
  (MS (mkR x1 (Z_to_bv 64 (e_SP E)) (e_gp E) (e_tp E) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

Ltac s2_old_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) => k m end.

Lemma sbuf_store_ok : forall E (m1 : mem) i, wr_at bsegs m1 (e_SBUF E) (e_scap E) -> (0 <= i < e_scap E)%Z ->
  store_ok bsegs m1 (wa (e_SBUF E + i)) 1 = true.
Proof. intros E m1 i H Hi. apply (wr_at_store_ok bsegs m1 (e_SBUF E) (e_scap E) i 1 H); lia. Qed.

Lemma sbuf_store_ok_at : forall E (m1 : mem) i a, wr_at bsegs m1 (e_SBUF E) (e_scap E) -> (0 <= i < e_scap E)%Z ->
  a = wa (e_SBUF E + i) -> store_ok bsegs m1 a 1 = true.
Proof. intros E m1 i a H Hi ->. apply sbuf_store_ok; assumption. Qed.

Lemma buf_read_at : forall (m : mem) A bs i a,
  bytes_at bsegs m A (padded_bytes bs) -> (0 <= i < blen bs + 64)%Z -> a = wa (A + i) ->
  ov_read_bytes bsegs m a 1 = Some [Z_to_bv 8 (B bs i)].
Proof. intros m A bs i a H Hi ->. apply buf_read; assumption. Qed.

Lemma wr_store_ok_at : forall (m : mem) A N i (j : nat) a,
  wr_at bsegs m A N -> (0 <= i)%Z -> (i + Z.of_nat j <= N)%Z -> a = wa (A + i) -> store_ok bsegs m a j = true.
Proof. intros m A N i j a H H0 H1 ->. apply (wr_at_store_ok bsegs m A N i j H); assumption. Qed.

Lemma zxb_B : forall bs i, bytes_ok bs -> zxb (Z_to_bv 8 (B bs i)) = Z_to_bv 64 (B bs i).
Proof. intros bs i H. apply zxb_small. apply B_range. exact H. Qed.

Ltac strip_base Ea A :=
  lazymatch Ea with
  | A => constr:(0%Z)
  | Z.add A ?i => constr:(i)
  | Z.add ?X ?c => let r := strip_base X A in constr:(Z.add r c)
  end.

Ltac s2_load_buf :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | H : bytes_at segs m ?A (padded_bytes ?bs) |- _ =>
          let Ea := addr_expr a in
          let idx := strip_base Ea A in
          rewrite (buf_read_at m A bs idx a H ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.

Ltac s2_store_wr :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
      let Ea := addr_expr a in
      match goal with
      | H : wr_at segs m ?A ?N |- _ =>
          let idx := strip_base Ea A in
          rewrite (wr_store_ok_at m A N idx n a H ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(unfold wa; f_equal; lia));
          cbv beta iota
      end
  end.

Ltac solve_store0 :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in addr_near k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Ltac s2_store_done_wr :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in
      (match goal with
       | H : wr_at segs m ?A ?N |- _ =>
           let idx := strip_base Ea A in
           let n := lazymatch bs with
                    | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat) | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
                    | [_] => constr:(1%nat) end in
           let HS := fresh "HSOK" in
           assert (HS : store_ok segs m a n = true)
             by (apply (wr_store_ok_at m A N idx n a H); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia])
       end);
      store_done
  | _ => idtac
  end.
Ltac sstep := zstep; s2norm; s2_store_done_wr.

Definition exit_k (E : s2env) (Q : machine_state -> Prop) : Prop :=
  forall err x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
         (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    s2_errok E err ->
    MEMX E err fc m1 ->
    evt bsegs Q
      (S2R E 0xcd488 x1 x5 x6 x7 (e_sp E) (Z_to_bv 64 (e_spa E)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (SHA (e_FF E))) x20
           x21 x22 x23 x24 x25 (Z_to_bv 64 (e_FF E)) x27 x28 x29 x30 x31 F fc m1).

Lemma nth_error_ex : forall {X} (l : list X) i, (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof. intros X l i H. destruct (nth_error l i) eqn:E; [eauto|]. apply nth_error_None in E. lia. Qed.

Lemma shzr_this : forall E (m1 : mem) x a, shz_all E m1 -> (e_THIS E <= x < e_THIS E + (96))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (S & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_doc : forall E (m1 : mem) x a, shz_all E m1 -> (e_DOC E <= x < e_DOC E + (24))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & S & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_idx : forall E (m1 : mem) x a, shz_all E m1 -> (e_IDX E <= x < e_IDX E + (4 * (e_len E + 3)))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & S & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_buf : forall E (m1 : mem) x a, shz_all E m1 -> (e_BUF E <= x < e_BUF E + (e_len E + 56))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & S & _ & _ & _ & _ & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_tape : forall E (m1 : mem) x a, shz_all E m1 -> (e_TAPE E <= x < e_TAPE E + (8 * e_tcap E))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & S & _ & _ & _ & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_sbuf : forall E (m1 : mem) x a, shz_all E m1 -> (e_SBUF E <= x < e_SBUF E + (e_scap E))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & S & _ & _ & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_oc : forall E (m1 : mem) x a, shz_all E m1 -> (e_OC E <= x < e_OC E + (8192))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & _ & S & _ & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_ia : forall E (m1 : mem) x a, shz_all E m1 -> (e_IA E <= x < e_IA E + (1024))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & _ & _ & S & _ & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_sown : forall E (m1 : mem) x a, shz_all E m1 -> (T_SOWN <= x < T_SOWN + (256))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & _ & _ & _ & S & _ & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_dig : forall E (m1 : mem) x a, shz_all E m1 -> (T_DIG <= x < T_DIG + (3544))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & _ & _ & _ & _ & S & _ & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_p10 : forall E (m1 : mem) x a, shz_all E m1 -> (T_P10 <= x < T_P10 + (184))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S & _ & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_p5 : forall E (m1 : mem) x a, shz_all E m1 -> (T_P5 <= x < T_P5 + (10416))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S & _) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Lemma shzr_esc : forall E (m1 : mem) x a, shz_all E m1 -> (T_ESC <= x < T_ESC + (256))%Z -> a = wa (SHA x) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros E m1 x a (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S) Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.

Ltac s2_shz_lemma E x :=
  lazymatch x with
  | context [e_THIS E] => constr:(shzr_this) | context [e_DOC E] => constr:(shzr_doc) | context [e_IDX E] => constr:(shzr_idx)
  | context [e_BUF E] => constr:(shzr_buf) | context [e_TAPE E] => constr:(shzr_tape) | context [e_SBUF E] => constr:(shzr_sbuf)
  | context [e_OC E] => constr:(shzr_oc) | context [e_IA E] => constr:(shzr_ia)
  | context [147744%Z] => constr:(shzr_sown) | context [148064%Z] => constr:(shzr_dig) | context [152480%Z] => constr:(shzr_p10)
  | context [152704%Z] => constr:(shzr_p5) | context [166624%Z] => constr:(shzr_esc)
  end.

Ltac s2_shz_side := unfold T_SOWN, T_DIG, T_P10, T_P5, T_ESC; lia.
Ltac s2_load_shadow :=
  match goal with
  | |- context [ov_read_bytes bsegs ?m ?a 1] =>
      let Ea := addr_expr a in
      let x := lazymatch Ea with (Z.shiftr ?x 3 + 2147450880)%Z => x end in
      lazymatch goal with
      | SHZh : a_shz ?E, MUh : munch _ (e_m0 ?E) m, WMh : wmono bsegs (e_m0 ?E) m |- _ =>
          let L := s2_shz_lemma E x in
          rewrite (L E m x a (SHZh m MUh WMh) ltac:(s2_shz_side) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.

Ltac s2_shz_norm := rewrite ?sxb_z8, ?zxb_z8, ?lbu_z8.

Definition rootprim_k (E : s2env) (Q : machine_state -> Prop) (pc : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs4 xs7 xt3 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (3)); CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E pc xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (SHA (e_BUF E + e_off E 0))) (Z_to_bv 64 (3)) (Z_to_bv 64 (e_IDX E + 4)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (SHA (e_IDX E))) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (e_TAPE E)) (Z_to_bv 64 (e_THIS E + 56)) xs7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_IDX E)) xt3 (Z_to_bv 64 (SHA (e_THIS E + 56))) xt5 xt6 F fc m1).

Definition objbegin_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xbb810 xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition arrbegin_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xbc308 xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition arrvalue_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xa2 xa3 xa4 xa5 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xbf93c xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_OC E + 8 * depth s)) (Z_to_bv 64 (e_OC E)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition objcont_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs5 xs7 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j176 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); CB 8 j176; C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * k s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xcd500 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (SHA (e_THIS E + 56))) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) xs7 xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition arrcont_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs5 xs7 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j176 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); CB 8 j176; C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * k s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xce2dc xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (SHA (e_THIS E + 56))) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) xs7 xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition scopeend_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xce260 xra xt0 (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition docend_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * k s)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xbcfe4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition arrstr_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs5 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xbfc7c xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition arrnum_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt2 xa1 xa3 xa4 xa5 xa6 xs5 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j184 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc04a4 xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_tok E (k s))) xa1 (Z_to_bv 64 (e_off E (k s))) xa3 xa4 xa5 xa6 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition arratom_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j184 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc056c xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_tok E (k s))) xa1 (Z_to_bv 64 (e_off E (k s))) xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition objstr_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc24b8 xra xt0 xt1 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (e_SBUF E + sb s + -1)) (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition objnum_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xa1 xa3 xa4 xa5 xa6 xa7 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc2d80 xra xt0 xt1 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_tok E (k s))) xa1 (Z_to_bv 64 (e_off E (k s))) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))) (Z_to_bv 64 (e_SBUF E + sb s + -1)) (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition objatom_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc2e4c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_tok E (k s))) xa1 (Z_to_bv 64 (e_off E (k s))) xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition keyb_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xa1 xa2 xa3 xa5 xa6 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j184 j192 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xcd7f8 xra xt0 xt1 (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa1 xa2 xa3 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xa5 xa6 xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition keya_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt2 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j152 j160 j168 j184 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; C8 (Z_to_bv 64 (18446744073709495296)); CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; C8 (Z_to_bv 64 (e_IDX E + 4 * k s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         ((false, W s) :: scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xbba48 xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s + 1)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_TAPE E + 8 * (W s + 1))) (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (8 * (depth s + 1))) (Z_to_bv 64 2449958197289549824) xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Ltac addr_leaf a := lazymatch a with Z.add ?x _ => addr_leaf x | _ => a end.

Ltac s2_timg_transport m a bs n Hn Ha Hl :=
  lazymatch goal with
  | H : tape_img ?E ?tws ?sbs m |- _ =>
      lazymatch goal with
      | OKh : env_ok E |- _ =>
        let b := addr_leaf a in
        first [ lazymatch b with
                | e_TAPE E => apply (tape_img_write_tape E OKh tws sbs m a bs n Hn Ha Hl) in H; [ | rewrite ?length_app, ?zupd_length; cbn [length]; tslia ]
                | e_SBUF E => apply (tape_img_write_sbuf E OKh tws sbs m a bs n Hn Ha Hl) in H; [ | rewrite ?length_app; cbn [length]; tslia ]
                | e_OC E => apply (tape_img_write_oc E OKh tws sbs m a bs n Hn Ha Hl) in H; [ | tslia ]
                | e_IA E => apply (tape_img_write_ia E OKh tws sbs m a bs n Hn Ha Hl) in H; [ | tslia ]
                | e_THIS E => apply (tape_img_write_this E OKh tws sbs m a bs n Hn Ha Hl) in H; [ | tslia ]
                | e_FF E => apply (tape_img_write_ff E OKh tws sbs m a bs n Hn Ha Hl) in H; [ | tslia ]
                | _ => apply (tape_img_write_stack E OKh tws sbs m a bs n Hn Ha Hl) in H; [ | tslia ]
                end
              | fail 100 "tape_img: cannot transport through the store at" a ]
      | _ => fail 100 "tape_img: no [env_ok] hypothesis for its environment in the context"
      end
  | _ => idtac
  end.

Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= s2_timg_transport m a bs n Hn Ha Hl.

Ltac s2_note_store :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in
      let NW := fresh "NEWCH" in

      let bs' := lazymatch bs with
                 | Z_to_le_bytes 8 ?lit => constr:(le8 (Z_to_bv 64 lit))
                 | Z_to_le_bytes 4 ?lit => constr:(le4 (Z_to_bv 64 lit))
                 | Z_to_le_bytes 1 ?lit => constr:(le1 (Z_to_bv 64 lit))
                 | _ => bs end in
      assert (NW : bytes_at segs (write_to_mem m (wa Ea) bs) Ea bs')
        by (change bs' with bs; apply bytes_at_write_same; [tlia | simpl_sizes; rewrite ?length_Z_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; tlia])
  end.

Ltac s2_errlit := left; lia.

Lemma MEMI_ghost : forall E tws sbs nxt sl sc fc (m1 : mem),
  MEMI E nxt sl sc fc m1 -> tape_img E tws sbs m1 -> MEMI (s2_ghost E tws sbs) nxt sl sc fc m1.
Proof.
  intros E tws sbs nxt sl sc fc m1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & _) TI.
  repeat (split; [assumption|]). exact TI.
Qed.

Lemma MEMX_ghost : forall E tws sbs err fc (m1 : mem), MEMX E err fc m1 -> tape_img E tws sbs m1 -> MEMX (s2_ghost E tws sbs) err fc m1.
Proof.
  intros E tws sbs err fc m1 (nxt & sc & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & j16 & j17 & j18 & j19 & j20 & j21 & j22 & j23 & j24 & j25 & j26 & j27 & HM) TI.
  exists nxt, sc, j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15, j16, j17, j18, j19, j20, j21, j22, j23, j24, j25, j26, j27. exact (MEMI_ghost E tws sbs _ _ _ _ m1 HM TI).
Qed.

Lemma arrvalue_k_hole : forall E Q (s : st), env_ok E -> (Z.of_nat (length (e_tws E)) + 1 <= e_tcap E)%Z ->
  (forall h, arrvalue_k (gapp E [h] []) Q s) -> arrvalue_k E Q s.
Proof.
  intros E Q s OK HL H. unfold arrvalue_k in *.
  intros until m1. intros HM.
  pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI).
  destruct (timg_hole8 E _ _ m1 (Z.of_nat (length (e_tws E))) TI ltac:(lia)) as (hv & HH).
  pose proof (bv_unsigned_in_range 64 hv) as HR. unfold bv_modulus in HR. cbn in HR.
  rewrite <- (Z_to_bv_bv_unsigned hv) in HH.
  pose proof (tape_img_app1 E _ _ m1 (bv_unsigned hv) _ OK TI HH eq_refl HL HR) as TI'.
  eapply (H (bv_unsigned hv)). exact (MEMI_ghost E _ _ _ _ _ _ m1 HM TI').
Qed.

Ltac s2_note_tape :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in let b := addr_leaf Ea in
      lazymatch b with e_TAPE _ => s2_note_store | _ => idtac end
  | _ => idtac
  end.

