(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK Require Import ZStep ZMem ZSysLite ZCall ZArr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma code_op_eq : forall e, code_op e = e mod 256.
Proof. intros e. unfold code_op. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma code_bits_eq : forall e, code_bits e = (Z.shiftr e 8) mod 256.
Proof. intros e. unfold code_bits. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma code_val_eq : forall e, code_val e = (Z.shiftr e 16) mod 65536.
Proof. intros e. unfold code_val. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma code_op_range : forall e, 0 <= code_op e < 256.
Proof. intros e. rewrite code_op_eq. apply Z.mod_pos_bound. lia. Qed.
Lemma code_bits_range : forall e, 0 <= code_bits e < 256.
Proof. intros e. rewrite code_bits_eq. apply Z.mod_pos_bound. lia. Qed.
Lemma code_val_range : forall e, 0 <= code_val e < 65536.
Proof. intros e. rewrite code_val_eq. apply Z.mod_pos_bound. lia. Qed.

Lemma le4_split : forall e,
  Z_to_le_bytes 4 e = Z_to_le_bytes 1 e ++ Z_to_le_bytes 1 (Z.shiftr e 8) ++ Z_to_le_bytes 2 (Z.shiftr e 16).
Proof.
  intros e. change 4%nat with (1 + (1 + 2))%nat. rewrite Z_to_le_bytes_add.
  change (8 * Z.of_nat 1) with 8. rewrite (Z_to_le_bytes_add 1 2).
  change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_shiftr by lia. reflexivity.
Qed.

Lemma Z_to_bv8_mod256 : forall v, Z_to_bv 8 (v mod 256) = Z_to_bv 8 v.
Proof.
  intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.
Lemma Z_to_le_bytes_1_mod : forall v, Z_to_le_bytes 1 (v mod 256) = Z_to_le_bytes 1 v.
Proof. intros v. cbn [Z_to_le_bytes]. rewrite Z_to_bv8_mod256. reflexivity. Qed.
Lemma mod_mul_mod : forall v a b, 0 < a -> 0 < b -> (v mod (a * b)) mod a = v mod a.
Proof.
  intros v a b Ha Hb.
  rewrite (Z.rem_mul_r v a b) by lia.
  replace (v mod a + a * ((v / a) mod b)) with (v mod a + ((v / a) mod b) * a) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma Z_to_le_bytes_2_mod : forall v, Z_to_le_bytes 2 (v mod 65536) = Z_to_le_bytes 2 v.
Proof.
  intros v. cbn [Z_to_le_bytes]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    change 65536 with (256 * 256). apply mod_mul_mod; lia.
  - f_equal. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite <- (Z_to_bv8_mod256 (v / 256)). rewrite <- (Z_to_bv8_mod256 (v mod 65536 / 256)). f_equal.
    change 65536 with (256 * 256).
    pose proof (Z.div_mod v (256 * 256) ltac:(lia)) as E.
    pose proof (Z.mod_pos_bound v (256 * 256) ltac:(lia)) as B.
    set (q := v / (256 * 256)) in *. set (r := v mod (256 * 256)) in *.
    rewrite E. replace (256 * 256 * q + r) with (r + (256 * q) * 256) by lia.
    rewrite Z.div_add by lia. replace (r / 256 + 256 * q) with (r / 256 + q * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Section A4.
Variable segs : list Segment.

Lemma mem_arr4_cells : forall M base n f i,
  mem_arr 4 segs M base n f -> 0 <= i < n ->
  mem_u8 segs M (base + 4 * i) (code_op (f i)) /\
  mem_u8 segs M (base + 4 * i + 1) (code_bits (f i)) /\
  mem_u16 segs M (base + 4 * i + 2) (code_val (f i)).
Proof.
  intros M base n f i Ha Hi.
  pose proof (mem_arr_get segs 4 M base n f i Ha Hi) as H. change (Z.to_nat 4) with 4%nat in H.
  rewrite le4_split in H.
  pose proof (mem_is_app_l segs M _ _ _ H) as H0.
  pose proof (mem_is_app_r segs M _ _ _ H) as H12. rewrite length_Z_to_le_bytes in H12. change (Z.of_nat 1) with 1 in H12.
  pose proof (mem_is_app_l segs M _ _ _ H12) as H1.
  pose proof (mem_is_app_r segs M _ _ _ H12) as H2. rewrite length_Z_to_le_bytes in H2. change (Z.of_nat 1) with 1 in H2.
  unfold mem_u8, mem_u16. rewrite code_op_eq, code_bits_eq, code_val_eq.
  rewrite Z_to_le_bytes_1_mod, Z_to_le_bytes_1_mod, Z_to_le_bytes_2_mod.
  replace (base + 4 * i + 2) with (base + 4 * i + 1 + 1) by lia.
  split; [exact H0 | split; [exact H1 | exact H2]].
Qed.

Lemma zu_lbu_arr4_op : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (code_op (f i)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  destruct (mem_arr4_cells M base n f i Ha Hi) as (H0 & _ & _).
  eapply zu_lbu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. exact (mem_u8_rdn _ _ _ _ H0).
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_small by (apply code_op_range). exact Hk.
Qed.

Lemma zu_lbu_arr4_bits : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i + 1 -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (code_bits (f i)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  destruct (mem_arr4_cells M base n f i Ha Hi) as (_ & H1 & _).
  eapply zu_lbu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. exact (mem_u8_rdn _ _ _ _ H1).
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_small by (apply code_bits_range). exact Hk.
Qed.

Lemma zu_lhu_arr4_val : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i + 2 -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (code_val (f i)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  destruct (mem_arr4_cells M base n f i Ha Hi) as (_ & _ & H2).
  eapply zu_lhu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. exact (mem_u16_rdn _ _ _ _ H2).
  - pose proof (bytes_le_cell 2 (code_val (f i)) ltac:(lia)) as B. change (Z.to_nat 2) with 2%nat in B.
    rewrite B. unfold cell_mod. change (2 ^ (8 * 2)) with 65536.
    rewrite Z.mod_small by (apply code_val_range). exact Hk.
Qed.
Lemma le2_split : forall e, Z_to_le_bytes 2 e = Z_to_le_bytes 1 e ++ Z_to_le_bytes 1 (Z.shiftr e 8).
Proof.
  intros e. change 2%nat with (1 + 1)%nat. rewrite Z_to_le_bytes_add.
  change (8 * Z.of_nat 1) with 8. reflexivity.
Qed.

Lemma mem_arr2_lo8 : forall M base n f i,
  mem_arr 2 segs M base n f -> 0 <= i < n ->
  mem_u8 segs M (base + 2 * i) ((f i) mod 256).
Proof.
  intros M base n f i Ha Hi.
  pose proof (mem_arr_get segs 2 M base n f i Ha Hi) as H. change (Z.to_nat 2) with 2%nat in H.
  rewrite le2_split in H.
  pose proof (mem_is_app_l segs M _ _ _ H) as H0.
  unfold mem_u8. rewrite Z_to_le_bytes_1_mod. exact H0.
Qed.

Lemma zu_lbu_arr2_lo : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 2 segs M base n f -> zrd_l Rb l rs + bv_signed imm = base + 2 * i -> 0 <= i < n ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd ((f i) mod 256) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  pose proof (mem_arr2_lo8 M base n f i Ha Hi) as H0.
  eapply zu_lbu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. exact (mem_u8_rdn _ _ _ _ H0).
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by lia. exact Hk.
Qed.
End A4.

Section A4W.
Variable segs : list Segment.

Lemma code_pack_small : forall op bits val, 0 <= op < 256 -> 0 <= bits < 256 -> 0 <= val < 65536 ->
  code_pack op bits val = op + 256 * bits + 65536 * val.
Proof.
  intros op bits val Ho Hb Hv. unfold code_pack, ZIface.wrap8, ZIface.wrap16.
  change 255 with (Z.ones 8). change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma mem_arr4_pack : forall M a op bits val,
  mem_u8 segs M a op -> mem_u8 segs M (a + 1) bits -> mem_u16 segs M (a + 2) val ->
  0 <= a -> a + 4 <= two64 -> 0 <= op < 256 -> 0 <= bits < 256 -> 0 <= val < 65536 ->
  mem_is segs M a (Z_to_le_bytes 4 (code_pack op bits val)).
Proof.
  intros M a op bits val H0 H1 H2 Ha Ha4 Ho Hb Hv.
  rewrite le4_split. unfold mem_u8, mem_u16 in *.
  assert (E0 : Z_to_le_bytes 1 (code_pack op bits val) = Z_to_le_bytes 1 op).
  { rewrite <- (Z_to_le_bytes_1_mod (code_pack _ _ _)), <- (Z_to_le_bytes_1_mod op). f_equal.
    rewrite code_pack_small by lia. rewrite Z.mod_small with (a := op) by lia.
    replace (op + 256 * bits + 65536 * val) with (op + (bits + 256 * val) * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (E1 : Z_to_le_bytes 1 (Z.shiftr (code_pack op bits val) 8) = Z_to_le_bytes 1 bits).
  { rewrite <- (Z_to_le_bytes_1_mod (Z.shiftr _ _)), <- (Z_to_le_bytes_1_mod bits). f_equal.
    rewrite code_pack_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (op + 256 * bits + 65536 * val) with (op + (bits + val * 256) * 256) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small op 256) by lia. rewrite Z.add_0_l.
    rewrite Z.mod_add by lia. rewrite !Z.mod_small by lia. reflexivity. }
  assert (E2 : Z_to_le_bytes 2 (Z.shiftr (code_pack op bits val) 16) = Z_to_le_bytes 2 val).
  { f_equal. rewrite code_pack_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
    replace (op + 256 * bits + 65536 * val) with ((op + 256 * bits) + val * 65536) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small (op + 256 * bits) 65536) by lia. lia. }
  rewrite E0, E1, E2.
  apply mem_is_app; [exact H0 | | lia | rewrite !length_app, !length_Z_to_le_bytes; cbn; lia].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 1) with 1.
  apply mem_is_app; [exact H1 | | lia | rewrite !length_Z_to_le_bytes; cbn; lia].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 1) with 1. replace (a + 1 + 1) with (a + 2) by lia. exact H2.
Qed.

Lemma arr4_hole : forall M base n f i,
  mem_arr 4 segs M base n f -> 0 <= i < n ->
  mem_arr 4 segs M base i f /\ mem_arr 4 segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)).
Proof.
  intros M base n f i H Hi.
  destruct (mem_arr_split segs 4 M base n f i H ltac:(lia)) as [H1 H23].
  destruct (mem_arr_split segs 4 M _ _ _ 1 H23 ltac:(lia)) as [_ H3].
  split; [exact H1|].
  replace (base + 4 * i + 4 * 1) with (base + 4 * (i + 1)) in H3 by lia.
  replace (n - i - 1) with (n - (i + 1)) in H3 by lia.
  eapply mem_arr_ext; [exact H3|]. intros j Hj. cbv beta. f_equal. lia.
Qed.

Lemma mem_arr4_fill : forall M base n f i v,
  mem_arr 4 segs M base i f ->
  mem_is segs M (base + 4 * i) (Z_to_le_bytes 4 v) ->
  mem_arr 4 segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  0 <= i < n -> base + 4 * n <= two64 ->
  mem_arr 4 segs M base n (zfupd f i v).
Proof.
  intros M base n f i v H1 Hc H3 Hi Hn.
  pose proof (mem_arr_bounds _ _ _ _ _ _ H1) as (B0 & _).
  assert (H2 : mem_arr 4 segs M (base + 4 * i) (i + 1 - i) (fun j => zfupd f i v (i + j))).
  { split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros j Hj. replace j with 0 by lia. rewrite Z.mul_0_r, !Z.add_0_r. rewrite zfupd_same. exact Hc. }
  assert (H1' : mem_arr 4 segs M base i (zfupd f i v)).
  { eapply mem_arr_ext; [exact H1|]. intros j Hj. rewrite zfupd_other by lia. reflexivity. }
  pose proof (mem_arr_join segs 4 M base (i + 1) i _ _ H1' H2 ltac:(lia)) as H12.
  assert (H3' : mem_arr 4 segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => zfupd f i v (i + 1 + j))).
  { eapply mem_arr_ext; [exact H3|]. intros j Hj. cbv beta. rewrite zfupd_other by lia. reflexivity. }
  pose proof (mem_arr_join segs 4 M base n (i + 1) _ _ H12 H3' ltac:(lia)) as H.
  eapply mem_arr_ext; [exact H|]. intros j Hj. cbv beta.
  destruct (Z.ltb_spec j (i + 1)); [destruct (Z.ltb_spec j i); [reflexivity | f_equal; lia] | f_equal; lia].
Qed.
End A4W.
