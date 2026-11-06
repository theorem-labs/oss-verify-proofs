(* Support for the walk of case 4 of the ubsan LLVMFuzzerTestOneInput (LLVMFuzzerTestOneInput_op4.v): the loop's
   frame cut into its six parts and joined back, op_begin's world as the machine writes it (copied from the
   build-independent Prog/T/LLVMFuzzerTestOneInput_op5.v op5_fn_put / op5_begin_world, renamed),
   and the bytes of the zeroed struct diginet_cmd. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the frame in six parts *)

Lemma rw_cells_merge_all : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge rsegs m A [] cs []) as M. rewrite app_nil_r in M. exact (M H).
Qed.

Lemma rw_cells_CB_len : forall m A n x, rw_cells rsegs m A [CB n x] -> length x = n.
Proof. intros m A n x [[[W _] _] _]. exact W. Qed.

Ltac fr_sizes H := cbn [cells_size csize Nat.add] in H;
  try change (Z.of_nat 16) with 16 in H; try change (Z.of_nat 32) with 32 in H; try change (Z.of_nat 40) with 40 in H.
Ltac fr_sizes_g := cbn [cells_size csize Nat.add];
  try change (Z.of_nat 16) with 16; try change (Z.of_nat 32) with 32; try change (Z.of_nat 40) with 40.

Lemma llvm_frame_split : forall regs0 m Sp j10 jio j60,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  rw_cells rsegs m Sp [C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3))] /\
  rw_cells rsegs m (Sp + 16) [CB 16 j10] /\
  rw_cells rsegs m (Sp + 32) [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
                              C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)))] /\
  rw_cells rsegs m (Sp + 64) [CB 32 jio] /\
  rw_cells rsegs m (Sp + 96) [CB 40 j60] /\
  rw_cells rsegs m (Sp + 136) (llvm_saved regs0).
Proof.
  intros regs0 m Sp j10 jio j60 H. unfold llvm_frame in H.
  change ([C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3)); CB 16 j10;
           C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
           C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)));
           CB 32 jio; CB 40 j60] ++ llvm_saved regs0)
    with ([C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3))] ++ [CB 16 j10] ++
          [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
           C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)))] ++
          [CB 32 jio] ++ [CB 40 j60] ++ llvm_saved regs0) in H.
  apply (proj1 (rw_cells_app _ _ _ _)) in H. destruct H as [H1 H]. fr_sizes H.
  apply (proj1 (rw_cells_app _ _ _ _)) in H. destruct H as [H2 H]. fr_sizes H.
  replace (Sp + 16 + 16) with (Sp + 32) in H by lia.
  apply (proj1 (rw_cells_app _ _ _ _)) in H. destruct H as [H3 H]. fr_sizes H.
  replace (Sp + 32 + 32) with (Sp + 64) in H by lia.
  apply (proj1 (rw_cells_app _ _ _ _)) in H. destruct H as [H4 H]. fr_sizes H.
  replace (Sp + 64 + 32) with (Sp + 96) in H by lia.
  apply (proj1 (rw_cells_app _ _ _ _)) in H. destruct H as [H5 H6]. fr_sizes H6.
  replace (Sp + 96 + 40) with (Sp + 136) in H6 by lia.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

Lemma llvm_frame_join : forall regs0 m Sp j10 jio j60,
  rw_cells rsegs m Sp [C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3))] ->
  rw_cells rsegs m (Sp + 16) [CB 16 j10] ->
  rw_cells rsegs m (Sp + 32) [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
                              C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)))] ->
  rw_cells rsegs m (Sp + 64) [CB 32 jio] ->
  rw_cells rsegs m (Sp + 96) [CB 40 j60] ->
  rw_cells rsegs m (Sp + 136) (llvm_saved regs0) ->
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60).
Proof.
  intros regs0 m Sp j10 jio j60 H1 H2 H3 H4 H5 H6. unfold llvm_frame.
  change ([C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3)); CB 16 j10;
           C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
           C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)));
           CB 32 jio; CB 40 j60] ++ llvm_saved regs0)
    with ([C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3))] ++ [CB 16 j10] ++
          [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
           C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)))] ++
          [CB 32 jio] ++ [CB 40 j60] ++ llvm_saved regs0).
  apply (proj2 (rw_cells_app _ _ _ _)). split; [exact H1|]. fr_sizes_g.
  apply (proj2 (rw_cells_app _ _ _ _)). split; [exact H2|]. fr_sizes_g.
  replace (Sp + 16 + 16) with (Sp + 32) by lia.
  apply (proj2 (rw_cells_app _ _ _ _)). split; [exact H3|]. fr_sizes_g.
  replace (Sp + 32 + 32) with (Sp + 64) by lia.
  apply (proj2 (rw_cells_app _ _ _ _)). split; [exact H4|]. fr_sizes_g.
  replace (Sp + 64 + 32) with (Sp + 96) by lia.
  apply (proj2 (rw_cells_app _ _ _ _)). split; [exact H5|]. fr_sizes_g.
  replace (Sp + 96 + 40) with (Sp + 136) by lia.
  exact H6.
Qed.

(* ---------------------------------------------------------------- op_begin's world *)

(* A put-write that misses g_fail_next (OFF_g_fail_next = 0xfdc8 = 64968, one byte; W_LEN = 65616) leaves it. *)
Lemma op4_fn_put : forall (u : list byte) k n v, Z.of_nat (length u) = 65616 -> 0 <= k ->
  k + Z.of_nat n <= 65616 -> (k + Z.of_nat n <= 64968 \/ 64969 <= k) ->
  g_fail_next (upd u k (put n v)) = g_fail_next u.
Proof.
  intros u k n v Hu Hk Hn Hd. unfold g_fail_next, OFF_g_fail_next.
  rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia].
Qed.

(* op_begin (fuzz_transport.c:388-394): the memsets of OW (OFF_OW = 65312, 304 bytes) and GOT (OFF_GOT = 65084,
   224 bytes), then OW.desk_off = -1 (A_OW_desk_off = 65544), then M.fail = g_fail_next (A_M_fail = 88), the byte
   read after the memsets; the machine writes in the model's order. *)
Lemma op4_begin_world : forall (Bx Bz : list byte), Z.of_nat (length Bx) = W_LEN ->
  Bz = upd (upd Bx 65312 (repeat (Z_to_bv 8 0) 304)) 65084 (repeat (Z_to_bv 8 0) 224) ->
  op_begin_m Bx = Some (upd (upd Bz 65544 (put 4 (-1))) 88 (put 4 (u_at Bz OFF_g_fail_next 1)), tt).
Proof.
  intros Bx Bz HL EZ.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (R304 : Z.of_nat (length (repeat (Z_to_bv 8 0) 304)) = 304) by (rewrite repeat_length; lia).
  assert (R224 : Z.of_nat (length (repeat (Z_to_bv 8 0) 224)) = 224) by (rewrite repeat_length; lia).
  assert (L1 : Z.of_nat (length (upd Bx 65312 (repeat (Z_to_bv 8 0) 304))) = W_LEN)
    by (rewrite length_upd; [exact HL | lia | rewrite R304; lia]).
  assert (LZ : Z.of_nat (length Bz) = 65616)
    by (rewrite EZ, length_upd; [rewrite L1; exact EWL | lia | rewrite R224, L1; lia]).
  unfold op_begin_m, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT.
  cbv zeta.
  change (Z.to_nat SZ_OW) with 304%nat. change (Z.to_nat SZ_GOT) with 224%nat.
  change (b8 0) with (Z_to_bv 8 0).
  rewrite <- EZ.
  replace (65312 + 232) with 65544 by lia. replace (0 + 88) with 88 by lia.
  assert (EFN : g_fail_next (upd Bz 65544 (put 4 (-1))) = u_at Bz OFF_g_fail_next 1).
  { change (u_at Bz OFF_g_fail_next 1) with (g_fail_next Bz).
    apply op4_fn_put; [exact LZ | lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia]. }
  rewrite EFN. reflexivity.
Qed.

(* ---------------------------------------------------------------- the bytes of the struct *)

Lemma op4_zeros8 : le8 (Z_to_bv 64 0) = repeat (b8 0) 8.
Proof. apply bytes_eq_of_zs. vm_compute. reflexivity. Qed.

Lemma op4_zeros32 : forall x : list byte,
  le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ x ++ [] =
  repeat (b8 0) 32 ++ x.
Proof. intros x. rewrite op4_zeros8, app_nil_r. reflexivity. Qed.

(* one byte of the input buffer, as bytes_at reads it (the plain Prog/T/LLVMFuzzerTestOneInput_disp.v disp_sub1) *)
Lemma op4_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* the byte at offset k of the input, for a load hook (solve_load_base's ov_read_bytes case) *)
Lemma op4_read1 : forall m data D k, bytes_at rsegs m data D -> 0 <= k -> k < Z.of_nat (length D) ->
  ov_read_bytes rsegs m (wa (data + k)) 1 = Some [nth (Z.to_nat k) D (b8 0)].
Proof.
  intros m data D k HD Hk Hl.
  rewrite (bytes_at_read rsegs m data D k 1 HD Hk) by lia.
  rewrite op4_sub1 by lia. reflexivity.
Qed.

(* fuzz_u8_m on a nonempty / an empty cursor *)
Lemma fu8_nz : forall D c, fi_n c <> 0 ->
  fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c))).
Proof. intros D c H. unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia | reflexivity]. Qed.

Lemma fu8_z : forall D c, fi_n c = 0 -> fuzz_u8_m D c = (c, 0).
Proof. intros D c H. unfold fuzz_u8_m. rewrite H. reflexivity. Qed.

Lemma at8_range : forall D k, 0 <= at8 D k < 256.
Proof.
  intros D k. unfold at8, bz. pose proof (bv_unsigned_in_range 8 (nth k D (b8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* ---------------------------------------------------------------- the compiler's two divisions *)

Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

(* (b * 57) >> 9 = b / 9 on a byte (the plain Prog/T/LLVMFuzzerTestOneInput_disp.v dis_div) *)
Lemma op4_div9 : forall b, 0 <= b < 256 -> b * 57 / 512 = b / 9.
Proof.
  intros b Hb.
  assert (Hr : 0 <= b mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod b 9 ltac:(lia)) as E.
  assert (Hq : 0 <= b / 9 <= 28).
  { split; [apply Z.div_pos; lia|].
    assert (b / 9 < 29) by (apply Z.div_lt_upper_bound; lia). lia. }
  replace (b * 57) with (512 * (b / 9) + (b / 9 + 57 * (b mod 9))) by lia.
  rewrite Z.mul_comm, Z.div_add_l by lia.
  rewrite (Z.div_small (b / 9 + 57 * (b mod 9)) 512) by lia. lia.
Qed.

(* 0x13e94-0x13eb4: key = ((kb % 9 + 1) << 16) | ab *)
Lemma op4_key_val : forall kb ab, 0 <= kb < 256 -> 0 <= ab < 256 ->
  Z.lor (Z.shiftl (Z.land ((bv_swrap 32 (bv_swrap 32 (kb - Z.shiftr (kb * 57) 9) mod 18446744073709551616 -
                                         Z.shiftl (Z.shiftr (kb * 57) 9) 3 mod 18446744073709551616) + 1)
                           mod 18446744073709551616) 255) 16 mod 18446744073709551616) ab
  = KEY (kb mod 9 + 1) ab.
Proof.
  intros kb ab Hk Ha.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 9) with 512. change (2 ^ 3) with 8. change (2 ^ 16) with 65536.
  rewrite !op4_div9 by exact Hk.
  assert (Hr : 0 <= kb mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod kb 9 ltac:(lia)) as E.
  assert (Hq : 0 <= kb / 9 <= 28).
  { split; [apply Z.div_pos; lia|].
    assert (kb / 9 < 29) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite (swrap32_small (kb - kb / 9)) by lia.
  rewrite (Z.mod_small (kb - kb / 9) 18446744073709551616) by lia.
  rewrite (Z.mod_small (kb / 9 * 8) 18446744073709551616) by lia.
  rewrite (swrap32_small (kb - kb / 9 - kb / 9 * 8)) by lia.
  replace (kb - kb / 9 - kb / 9 * 8 + 1) with (kb mod 9 + 1) by lia.
  rewrite (Z.mod_small (kb mod 9 + 1) 18446744073709551616) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small (kb mod 9 + 1) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
  rewrite (Z.mod_small ((kb mod 9 + 1) * 65536) 18446744073709551616) by lia.
  unfold KEY. f_equal. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_small. change (2 ^ 16) with 65536. lia.
Qed.

(* the magic number of the division by 25 (fuzz_transport.c:1079, w % (SPEC_CMD_MAX + 1)) *)
Lemma div25_magic : forall w, 0 <= w < 65536 -> 83887 * w / 2097152 = w / 25.
Proof.
  intros w Hw.
  assert (Hu : 0 <= w / 25 <= 2622)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hv : 0 <= w mod 25 < 25) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod w 25 ltac:(lia)) as E.
  replace (83887 * w) with (w / 25 * 2097152 + (23 * (w / 25) + 83887 * (w mod 25))) by lia.
  rewrite Z.div_add_l by lia.
  rewrite (Z.div_small (23 * (w / 25) + 83887 * (w mod 25)) 2097152) by lia. lia.
Qed.

(* 0x14488-0x144bc: a1 = w mod 25 *)
Lemma op4_mod25 : forall w, 0 <= w < 65536 ->
  w - (Z.shiftr ((Z.shiftr (Z.shiftl (bv_swrap 32 (w - Z.shiftr (w * 18351 mod 18446744073709551616) 16)
                                        mod 18446744073709551616) 48
                              mod 18446744073709551616) 49
                   + Z.shiftr (w * 18351 mod 18446744073709551616) 16)
                  mod 18446744073709551616) 4 * 25) mod 18446744073709551616
  = w mod 25.
Proof.
  intros w Hw.
  rewrite (Z.mod_small (w * 18351) 18446744073709551616) by lia.
  rewrite (Z.shiftr_div_pow2 (w * 18351) 16) by lia. change (2 ^ 16) with 65536.
  set (q0 := w * 18351 / 65536) in *.
  assert (Hq0 : 0 <= q0 <= w).
  { split; [apply Z.div_pos; lia|]. unfold q0. apply Z.div_le_upper_bound; lia. }
  rewrite (swrap32_small (w - q0)) by lia.
  rewrite (Z.mod_small (w - q0) 18446744073709551616) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small ((w - q0) * 2 ^ 48) 18446744073709551616)
    by (change (2 ^ 48) with 281474976710656; lia).
  rewrite (Z.shiftr_div_pow2 ((w - q0) * 2 ^ 48) 49) by lia.
  replace (2 ^ 49) with (2 ^ 48 * 2) by reflexivity.
  rewrite <- Z.div_div by (change (2 ^ 48) with 281474976710656; lia).
  rewrite Z.div_mul by (change (2 ^ 48) with 281474976710656; lia).
  assert (Hd2 : 0 <= (w - q0) / 2 <= 32768)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (Z.mod_small ((w - q0) / 2 + q0) 18446744073709551616) by lia.
  rewrite (Z.shiftr_div_pow2 ((w - q0) / 2 + q0) 4) by lia. change (2 ^ 4) with 16.
  (* ((w - q0)/2 + q0)/16 = (w + q0)/32 = (83887 w / 65536)/32 = w/25 *)
  replace ((w - q0) / 2 + q0) with ((w - q0 + q0 * 2) / 2) by (rewrite Z.div_add by lia; reflexivity).
  replace (w - q0 + q0 * 2) with (w + q0) by lia.
  rewrite Z.div_div by lia. change (2 * 16) with 32.
  unfold q0. replace (w + w * 18351 / 65536) with ((w * 65536 + w * 18351) / 65536)
    by (rewrite Z.div_add_l by lia; lia).
  replace (w * 65536 + w * 18351) with (83887 * w) by lia.
  rewrite Z.div_div by lia. change (65536 * 32) with 2097152.
  rewrite div25_magic by exact Hw.
  assert (Hu : 0 <= w / 25 <= 2622)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (Z.mod_small (w / 25 * 25) 18446744073709551616) by lia.
  pose proof (Z.div_mod w 25 ltac:(lia)). lia.
Qed.

(* the u16 the machine builds from the two bytes *)
Lemma op4_w16 : forall lo8 hi8, 0 <= lo8 < 256 -> 0 <= hi8 < 256 ->
  Z.lor (Z.shiftl hi8 8 mod 18446744073709551616) lo8 = lo8 + 256 * hi8.
Proof.
  intros lo8 hi8 Hl Hh.
  rewrite (Z.mod_small (Z.shiftl hi8 8) 18446744073709551616)
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
  rewrite Z.lor_comm. apply lor_shiftl8_add; lia.
Qed.

(* the model's u16 *)
Lemma op4_u16_model : forall lo8 hi8, 0 <= lo8 < 256 -> 0 <= hi8 < 256 ->
  Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16 = lo8 + 256 * hi8.
Proof.
  intros lo8 hi8 Hl Hh. rewrite lor_shiftl8_add by lia.
  apply Z.mod_small. change (2 ^ 16) with 65536. lia.
Qed.

(* the byte a register's low 8 bits store *)
Lemma op4_sb : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof.
  intros z. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
  pose proof (Z.div_mod z 18446744073709551616 ltac:(lia)) as E.
  replace (z mod 18446744073709551616)
    with (z + - (72057594037927936 * (z / 18446744073709551616)) * 256) by lia.
  apply Z_mod_plus_full.
Qed.

(* a slice of the input buffer *)
Lemma op4_sub_at : forall m data D k n, bytes_at rsegs m data D -> 0 <= k -> (Z.to_nat k + n <= length D)%nat ->
  bytes_at rsegs m (data + k) (sub D k n).
Proof.
  intros m data D k n HD Hk Hn.
  rewrite <- (firstn_skipn (Z.to_nat k) D) in HD.
  apply (proj1 (bytes_at_app rsegs m data _ _)) in HD. destruct HD as [_ HD].
  rewrite firstn_length in HD.
  replace (Z.of_nat (Init.Nat.min (Z.to_nat k) (length D))) with k in HD by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat k) D)) in HD.
  apply (proj1 (bytes_at_app rsegs m (data + k) _ _)) in HD. destruct HD as [HD _].
  exact HD.
Qed.

Lemma skipn_repeat_app : forall (x : byte) k n (R : list byte), (k <= n)%nat ->
  skipn k (repeat x n ++ R) = repeat x (n - k) ++ R.
Proof.
  induction k as [|k IH]; intros n R H; [rewrite Nat.sub_0_r; reflexivity|].
  destruct n as [|n]; [lia|]. cbn [repeat app skipn Nat.sub]. apply IH. lia.
Qed.

Lemma firstn_repeat_app : forall (x : byte) k n (R : list byte), (k <= n)%nat ->
  firstn k (repeat x n ++ R) = repeat x k.
Proof.
  induction k as [|k IH]; intros n R H; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [repeat app firstn]. f_equal. apply IH. lia.
Qed.

Lemma op4_land16 : forall x, 0 <= x < 65536 -> Z.land x 65535 = x.
Proof.
  intros x Hx. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 16) with 65536. lia.
Qed.

(* the world across a write confined to the loop's frame (the kit's transport_chunks drops it: its side goal
   holds Z.of_nat (Z.to_nat W_LEN)) *)
Lemma wmem_frame_transport : forall m m' Sp B,
  wmem rsegs m B -> munch [(Sp, Sp + 240)] m m' -> wmono rsegs m m' ->
  W_BASE_UBSAN + W_LEN <= Sp ->
  wmem rsegs m' B.
Proof.
  intros m m' Sp B HW MU WMO H.
  eapply rw_cells_transport; [exact HW | exact MU | exact WMO |].
  cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold W_LEN; lia).
  split; [left; lia | exact I].
Qed.
