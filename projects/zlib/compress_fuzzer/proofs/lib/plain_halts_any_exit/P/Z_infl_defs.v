(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition Z_INFLATE : Z := 0x1d1cc.
Definition PC_DISPATCH : Z := 0x1d340.
Definition PC_LEAVE : Z := 0x1ed3c.
Definition PC_EPILOGUE : Z := 0x1eec8.
Definition A_JUMPTAB : Z := 0x12520.
Definition INF_FRAME : Z := 224.

Definition PC_HEAD : Z := 0x1d364.     Definition PC_DICTID : Z := 0x1d424.   Definition PC_DICT : Z := 0x1d654.
Definition PC_TYPE : Z := 0x1d69c.     Definition PC_TYPEDO : Z := 0x1d6ac.   Definition PC_STORED : Z := 0x1d474.
Definition PC_COPY_ : Z := 0x1d760.    Definition PC_COPY : Z := 0x1d768.     Definition PC_TABLE : Z := 0x1d4c8.
Definition PC_LENLENS : Z := 0x1d5e8.  Definition PC_CODELENS : Z := 0x1d414. Definition PC_LEN_ : Z := 0x1e61c.
Definition PC_LEN : Z := 0x1e624.      Definition PC_LENEXT : Z := 0x1d3cc.   Definition PC_DIST : Z := 0x1e870.
Definition PC_DISTEXT : Z := 0x1d41c.  Definition PC_MATCH : Z := 0x1eaac.    Definition PC_LIT : Z := 0x1d3b0.
Definition PC_CHECK : Z := 0x1d59c.    Definition PC_LENGTH : Z := 0x1d5f8.   Definition PC_DONE : Z := 0x1ef68.  (* 1.4: jump table entry 28 (0xc9d4 + 0x12520); pcmap had left it HAND *)
Definition PC_BAD : Z := 0x1ed3c.      Definition PC_MEM : Z := 0x1ee6c.

Record ictx : Type := mkIX {
  ix_L : ilay; ix_flush : Z; ix_lo : Z; ix_input : arr; ix_rest0 : list byte; ix_hasw : bool; ix_m0 : mem;
  ix_sp : word; ix_ra : word; ix_gp : word; ix_tp : word;
  ix_s0 : word; ix_s1 : word; ix_s2 : word; ix_s3 : word; ix_s4 : word; ix_s5 : word;
  ix_s6 : word; ix_s7 : word; ix_s8 : word; ix_s9 : word; ix_s10 : word; ix_s11 : word;
  ix_F : bvmap 5 word; ix_fc : bv 32
}.

Definition ix_W (X : ictx) : list ivl :=
  [(ix_lo X, bv_unsigned (ix_sp X)); (il_S (ix_L X), il_S (ix_L X) + 112); (il_As (ix_L X), il_As (ix_L X) + ZI_SIZE);
   (il_NO (ix_L X), il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X)))].

Notation ix_nin X := (arr_len (ix_input X)) (only parsing).
Record ix_ok (X : ictx) : Prop := mkIXok {
  xo_stack : ix_lo X <= bv_unsigned (ix_sp X) - 1024 /\ 0x5c000 <= ix_lo X /\ bv_unsigned (ix_sp X) <= il_S (ix_L X)
             /\ il_S (ix_L X) + 112 < 2^63 /\ il_S (ix_L X) mod 8 = 0;
  xo_state : 0 < il_As (ix_L X) /\ il_As (ix_L X) + ZI_SIZE <= ix_lo X;
  xo_ni : 0 < il_NI (ix_L X) /\ 0 <= ix_nin X /\ il_NI (ix_L X) + ix_nin X <= ix_lo X;
  xo_no : 0 < il_NO (ix_L X) /\ il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X)) <= ix_lo X;
  xo_io : apart (il_NI (ix_L X)) (ix_nin X) (il_NO (ix_L X)) (Z.of_nat (length (ix_rest0 X)));
  xo_is : apart (il_NI (ix_L X)) (ix_nin X) (il_As (ix_L X)) ZI_SIZE;
  xo_os : apart (il_NO (ix_L X)) (Z.of_nat (length (ix_rest0 X))) (il_As (ix_L X)) ZI_SIZE;

  xo_win : ix_hasw X = true -> 0 < il_Aw (ix_L X) /\ il_Aw (ix_L X) + ZI_WIN <= ix_lo X;
  xo_iw : ix_hasw X = true -> apart (il_NI (ix_L X)) (ix_nin X) (il_Aw (ix_L X)) ZI_WIN;
  xo_ow : ix_hasw X = true -> apart (il_NO (ix_L X)) (Z.of_nat (length (ix_rest0 X))) (il_Aw (ix_L X)) ZI_WIN;
  xo_sw : ix_hasw X = true -> apart (il_As (ix_L X)) ZI_SIZE (il_Aw (ix_L X)) ZI_WIN
}.

Definition iframe_cells (X : ictx) (r : iregs) (retw : word) (j : list byte) : list cell :=
  [C8 (wz (il_As (ix_L X) + 140)); C8 (wz (il_As (ix_L X) + 136)); C8 (wz (il_As (ix_L X) + 1384)); C8 (wz (il_As (ix_L X) + 808));
   C8 (wz (il_As (ix_L X) + 160)); C8 (wz (ix_flush X + -5)); C8 (wz (il_As (ix_L X) + 7160));
   C8 (wz (ir_in r)); C8 retw; C8 (wz 16209); C8 (wz (ir_out r)); C8 (wz 18446744073709535436);
   C8 (wz (il_S (ix_L X))); C8 (wz (ix_flush X)); CB 8 j;
   C8 (ix_s11 X); C8 (ix_s10 X); C8 (ix_s9 X); C8 (ix_s8 X); C8 (ix_s7 X); C8 (ix_s6 X); C8 (ix_s5 X); C8 (ix_s4 X);
   C8 (ix_s3 X); C8 (ix_s2 X); C8 (ix_s1 X); C8 (ix_s0 X); C8 (ix_ra X)].

Definition iframe (X : ictx) (r : iregs) (m : mem) : Prop :=
  exists j, rw_cells psegs m (bv_unsigned (ix_sp X) + -224) (iframe_cells X r (wz (ir_ret r)) j).
Definition iframeL (X : ictx) (r : iregs) (m : mem) : Prop :=
  exists retw j, rw_cells psegs m (bv_unsigned (ix_sp X) + -224) (iframe_cells X r retw j).

Definition iin (m : mem) (X : ictx) : Prop :=
  u8ro psegs m (il_NI (ix_L X)) (av8 (ix_input X) (arr_len (ix_input X))).
Definition iout_bytes (rest0 : list byte) (c : icall) (put : Z) : list byte :=
  av8 (ic_outbuf c) put ++ skipn (Z.to_nat put) rest0.
Definition iout (m : mem) (L : ilay) (rest0 : list byte) (c : icall) (put : Z) : Prop :=
  u8arr psegs m (il_NO L) (iout_bytes rest0 c put).

Lemma iout_bytes_length : forall rest0 c put, 0 <= put <= Z.of_nat (length rest0) -> length (iout_bytes rest0 c put) = length rest0.
Proof. intros rest0 c put H. unfold iout_bytes. rewrite length_app, av8_length, length_skipn. lia. Qed.

Lemma iout_bytes_store : forall rest0 c put v, 0 <= put < Z.of_nat (length rest0) -> put < arr_len (ic_outbuf c) ->
  upd (iout_bytes rest0 c put) (Z.to_nat put) (Z_to_bv 8 v)
  = iout_bytes rest0 (icset_outbuf c (arr_set (ic_outbuf c) put v)) (put + 1).
Proof.
  intros rest0 c put v Hp Ha. apply list_ext_nth.
  - rewrite upd_length, !iout_bytes_length by lia. reflexivity.
  - intros k Hk. rewrite upd_length, iout_bytes_length in Hk by lia.
    unfold iout_bytes. cbn [ic_outbuf icset_outbuf].
    destruct (Nat.eq_dec k (Z.to_nat put)) as [E|NE].
    + subst k. rewrite nth_error_upd_same by (rewrite length_app, av8_length, length_skipn; lia).
      rewrite nth_error_app1 by (rewrite av8_length; lia).
      rewrite (av8_nth _ (put + 1) put) by lia. rewrite arr_get_set_same by lia. reflexivity.
    + rewrite nth_error_upd_other by (intros E; apply NE; symmetry; exact E).
      destruct (Nat.lt_ge_cases k (Z.to_nat put)) as [Hlt|Hge].
      * rewrite !nth_error_app1 by (rewrite av8_length; lia).
        replace k with (Z.to_nat (Z.of_nat k)) by lia.
        rewrite (av8_nth _ put (Z.of_nat k)), (av8_nth _ (put + 1) (Z.of_nat k)) by lia.
        rewrite arr_get_set_other by lia. reflexivity.
      * rewrite !nth_error_app2 by (rewrite av8_length; lia). rewrite !av8_length, !nth_error_skipn.
        f_equal. lia.
Qed.

Lemma iout_bytes_0 : forall rest0 c, iout_bytes rest0 c 0 = rest0.
Proof. intros. unfold iout_bytes, av8. reflexivity. Qed.

Global Opaque iout_bytes.

Definition IMEMg (fr : ictx -> iregs -> mem -> Prop) (X : ictx) (w : iw) (m : mem) : Prop :=
  fr X (w_r w) m
  /\ stk psegs m (ix_lo X) (bv_unsigned (ix_sp X) + -224)
  /\ IREP m (ix_L X) (w_s w) (w_c w)
  /\ iin m X
  /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv psegs m /\ munch (ix_W X) (ix_m0 X) m /\ wmono psegs (ix_m0 X) m.
Definition IMEM := IMEMg iframe.
Definition IMEML := IMEMg iframeL.

Definition ILOOP (X : ictx) (w : iw) (pc : Z) (x8 x12 : word) : machine_state -> Prop :=
  fun ms => exists x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x30 m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X)))
                 x8 (wz (il_S (ix_L X))) (wz (ix_flush X)) x12 x13 x14 x15 x16 x17
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 75040)
                 x27 (wz (il_NI (ix_L X) + ir_next (w_r w))) x28 (wz 30) x30 (wz (-16180)))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Definition ILEAVE (X : ictx) (w : iw) : machine_state -> Prop :=
  fun ms => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x27 x28 x29 x30 x31 m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X)))
                 (wz (ir_ret (w_r w))) (wz (il_S (ix_L X))) (wz (ix_flush X)) x12 x13 x14 x15 x16 x17
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) x19 x20
                 x21 (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) x24
                 x27 (wz (il_NI (ix_L X) + ir_next (w_r w))) x28 x29 x30 x31)
            (ix_F X) (wz PC_LEAVE) (ix_fc X) None m (seg_rom psegs)
    /\ IMEML X w m.

Definition RST (w : iw) : Prop :=
  ic_next_in (w_c w) = ir_next (w_r w) /\ ic_avail_in (w_c w) = ir_have (w_r w) /\ ic_next_out (w_c w) = ir_put (w_r w)
  /\ ic_avail_out (w_c w) = ir_left (w_r w) /\ ir_put (w_r w) = 0.

Definition IRET (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17
                 x9 x18 x19 (wz rc) x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
            (ix_F X) (wz PC_EPILOGUE) (ix_fc X) None m (seg_rom psegs)
    /\ IMEML X w m /\ (rc = Z_NEED_DICT -> RST w).

Lemma ILOOP_intro : forall X w pc x8 x12 x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x9 = wz (ir_have (w_r w)) -> x10 = wz (il_S (ix_L X)) -> x11 = wz (ix_flush X) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 75040 -> x25 = wz (il_As (ix_L X)) ->
  x26 = wz (il_NI (ix_L X) + ir_next (w_r w)) -> x29 = wz 30 -> x31 = wz (-16180) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOP X w pc x8 x12 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                          F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOP. do 12 eexists. split; [reflexivity| assumption]. Qed.

Lemma ILEAVE_intro : forall X w x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X -> x8 = wz (ir_ret (w_r w)) ->
  x9 = wz (ir_have (w_r w)) -> x10 = wz (il_S (ix_L X)) -> x11 = wz (ix_flush X) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x25 = wz (il_As (ix_L X)) ->
  x26 = wz (il_NI (ix_L X) + ir_next (w_r w)) -> F = ix_F X -> fc = ix_fc X ->
  IMEML X w m ->
  ILEAVE X w (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                 F (wz PC_LEAVE) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILEAVE. do 19 eexists. split; [reflexivity| assumption]. Qed.

Lemma IRET_intro : forall X rc w x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X -> x20 = wz rc -> F = ix_F X -> fc = ix_fc X ->
  IMEML X w m -> (rc = Z_NEED_DICT -> RST w) ->
  IRET X rc w (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                  F (wz PC_EPILOGUE) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold IRET. do 28 eexists. split; [reflexivity|]. split; assumption. Qed.

Definition ILOOP27 (X : ictx) (w : iw) (pc : Z) (x8 x12 x26 : word) : machine_state -> Prop :=
  fun ms => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x30 m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X)))
                 x8 (wz (il_S (ix_L X))) (wz (ix_flush X)) x12 x13 x14 x15 x16 x17
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 75040)
                 (wz (il_NI (ix_L X) + ir_next (w_r w))) x26 x28 (wz 30) x30 (wz (-16180)))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOP27_intro : forall X w pc x8 x12 x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x9 = wz (ir_have (w_r w)) -> x10 = wz (il_S (ix_L X)) -> x11 = wz (ix_flush X) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 75040 -> x25 = wz (il_As (ix_L X)) ->
  x27 = wz (il_NI (ix_L X) + ir_next (w_r w)) -> x29 = wz 30 -> x31 = wz (-16180) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOP27 X w pc x8 x12 x26 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                          F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOP27. do 11 eexists. split; [reflexivity| assumption]. Qed.

Definition NBJ (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (n : Z) (pcj : Z) (x8 x26 : word) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 x12, NEEDBITS n (mkW s c r) = ARun tt (mkW s c r1)
                    /\ ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8))
                    /\ ILOOP27 X (mkW s c r1) pcj x8 x12 x26 ms')
    \/ (exists r1, NEEDBITS n (mkW s c r) = ALeave (mkW s c r1) /\ (r1 = r \/ r1 = pullr c r) /\ ILEAVE X (mkW s c r1) ms').

Definition NBJ26 (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (n : Z) (pcj : Z) (x8 : word) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 x12, NEEDBITS n (mkW s c r) = ARun tt (mkW s c r1)
                    /\ ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8))
                    /\ ILOOP X (mkW s c r1) pcj x8 x12 ms')
    \/ (exists r1, NEEDBITS n (mkW s c r) = ALeave (mkW s c r1) /\ (r1 = r \/ r1 = pullr c r) /\ ILEAVE X (mkW s c r1) ms').

Definition IPOST (X : ictx) {A} (res : ares A) : machine_state -> Prop :=
  match res with
  | ARun _ w' => fun ms => exists x8, ILOOP X w' PC_DISPATCH x8 (wz (is_mode (w_s w'))) ms
  | ALeave w' => ILEAVE X w'
  | ARet rc w' => IRET X rc w'
  end.

Definition ISR (s : inflate_state) : Prop :=
  (is_last s = 0 \/ is_last s = 1)
  /\ (is_havedict s = 0 \/ is_havedict s = 1).

Definition NOPUTb (m put : Z) : bool := ((m =? DICTID) || (m =? DICT) || (m =? MEM)) && negb (put =? 0).
Definition OBYT (X : ictx) (w : iw) : Prop :=
  (forall i, 0 <= i < ir_put (w_r w) -> 0 <= arr_get (ic_outbuf (w_c w)) i < 256)
  /\ (forall i, 0 <= i < arr_len (is_window (w_s w)) -> 0 <= arr_get (is_window (w_s w)) i < 256)
  /\ 0 <= ir_out (w_r w) - ir_left (w_r w) <= ir_put (w_r w)
  /\ NOPUTb (is_mode (w_s w)) (ir_put (w_r w)) = false

  /\ (ix_hasw X = true -> is_window_blk (w_s w) <> None).

Lemma NOPUTb_false : forall m put, NOPUTb m put = false -> m = DICTID \/ m = DICT \/ m = MEM -> put = 0.
Proof.
  intros m put H Hm. unfold NOPUTb in H. apply andb_false_iff in H. destruct H as [H|H].
  - exfalso. destruct Hm as [-> | [-> | ->]]; discriminate H.
  - apply negb_false_iff in H. apply Z.eqb_eq in H. exact H.
Qed.

Definition PATI (X : ictx) (w : iw) : Prop :=
  let s := w_s w in let r := w_r w in
  is_wrap s = 5 /\ is_wbits s = 15 /\ is_head s = 0
  /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD) /\ ir_put r = 0 /\ ir_out r = ir_left r))
  /\ ~ (FLAGS <= is_mode s <= HCRC)
  /\ (is_window_blk s <> None -> ix_hasw X = true)
  /\ ic_input (w_c w) = ix_input X /\ arr_len (ix_input X) <= 1
  /\ arr_len (ic_outbuf (w_c w)) = Z.of_nat (length (ix_rest0 X)) /\ (length (ix_rest0 X) <= 1)%nat
  /\ ISR s
  /\ OBYT X w.

Ltac isep_with XO f := let H := fresh "SEP" in pose proof (f _ XO) as H; unfold apart in H; first [ clear - H; lia | lia ].
Ltac k1i_isep_with_fast XO f := let H := fresh "SEP" in pose proof (f _ XO) as H; unfold apart in H; clear - H; lia.

Ltac isep_win XO f :=
  lazymatch goal with
  | HASW : ix_hasw _ = true |- _ =>
      let H := fresh "SEP" in let H2 := fresh "SEPW" in
      pose proof (f _ XO HASW) as H; pose proof (xo_win _ XO HASW) as H2; unfold apart in H; first [ clear - H H2; lia | lia ]
  end.
Ltac k1i_isep_win_fast XO f :=
  lazymatch goal with
  | HASW : ix_hasw _ = true |- _ =>
      let H := fresh "SEP" in let H2 := fresh "SEPW" in
      pose proof (f _ XO HASW) as H; pose proof (xo_win _ XO HASW) as H2; unfold apart in H; clear - H H2; lia
  end.
Ltac isep :=
  lazymatch goal with
  | XO : ix_ok ?X |- _ =>
      lazymatch goal with
      | |- context [il_Aw (ix_L X)] =>
          lazymatch goal with
          | |- context [il_NO (ix_L X)] => isep_win XO xo_ow
          | |- context [il_NI (ix_L X)] => isep_win XO xo_iw
          | |- context [il_As (ix_L X)] => isep_win XO xo_sw
          | |- _ => isep_win XO xo_sw
          end
      | |- context [il_NO (ix_L X)] =>
          lazymatch goal with
          | |- context [il_NI (ix_L X)] => isep_with XO xo_io
          | |- context [il_As (ix_L X)] => isep_with XO xo_os
          end
      | |- context [il_NI (ix_L X)] =>
          lazymatch goal with
          | |- context [il_As (ix_L X)] => isep_with XO xo_is
          end
      end
  end.
Ltac k1i_isep_fast :=
  lazymatch goal with
  | XO : ix_ok ?X |- _ =>
      lazymatch goal with
      | |- context [il_Aw (ix_L X)] =>
          lazymatch goal with
          | |- context [il_NO (ix_L X)] => k1i_isep_win_fast XO xo_ow
          | |- context [il_NI (ix_L X)] => k1i_isep_win_fast XO xo_iw
          | |- context [il_As (ix_L X)] => k1i_isep_win_fast XO xo_sw
          | |- _ => k1i_isep_win_fast XO xo_sw
          end
      | |- context [il_NO (ix_L X)] =>
          lazymatch goal with
          | |- context [il_NI (ix_L X)] => k1i_isep_with_fast XO xo_io
          | |- context [il_As (ix_L X)] => k1i_isep_with_fast XO xo_os
          end
      | |- context [il_NI (ix_L X)] =>
          lazymatch goal with
          | |- context [il_As (ix_L X)] => k1i_isep_with_fast XO xo_is
          end
      end
  end.
Ltac k1i_side := first [ exact I | k1i_isep_fast | k1_zsep_fast | lia ].
Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::=
  first [ exact I | k1i_isep_fast | k1_zsep_fast
        | solve [ repeat (match goal with |- _ /\ _ => split end);
                  first [ exact I | k1i_isep_fast | k1_zsep_fast | lia | isep | zsep ] ]
        | lia ].

Ltac ix_open XO :=
  let a := fresh "XSt" in let b := fresh "XAs" in let c := fresh "XNi" in let d := fresh "XNo" in
  pose proof (xo_stack _ XO) as a; pose proof (xo_state _ XO) as b; pose proof (xo_ni _ XO) as c; pose proof (xo_no _ XO) as d.

Definition ix_Wf (X : ictx) : list ivl :=
  [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168);
   (il_NO (ix_L X), il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X)))].

Definition ix_WfS (X : ictx) : list ivl := (il_S (ix_L X), il_S (ix_L X) + 112) :: ix_Wf X.

Ltac iarm_open HL :=
  let x5 := fresh "x5" in let x6 := fresh "x6" in let x7 := fresh "x7" in let x13 := fresh "x13" in let x14 := fresh "x14" in
  let x15 := fresh "x15" in let x16 := fresh "x16" in let x17 := fresh "x17" in let x27 := fresh "x27" in let x28 := fresh "x28" in
  let x30 := fresh "x30" in let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & (jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.

Ltac iarm_open27 HL :=
  let x5 := fresh "x5" in let x6 := fresh "x6" in let x7 := fresh "x7" in let x13 := fresh "x13" in let x14 := fresh "x14" in
  let x15 := fresh "x15" in let x16 := fresh "x16" in let x17 := fresh "x17" in let x28 := fresh "x28" in
  let x30 := fresh "x30" in let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x30 & m & -> & (jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.

Ltac ifine m :=
  let MUf := fresh "MUf" in let WMf := fresh "WMf" in
  lazymatch goal with X : ictx |- _ =>
    pose proof (munch_refl (ix_Wf X) m) as MUf; unfold ix_Wf in MUf; pose proof (wmono_refl psegs m) as WMf end.
Ltac ifineS m :=
  let MUf := fresh "MUf" in let WMf := fresh "WMf" in
  lazymatch goal with X : ictx |- _ =>
    pose proof (munch_refl (ix_WfS X) m) as MUf; unfold ix_WfS, ix_Wf in MUf; pose proof (wmono_refl psegs m) as WMf end.

Ltac ireg :=
  first [ reflexivity | f_equal; lia
        | f_equal; rewrite ?bv_swrap32_id, ?wrap32_id, ?wrap64_id by lia; lia
        | apply Z_to_bv_eqm; rewrite ?wrap64_mod, ?wrap32_mod, ?Z.mod_mod by lia; first [ reflexivity | Z.div_mod_to_equations; lia ] ].

Lemma IMEMg_intro : forall fr X w m, fr X (w_r w) m -> stk psegs m (ix_lo X) (bv_unsigned (ix_sp X) + -224) ->
  izs m (ix_L X) (w_c w) -> IST m (ix_L X) (w_s w) -> iin m X -> iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w)) ->
  mem_inv psegs m -> munch (ix_W X) (ix_m0 X) m -> wmono psegs (ix_m0 X) m -> IMEMg fr X w m.
Proof. intros. unfold IMEMg, IREP. split; [assumption|]. split; [assumption|]. split; [split; assumption|]. repeat (split; [assumption|]). assumption. Qed.
Definition IMEM_intro := IMEMg_intro iframe.
Definition IMEML_intro := IMEMg_intro iframeL.

Lemma IMEM_regs : forall X s c r r' m, IMEM X (mkW s c r) m ->
  ir_in r' = ir_in r -> ir_out r' = ir_out r -> ir_ret r' = ir_ret r -> ir_put r' = ir_put r -> IMEM X (mkW s c r') m.
Proof.
  intros X s c r r' m (HF & HR) E1 E2 E3 E4. unfold IMEM, IMEMg in *. cbn [w_s w_c w_r] in *. rewrite E4. split; [|exact HR].
  destruct HF as (j & HF). exists j. unfold iframe_cells in *. rewrite E1, E2, E3. exact HF.
Qed.

Lemma IMEML_of_IMEM : forall X s c r r' m, IMEM X (mkW s c r) m ->
  ir_in r' = ir_in r -> ir_out r' = ir_out r -> ir_put r' = ir_put r -> IMEML X (mkW s c r') m.
Proof.
  intros X s c r r' m (HF & HR) E1 E2 E3. unfold IMEML, IMEMg in *. cbn [w_s w_c w_r] in *. rewrite E3. split; [|exact HR].
  destruct HF as (j & HF). exists (wz (ir_ret r)), j. unfold iframe_cells in *. rewrite E1, E2. exact HF.
Qed.

Lemma PATI_regs : forall X s c r r1, PATI X (mkW s c r) ->
  ir_put r1 = ir_put r -> ir_out r1 = ir_out r -> ir_left r1 = ir_left r -> PATI X (mkW s c r1).
Proof. intros X s c r r1 H E1 E2 E3. unfold PATI, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3. exact H. Qed.

Lemma PATI_step_out : forall X s c r s' c' r', PATI X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  0 <= ir_out r' - ir_left r' <= ir_put r' -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> PATI X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' (P1 & P2 & P3 & _ & _ & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & _ & _ & P16)) E1 E2 E3 E4 NG E6 E7 E8 E9 E10 HO HN HI.
  unfold PATI, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E6, E7, E8, E10. rewrite E9 in *.
  repeat (split; [first [assumption | left; assumption]|]). assumption.
Qed.

Lemma PATI_step : forall X s c r s' c' r', PATI X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  ir_out r' = ir_out r -> ir_left r' = ir_left r -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> PATI X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' HP E1 E2 E3 E4 NG E6 E7 E8 E9 E10 E11 E12 HN HI.
  eapply PATI_step_out; try eassumption. rewrite E9, E11, E12.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & H & _)). exact H.
Qed.

Definition arm_stmt (flush M PC : Z) (arm : AM unit) : Prop := forall X w x12 ms,
  ix_flush X = flush -> ILOOP X w PC (wz (-3)) x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = M ->
  evt psegs (fun ms' => IPOST X (arm w) ms' /\ PATI X (wof (arm w))) ms.

