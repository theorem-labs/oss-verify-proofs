(* The program points of the tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput (op_submit's g_raw == 0 arm,
   fuzz/fuzz_transport.c:1085-1121), as machine-state predicates, and the tactics of its walk. Each stretch between
   two of them is a lemma of its own file (U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_<x>.v):
     t4_SA   0x14220  serial = g_ncmd in s0, g_cmd[serial] zeroed, len in a0, the cursor after the length byte  (_a1)
     t4_SB1  0x1425c  the four bytes TAG, serial & 0x7f, serial >> 7, len stored, n = min(len - 3, in.n) in s6 (_a)
     t4_SB   0x1427c  the input bytes copied: the struct at sp+0x60 is the model's cmd_struct (t4_cs)          (_a)
     t4_SC   0x142e8  sys (DgnSpec system_at over the first len bytes) in s10                                  (_b)
     t4_SD   0x14384  at (submit_find_at) in s4, as an unsigned 32-bit value                                   (_c)
   then _d.v's t4_SW (0x143b4, want in s7) and the three calls up to 0x143f0 (_op4_tag_rec.v's t4r_at).
   A register whose value matters is an existential with an equation, so a stretch never depends on the syntactic
   form the previous one left. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid
  LLVMFuzzerTestOneInput_op4_lib LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- tactics *)

(* print the goal into the build log *)
Ltac t4_goal := match goal with |- ?G => idtac G end.
Tactic Notation "t4_dbg" string(s) := idtac s; t4_goal.

(* a branch whose condition the context decides (U/Prog/T/LLVMFuzzerTestOneInput_op4_defs.v brv / br) *)
Ltac t4_zsolve := first [ lia | (Z.div_mod_to_equations; lia) ].
Ltac t4_bsolve :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); t4_bsolve
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); t4_bsolve
  | |- Z.eqb _ _ = true => apply Z.eqb_eq; t4_zsolve
  | |- Z.eqb _ _ = false => apply Z.eqb_neq; t4_zsolve
  | |- Z.ltb _ _ = true => apply Z.ltb_lt; t4_zsolve
  | |- Z.ltb _ _ = false => apply Z.ltb_ge; t4_zsolve
  | |- Z.leb _ _ = true => apply Z.leb_le; t4_zsolve
  | |- Z.leb _ _ = false => apply Z.leb_gt; t4_zsolve
  | |- _ = _ => reflexivity
  end.
Ltac t4_brv v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v;
      [cbv iota | symmetry; rewrite ?bv_lts_zero_r; cbn [Z.b2z]; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit_wrap;
                  t4_bsolve]
  end.
Ltac t4_br := first [ t4_brv true | t4_brv false
                    | match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                        idtac "BRFAIL:" c; fail 100 "t4_br: the branch condition is not decided" end ].

(* two words given by their values *)
Ltac t4_weq :=
  first [ reflexivity
        | (f_equal; lia)
        | (apply wk_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia)
        | (idtac "WEQFAIL"; match goal with |- ?G => idtac G end; fail 1) ].

(* the return address of a call, as a literal pc *)
Ltac t4_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      rewrite (ret_pc_even n) by (first [lia | reflexivity])
  end.

(* ---------------------------------------------------------------- the model's pieces, in range *)

Definition t4_ok (D : list byte) (ops before : Z) (c3 : fuzz_in) (B1 : list byte) (display key : Z) : Prop :=
  0 <= ops < OPS_MAX /\ llvm_cursor D c3 /\ 0 <= before < 2 ^ 32 /\ 0 <= display <= 1 /\ 0 <= key < 2 ^ 32 /\
  g_ncmd B1 < CMDS_MAX.

Lemma t4_ncmd_rng : forall B, 0 <= g_ncmd B < 2 ^ 32.
Proof.
  intros B. pose proof (u_at_range B OFF_g_ncmd 4) as R.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R.
Qed.

Lemma t4_nq_rng : forall B, 0 <= g_nq B < 2 ^ 32.
Proof.
  intros B. pose proof (u_at_range B OFF_g_nq 4) as R.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R.
Qed.

Lemma t4_qat_rng : forall B i, 0 <= Q_at B i < 2 ^ 32.
Proof.
  intros B i. pose proof (u_at_range B (OFF_g_q + 4 * i) 4) as R.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R.
Qed.

Lemma t4_key_rng : forall B i, 0 <= Cmd_key B i < 2 ^ 32.
Proof.
  intros B i. pose proof (u_at_range B (A_Cmd_key i) 4) as R.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R.
Qed.

Lemma t4_len_rng : forall D c3, 3 <= t4_len D c3 <= 24.
Proof.
  intros D c3. unfold t4_len.
  pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c3)) 22 ltac:(lia)). lia.
Qed.

Lemma t4_cur4 : forall D c3, llvm_cursor D c3 -> llvm_cursor D (t4_c4 D c3).
Proof. intros D c3 H. unfold t4_c4. apply t4_cursor_u8. exact H. Qed.

Lemma t4_tk_facts : forall D c3, llvm_cursor D c3 ->
  t4_off D c3 = fi_off (t4_c4 D c3) /\
  t4_n D c3 = (if t4_len D c3 - 3 <? fi_n (t4_c4 D c3) then t4_len D c3 - 3 else fi_n (t4_c4 D c3)) /\
  0 <= t4_n D c3 <= 21 /\ t4_n D c3 <= fi_n (t4_c4 D c3) /\
  fi_off (t4_c5 D c3) = fi_off (t4_c4 D c3) + t4_n D c3 /\
  fi_n (t4_c5 D c3) = fi_n (t4_c4 D c3) - t4_n D c3.
Proof.
  intros D c3 HC.
  assert (HC4 : llvm_cursor D (t4_c4 D c3)) by (apply t4_cur4; exact HC).
  destruct HC4 as (H1 & H2 & H3).
  pose proof (t4_len_rng D c3) as HL.
  unfold t4_c5, t4_off, t4_n, t4_tk, fuzz_take_m. cbn [fst snd fi_off fi_n].
  destruct (Z.ltb_spec (t4_len D c3 - 3) (fi_n (t4_c4 D c3))) as [E|E];
    (split; [reflexivity|]); (split; [reflexivity|]); repeat split; lia.
Qed.

Lemma t4_cur5 : forall D c3, llvm_cursor D c3 -> llvm_cursor D (t4_c5 D c3).
Proof.
  intros D c3 H. unfold t4_c5, t4_tk. apply t4_cursor_take; [apply t4_cur4; exact H|].
  pose proof (t4_len_rng D c3). lia.
Qed.

Lemma t4_cbD : forall D c3, llvm_cursor D c3 ->
  0 <= t4_off D c3 /\ 0 <= t4_n D c3 <= 21 /\ t4_off D c3 + t4_n D c3 <= Z.of_nat (length D).
Proof.
  intros D c3 HC. pose proof (t4_tk_facts D c3 HC) as (E1 & _ & E3 & E4 & _ & _).
  pose proof (t4_cur4 D c3 HC) as (H1 & H2 & H3). rewrite E1. repeat split; lia.
Qed.

Lemma t4_c4_z : forall D c3, fi_n c3 = 0 -> t4_c4 D c3 = c3 /\ t4_len D c3 = 3.
Proof. intros D c3 H. unfold t4_len, t4_c4, fuzz_u8_m. rewrite H. cbn. split; reflexivity. Qed.

Lemma t4_c4_nz : forall D c3, fi_n c3 <> 0 ->
  t4_c4 D c3 = FuzzIn (fi_off c3 + 1) (fi_n c3 - 1) /\
  t4_len D c3 = bv_unsigned (nth (Z.to_nat (fi_off c3)) D (b8 0)) mod 22 + 3.
Proof.
  intros D c3 H. unfold t4_len, t4_c4, fuzz_u8_m.
  destruct (Z.eqb_spec (fi_n c3) 0); [lia|]. cbn [fst snd]. split; reflexivity.
Qed.

(* ---------------------------------------------------------------- the frame's scratch cells, by name *)

(* the struct diginet_cmd at sp+0x60 after the four byte stores of 0x1423c-0x14248 *)
Definition t4_pfx (B1 : list byte) : list byte :=
  [b8 TAG; b8 (Z.land (g_ncmd B1) 0x7f); b8 (Z.land (Z.shiftr (g_ncmd B1) 7) 0x7f)].

Definition t4_j60s (B1 D : list byte) (c3 : fuzz_in) (display key : Z) (jhi : list byte) : list byte :=
  cmd_struct (t4_pfx B1 ++ repeat (b8 0) 21) (t4_len D c3) display key ++ jhi.

(* the 16 bytes at sp+0x10 after `sd a4, 0x10(sp)` (the cursor's n after the length byte) *)
Definition t4_j10 (D : list byte) (c3 : fuzz_in) (before : Z) : list byte :=
  le8 (Z_to_bv 64 (fi_n (t4_c4 D c3))) ++ le8 (Z_to_bv 64 (bv_swrap 32 before)).

Lemma t4_j10_len : forall D c3 before, length (t4_j10 D c3 before) = 16%nat.
Proof. intros. unfold t4_j10. rewrite app_length, !length_le8. reflexivity. Qed.

Lemma t4_j60s_len : forall B1 D c3 display key jhi, length jhi = 8%nat ->
  length (t4_j60s B1 D c3 display key jhi) = 40%nat.
Proof.
  intros B1 D c3 display key jhi H. unfold t4_j60s, cmd_struct, t4_pfx.
  rewrite !app_length, repeat_length, length_put, H. reflexivity.
Qed.

Lemma t4_cs_jhi_len : forall B1 D c3 display key jhi, llvm_cursor D c3 -> length jhi = 8%nat ->
  length (t4_cs B1 D c3 display key ++ jhi) = 40%nat.
Proof.
  intros B1 D c3 display key jhi HC H. pose proof (t4_cbD D c3 HC) as (H1 & H2 & H3).
  rewrite app_length, (t4_cs_len B1 D c3 display key H1 H2 H3), H. reflexivity.
Qed.

(* ---------------------------------------------------------------- arithmetic of the length byte *)

(* the compiler's reciprocal of 22 (0x0ba2e8ba2e8ba2e9 at 0x10400): a mulhu, no shift, for a byte dividend *)
Lemma t4_magic : forall b K, 0 <= b < 256 -> 2 ^ 64 <= 22 * K ->
  11 * (22 * K - 2 ^ 64) + 21 * K < 2 ^ 64 -> Z.shiftr (b * K) 64 = b / 22.
Proof.
  intros b K Hb HK HB. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod b 22 ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound b 22 ltac:(lia)) as R.
  assert (Hq : 0 <= b / 22 <= 11).
  { split; [apply Z.div_pos; lia|].
    assert (b / 22 < 12) by (apply Z.div_lt_upper_bound; lia). lia. }
  remember (b / 22) as q eqn:Eq. remember (b mod 22) as r eqn:Er.
  assert (HKp : 0 <= K) by lia.
  assert (HB2 : b * K = q * 2 ^ 64 + ((22 * K - 2 ^ 64) * q + r * K)).
  { replace b with (22 * q + r) at 1 by lia. ring. }
  rewrite HB2, Z.div_add_l by lia.
  rewrite (Z.div_small ((22 * K - 2 ^ 64) * q + r * K) (2 ^ 64)) by nia.
  lia.
Qed.

(* the machine's len (0x141e8-0x14208) against the model's: every mulhu by the reciprocal rewritten, then the two
   compared modulo 2^64 *)
Ltac t4_len_eq x :=
  apply wk_bv_eqm; rewrite ?unsigned_lit_wrap;
  repeat match goal with
  | |- context [Z.shiftr (x * ?k) 64] => rewrite (t4_magic x k) by lia
  | |- context [Z.shiftr (?k * x) 64] => rewrite (Z.mul_comm k x), (t4_magic x k) by lia
  end;
  Z.div_mod_to_equations; lia.

(* ---------------------------------------------------------------- llvm_mem across a fill of the world *)

Lemma t4_after_fill : forall data D regs0 m0 Sp lo B m m' k n src j10 jio j60 X,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  munch [(X, X + n)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' X [CB (Z.to_nat n) src] -> X = W_BASE_UBSAN + k ->
  0 <= k -> 0 <= n -> k + n <= W_LEN -> g_fail_next (upd B k src) <= 1 ->
  llvm_mem data D regs0 m0 Sp lo (upd B k src) m' j10 jio j60.
Proof.
  intros data D regs0 m0 Sp lo B m m' k n src j10 jio j60 X HM MU WMO MI CZ -> Hk Hn Hkn HF.
  exact (llvm_mem_after_fill data D regs0 m0 Sp lo B m m' k n src j10 jio j60 HM MU WMO MI CZ Hk Hn Hkn HF).
Qed.

(* ---------------------------------------------------------------- the program points *)

Section T4.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo ops before : Z)
  (c3 : fuzz_in) (B1 : list byte) (display key : Z) (F : bvmap 5 word) (fc : bv 32).

Definition t4_SA (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jlo jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14220) fc None m (seg_rom rsegs) /\
    s0 = Z_to_bv 64 (g_ncmd B1) /\ s2 = Z_to_bv 64 (229576 + g_ncmd B1 * 40) /\ s5 = Z_to_bv 64 229576 /\
    s7 = Z_to_bv 64 (data + fi_off (t4_c4 D c3)) /\ s8 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) /\
    s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) /\ s10 = Z_to_bv 64 (Sp + 97) /\ s11 = Z_to_bv 64 ops /\
    a0 = Z_to_bv 64 (t4_len D c3) /\ a4 = Z_to_bv 64 (fi_n (t4_c4 D c3)) /\
    t4_ok D ops before c3 B1 display key /\ length jlo = 8%nat /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo (t4_B2 B1) m (jlo ++ le8 (Z_to_bv 64 (bv_swrap 32 before))) jio
      (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi).

Definition t4_SB1 (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jlo jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1425c) fc None m (seg_rom rsegs) /\
    s0 = Z_to_bv 64 (g_ncmd B1) /\ s1 = Z_to_bv 64 240 /\ s2 = Z_to_bv 64 (229576 + g_ncmd B1 * 40) /\
    s4 = Z_to_bv 64 19 /\ s5 = Z_to_bv 64 229576 /\ s6 = Z_to_bv 64 (t4_n D c3) /\
    s7 = Z_to_bv 64 (data + fi_off (t4_c4 D c3)) /\ s8 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) /\
    s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) /\ s10 = Z_to_bv 64 (Sp + 97) /\ s11 = Z_to_bv 64 ops /\
    a4 = Z_to_bv 64 (fi_n (t4_c4 D c3)) /\
    t4_ok D ops before c3 B1 display key /\ length jlo = 8%nat /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo (t4_B2 B1) m (jlo ++ le8 (Z_to_bv 64 (bv_swrap 32 before))) jio
      (t4_j60s B1 D c3 display key jhi).

Definition t4_SB (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1427c) fc None m (seg_rom rsegs) /\
    s0 = Z_to_bv 64 (g_ncmd B1) /\ s1 = Z_to_bv 64 240 /\ s2 = Z_to_bv 64 (229576 + g_ncmd B1 * 40) /\
    s3 = Z_to_bv 64 (data + fi_off (t4_c5 D c3)) /\ s4 = Z_to_bv 64 19 /\ s5 = Z_to_bv 64 229576 /\
    s6 = Z_to_bv 64 (t4_n D c3) /\ s8 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) /\
    s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) /\ s10 = Z_to_bv 64 (Sp + 97) /\ s11 = Z_to_bv 64 ops /\
    t4_ok D ops before c3 B1 display key /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo (t4_B2 B1) m (t4_j10 D c3 before) jio (t4_cs B1 D c3 display key ++ jhi).

Definition t4_SC (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x142e8) fc None m (seg_rom rsegs) /\
    s0 = Z_to_bv 64 (g_ncmd B1) /\ s2 = Z_to_bv 64 (229576 + g_ncmd B1 * 40) /\
    s3 = Z_to_bv 64 (data + fi_off (t4_c5 D c3)) /\ s5 = Z_to_bv 64 229576 /\
    s6 = Z_to_bv 64 (t4_n D c3) /\ s8 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) /\
    s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) /\ s10 = Z_to_bv 64 (Z.b2z (t4_sys B1 D c3)) /\
    s11 = Z_to_bv 64 ops /\
    t4_ok D ops before c3 B1 display key /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo (t4_B2 B1) m (t4_j10 D c3 before) jio (t4_cs B1 D c3 display key ++ jhi).

Definition t4_SD (at_ : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14384) fc None m (seg_rom rsegs) /\
    s0 = Z_to_bv 64 (g_ncmd B1) /\ s2 = Z_to_bv 64 (229576 + g_ncmd B1 * 40) /\
    s3 = Z_to_bv 64 (data + fi_off (t4_c5 D c3)) /\ s4 = Z_to_bv 64 (at_ mod 2 ^ 32) /\ s5 = Z_to_bv 64 229576 /\
    s6 = Z_to_bv 64 (t4_n D c3) /\ s8 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) /\
    s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) /\ s10 = Z_to_bv 64 (Z.b2z (t4_sys B1 D c3)) /\
    s11 = Z_to_bv 64 ops /\
    t4_ok D ops before c3 B1 display key /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo (t4_B2 B1) m (t4_j10 D c3 before) jio (t4_cs B1 D c3 display key ++ jhi).

End T4.
