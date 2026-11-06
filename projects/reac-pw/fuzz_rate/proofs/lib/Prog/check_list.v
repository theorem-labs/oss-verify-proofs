From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import check_list_c.
Import ListNotations.
Open Scope Z_scope.

(** check_list of the plain image (0x1466c, 50 instructions), walked with Lib/Tac.v and Lib/Step.v. The prologue
    carves the 16-byte frame and stores ra at sp + 8. The case split is on hz = bv_unsigned a0 (rate_bit_cases):
    for 44100 / 48000 / 96000 the walk is on literals (a0 becomes the literal), and loop 1 (0x14684) and loop 2
    (0x146bc) hit at pass 1 / 2 / 3 with the `lw` of closed_list (0x10648, image bytes); for any other hz both loops
    run three passes with no hit (the `beq` against the three words is false by the premises), loop 1 leaves by
    `mv a5, zero; j 0x146ac` with a5 = 0, and loop 2's `xor; seqz` gives 0 ([seqz_ne]). So `bne a1, a5` (a1 =
    rate_bit hz) and `bne a2, a0` (a2 = rate_closed hz) are never taken. The best chain then splits on bits 2, 1, 0
    of mask = bv_unsigned a3: `andi a0, a3, 4` taken -> 96000 (0x1470c), else `andi a0, a3, 2` taken -> 48000
    (0x14724), else `slli; srai; and` gives 44100 or 0 ([clist_bit0]); each equals rate_best mask = a4, so the
    branches to the abort call at 0x14730 are never taken. The epilogue at 0x14718 reloads ra and frees the frame. *)

Lemma rb2 : forall mk, Z.testbit mk 2 = true -> rate_best mk = 96000.
Proof. intros mk H. unfold rate_best. rewrite H. reflexivity. Qed.
Lemma rb1 : forall mk, Z.testbit mk 2 = false -> Z.testbit mk 1 = true -> rate_best mk = 48000.
Proof. intros mk H2 H1. unfold rate_best. rewrite H2, H1. reflexivity. Qed.
Lemma rb0 : forall mk, Z.testbit mk 2 = false -> Z.testbit mk 1 = false ->
  rate_best mk = if Z.testbit mk 0 then 44100 else 0.
Proof. intros mk H2 H1. unfold rate_best. rewrite H2, H1. reflexivity. Qed.

Lemma rc1 : forall hz, rate_bit hz <> 0 -> rate_closed hz = 1.
Proof. intros hz H. unfold rate_closed. destruct (Z.eqb_spec (rate_bit hz) 0); [contradiction|reflexivity]. Qed.
Lemma rc0 : forall hz, rate_bit hz = 0 -> rate_closed hz = 0.
Proof. intros hz H. unfold rate_closed. rewrite H. reflexivity. Qed.

Lemma word_of_unsigned : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z H. rewrite <- H. symmetry. apply Z_to_bv_lit_self. Qed.

(** `xor a0, a0, a6; seqz a0, a0` with a6 = c and hz <> c. *)
Lemma seqz_ne : forall (x : word) c, 0 <= c < 2^64 -> bv_unsigned x <> c ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned x) c)) 1 = Z_to_bv 64 0.
Proof.
  intros x c Hc Hne. pose proof (zr_word x) as Rx. unfold inr64 in Rx.
  assert (L : 0 <= Z.lxor (bv_unsigned x) c < 2^64) by (apply Z_lxor_range; lia).
  unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned x) c) 1) as [H|H]; [|reflexivity].
  exfalso. apply Hne. apply Z.lxor_eq_0_iff. lia.
Qed.

(** `slli a3, a3, 63; srai a3, a3, 63` keeps bit 0 of mask as all-ones or zero; `and` with 44100. *)
Lemma shl63 : forall v, Z_to_bv 64 (Z.shiftl v 63) = Z_to_bv 64 (if Z.testbit v 0 then 2^63 else 0).
Proof.
  intros v. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.bit0_odd.
  rewrite (Z.div_mod v 2) at 1 by lia. rewrite Zmod_odd.
  destruct (Z.odd v).
  - replace ((2 * (v / 2) + 1) * 2 ^ 63) with (2 ^ 63 + v / 2 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - replace ((2 * (v / 2) + 0) * 2 ^ 63) with (0 + v / 2 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma clist_bit0 : forall v,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl v 63))) 63))) 44100) =
  Z_to_bv 64 (if Z.testbit v 0 then 44100 else 0).
Proof. intros v. rewrite shl63. destruct (Z.testbit v 0); apply (f_equal (Z_to_bv 64)); reflexivity. Qed.

(** A branch whose condition the context decides by evaluation or by the premises. *)
Ltac br := first [ if_false | if_true | idtac ].
(** A branch decided by a hypothesis about a mask bit: drop the arm lia refutes. *)
Ltac kill K := first [ exfalso; zify_cond K; lia | idtac ].
Ltac brk := let K := fresh "K" in if_cases K; kill K.

(** 0x14718: ld ra, 8(sp); addi sp, sp, 16; ret. *)
Ltac epilogue FR ST Sp := step; step; step; release_frame FR ST Sp; finish.

(** 0x146e0 to the return: the best chain, split on bits 2, 1, 0 of mask. *)
Ltac tail a3 a4 HA4 FR ST Sp :=
  let B2 := fresh "B2" in let B1 := fresh "B1" in let B0 := fresh "B0" in
  let T2 := fresh "T2" in let T1 := fresh "T1" in
  destruct (Z.testbit (bv_unsigned a3) 2) eqn:B2;
  pose proof (testbit_land_pow (bv_unsigned a3) 2 ltac:(lia)) as T2; rewrite B2 in T2;
  change (2 ^ 2) with 4 in T2; cbn [negb] in T2;
  [ rewrite (rb2 _ B2) in HA4; subst a4; apply Z.eqb_neq in T2;
    (* andi a0, a3, 4; bnez a0: taken to 0x1470c *)
    step; step; brk;
    (* lui a0, 0x17; addiw a0, a0, 0x700; bne a4, a0: not taken *)
    step; step; step; br;
    epilogue FR ST Sp
  | apply Z.eqb_eq in T2;
    destruct (Z.testbit (bv_unsigned a3) 1) eqn:B1;
    pose proof (testbit_land_pow (bv_unsigned a3) 1 ltac:(lia)) as T1; rewrite B1 in T1;
    change (2 ^ 1) with 2 in T1; cbn [negb] in T1;
    [ rewrite (rb1 _ B2 B1) in HA4; subst a4; apply Z.eqb_neq in T1;
      (* andi a0, a3, 4; bnez a0: not taken; andi a0, a3, 2; bnez a0: taken to 0x14724 *)
      step; step; brk; step; step; brk;
      (* lui a0, 0xc; addiw a0, a0, -0x480; beq a4, a0: taken to 0x14718 *)
      step; step; step; br;
      epilogue FR ST Sp
    | rewrite (rb0 _ B2 B1) in HA4; apply Z.eqb_eq in T1;
      (* andi a0, a3, 4; bnez a0: not taken; andi a0, a3, 2; bnez a0: not taken *)
      step; step; brk; step; step; brk;
      (* slli a3, a3, 63; lui a0, 0xb; srai a3, a3, 63; addiw a0, a0, -0x3bc; and a0, a3, a0 *)
      step; step; step; step; step;
      rewrite clist_bit0;
      destruct (Z.testbit (bv_unsigned a3) 0) eqn:B0; rewrite ?B0 in HA4; subst a4;
      (* beq a4, a0: taken to 0x14718 *)
      step; br;
      epilogue FR ST Sp ] ].

(** One miss pass of loop 1 (lw t0; beq a0, t0; addi a5; addi a6; addi a7; bnez a6) or loop 2 (lw a6; beq a0, a6;
    mv a7, a5; addi a5; addi a1; bnez a7). *)
Ltac miss := step; step; br; step; step; step; step; br.

Theorem check_list_holds : check_list_contract.
Proof.
  unfold check_list_contract, CHECK_LIST, CHECK_LIST_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo HA1 HA2 HA4 ST HK HW MI.
  clear HW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 16, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  destruct (rate_bit_cases (bv_unsigned a0)) as [[E R]|[[E R]|[[E R]|(N1&N2&N3&R)]]].
  - (* hz = 44100: both loops hit at pass 1 *)
    rewrite (rc1 _ ltac:(rewrite R; discriminate)) in HA2. rewrite R in HA1. subst a1 a2.
    apply word_of_unsigned in E. unfold RATE_44K1 in E. subst a0. clear R.
    (* addi sp, sp, -16; sd ra, 8(sp); mv a5, zero; addi a6, zero, 3; auipc a7; addi a7, a7, -0x34 *)
    step. step. step. step. step. step.
    (* lw t0; beq a0, t0: taken to 0x146a4 *)
    step. step. br.
    (* addi a6, zero, 1; sllw a5, a6, a5; bne a1, a5: not taken *)
    step. step. step. br.
    (* addi a5, zero, 2; auipc a1; addi a1, a1, -0x6c; lw a6; beq a0, a6: taken to 0x146d4 *)
    step. step. step. step. step. br.
    (* xor a0, a0, a6; seqz a0, a0; bne a2, a0: not taken *)
    step. step. step. br.
    tail a3 a4 HA4 FR ST Sp.
  - (* hz = 48000: both loops hit at pass 2 *)
    rewrite (rc1 _ ltac:(rewrite R; discriminate)) in HA2. rewrite R in HA1. subst a1 a2.
    apply word_of_unsigned in E. unfold RATE_48K in E. subst a0. clear R.
    step. step. step. step. step. step.
    miss. step. step. br.
    step. step. step. br.
    step. step. step. miss. step. step. br.
    step. step. step. br.
    tail a3 a4 HA4 FR ST Sp.
  - (* hz = 96000: both loops hit at pass 3 *)
    rewrite (rc1 _ ltac:(rewrite R; discriminate)) in HA2. rewrite R in HA1. subst a1 a2.
    apply word_of_unsigned in E. unfold RATE_96K in E. subst a0. clear R.
    step. step. step. step. step. step.
    miss. miss. step. step. br.
    step. step. step. br.
    step. step. step. miss. miss. step. step. br.
    step. step. step. br.
    tail a3 a4 HA4 FR ST Sp.
  - (* any other hz: no hit in either loop *)
    unfold RATE_44K1, RATE_48K, RATE_96K in *.
    rewrite (rc0 _ R) in HA2. rewrite R in HA1. subst a1 a2. clear R.
    step. step. step. step. step. step.
    miss. miss. miss.
    (* mv a5, zero; j 0x146ac (over the sllw); bne a1, a5: not taken *)
    step. step. step. br.
    (* addi a5, zero, 2; auipc a1; addi a1, a1, -0x6c; three miss passes *)
    step. step. step. miss. miss. miss.
    (* xor a0, a0, a6 (a6 = 96000); seqz a0, a0: 0; bne a2, a0: not taken *)
    step. step. rewrite (seqz_ne a0 96000) by lia. step. br.
    tail a3 a4 HA4 FR ST Sp.
Qed.
