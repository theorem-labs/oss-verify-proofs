From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import check_cells_c.
Import ListNotations.
Open Scope Z_scope.

(** check_cells of the UBSan image (0x149e4, 41 instructions), walked with Lib/Tac.v and Lib/Step.v. The prologue
    carves the 16-byte frame and stores ra at sp - 8; the bytes_at premises of out (below lo) and of x (at or above
    sp) are carried across that store. `andi a3, a2, 3` is 0 since x is 4-aligned ([andi3_zero]), so `bnez a3` (to
    the trap 0x14a7c) is not taken; `lw a3, 0(a2)` reads x->rc = le4 rc, sign-extended ([cc_sx32]), so `bne a1, a3`
    is not taken; `blez a1` goes to the epilogue for rc <= 0. For rc > 0 the set-up leaves a5 = ~out,
    a1 = ~(x + 4), a6 = 12 rc, a7 = 30, and the loop at 0x14a2c ([loop], on the number i of cells already compared:
    a0 = out + 3i + 1, a3 = 3i, a4 = 12i) tests the three UBSan traps, all false: ~out <u 3i and ~(x + 4) <u 12i by
    the bounds of the bytes_at premises (out + 3 rc, x + 4 + 12 rc <= 2^64), 3i = 30 by i < rc <= 10. It then reads
    cell i of out with three `lbu` and of x with three `lw` ([cell_reads]); each field fits a byte (cell_bytes_ok), so
    `lw` and `lbu` give the same word ([cc_sx32], [cc_zxb]) and no `bne` is taken; `bne a6, a4` leaves the loop after
    cell rc - 1. The epilogue ([exit_ok]) reloads ra, frees the frame and returns. *)

(** `lw` sign-extends the low 32 bits: the identity on a 64-bit literal in the 32-bit signed range. *)
Lemma cc_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations; lia.
Qed.

(** `lbu` zero-extends a byte: the identity on a value of [0, 256). *)
Lemma cc_zxb : forall z, 0 <= z < 256 -> zxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(** The word `andi a3, a2, 3` leaves, in the form the step tactics write it, for a 4-aligned a2. *)
Lemma andi3_zero : forall x : word, bv_unsigned x mod 4 = 0 -> Z_to_bv 64 (Z.land (bv_unsigned x) 3) = Z_to_bv 64 0.
Proof. intros x Hx. f_equal. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact Hx. Qed.

Lemma cc_flat_map_app : forall {A B} (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. induction l1 as [|a l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma ha_cells_bytes_split : forall l1 c l2,
  ha_cells_bytes (l1 ++ c :: l2) = ha_cells_bytes l1 ++ ha_cell_bytes c ++ ha_cells_bytes l2.
Proof. intros. unfold ha_cells_bytes. rewrite cc_flat_map_app. reflexivity. Qed.

Lemma x_cells_bytes_split : forall l1 c l2,
  x_cells_bytes (l1 ++ c :: l2) = x_cells_bytes l1 ++ x_cell_bytes c ++ x_cells_bytes l2.
Proof. intros. unfold x_cells_bytes. rewrite cc_flat_map_app. reflexivity. Qed.

(** A read of n bytes at offset k of a bytes_at premise, at an address and with a byte list given up to equality. *)
Lemma read_at : forall m a bs (k : Z) n a' bs',
  bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  a' = a + k -> firstn n (skipn (Z.to_nat k) bs) = bs' -> ov_read_bytes rsegs m (wa a') n = Some bs'.
Proof. intros m a bs k n a' bs' H Hk Hn -> <-. apply bytes_at_read; assumption. Qed.

(** The read of a whole bytes_at premise. *)
Lemma read_all_at : forall m a bs a' n, bytes_at rsegs m a bs -> a' = a -> n = length bs ->
  ov_read_bytes rsegs m (wa a') n = Some bs.
Proof.
  intros m a bs a' n H -> ->.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. change (skipn 0 bs) with bs in R.
  rewrite firstn_all in R. exact R.
Qed.

(** The six loads of cell i: its three bytes in out (at A0 + 3i) and its three ints in x (at X + 4 + 12i). *)
Lemma cell_reads : forall m A0 X cs i ch p v,
  bytes_at rsegs m A0 (ha_cells_bytes cs) -> bytes_at rsegs m (X + 4) (x_cells_bytes cs) ->
  nth_error cs (Z.to_nat i) = Some (ch, p, v) -> 0 <= i ->
  ov_read_bytes rsegs m (wa (A0 + 3 * i)) 1 = Some [Z_to_bv 8 ch] /\
  ov_read_bytes rsegs m (wa (A0 + 3 * i + 1)) 1 = Some [Z_to_bv 8 p] /\
  ov_read_bytes rsegs m (wa (A0 + 3 * i + 2)) 1 = Some [Z_to_bv 8 v] /\
  ov_read_bytes rsegs m (wa (X + 12 * i + 4)) 4 = Some (le4 (Z_to_bv 64 ch)) /\
  ov_read_bytes rsegs m (wa (X + 12 * i + 8)) 4 = Some (le4 (Z_to_bv 64 p)) /\
  ov_read_bytes rsegs m (wa (X + 12 * i + 12)) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m A0 X cs i ch p v HO HX E Hi.
  destruct (nth_error_split cs (Z.to_nat i) (ch, p, v) E) as (l1 & l2 & -> & L1).
  rewrite ha_cells_bytes_split in HO. rewrite x_cells_bytes_split in HX.
  apply bytes_at_app in HO. destruct HO as [_ HO]. apply bytes_at_app in HO. destruct HO as [HO _].
  apply bytes_at_app in HX. destruct HX as [_ HX]. apply bytes_at_app in HX. destruct HX as [HX _].
  cbn [ha_cell_bytes x_cell_bytes] in HO, HX.
  apply bytes_at_app in HX. destruct HX as [Hc HX]. apply bytes_at_app in HX. destruct HX as [Hp Hv].
  pose proof (length_ha_cells_bytes l1) as L2. pose proof (length_x_cells_bytes l1) as L3.
  pose proof (length_le4 (Z_to_bv 64 ch)) as L4. pose proof (length_le4 (Z_to_bv 64 p)) as L5.
  split; [| split; [| split; [| split; [| split]]]].
  - eapply read_at with (k := 0); [exact HO | lia | cbn; lia | lia | reflexivity].
  - eapply read_at with (k := 1); [exact HO | lia | cbn; lia | lia | reflexivity].
  - eapply read_at with (k := 2); [exact HO | lia | cbn; lia | lia | reflexivity].
  - eapply read_all_at; [exact Hc | lia | symmetry; apply length_le4].
  - eapply read_all_at; [exact Hp | lia | symmetry; apply length_le4].
  - eapply read_all_at; [exact Hv | lia | symmetry; apply length_le4].
Qed.

(** A branch condition the context refutes. *)
Ltac kill K :=
  exfalso; zify_cond K;
  repeat match goal with
         | H : context [Z.ltb _ _] |- _ => revert H
         | H : context [Z.leb _ _] |- _ => revert H
         | H : context [Z.eqb _ _] |- _ => revert H
         end;
  repeat match goal with
         | |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y)
         | |- context [(?x <=? ?y)%Z] => destruct (Z.leb_spec x y)
         | |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y)
         end;
  cbn [andb orb negb Z.b2z]; intros; try discriminate; Z.div_mod_to_equations; lia.

(** A branch whose one side the context refutes: that side is closed, the other is left. *)
Ltac nt := let K := fresh "K" in if_cases K; [ first [ kill K | clear K ] .. ].

(** The unsigned value of a register the set-up wrote (~out, ~(x + 4), 16 rc - 4 rc): the innermost
    bv_unsigned (Z_to_bv 64 e) first. *)
Ltac uv :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
             lazymatch e with context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => idtac end;
             rewrite (unsigned_lit e) by (rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?zb_lxor_ones by lia; lia)
         | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia
         | |- context [Z.shiftl ?x ?k] => rewrite (Z.shiftl_mul_pow2 x k) by lia
         end;
  lia.

Section Loop.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w1 w5 w6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo Sp A0 X rc : Z)
            (cs : list cell) (junk : list byte).
  Hypothesis FR : rw_cells rsegs m (Sp + -16) [CB 8 junk; C8 ra].
  Hypothesis ST : stk rsegs m lo (Sp + -16).
  Hypothesis MU : munch [(Sp - 16, Sp)] m0 m.
  Hypothesis WM : wmono rsegs m0 m.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis HSp : 0 <= Sp < 2 ^ 64.
  Hypothesis Hlo : lo <= Sp + -16.
  Hypothesis HL : Z.of_nat (length cs) = rc.
  Hypothesis HOK : Forall cell_bytes_ok cs.
  Hypothesis HO : bytes_at rsegs m A0 (ha_cells_bytes cs).
  Hypothesis HX : bytes_at rsegs m (X + 4) (x_cells_bytes cs).
  Hypothesis Hrc : rc <= 10.
  Hypothesis BO : A0 + 3 * rc <= 2 ^ 64.
  Hypothesis BX : X + 4 + 12 * rc <= 2 ^ 64.
  Hypothesis H1 : bv_unsigned w1 = 18446744073709551615 - (X + 4).
  Hypothesis H5 : bv_unsigned w5 = 18446744073709551615 - A0.
  Hypothesis H6 : bv_unsigned w6 = 12 * rc.

  Abbreviation POST := (fun ms' : machine_state =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 16, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp).
  Abbreviation CST pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (Sp + -16)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  (** The epilogue at 0x14a70: ld ra, 8(sp); addi sp, sp, 16; ret. *)
  Lemma exit_ok : forall x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17,
    evt rsegs POST (CST 0x14a70 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17.
    pose proof FR as FR0. pose proof ST as ST0.
    step. step. step.
    release_frame FR0 ST0 Sp.
    finish.
  Qed.

  (** The loop at 0x14a2c after i cells compared equal (0 <= i < rc). *)
  Lemma loop : forall (n : nat) (i : Z) (x5 x6 x7 x10 x13 x14 : word),
    n = Z.to_nat (rc - i) -> 0 <= i < rc ->
    x10 = Z_to_bv 64 (A0 + 3 * i + 1) -> x13 = Z_to_bv 64 (3 * i) -> x14 = Z_to_bv 64 (12 * i) ->
    evt rsegs POST (CST 0x14a2c x5 x6 x7 x10 w1 (Z_to_bv 64 (X + 8)) x13 x14 w5 w6 (Z_to_bv 64 30)).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros i x5 x6 x7 x10 x13 x14 Hn Hi E10 E13 E14. subst x10 x13 x14.
    destruct (nth_error cs (Z.to_nat i)) as [[[ch p] v]|] eqn:Ec;
      [| exfalso; apply nth_error_None in Ec; lia].
    assert (OK : cell_bytes_ok (ch, p, v)).
    { rewrite Forall_forall in HOK. apply HOK. eapply nth_error_In. exact Ec. }
    destruct OK as (Hch & Hp & Hv).
    destruct (cell_reads m A0 X cs i ch p v HO HX Ec ltac:(lia)) as (R0 & R1 & R2 & R3 & R4 & R5).
    (* bltu a5, a3: not taken (out + 3i does not wrap) *)
    step. nt.
    (* beq a3, a7: not taken (i <> 10) *)
    step. nt.
    (* bltu a1, a4: not taken (x + 4 + 12i does not wrap) *)
    step. nt.
    (* lbu t1, -1(a0); add t0, a2, a4; lw t2, -4(t0): ch twice *)
    step. step. step. clear R0 R3.
    rewrite (cc_zxb ch), (cc_sx32 ch) by lia.
    (* bne t2, t1: not taken *)
    step. nt.
    (* lbu t1, 0(a0); lw t2, 0(t0): p twice *)
    step. step. clear R1 R4.
    rewrite (cc_zxb p), (cc_sx32 p) by lia.
    step. nt.
    (* lbu t1, 1(a0); lw t0, 4(t0): v twice *)
    step. step. clear R2 R5.
    rewrite (cc_zxb v), (cc_sx32 v) by lia.
    step. nt.
    (* addi a4, a4, 12; addi a0, a0, 3; addi a3, a3, 3 *)
    step. step. step.
    (* bne a6, a4 *)
    step.
    if_cases KB.
    - (* taken: cell i + 1 is next *)
      assert (Hi1 : i + 1 < rc) by (zify_cond KB; lia).
      apply (IH (Z.to_nat (rc - (i + 1))) ltac:(lia) (i + 1));
        [ reflexivity | lia | word_eq_tac | word_eq_tac | word_eq_tac ].
    - (* not taken: all rc cells compared *)
      apply exit_ok.
  Qed.
End Loop.

Theorem check_cells_holds : check_cells_contract.
Proof.
  unfold check_cells_contract, CHECK_CELLS, CHECK_CELLS_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo rc cs HA1 Hrc HAL HR HK HC ST HF HW MI.
  subst a1. clear HW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. pose proof (zr_word a2) as Ra2. unfold inr64 in Ra0, Ra2.
  pose proof (proj1 ST) as Hlo0.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 16, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (Z_lt_le_dec 0 rc) as [Hpos | Hneg].
  - (* rc > 0: the loop *)
    destruct (HC Hpos) as (HL & HOK & HO & HOlo & HX). clear HC.
    pose proof (length_ha_cells_bytes cs) as LO. pose proof (length_x_cells_bytes cs) as LX.
    pose proof (bytes_at_bound _ _ _ _ HO) as BO. pose proof (bytes_at_bound _ _ _ _ HX) as BX.
    carve_frame 16%nat ST.
    (* addi sp, sp, -16; sd ra, 8(sp) *)
    step. step.
    pose proof (bytes_at_read rsegs _ (bv_unsigned a2) _ 0 4 HR ltac:(lia) ltac:(rewrite length_le4; lia)) as RX.
    change (firstn 4 (skipn (Z.to_nat 0) (le4 (Z_to_bv 64 rc)))) with (le4 (Z_to_bv 64 rc)) in RX.
    rewrite (wa_of_var a2 (bv_unsigned a2 + 0)) in RX by lia.
    (* andi a3, a2, 3: 0 *)
    step. rewrite (andi3_zero a2 HAL).
    (* bnez a3: not taken *)
    step. nt.
    (* lw a3, 0(a2): rc *)
    step. rewrite (cc_sx32 rc) by lia.
    (* bne a1, a3: not taken *)
    step. nt.
    (* blez a1: not taken *)
    step. nt.
    (* mv a3, zero; mv a4, zero; not a5, a0; addi a6, a2, 4; slli a7, a1, 2; slli t0, a1, 4; addi a0, a0, 1;
       addi a2, a2, 8; not a1, a6; sub a6, t0, a7; addi a7, zero, 0x1e *)
    do 11 step.
    eapply loop with (A0 := bv_unsigned a0) (X := bv_unsigned a2) (i := 0) (n := Z.to_nat rc);
      first [ eassumption | lia | word_eq_tac | uv ].
  - (* rc <= 0: straight to the epilogue *)
    clear HC.
    carve_frame 16%nat ST.
    (* addi sp, sp, -16; sd ra, 8(sp) *)
    step. step.
    pose proof (bytes_at_read rsegs _ (bv_unsigned a2) _ 0 4 HR ltac:(lia) ltac:(rewrite length_le4; lia)) as RX.
    change (firstn 4 (skipn (Z.to_nat 0) (le4 (Z_to_bv 64 rc)))) with (le4 (Z_to_bv 64 rc)) in RX.
    rewrite (wa_of_var a2 (bv_unsigned a2 + 0)) in RX by lia.
    (* andi a3, a2, 3: 0 *)
    step. rewrite (andi3_zero a2 HAL).
    (* bnez a3: not taken *)
    step. nt.
    (* lw a3, 0(a2): rc *)
    step. rewrite (cc_sx32 rc) by lia.
    (* bne a1, a3: not taken *)
    step. nt.
    (* blez a1: taken *)
    step. nt.
    eapply exit_ok; first [ eassumption | lia ].
Qed.
