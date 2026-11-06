From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import check_cells_valid_c.
Import ListNotations.
Open Scope Z_scope.

(** check_cells_valid of the plain image (0x146e0, 23 instructions), walked with Lib/Tac.v and Lib/Step.v. The
    prologue saves ra in the 16-byte frame; the cells lie below the stack region, so the bytes_at premise on them is
    carried across that store. For rc <= 0 `blez a1` goes to the epilogue. Else the loop at 0x146f8 runs over the
    cells with a0 = out + 2 + 3i and a1 = rc - i ([ccv_loop], by induction on the cells not yet read): it reads the
    three bytes of cell i, each test against 47, 2 and (param = 2 ? 0x37 : 1) is false by cell_valid, and `bnez a1`
    goes back while cells remain, else to the epilogue (0x1472c), which reloads ra and frees the frame. *)

Lemma ccv_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma ccv_zxb : forall z, 0 <= z < 256 -> bv_unsigned (zxb (Z_to_bv 8 z)) = z.
Proof.
  intros z Hz. unfold zxb. rewrite ccv_u8 by lia. apply unsigned_lit. lia.
Qed.

Lemma ccv_s64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2) with (2^63). lia.
Qed.

(** The three bytes of the cell at X. *)
Lemma ccv_read3 : forall m X (b0 b1 b2 : byte) rest,
  bytes_at rsegs m X (b0 :: b1 :: b2 :: rest) ->
  ov_read_bytes rsegs m (wa (X + 0)) 1 = Some [b0] /\
  ov_read_bytes rsegs m (wa (X + 1)) 1 = Some [b1] /\
  ov_read_bytes rsegs m (wa (X + 2)) 1 = Some [b2].
Proof.
  intros m X b0 b1 b2 rest H. split; [|split].
  - exact (bytes_at_read rsegs m X _ 0 1 H ltac:(lia) ltac:(cbn; lia)).
  - exact (bytes_at_read rsegs m X _ 1 1 H ltac:(lia) ltac:(cbn; lia)).
  - exact (bytes_at_read rsegs m X _ 2 1 H ltac:(lia) ltac:(cbn; lia)).
Qed.

(** A branch whose condition the context decides. *)
Ltac ccv_br := first [ if_false | if_true ].

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop).

  Notation ST pc x10 x11 x14 x15 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 47) (Z_to_bv 64 2) x14 x15 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  (** The loop head 0x146f8 with a0 = X + 2 at the next cell, a1 = L cells left (rest), a2 = 47, a3 = 2. *)
  Lemma ccv_loop : forall rest X L x14 x15,
    bytes_at rsegs m X (ha_cells_bytes rest) -> Forall cell_valid rest ->
    L = Z.of_nat (length rest) -> 1 <= L < 2^31 ->
    (forall x10 x11 x14' x15', evt rsegs Q (ST 0x1472c x10 x11 x14' x15')) ->
    evt rsegs Q (ST 0x146f8 (Z_to_bv 64 (X + 2)) (Z_to_bv 64 L) x14 x15).
  Proof.
    induction rest as [|[[ch p] v] rest IH]; intros X L x14 x15 HB HV HL HR EXIT.
    - cbn [length Z.of_nat] in HL. lia.
    - apply Forall_cons_iff in HV. destruct HV as [Hc HV].
      unfold cell_valid in Hc. unfold HA_CHANNELS, HA_SENS, HA_SENS_MAX in Hc.
      destruct Hc as (Hch & Hp & Hv).
      assert (Hv8 : 0 <= v <= 55) by (destruct (p =? 2); lia).
      change (bytes_at rsegs m X (Z_to_bv 8 ch :: Z_to_bv 8 p :: Z_to_bv 8 v :: ha_cells_bytes rest)) in HB.
      destruct (ccv_read3 m X _ _ _ _ HB) as (R0 & R1 & R2).
      rewrite Z.add_0_r in R0.
      assert (HT : bytes_at rsegs m (X + 3) (ha_cells_bytes rest))
        by exact (proj2 (proj1 (bytes_at_app rsegs m X [Z_to_bv 8 ch; Z_to_bv 8 p; Z_to_bv 8 v]
                                  (ha_cells_bytes rest)) HB)).
      clear HB.
      pose proof (ccv_zxb ch ltac:(lia)) as E0. pose proof (ccv_zxb p ltac:(lia)) as E1.
      pose proof (ccv_zxb v ltac:(lia)) as E2.
      pose proof (ccv_u8 ch ltac:(lia)) as E0'. pose proof (ccv_u8 p ltac:(lia)) as E1'.
      pose proof (ccv_u8 v ltac:(lia)) as E2'.
      cbn [length] in HL. rewrite Nat2Z.inj_succ in HL.
      (* lbu a4, -2(a0); bltu a2, a4: not taken (ch <= 47) *)
      step. step. ccv_br.
      (* lbu a4, -1(a0); bltu a3, a4: not taken (param <= 2) *)
      step. step. ccv_br.
      (* beq a4, a3 *)
      step.
      destruct (Z.eq_dec p 2) as [Ep | Ep].
      + rewrite (proj2 (Z.eqb_eq p 2) Ep) in Hv.
        (* taken: addi a4, zero, 0x37 *)
        ccv_br. step.
        (* lbu a5, 0(a0); bltu a4, a5: not taken (value <= 0x37) *)
        step. step. ccv_br.
        (* addi a1, a1, -1; addi a0, a0, 3; bnez a1 *)
        step. step. step.
        let K := fresh "K" in
        if_cases K; zify_cond K.
        * match goal with |- context [Z_to_bv 64 (X + ?k)] => replace (X + k) with (X + 3 + 2) by lia end.
          apply (IH (X + 3) (L + -1)); [exact HT | exact HV | lia | lia | exact EXIT].
        * apply EXIT.
      + rewrite (proj2 (Z.eqb_neq p 2) Ep) in Hv.
        (* not taken: addi a4, zero, 1; j 0x14718 *)
        ccv_br. step. step.
        (* lbu a5, 0(a0); bltu a4, a5: not taken (value <= 1) *)
        step. step. ccv_br.
        (* addi a1, a1, -1; addi a0, a0, 3; bnez a1 *)
        step. step. step.
        let K := fresh "K" in
        if_cases K; zify_cond K.
        * match goal with |- context [Z_to_bv 64 (X + ?k)] => replace (X + k) with (X + 3 + 2) by lia end.
          apply (IH (X + 3) (L + -1)); [exact HT | exact HV | lia | lia | exact EXIT].
        * apply EXIT.
  Qed.
End Loop.

Theorem check_cells_valid_holds : check_cells_valid_contract.
Proof.
  unfold check_cells_valid_contract, CHECK_CELLS_VALID, CHECK_CELLS_VALID_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo rc cs HA1 HRC HPRE ST HK HW MI.
  subst a1. clear HW.
  pose proof (ccv_s64 rc ltac:(lia)) as Hs.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 16, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  destruct (Z_lt_le_dec 0 rc) as [Hpos | Hneg].
  - destruct (HPRE Hpos) as (HB & HL & HV & HLO). clear HPRE.
    assert (HL3 : Z.of_nat (length (ha_cells_bytes cs)) = 3 * rc) by (rewrite length_ha_cells_bytes; lia).
    (* addi sp, sp, -16; sd ra, 8(sp): the cells lie below lo, so HB survives the store *)
    step. step.
    (* blez a1: not taken *)
    step. ccv_br.
    (* addi a0, a0, 2; addi a2, zero, 0x2f; addi a3, zero, 2 *)
    step. step. step.
    eapply ccv_loop with (rest := cs); [ exact HB | exact HV | symmetry; exact HL | lia | ].
    intros x10 x11 x14 x15.
    (* ld ra, 8(sp); addi sp, sp, 16; ret *)
    step. step. step.
    release_frame FR ST Sp.
    finish.
  - clear HPRE.
    (* addi sp, sp, -16; sd ra, 8(sp) *)
    step. step.
    (* blez a1: taken to 0x1472c; ld ra, 8(sp); addi sp, sp, 16; ret *)
    step. ccv_br.
    step. step. step.
    release_frame FR ST Sp.
    finish.
Qed.
