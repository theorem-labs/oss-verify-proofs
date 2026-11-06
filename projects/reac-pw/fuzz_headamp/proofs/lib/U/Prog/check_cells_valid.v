From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import check_cells_valid_c.
Import ListNotations.
Open Scope Z_scope.

(** check_cells_valid of the UBSan image (0x1491c, 28 instructions), walked with Lib/Tac.v and Lib/Step.v. For
    rc <= 0 `blez a1` goes to the `ret`. Else, with a1 = 3 rc, a3 = ~out, a4 = out + 2, a5 = 47, a6 = 2, the loop at
    0x1493c runs over the byte offset a2 = 3i ([ccvu_loop], by induction on the cells not yet read): the pointer
    overflow test ~out <u 3i is false because out + 3 rc <= 2^64 (bytes_at's bound), each test of cell i against 47,
    2 and (param = 2 ? 0x37 : 1) is false by cell_valid, and `bne a1, a2` goes back while cells remain, else to the
    `ret` at 0x14978. No store, no stack. *)

Lemma ccvu_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma ccvu_zxb : forall z, 0 <= z < 256 -> bv_unsigned (zxb (Z_to_bv 8 z)) = z.
Proof.
  intros z Hz. unfold zxb. rewrite ccvu_u8 by lia. apply unsigned_lit. lia.
Qed.

Lemma ccvu_s64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2) with (2^63). lia.
Qed.

(** The three bytes of the cell at X. *)
Lemma ccvu_read3 : forall m X (b0 b1 b2 : byte) rest,
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
Ltac ccvu_br := first [ if_false | if_true ].

Section Loop.
  Variables (ra sp gp tp t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N NA : word).

  Notation POST := (fun ms' : machine_state => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)).
  Notation ST pc x5 x12 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 N x12 NA (Z_to_bv 64 (bv_unsigned a0 + 2)) (Z_to_bv 64 47)
             (Z_to_bv 64 2) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  (** The loop head 0x1493c with a2 = K, the byte offset of the next cell (rest the cells left), a1 = N = 3 rc and
      a3 = NA = ~out. *)
  Lemma ccvu_loop : forall rc,
    bv_unsigned N = 3 * rc -> bv_unsigned NA = 2^64 - 1 - bv_unsigned a0 -> rc < 2^31 ->
    forall rest K x5 x17,
    bytes_at rsegs m (bv_unsigned a0 + K) (ha_cells_bytes rest) -> Forall cell_valid rest ->
    K + 3 * Z.of_nat (length rest) = 3 * rc -> 0 <= K -> rest <> [] ->
    evt rsegs POST (ST 0x1493c x5 (Z_to_bv 64 K) x17).
  Proof.
    intros rc HN HNA HRC rest.
    pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
    induction rest as [|[[ch p] v] rest IH]; intros K x5 x17 HB HV HK HK0 HNE.
    - exfalso. apply HNE. reflexivity.
    - apply Forall_cons_iff in HV. destruct HV as [Hc HV].
      unfold cell_valid in Hc. unfold HA_CHANNELS, HA_SENS, HA_SENS_MAX in Hc.
      destruct Hc as (Hch & Hp & Hv).
      assert (Hv8 : 0 <= v <= 55) by (destruct (p =? 2); lia).
      change (bytes_at rsegs m (bv_unsigned a0 + K)
                (Z_to_bv 8 ch :: Z_to_bv 8 p :: Z_to_bv 8 v :: ha_cells_bytes rest)) in HB.
      pose proof (bytes_at_bound rsegs m _ _ HB) as HBB. cbn [length] in HBB.
      destruct (ccvu_read3 m _ _ _ _ _ HB) as (R0 & R1 & R2).
      rewrite Z.add_0_r in R0.
      assert (HT : bytes_at rsegs m (bv_unsigned a0 + (K + 3)) (ha_cells_bytes rest)).
      { replace (bv_unsigned a0 + (K + 3)) with (bv_unsigned a0 + K + 3) by lia.
        exact (proj2 (proj1 (bytes_at_app rsegs m (bv_unsigned a0 + K) [Z_to_bv 8 ch; Z_to_bv 8 p; Z_to_bv 8 v]
                               (ha_cells_bytes rest)) HB)). }
      clear HB.
      pose proof (ccvu_zxb ch ltac:(lia)) as E0. pose proof (ccvu_zxb p ltac:(lia)) as E1.
      pose proof (ccvu_zxb v ltac:(lia)) as E2.
      pose proof (ccvu_u8 ch ltac:(lia)) as E0'. pose proof (ccvu_u8 p ltac:(lia)) as E1'.
      pose proof (ccvu_u8 v ltac:(lia)) as E2'.
      cbn [length] in HK. rewrite Nat2Z.inj_succ in HK.
      pose proof (unsigned_lit K ltac:(lia)) as EK.
      (* bltu a3, a2: not taken (no pointer overflow at out + K) *)
      step. ccvu_br.
      (* add a7, a0, a2; lbu t0, 0(a7); bltu a5, t0: not taken (ch <= 47) *)
      step. step. step. ccvu_br.
      (* lbu a7, 1(a7); bltu a6, a7: not taken (param <= 2) *)
      step. step. ccvu_br.
      (* beq a7, a6 *)
      step.
      destruct (Z.eq_dec p 2) as [Ep | Ep].
      + rewrite (proj2 (Z.eqb_eq p 2) Ep) in Hv.
        (* taken: addi a7, zero, 0x37 *)
        ccvu_br. step.
        (* add t0, a4, a2; lbu t0, 0(t0); bltu a7, t0: not taken (value <= 0x37) *)
        step. step. step. ccvu_br.
        (* addi a2, a2, 3; bne a1, a2 *)
        step. step.
        let KK := fresh "KK" in
        if_cases KK; zify_cond KK.
        * assert (NE : rest <> []) by (intro E; subst rest; cbn in HK; lia).
          apply (IH (K + 3)); [exact HT | exact HV | lia | lia | exact NE].
        * (* ret *)
          step. finish.
      + rewrite (proj2 (Z.eqb_neq p 2) Ep) in Hv.
        (* not taken: addi a7, zero, 1; j 0x14964 *)
        ccvu_br. step. step.
        (* add t0, a4, a2; lbu t0, 0(t0); bltu a7, t0: not taken (value <= 1) *)
        step. step. step. ccvu_br.
        (* addi a2, a2, 3; bne a1, a2 *)
        step. step.
        let KK := fresh "KK" in
        if_cases KK; zify_cond KK.
        * assert (NE : rest <> []) by (intro E; subst rest; cbn in HK; lia).
          apply (IH (K + 3)); [exact HT | exact HV | lia | lia | exact NE].
        * (* ret *)
          step. finish.
  Qed.
End Loop.

Theorem check_cells_valid_holds : check_cells_valid_contract.
Proof.
  unfold check_cells_valid_contract, CHECK_CELLS_VALID.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m rc cs HA1 HRC HPRE.
  subst a1.
  pose proof (ccvu_s64 rc ltac:(lia)) as Hs.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  destruct (Z_lt_le_dec 0 rc) as [Hpos | Hneg].
  - destruct (HPRE Hpos) as (HB & HL & HV). clear HPRE.
    (* blez a1: not taken *)
    step. ccvu_br.
    (* mv a2, zero; not a3, a0; slli a6, a1, 1; addi a4, a0, 2; addi a5, zero, 0x2f; add a1, a6, a1;
       addi a6, zero, 2 *)
    step. step. step. step. step. step. step.
    eapply ccvu_loop with (rc := rc) (rest := cs) (K := 0).
    + (* a1 = 3 rc *)
      rewrite ?(unsigned_lit rc) by lia. rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?Z.pow_1_r.
      rewrite unsigned_lit by lia. lia.
    + (* a3 = ~out *)
      rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia.
    + lia.
    + rewrite Z.add_0_r. exact HB.
    + exact HV.
    + lia.
    + lia.
    + intros E. subst cs. cbn in HL. lia.
  - clear HPRE.
    (* blez a1: taken to 0x14978; ret *)
    step. ccvu_br.
    step. finish.
Qed.
