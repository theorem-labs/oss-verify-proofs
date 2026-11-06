(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].

Definition fromch_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A off stop lo : Z) (txt : list byte) (b : byte),
  mem_inv segs m -> frm0 fc ->
  stk segs m lo (bv_unsigned sp) -> (lo + FF_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z ->
  (0 <= off <= stop)%Z -> nth_error txt (Z.to_nat stop) = Some b -> numchar (bv_unsigned b) = false ->
  evt segs (ff_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition FROMCH_ENTRY : Z := 0x28d00.
Definition FROMCH_GTOP : Z := 0xab000.
Definition fc_ff_stmt : Prop := ff_stmt_g psegs 0x28d4c FROMCH_GTOP.

Section FROMCH.
  Hypothesis HFF : fc_ff_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (A off stop lo : Z) (txt : list byte) (b : byte).
  Hypothesis MI : mem_inv psegs m.
  Hypothesis FRM : frm0 fc.
  Hypothesis ST : stk psegs m lo (bv_unsigned sp).
  Hypothesis ROOM : (lo + FF_STACK <= bv_unsigned sp)%Z.
  Hypothesis GTOP : (FROMCH_GTOP <= lo)%Z.
  Hypothesis TXT : bytes_at psegs m A txt.
  Hypothesis TLO : (A + Z.of_nat (length txt) <= lo)%Z.
  Hypothesis TMAX : (Z.of_nat (length txt) < NUM_TXT_MAX)%Z.
  Hypothesis HOFF : (0 <= off <= stop)%Z.
  Hypothesis HSTOP : nth_error txt (Z.to_nat stop) = Some b.
  Hypothesis HNC : numchar (bv_unsigned b) = false.

  Notation fc_post := (ff_post_g psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m).

  Notation FCS pc xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 (A + off)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).

  Lemma fc_stop_lt : (stop < Z.of_nat (length txt))%Z.
  Proof using HSTOP HOFF.
    assert (X : nth_error txt (Z.to_nat stop) <> None) by (rewrite HSTOP; discriminate). apply nth_error_Some in X. lia.
  Qed.

  Lemma fc_end : forall (e : Z) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (off <= e <= stop)%Z ->
    evt psegs fc_post (FCS 0x28d48 xt0 xt1 xt2 (Z_to_bv 64 (A + e)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using HFF MI FRM ST ROOM GTOP TXT TLO TMAX HOFF HSTOP.
    intros until xt6. intros He.
    pose proof fc_stop_lt as SL.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    zstep.
    pose proof HFF as HS. unfold fc_ff_stmt, ff_stmt_g in HS.
    eapply evt_eq; [| eapply HS with (A := A) (FIRST := (A + off)%Z) (LAST := (A + e)%Z) (lo := lo) (txt := txt)];
      [ num_st_eq | .. ]; unfold FROMCH_GTOP in *;
      [ exact MI | exact FRM | exact ST | exact ROOM | exact GTOP | exact TXT | exact TLO | exact TMAX | lia | lia ].
  Qed.

  Lemma fc_iter : forall (cur : Z) xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (off <= cur <= stop)%Z ->
    (forall xa5' xa6', (cur + 1 <= stop)%Z ->
       evt psegs fc_post (FCS 0x28d28 xt0 xt1 xt2 (Z_to_bv 64 (A + (cur + 1))) (Z_to_bv 64 10) (Z_to_bv 64 58) (Z_to_bv 64 NUMMASK) xa5' xa6' xa7 xt3 xt4 xt5 xt6)) ->
    evt psegs fc_post (FCS 0x28d28 xt0 xt1 xt2 (Z_to_bv 64 (A + cur)) (Z_to_bv 64 10) (Z_to_bv 64 58) (Z_to_bv 64 NUMMASK) xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using HFF MI FRM ST ROOM GTOP TXT TLO TMAX HOFF HSTOP HNC.
    intros until xt6. intros Hc K.
    pose proof fc_stop_lt as SL.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    unfold NUMMASK in *. unfold NUM_TXT_MAX in *.
    zstep.
    replace (A + cur - A)%Z with cur by lia.
    set (c := nth (Z.to_nat cur) txt (Z_to_bv 8 0)).
    assert (CR : (0 <= bv_unsigned c < 256)%Z) by (pose proof (bv_unsigned_in_range 8 c) as R; unfold bv_modulus in R; cbn in R; lia).
    assert (CS : cur = stop -> numchar (bv_unsigned c) = false).
    { intros ->. unfold c. rewrite (nth_error_nth _ _ _ HSTOP). exact HNC. }
    clearbody c.
    zstep. zstep. if_cases K0; zify_cond K0.
    { assert (NC : numchar (bv_unsigned c) = true).
      { unfold numchar. rewrite (proj2 (Z.leb_le 48 (bv_unsigned c))), (proj2 (Z.leb_le (bv_unsigned c) 57)) by lia. reflexivity. }
      assert (cur <> stop) by (intros X; specialize (CS X); congruence).
      zstep. eapply evt_eq; [| eapply K]; [num_st_eq | lia]. }
    zstep. zstep. if_cases K1; zify_cond K1.
    { eapply evt_eq; [| eapply (fc_end cur)]; [num_st_eq | lia]. }
    zstep. zstep. zstep.
    assert (K43 : (43 <= bv_unsigned c <= 101)%Z) by lia.
    replace ((bv_unsigned c + -43) mod 64)%Z with (bv_unsigned c - 43)%Z by (rewrite Z.mod_small; lia).
    assert (ND : ~ (48 <= bv_unsigned c <= 57)%Z) by lia.
    pose proof (numchar_mask (bv_unsigned c) CR ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
    destruct (numchar (bv_unsigned c)) eqn:NC.
    - assert (cur <> stop) by (intros X; specialize (CS X); congruence).
      change (negb (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0))) with true. cbv iota.
      zstep. eapply evt_eq; [| eapply K]; [num_st_eq | lia].
    - change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
      eapply evt_eq; [| eapply (fc_end cur)]; [num_st_eq | lia].
  Qed.

  Lemma fc_scan : forall (f : nat) (cur : Z) xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (off <= cur <= stop)%Z -> (stop - cur <= Z.of_nat f)%Z ->
    evt psegs fc_post (FCS 0x28d28 xt0 xt1 xt2 (Z_to_bv 64 (A + cur)) (Z_to_bv 64 10) (Z_to_bv 64 58) (Z_to_bv 64 NUMMASK) xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using HFF MI FRM ST ROOM GTOP TXT TLO TMAX HOFF HSTOP HNC.
    intros f. induction f as [|f IH]; intros until xt6; intros Hc Hf; eapply fc_iter; try eassumption; intros xa5' xa6' Hn.
    - exfalso; lia.
    - eapply IH; lia.
  Qed.

  Lemma fc_body : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt psegs fc_post (FCS FROMCH_ENTRY t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof using HFF MI FRM ST ROOM GTOP TXT TLO TMAX HOFF HSTOP HNC.
    intros. unfold FROMCH_ENTRY.
    do 9 zstep.
    eapply evt_eq; [| eapply (fc_scan (Z.to_nat stop) off)]; [unfold NUMMASK; num_st_eq | lia | lia].
  Qed.
End FROMCH.

Theorem fromch_spec : fc_ff_stmt -> fromch_stmt_g psegs FROMCH_ENTRY FROMCH_GTOP.
Proof.
  intros HS. unfold fromch_stmt_g. intros until b. intros MI FRM ST ROOM GTOP TXT TLO TMAX HOFF HSTOP HNC.
  exact (fc_body HS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A off stop lo txt b MI FRM ST ROOM GTOP TXT TLO TMAX HOFF HSTOP HNC
           t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Qed.
