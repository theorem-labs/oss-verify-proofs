(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Sj_num_iface Sj_num_kitu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].

Definition fromchu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A off stop lo : Z) (txt : list byte) (b : byte),
  mem_inv segs m -> frm0 fc ->
  stk segs m lo (bv_unsigned sp) -> (lo + FFU_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z -> (0 < A)%Z ->
  (0 <= off <= stop)%Z -> nth_error txt (Z.to_nat stop) = Some b -> numchar (bv_unsigned b) = false ->
  evt segs (ffu_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition FROMCHU_ENTRY : Z := 0x2a094.
Definition fcu_ff_stmt : Prop := ffu_stmt_g usegs 0x2a0fc NUMU_GTOP.

Section FROMCHU.
  Hypothesis HFF : fcu_ff_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (A off stop lo : Z) (txt : list byte) (b : byte).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis FRM : frm0 fc.
  Hypothesis ST : stk usegs m lo (bv_unsigned sp).
  Hypothesis ROOM : (lo + FFU_STACK <= bv_unsigned sp)%Z.
  Hypothesis GTOP : (NUMU_GTOP <= lo)%Z.
  Hypothesis SP16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis TXT : bytes_at usegs m A txt.
  Hypothesis TLO : (A + Z.of_nat (length txt) <= lo)%Z.
  Hypothesis TMAX : (Z.of_nat (length txt) < NUM_TXT_MAX)%Z.
  Hypothesis A0 : (0 < A)%Z.
  Hypothesis HOFF : (0 <= off <= stop)%Z.
  Hypothesis HSTOP : nth_error txt (Z.to_nat stop) = Some b.
  Hypothesis HNC : numchar (bv_unsigned b) = false.

  Notation fc_post := (ffu_post_g usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m).

  Notation SC pc e xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 (A + off)) (Z_to_bv 64 (A + e)) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615)
             (Z_to_bv 64 58) (Z_to_bv 64 NUMMASK) xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma fu_stop_lt : (stop < Z.of_nat (length txt))%Z.
  Proof using HSTOP HOFF.
    clear - HSTOP HOFF.
    assert (X : nth_error txt (Z.to_nat stop) <> None) by (rewrite HSTOP; discriminate). apply nth_error_Some in X. lia.
  Qed.

  Lemma fu_end : forall (e : Z) xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6,
    (off <= e <= stop)%Z ->
    evt usegs fc_post (SC 0x2a0f4 e xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using HFF MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HOFF HSTOP.
    intros until xt6. intros He.
    pose proof fu_stop_lt as SL.
    zstep.
    pose proof HFF as HS. unfold fcu_ff_stmt, ffu_stmt_g in HS.
    eapply evt_eq; [| eapply HS with (A := A) (FIRST := (A + off)%Z) (LAST := (A + e)%Z) (lo := lo) (txt := txt)];
      [ num_st_eq | .. ];
      [ exact MI | exact FRM | exact ST | exact ROOM | exact GTOP | exact SP16 | exact TXT | exact TLO | exact TMAX | exact A0 | lia | lia ].
  Qed.

  Lemma fu_test : forall (e c : Z) xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6,
    (off <= e <= stop)%Z -> (0 <= c < 256)%Z -> ~ (48 <= c <= 57)%Z -> (e = stop -> numchar c = false) ->
    (forall xa6' xa7', (e < stop)%Z -> evt usegs fc_post (SC 0x2a0dc e xt0 xt1 xt2 xa6' xa7' xt3 xt4 xt5 xt6)) ->
    evt usegs fc_post (SC 0x2a0c8 e xt0 xt1 xt2 (Z_to_bv 64 c) xa7 xt3 xt4 xt5 xt6).
  Proof using HFF MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HOFF HSTOP.
    intros until xt6. intros He Hc ND CS K. unfold NUMMASK in *.
    zstep. zstep. if_cases K1; zify_cond K1.
    { eapply evt_eq; [| eapply (fu_end e)]; [unfold NUMMASK; num_st_eq | lia]. }
    zstep. zstep. zstep.
    assert (K43 : (43 <= c <= 101)%Z) by lia.
    replace ((c + -43) mod 64)%Z with (c - 43)%Z by (rewrite Z.mod_small; lia).
    pose proof (numchar_mask c Hc ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
    destruct (numchar c) eqn:NC.
    - assert (e <> stop) by (intros X; specialize (CS X); congruence).
      change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false. cbv iota.
      eapply evt_eq; [| eapply K]; [num_st_eq | lia].
    - change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
      eapply evt_eq; [| eapply (fu_end e)]; [unfold NUMMASK; num_st_eq | lia].
  Qed.

  Lemma fu_byte : forall e, (0 <= e)%Z ->
    let c := bv_unsigned (nth (Z.to_nat e) txt (Z_to_bv 8 0)) in
    (0 <= c < 256)%Z /\ (e = stop -> numchar c = false).
  Proof using HSTOP HNC.
    clear - HSTOP HNC.
    intros e He c. split.
    - pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat e) txt (Z_to_bv 8 0))) as R. unfold bv_modulus in R. cbn in R. unfold c. lia.
    - intros ->. unfold c. rewrite (nth_error_nth _ _ _ HSTOP). exact HNC.
  Qed.

  Lemma fu_numchar_digit : forall c, (48 <= c <= 57)%Z -> numchar c = true.
  Proof. intros c H. unfold numchar. rewrite (proj2 (Z.leb_le 48 c)), (proj2 (Z.leb_le c 57)) by lia. reflexivity. Qed.

  Lemma fu_iter : forall (cur : Z) xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6,
    (off <= cur < stop)%Z ->
    (forall xa6' xa7', (cur + 1 < stop)%Z -> evt usegs fc_post (SC 0x2a0dc (cur + 1) xt0 xt1 xt2 xa6' xa7' xt3 xt4 xt5 xt6)) ->
    evt usegs fc_post (SC 0x2a0dc cur xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using HFF MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HOFF HSTOP HNC.
    intros until xt6. intros Hc K.
    pose proof fu_stop_lt as SL.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR.
    unfold NUM_TXT_MAX, FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in *.
    zstep. if_cases KM; zify_cond KM; [exfalso; lia|].
    zstep. zstep.
    replace (A + cur + 1 - A)%Z with (cur + 1)%Z by lia.
    destruct (fu_byte (cur + 1)%Z ltac:(lia)) as [CR CS].
    set (c := bv_unsigned (nth (Z.to_nat (cur + 1)) txt (Z_to_bv 8 0))) in *. clearbody c.
    zstep. zstep. if_cases K0; zify_cond K0.
    - eapply evt_eq; [| eapply (fu_test (cur + 1)%Z c)]; [num_st_eq | lia | lia | lia | exact CS |].
      intros. eapply evt_eq; [| eapply K]; [num_st_eq | lia].
    - assert (NC : numchar c = true) by (apply fu_numchar_digit; lia).
      assert (cur + 1 <> stop)%Z by (intros X; specialize (CS X); congruence).
      zstep. eapply evt_eq; [| eapply K]; [num_st_eq | lia].
  Qed.

  Lemma fu_scan : forall (f : nat) (cur : Z) xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6,
    (off <= cur < stop)%Z -> (stop - cur <= Z.of_nat f)%Z ->
    evt usegs fc_post (SC 0x2a0dc cur xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using HFF MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HOFF HSTOP HNC.
    intros f. induction f as [|f IH]; intros until xt6; intros Hc Hf; [exfalso; lia|].
    eapply fu_iter; [lia |]. intros xa6' xa7' Hn.
    eapply IH; lia.
  Qed.

  Lemma fu_body : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt usegs fc_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FROMCHU_ENTRY) fc None m (seg_rom usegs)).
  Proof using HFF MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HOFF HSTOP HNC.
    intros. unfold FROMCHU_ENTRY.
    pose proof fu_stop_lt as SL.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR.
    unfold NUM_TXT_MAX, FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in *.
    zstep. if_cases KN; zify_cond KN; [exfalso; lia|].
    do 9 zstep.
    zstep.
    replace (A + off - A)%Z with off by lia.
    destruct (fu_byte off ltac:(lia)) as [CR CS].
    set (c := bv_unsigned (nth (Z.to_nat off) txt (Z_to_bv 8 0))) in *. clearbody c.
    zstep. zstep. if_cases K0; zify_cond K0.
    -
      assert (NC : numchar c = true) by (apply fu_numchar_digit; lia).
      assert (off <> stop)%Z by (intros X; specialize (CS X); congruence).
      eapply evt_eq; [| eapply (fu_scan (Z.to_nat stop) off)]; [unfold NUMMASK; num_st_eq | lia | lia].
    - eapply evt_eq; [| eapply (fu_test off c)]; [unfold NUMMASK; num_st_eq | lia | lia | lia | exact CS |].
      intros. eapply evt_eq; [| eapply (fu_scan (Z.to_nat stop) off)]; [unfold NUMMASK; num_st_eq | lia | lia].
  Qed.
End FROMCHU.

Theorem fromchu_spec : fcu_ff_stmt -> fromchu_stmt_g usegs FROMCHU_ENTRY NUMU_GTOP.
Proof.
  intros HS. unfold fromchu_stmt_g. intros until b. intros MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HOFF HSTOP HNC.
  exact (fu_body HS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A off stop lo txt b MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HOFF HSTOP HNC
           t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Qed.
