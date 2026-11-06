(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): the digit loop of the inline
   m_split (fuzz_segconf.c:329-334), 0x13db0 .. 0x13dd0 (plain binary):
     0x13db0 addi a3,a2,-0x3a ; 0x13db4 bltu a3,s11 -> 0x13d74 (s11 = -10: a2 is not a digit) ;
     0x13db8 mul s5,s5,a4 (a4 = 10) ; 0x13dbc andi a2,a2,0xf ; 0x13dc0 add s5,s5,a2 ;
     0x13dc4 bltu s8,s5 -> 0x13d74 (s8 = 4094) ; 0x13dc8 lbu a2,0(a1) ; 0x13dcc addi a1,a1,1 ;
     0x13dd0 bnez a2 -> 0x13db0 ; falls to 0x13dd4.
   - v01d_turn: one turn from 0x13db0 with the character q in a2 and the byte b at a1: the digit test
     (a2 - 58 <u 2^64 - 10 exactly when a2 is not in 48 .. 57, V01DigPure.vd_dig_ltu), a2 & 15 = a2 - 48 for a digit
     (vd_dig_land), the bound vid * 10 + (a2 - 48) <= 4094, then b: 0 exits at 0x13dd4, else back to 0x13db0.
   - v01_dig (V01_Inv.v01_dig_stmt): by induction on rest (the characters after q, then the NUL), each exit matching
     SegModel.m_digits (V01DigPure.vd_m_digits_cons).
   V01DigPure holds the lemmas that name no address of the plain image and no register.
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import V01_Inv.
Import ListNotations.
Open Scope Z_scope.

Module V01DigPure.

(* ---- The model ---- *)
(* One step of SegModel.m_digits: the character test and the bound in one boolean. *)
Lemma vd_m_digits_cons : forall q r vid, m_digits (q :: r) vid =
  if (q <? 48) || (57 <? q) || (4094 <? vid * 10 + (q - 48)) then None else m_digits r (vid * 10 + (q - 48)).
Proof. intros q r vid. cbn [m_digits]. destruct ((q <? 48) || (57 <? q)); reflexivity. Qed.

Lemma vd_bad_digit : forall q v, q < 48 \/ 57 < q -> (q <? 48) || (57 <? q) || (4094 <? v) = true.
Proof.
  intros q v H. apply orb_true_iff. left. apply orb_true_iff.
  destruct H as [H|H]; [left | right]; apply Z.ltb_lt; exact H.
Qed.

Lemma vd_bad_over : forall q v, 4094 < v -> (q <? 48) || (57 <? q) || (4094 <? v) = true.
Proof. intros q v H. apply orb_true_iff. right. apply Z.ltb_lt. exact H. Qed.

Lemma vd_good : forall q v, 48 <= q <= 57 -> v <= 4094 -> (q <? 48) || (57 <? q) || (4094 <? v) = false.
Proof.
  intros q v Hq Hv. apply orb_false_iff. split; [apply orb_false_iff; split|]; apply Z.ltb_ge; lia.
Qed.

Lemma vd_good_inv : forall q v, (q <? 48) || (57 <? q) || (4094 <? v) = false -> 48 <= q <= 57 /\ v <= 4094.
Proof.
  intros q v H. apply orb_false_iff in H. destruct H as [H H3]. apply orb_false_iff in H. destruct H as [H1 H2].
  apply Z.ltb_ge in H1. apply Z.ltb_ge in H2. apply Z.ltb_ge in H3. lia.
Qed.

Lemma vd_dig_bad_b : forall q, q < 48 \/ 57 < q -> (q <? 48) || (57 <? q) = true.
Proof.
  intros q H. apply orb_true_iff. destruct H as [H|H]; [left | right]; apply Z.ltb_lt; exact H.
Qed.

Lemma vd_dig_good_b : forall q, 48 <= q <= 57 -> (q <? 48) || (57 <? q) = false.
Proof. intros q H. apply orb_false_iff. split; apply Z.ltb_ge; lia. Qed.

(* ---- The arithmetic of the code ---- *)
Lemma vd_mod_neg : forall x, - 2 ^ 64 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof.
  intros x Hx.
  replace (x mod 2 ^ 64) with ((x + 2 ^ 64 + -1 * 2 ^ 64) mod 2 ^ 64) by (f_equal; lia).
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* The digit test of 0x13db0 / 0x13db4 on a character 0 <= q < 256: (q - 58) mod 2^64 <u 2^64 - 10 exactly when q is
   not in '0' .. '9'. *)
Lemma vd_dig_test : forall q, 0 <= q < 256 ->
  ((q + -58) mod 2 ^ 64 <? 2 ^ 64 - 10) = (q <? 48) || (57 <? q).
Proof.
  intros q Hq. destruct (Z_lt_le_dec q 58) as [Hl|Hl].
  - rewrite (vd_mod_neg (q + -58)) by lia.
    destruct (Z.ltb_spec (q + -58 + 2 ^ 64) (2 ^ 64 - 10)) as [H|H];
      destruct (Z.ltb_spec q 48) as [H1|H1]; destruct (Z.ltb_spec 57 q) as [H2|H2]; cbn [orb];
      first [reflexivity | exfalso; lia].
  - rewrite (Z.mod_small (q + -58) (2 ^ 64)) by lia.
    destruct (Z.ltb_spec (q + -58) (2 ^ 64 - 10)) as [H|H];
      destruct (Z.ltb_spec q 48) as [H1|H1]; destruct (Z.ltb_spec 57 q) as [H2|H2]; cbn [orb];
      first [reflexivity | exfalso; lia].
Qed.

Lemma vd_dig_ltu : forall q, 0 <= q < 256 ->
  bv_ltu (Z_to_bv 64 (q + -58)) (Z_to_bv 64 (-10)) = (q <? 48) || (57 <? q).
Proof.
  intros q Hq. rewrite bv_ltu_Z, !unsigned_lit_wrap.
  replace ((-10) mod 2 ^ 64) with (2 ^ 64 - 10) by reflexivity.
  apply vd_dig_test. exact Hq.
Qed.

(* bltu on two values in range. *)
Lemma vd_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. rewrite bv_ltu_Z, !unsigned_lit by lia. reflexivity. Qed.

(* 0x13dbc `andi a2,a2,0xf` on a digit. *)
Lemma vd_dig_land : forall q, 48 <= q <= 57 -> Z.land q 15 = q - 48.
Proof.
  intros q Hq.
  assert (E : q = 48 \/ q = 49 \/ q = 50 \/ q = 51 \/ q = 52 \/ q = 53 \/ q = 54 \/ q = 55 \/ q = 56 \/ q = 57)
    by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; subst q; reflexivity.
Qed.

(* ---- Bytes ---- *)
Lemma vd_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma vd_byte_nz : forall b : byte, b <> ZERO -> bv_unsigned b <> 0.
Proof. intros b H E. apply H. apply bv_eq. rewrite E. reflexivity. Qed.

(* The first byte of b :: bs at a, read as one byte (the `lbu`). *)
Lemma vd_rd1 : forall segs m a b bs, bytes_at segs m a (b :: bs) -> ov_read_bytes segs m (wa a) 1 = Some [b].
Proof.
  intros segs m a b bs H.
  replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read segs m a (b :: bs) 0 1 H) by (cbn; lia).
  reflexivity.
Qed.

Lemma vd_tl : forall segs m a b bs, bytes_at segs m a (b :: bs) -> bytes_at segs m (a + 1) bs.
Proof.
  intros segs m a b bs H. apply (bytes_at_app segs m a [b] bs) in H. destruct H as [_ H]. exact H.
Qed.

End V01DigPure.

(* ---- Branches ---- *)
(* A branch condition the context refutes, in any shape zify_cond takes. *)
Ltac v01d_close K :=
  zify_cond K;
  repeat (rewrite unsigned_lit in K by lia);
  rewrite ?unsigned_lit_wrap in K;
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
  lia.
(* The branch is taken (v01d_tk) or not (v01d_nt); a condition already reduced to true / false needs no proof. *)
Ltac v01d_tk :=
  cbv iota;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; cbv iota; [clear K | exfalso; v01d_close K]
  | _ => idtac
  end.
Ltac v01d_nt :=
  cbv iota;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; cbv iota; [exfalso; v01d_close K | clear K]
  | _ => idtac
  end.

(* ---- One turn: 0x13db0 with the character q in a2 and the byte b at a1 = ptr ---- *)
Lemma v01d_turn : forall (Q : machine_state -> Prop) (m : word -> option byte) (q vid ptr : Z) (b : byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32),
  0 < q < 256 -> 0 <= vid <= 4094 -> 0 <= ptr ->
  ov_read_bytes rsegs m (wa ptr) 1 = Some [b] ->
  ((q <? 48) || (57 <? q) || (4094 <? vid * 10 + (q - 48)) = true -> forall a1' a2' a3' s5' : word,
     evt rsegs Q (vst 0x13d74 ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' (Z_to_bv 64 10) a5 a6 a7 s2 s3 s4 s5' s6 s7
                    (Z_to_bv 64 4094) s9 s10 (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m)) ->
  ((q <? 48) || (57 <? q) || (4094 <? vid * 10 + (q - 48)) = false -> bv_unsigned b = 0 ->
   forall a1' a2' a3' : word,
     evt rsegs Q (vst 0x13dd4 ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' (Z_to_bv 64 10) a5 a6 a7 s2 s3 s4
                    (Z_to_bv 64 (vid * 10 + (q - 48))) s6 s7 (Z_to_bv 64 4094) s9 s10 (Z_to_bv 64 (-10))
                    t3 t4 t5 t6 F fc m)) ->
  ((q <? 48) || (57 <? q) || (4094 <? vid * 10 + (q - 48)) = false -> bv_unsigned b <> 0 ->
   forall a3' : word,
     evt rsegs Q (vst 0x13db0 ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (ptr + 1)) (Z_to_bv 64 (bv_unsigned b)) a3'
                    (Z_to_bv 64 10) a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (vid * 10 + (q - 48))) s6 s7 (Z_to_bv 64 4094)
                    s9 s10 (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m)) ->
  evt rsegs Q (vst 0x13db0 ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 ptr) (Z_to_bv 64 q) a3 (Z_to_bv 64 10) a5 a6
                 a7 s2 s3 s4 (Z_to_bv 64 vid) s6 s7 (Z_to_bv 64 4094) s9 s10 (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m).
Proof.
  intros Q m q vid ptr b ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 F fc
    Hq Hv Hp HR HJ HZ HC.
  pose proof (V01DigPure.vd_byte_rng b) as Rb.
  unfold vst.
  (* 0x13db0 addi a3,a2,-0x3a ; 0x13db4 bltu a3,s11 -> 0x13d74: the digit test *)
  zstep. zstep.
  try rewrite (V01DigPure.vd_dig_ltu q) by lia.
  assert (DQ : (q < 48 \/ 57 < q) \/ 48 <= q <= 57) by lia.
  destruct DQ as [P|P].
  - (* not a digit: m_digits refuses *)
    try rewrite (V01DigPure.vd_dig_bad_b q P).
    v01d_tk.
    eapply HJ. apply V01DigPure.vd_bad_digit. exact P.
  - try rewrite (V01DigPure.vd_dig_good_b q P).
    v01d_nt.
    (* 0x13db8 mul s5,s5,a4 ; 0x13dbc andi a2,a2,0xf (a2 & 15 = a2 - 48) *)
    zstep. zstep.
    rewrite (V01DigPure.vd_dig_land q P).
    (* 0x13dc0 add s5,s5,a2 ; 0x13dc4 bltu s8,s5 -> 0x13d74: the bound 4094 *)
    zstep. zstep.
    try rewrite (V01DigPure.vd_ltu 4094 (vid * 10 + (q - 48))) by lia.
    destruct (Z_lt_le_dec 4094 (vid * 10 + (q - 48))) as [O|O].
    + try rewrite (proj2 (Z.ltb_lt _ _) O).
      v01d_tk.
      eapply HJ. apply V01DigPure.vd_bad_over. exact O.
    + try rewrite (proj2 (Z.ltb_ge _ _) O).
      v01d_nt.
      (* 0x13dc8 lbu a2,0(a1) ; 0x13dcc addi a1,a1,1 ; 0x13dd0 bnez a2 -> 0x13db0 *)
      zstep. zstep. zstep.
      destruct (Z.eq_dec (bv_unsigned b) 0) as [B0|B0].
      * v01d_nt.
        eapply HZ; [apply V01DigPure.vd_good; [exact P | exact O] | exact B0].
      * v01d_tk.
        eapply HC; [apply V01DigPure.vd_good; [exact P | exact O] | exact B0].
Qed.

(* ---- The loop ---- *)
Lemma v01_dig : v01_dig_stmt.
Proof.
  unfold v01_dig_stmt. intros Q m rest.
  induction rest as [|r rest IH];
    intros q vid ptr ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 F fc
      Hq Hv Hp HB HN HJ HK; cbn [app] in HB.
  - (* the NUL at ptr: q is the last character; 0x13dd4 *)
    apply (v01d_turn Q m q vid ptr ZERO ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6
             F fc Hq Hv Hp (V01DigPure.vd_rd1 rsegs m ptr ZERO [] HB)).
    + intros E a1' a2' a3' s5'. apply HJ. rewrite V01DigPure.vd_m_digits_cons, E. reflexivity.
    + intros E _ a1' a2' a3'. apply HK. rewrite V01DigPure.vd_m_digits_cons, E. reflexivity.
    + intros _ E. exfalso. apply E. reflexivity.
  - (* the character r follows q: the next turn *)
    pose proof (V01DigPure.vd_byte_rng r) as Rr.
    assert (Hr : bv_unsigned r <> 0).
    { apply V01DigPure.vd_byte_nz. intros Er. apply HN. cbn [In]. left. exact Er. }
    apply (v01d_turn Q m q vid ptr r ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6
             F fc Hq Hv Hp (V01DigPure.vd_rd1 rsegs m ptr r (rest ++ [ZERO]) HB)).
    + intros E a1' a2' a3' s5'. apply HJ. rewrite V01DigPure.vd_m_digits_cons, E. reflexivity.
    + intros _ E. exfalso. exact (Hr E).
    + intros E _ a3'.
      destruct (V01DigPure.vd_good_inv q (vid * 10 + (q - 48)) E) as [Pq Pv].
      apply IH.
      * lia.
      * lia.
      * lia.
      * exact (V01DigPure.vd_tl rsegs m ptr r (rest ++ [ZERO]) HB).
      * intros Hin. apply HN. cbn [In]. right. exact Hin.
      * intros N a1' a2' a3'' s5'. apply HJ. rewrite V01DigPure.vd_m_digits_cons, E. exact N.
      * intros v N a1' a2' a3''. apply HK. rewrite V01DigPure.vd_m_digits_cons, E. exact N.
Qed.
