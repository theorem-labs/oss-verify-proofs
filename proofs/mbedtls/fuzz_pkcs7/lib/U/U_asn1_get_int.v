(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_asn1_get_tag U_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_ASN1_GET_INT : Z := 0x1e6d0.

(* [comment removed for export] *)
Notation ASN1_GET_INT_STACK := 32 (only parsing).

Definition asn1_get_int_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP VALP P END lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r p' : Z) (v : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_INT_STACK, bv_unsigned sp)] m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ a0 = Z_to_bv 64 r /\ (-0x7f < r <= 0)
    /\ rw_cells segs m' PP [C8 (Z_to_bv 64 p')]
    /\ rw_cells segs m' VALP [C4 v]
    /\ stk segs m' lo (bv_unsigned sp)
    /\ P <= p' <= END
    /\ (r = 0 -> P + 3 <= p').

Definition asn1_get_int_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP VALP P END BUF lo : Z) (bs : list byte) (valv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m VALP [C4 valv] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= VALP \/ VALP + 4 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP) ->
  (* [comment removed for export] *)
  PP mod 8 = 0 -> VALP mod 4 = 0 -> 0 < PP -> 0 < VALP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_INT_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (VALP + 4 <= lo \/ bv_unsigned sp <= VALP) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 VALP ->
  evt segs (asn1_get_int_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).


Lemma ro_byte_of_bytes : forall segs m BUF bs a,
  bytes_at segs m BUF bs -> BUF <= a -> a < BUF + Z.of_nat (length bs) ->
  ro_cells segs m a [C1 (nth (Z.to_nat (a - BUF)) bs (Z_to_bv 8 0))].
Proof.
  intros segs m BUF bs a [H0 [H1 H]] Ha1 Ha2.
  split; [cbn; tauto|].
  cbn [cells_bytes cbytes app].
  assert (Hi : (Z.to_nat (a - BUF) < length bs)%nat) by lia.
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by lia. subst k. cbn [nth_error].
  replace (a + Z.of_nat 0) with (BUF + Z.of_nat (Z.to_nat (a - BUF))) by lia.
  rewrite H by exact Hi. apply nth_error_nth'. exact Hi.
Qed.

Local Ltac len_post :=
  repeat match goal with H : ?x = Z_to_bv 64 _ |- _ => is_var x; subst x end;
  match goal with HR : ?r = 0 -> _, HB : -127 < ?r <= 0 |- _ =>
    let a := fresh "HR" in let b := fresh "HR" in let rn := fresh "RN" in
    destruct (Z.eq_dec r 0) as [R0|R0];
    [ subst r; specialize (HR eq_refl); destruct HR as [a b]
    | assert (rn : r <= -1) by lia; clear HR R0 ] end.
Local Ltac bvu_ranges :=
  repeat match goal with
  | H : context [bv_unsigned ?w] |- _ => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 w) end
  | |- context [bv_unsigned ?w] => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 w) end
  end.
Local Ltac call_len spec ppv bufv bsv lenp csp :=
  lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  lazymatch goal with H : rw_cells _ _ ppv [C8 (Z_to_bv 64 ?p)] |- _ =>
    let SP := fresh "SP" in
    pose proof spec as SP; unfold asn1_get_len_stmt, U_ASN1_GET_LEN in SP;
    callx_sp csp
      (eapply SP with (PP := ppv) (LENP := lenp) (P := p) (END := e) (BUF := bufv) (bs := bsv);
       rewrite ?(unsigned_lit csp) by plia; try eassumption; try reflexivity; try plia; try (bvu_ranges; plia));
    clear SP
  end end;
  len_post.
Local Ltac weq := first [ reflexivity | f_equal; lia | rewrite ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned ].
Local Ltac run_i := lxp_run (PLAN [0x1e4e4; 0x1e760; 0x1e7d8; 0x1e84c] [] 300%N).
Local Ltac run_l := lxp_run (PLAN [0x1e760; 0x1e7d8; 0x1e84c] [] 200%N).
Section Walk.
  Context {L : heap_layout}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP VALP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= VALP \/ VALP + 4 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis VALB : 0 <= VALP /\ VALP + 4 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : VALP mod 4 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < VALP.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - ASN1_GET_INT_STACK.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : VALP + 4 <= lo \/ bv_unsigned sp <= VALP.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  Notation W := [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_INT_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_int_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m).

  Lemma valB_lor : forall v b, 0 <= v -> 0 <= b < 256 -> Z.lor (256 * v) b = 256 * v + b.
  Proof.
    intros v b Hv Hb.
    assert (E : Z.shiftl v 8 = 256 * v) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
    rewrite <- E. rewrite lor_shl8_byte by lia. rewrite E. lia.
  Qed.

  Local Ltac valB_dead :=
    exfalso;
    lazymatch goal with K : (if _ =? _ then false else true) = true |- _ =>
      repeat (match type of K with context [Z.lor (256 * ?v) ?w] =>
        lazymatch v with context [Z.lor _ _] => fail | _ => rewrite (valB_lor v w) in K by lia end end);
      unfold zlow in K; rewrite ?Z.shiftr_div_pow2 in K by lia;
      change (2 ^ 32) with 4294967296 in K; change (2 ^ 23) with 8388608 in K;
      change (2 ^ 64) with 18446744073709551616 in K;
      lazymatch type of K with (if ?a =? ?b then _ else _) = _ =>
        destruct (Z.eqb_spec a b) as [E|E]; [discriminate K|]; apply E; clear K E end;
      lazymatch goal with |- ((?V mod 4294967296) / 8388608) mod _ = _ =>
        rewrite (Z.mod_small V 4294967296) by lia; rewrite (Z.div_small V 8388608) by lia; reflexivity end
    end.

  Lemma valB_entry : forall (cur rem : Z) (valw x1 x5 x6 x7 x10 x13 x14 x15 x17 x28 x29 x30 x31 : word) (mm : mem),
    0 <= rem <= 4 -> P + 2 <= cur -> cur + rem <= END -> P + 3 <= cur + rem ->
    (rem = 4 -> bv_unsigned (nth (Z.to_nat (cur - BUF)) bs (Z_to_bv 8 0)) < 128) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 cur)] -> rw_cells usegs mm VALP [C4 valw] ->
    rw_cells usegs mm (bv_unsigned sp + -32) [C8 (Z_to_bv 64 rem)] ->
    rw_cells usegs mm (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra] ->
    bytes_at usegs mm BUF bs -> stk usegs mm lo (bv_unsigned sp + -32) ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 PP) (Z_to_bv 64 VALP)
              x10 (Z_to_bv 64 VALP) (Z_to_bv 64 cur) x13 x14 x15 (Z_to_bv 64 rem) x17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1e7d8) fc None mm (seg_rom usegs)).
  Proof.
  intros cur rem valw x1 x5 x6 x7 x10 x13 x14 x15 x17 x28 x29 x30 x31 mm Hrem Hc HE HP3 H128 HPP HVAL HSL HSV HBUF ST MU WM MI.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (R : rem = 0 \/ rem = 1 \/ rem = 2 \/ rem = 3 \/ rem = 4) by lia.
  destruct R as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ].
  5: (specialize (H128 eq_refl);
      pose proof (ro_byte_of_bytes usegs mm BUF bs cur HBUF ltac:(lia) ltac:(lia)) as RB;
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (cur - BUF)) bs (Z_to_bv 8 0))) as CR; unfold bv_modulus in CR; cbn in CR;
      rewrite <- (@stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 (nth (Z.to_nat (cur - BUF)) bs (Z_to_bv 8 0))) in RB;
      remember (bv_unsigned (nth (Z.to_nat (cur - BUF)) bs (Z_to_bv 8 0))) as c eqn:Ec).
  all: lxp_run (PLAN [0x1e84c] [] 300%N).
  all: try lxp_ret.
  all: lxp_at 0x1e84c; valB_dead.
  Qed.

  Lemma loopA_walk : forall (k : nat) (p1 len i : Z) (a3w a4w a5w a7w slw valw x1 x5 x6 x7 x12 x28 x29 x30 x31 : word) (mm : mem),
    Z.to_nat (len - i) = k -> 0 <= i < len -> P + 2 <= p1 -> p1 + len <= END ->
    a3w = Z_to_bv 64 len -> a4w = Z_to_bv 64 p1 -> a5w = Z_to_bv 64 i -> a7w = Z_to_bv 64 (-1 - i) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 (p1 + i))] -> rw_cells usegs mm VALP [C4 valw] ->
    rw_cells usegs mm (bv_unsigned sp + -32) [C8 slw] -> bv_unsigned slw = len - i ->
    rw_cells usegs mm (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra] ->
    bytes_at usegs mm BUF bs -> stk usegs mm lo (bv_unsigned sp + -32) ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 PP) (Z_to_bv 64 VALP)
              (Z_to_bv 64 (-100)) (Z_to_bv 64 VALP) x12 a3w a4w a5w
              (Z_to_bv 64 (-1)) a7w s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1e760) fc None mm (seg_rom usegs)).
  Proof.
  induction k as [|k IH]; intros p1 len i a3w a4w a5w a7w slw valw x1 x5 x6 x7 x12 x28 x29 x30 x31 mm Hk Hi Hp1 HE -> -> -> -> HPP HVAL HSL HSLv HSV HBUF ST MU WM MI; [lia|].
  pose proof (ro_byte_of_bytes usegs mm BUF bs (p1 + i) HBUF ltac:(lia) ltac:(lia)) as RB.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (p1 + i - BUF)) bs (Z_to_bv 8 0))) as CR. unfold bv_modulus in CR. cbn in CR.
  rewrite <- (@stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 (nth (Z.to_nat (p1 + i - BUF)) bs (Z_to_bv 8 0))) in RB.
  remember (bv_unsigned (nth (Z.to_nat (p1 + i - BUF)) bs (Z_to_bv 8 0))) as c eqn:Ec.
  pose proof (bv_unsigned_in_range 64 slw) as SLR. unfold bv_modulus in SLR. cbn in SLR.
  replace slw with (Z_to_bv 64 (len - i)) in HSL by (rewrite <- HSLv; apply Z_to_bv_bv_unsigned). clear HSLv.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  run_l.
  all: try lxp_ret.
  all: try (lxp_at 124768; eapply (IH p1 len (i + 1)); try weq; lxp_apply_post).
  all: try (lxp_at 124888; eapply valB_entry; lxp_apply_post).
  all: try (intros _; rewrite <- Ec; unfold zswrap in *; lia).
  Qed.
End Walk.

Lemma U_asn1_get_int_spec {L : heap_layout} : asn1_get_int_stmt usegs U_ASN1_GET_INT.
Proof.
  unfold asn1_get_int_stmt, U_ASN1_GET_INT.
  intros until valv.
  intros HPP HVAL HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof (munch_refl [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_INT_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HVAL) as VALB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, VALB.
  pose proof (proj1 HBUF) as BUF0.
  pose proof (@alloc_ceiling_pos L) as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  pose proof (proj1 ST) as LO0.
  carve_frame 32%nat ST.
  lxp_split_frame [8;8;8;8]%nat.
  run_i.
  all: try lxp_ret.
  lxp_gc. try lxp_statics.
  lxp_cells FR.
  lxp_chunk_split FR 1%nat FL FR.
  call_len U_asn1_get_len_spec PP BUF bs (bv_unsigned sp + -32) (bv_unsigned sp + -32).
  all: run_i.
  all: try lxp_ret.
  all: try (lxp_at 124768;
    lazymatch goal with |- context [mkR _ _ _ _ _ _ _ _ _ _ _ _ ?a3 (Z_to_bv 64 ?q) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] =>
      eapply loopA_walk with (i := 0) (len := bv_unsigned a3) (p1 := q) (BUF := BUF) (bs := bs) (P := P) (END := END) (lo := lo) (m := m) end; try weq; lxp_apply_post).
Qed.
