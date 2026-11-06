(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd.U_resize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt.U_span_index_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt.
Import ListNotations.

Module U_resize.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_bigadd.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd.U_resize_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (vec v : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len n : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 <= len <= 62)%Z.
  Hypothesis Hn : (len < n <= 62)%Z.

  Notation A := (bv_unsigned vec).
  Notation POST := (resize_post ra sp gp tp t0 t1 t2 s0 s1 vec (Z_to_bv 64 n) v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ws len n m0).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (j : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat (n - j) = k)%nat -> (len <= j < n)%Z ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      fill_from cur (Z.to_nat j) (Z.to_nat (n - j)) v = fill_from ws (Z.to_nat len) (Z.to_nat (n - len)) v ->
      munch (resize_W A) m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 vec (Z_to_bv 64 n) v (Z_to_bv 64 (A + 8 * j)) (Z_to_bv 64 (n - j + 1))
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 1) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x278e8) fc None m (seg_rom USEGS)).

  #[using="Hlen LEN Hn"] Lemma fill_loop : forall k, loop_ok k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold loop_ok; intros j cur m Hk Hj CUR Hcur LC FILL MU WM.
    { exfalso. lia. }
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
    cbv delta [resize_W] in MU.
    pose proof (u64arr_store_ok USEGS m A cur j (Z_to_bv 64 (A + 8 * j)) CUR ltac:(lia) eq_refl) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur j v CUR ltac:(lia)) as CUR'.
    store_done.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z.to_nat (n - j)) with (S (Z.to_nat (n - (j + 1)))) in FILL by lia.
    cbn [fill_from] in FILL. replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) in FILL by lia.
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb. rewrite ?signed_lit in Hb by lia.
      replace (A + 8 * j + 8)%Z with (A + 8 * (j + 1))%Z by lia.
      replace (Z_to_bv 64 (n - j)) with (Z_to_bv 64 (n - (j + 1) + 1)) by (f_equal; lia).
      eapply (IH (j + 1)%Z); try eassumption; try lia.
      rewrite upd_length. exact Hcur.
    - (* [comment removed for export] *)
      cond_cleanup Hb. rewrite ?signed_lit in Hb by lia.
      assert (Hjn : (j + 1 = n)%Z) by lia.
      replace (Z.to_nat (n - (j + 1))) with 0%nat in FILL by lia. cbn [fill_from] in FILL.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      unfold resize_post. unfold resize_ws.
      replace (n <=? len)%Z with false by (symmetry; apply Z.leb_gt; lia). rewrite <- FILL.
      finish.
  Qed.
End Loop.

Lemma resize_spec : resize_stmt.
Proof.
  unfold resize_stmt. intros until n. intros LIMBS Hlen LC LEN Ha1 Hn.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
  pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
  pose proof (munch_refl (resize_W (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  cbv delta [resize_W] in MU.
  subst a1.
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  if_cases Hge.
  { (* [comment removed for export] *)
    cond_cleanup Hge.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold resize_post, resize_ws.
    replace (n <=? len)%Z with true by (symmetry; apply Z.leb_le; lia).
    finish. }
  cond_cleanup Hge.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit len) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit len), (unsigned_lit n) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit (n - len)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  replace ((n - len) * 2 ^ 3)%Z with (8 * (n - len))%Z by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  if_cases Hle. { cond_cleanup Hle. rewrite ?signed_lit in Hle by lia. exfalso. lia. }
  clear Hle.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  eapply (fill_loop ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a2 F fc m ws len n
            Hlen LEN ltac:(lia) (Z.to_nat (n - len)) len); try eassumption; try lia.
  reflexivity.
Qed.
End U_resize.

Module U_span_index.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt.U_span_index_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma span_index_spec : span_index_stmt.
Proof.
  unfold span_index_stmt. intros until i. intros RD Ha1 Hi Pnz Pal Pnw.
  pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
  subst a1.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit i) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  setcmp. decide_ltb.
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  rewrite unsigned_lit by lia. rewrite land7_aligned by lia.
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  unfold span_index_post. replace (i * 8)%Z with (8 * i)%Z by lia.
  finish. all: first [apply munch_refl | apply wmono_refl | exact I].
Qed.
End U_span_index.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

(* [comment removed for export] *)
Lemma land_negmask : forall x, (0 <= x < 64)%Z ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltiu (Z_to_bv 64 x) 64)))) (bv_unsigned (Z_to_bv 64 x)))
  = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite v_sltiu_b2z. rewrite (unsigned_lit x) by lia. change (bv_wrap 64 64) with 64%Z.
  replace (x <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit_wrap. change ((0 - 1) mod 2 ^ 64)%Z with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ripple_count : forall N idx, (0 <= idx <= N)%Z -> (N < 2^64)%Z ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 N) (Z_to_bv 64 (N - idx))) + -1)))
                     (bv_unsigned (Z_to_bv 64 (N - idx))))
  = Z_to_bv 64 (N - idx).
Proof.
  intros N idx Hi HN. rewrite v_sltu_b2z. rewrite (unsigned_lit N) by lia. rewrite !(unsigned_lit (N - idx)) by lia.
  replace (N <? N - idx)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  rewrite (unsigned_lit 0) by lia. change (0 + -1)%Z with (-1)%Z.
  rewrite unsigned_lit_wrap. change ((-1) mod 2 ^ 64)%Z with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis resize_spec : resize_stmt.
  Hypothesis span_index_spec : span_index_stmt.
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10 s11 : word).
  Variables (xv yv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws ys : list word) (len ylen start : Z) (nl ny ns : nat).
  Hypothesis Hnl : len = Z.of_nat nl.
  Hypothesis Hny : ylen = Z.of_nat ny.
  Hypothesis Hns : start = Z.of_nat ns.
  Hypothesis Hxl : length ws = 62%nat.
  Hypothesis Hyl : length ys = 62%nat.
  Hypothesis XLEN : (0 <= len <= 62)%Z.
  Hypothesis YLEN : (0 <= ylen <= 62)%Z.
  Hypothesis START : (0 <= start)%Z.
  Hypothesis FIT : (ylen + start <= 62)%Z.
  Hypothesis XAL : (bv_unsigned xv mod 8 = 0)%Z.
  Hypothesis YAL : (bv_unsigned yv mod 8 = 0)%Z.
  Hypothesis YNZ : (bv_unsigned yv <> 0)%Z.
  Hypothesis YEND : (bv_unsigned yv + 496 < 2^64)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis CAP : boxed (bval ws nl + bval ys ny * 2 ^ (64 * start) < BIG_CAP)%Z.
  Hypothesis SEP1 : (bv_unsigned xv + 498 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned xv)%Z.
  Hypothesis SEP2 : (bv_unsigned yv + 496 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned yv)%Z.
  Hypothesis SEP3 : (bv_unsigned xv + 498 <= bv_unsigned yv \/ bv_unsigned yv + 496 <= bv_unsigned xv)%Z.

  Notation X := (bv_unsigned xv).
  Notation Y := (bv_unsigned yv).
  Notation SP := (bv_unsigned sp).
  Notation W := [((SP - 112)%Z, SP); (X, (X + 498)%Z)].
  Notation POST := (large_add_from_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10 s11 F fc X Y ylen start ws ys len m0).
  Notation FRAME jk m := (rw_cells USEGS m (SP + -112)
     [CB 8 jk; C8 yv; C8 (Z_to_bv 64 ylen); C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NOTX := (Z_to_bv 64 (Z.lxor X 18446744073709551615)).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 xv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 yv) as RB; unfold bv_modulus in RB;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp.

  (* [comment removed for export] *)
  Definition epi_ok : Prop :=
    forall (jk : list byte) (rar t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r s5r s6r s7r s8r s9r t3 t4 t5 t6 : word)
           (m : word -> option byte) (ws' : list word) (len' : Z),
      FRAME jk m -> stk USEGS m (SP + -112) (SP + -112) ->
      u64arr USEGS m X ws' -> length ws' = 62%nat ->
      rw_cells USEGS m (X + 496) [C2 (Z_to_bv 64 len')] ->
      u64arr USEGS m Y ys ->
      munch W m0 m -> wmono USEGS m0 m ->
      (Z.max len (ylen + start) <= len' <= Z.max len (ylen + start) + 1 /\ len' <= 62)%Z ->
      boxed (bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) + bval ys (Z.to_nat ylen) * 2 ^ (64 * start)))%Z ->
      evt USEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 xv (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
                 s2r s3r s4r s5r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27670) fc None m (seg_rom USEGS)).

  Lemma epilogue : epi_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    unfold epi_ok. intros until len'. intros FR ST XL Hxl' XC YL MU WM HB HV. bounds.
    do 13 step.
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold large_add_from_post. finish.
    { exact XL. } { exact Hxl'. } { exact XC. } all: try lia. exact HV.
  Qed.

  Section RS.
  Variables (N : Z) (nN : nat) (x0 : list word).
  Hypothesis HnN : N = Z.of_nat nN.
  Hypothesis HN : N = Z.max len (ylen + start).
  Hypothesis Hx0l : length x0 = 62%nat.
  Hypothesis HX0 : boxed (bval x0 nN = bval ws nl).

  (* [comment removed for export] *)
  Definition rip_ok (k : nat) : Prop :=
    forall (j : nat) (jk : list byte) (rar t0 t1 t2 a4 a5 a6 a7 s3r s5r s7r s8r s9r t3 t4 t5 t6 : word) (cur : list word) (m : word -> option byte),
      (nN - j = k)%nat -> (ny + ns <= j <= nN)%nat ->
      FRAME jk m -> stk USEGS m (SP + -112) (SP + -112) ->
      u64arr USEGS m X cur -> length cur = 62%nat -> rw_cells USEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr USEGS m Y ys ->
      boxed (rip_inv x0 cur ys ns ny j) ->
      munch W m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 xv (Z_to_bv 64 1)
                 (Z_to_bv 64 N) (Z_to_bv 64 (Z.of_nat j - 64)) (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 (N - Z.of_nat j)) a4 a5 a6 a7
                 (Z_to_bv 64 start) s3r NOTX s5r (Z_to_bv 64 (63 - start)) s7r s8r s9r s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27614) fc None m (seg_rom USEGS)).

  Lemma rip_loop : epi_ok -> forall k, rip_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI. induction k as [|k IH]; unfold rip_ok;
      intros j jk rar t0 t1 t2 a4 a5 a6 a7 s3r s5r s7r s8r s9r t3 t4 t5 t6 cur m Hk Hj FR ST XL Hcur XC YL RI MU WM; bounds.
    - (* [comment removed for export] *)
      assert (HjN : j = nN) by lia. subst j. rewrite <- HnN.
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
      assert (ROOM : (N <= 61)%Z).
      { pose proof (rip_room x0 cur ys _ _ _ RI) as R. unfold boxed in HX0, CAP. rewrite HX0, <- Hns in R. specialize (R CAP). lia. }
      replace (N - N)%Z with 0%Z by lia.
      step. (* [comment removed for export] *)
      if_true.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit N) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (N * 2 ^ 3)%Z with (8 * N)%Z by lia.
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok USEGS m X cur N (Z_to_bv 64 (X + 8 * N)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)).
      pose proof (u64arr_write USEGS m X cur N (Z_to_bv 64 1) XL ltac:(lia)) as XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply EPI; try eassumption.
      + rewrite upd_length. exact Hcur.
      + lia.
      + unfold boxed in *. replace (Z.to_nat (N + 1)) with (S nN) by lia. replace (Z.to_nat N) with nN by lia.
        rewrite (rip_inv_push x0 cur ys _ _ _ RI) by (rewrite ?Hx0l, ?Hcur; lia).
        rewrite HX0, <- Hns. rewrite Hnl, Hny, !Nat2Z.id. reflexivity.
    - destruct (Nat.eq_dec j nN) as [->|Hne].
      { eapply (IH nN jk rar); try eassumption; lia. }
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz.
      { exfalso. first [ lia | revert Hz; replace (Z.of_nat j - 64 + 1)%Z with ((Z.of_nat j - 63 + 2^64) + (-1) * 2^64)%Z by lia;
        change 18446744073709551616%Z with (2^64)%Z; rewrite Z.mod_add, Z.mod_small by lia; lia ]. }
      clear Hz.
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ x0 j = bv_unsigned w).
      { unfold boxed in RI. destruct RI as (_ & RIag & _). unfold limbZ. rewrite <- (RIag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read USEGS m X cur (Z.of_nat j) w (Z_to_bv 64 (X + 8 * Z.of_nat j)) XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok USEGS m X cur (Z.of_nat j) (Z_to_bv 64 (X + 8 * Z.of_nat j)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write USEGS m X cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + 1)) XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc.
      + (* [comment removed for export] *)
        assert (Hwr : (bv_unsigned w + 1 = 2^64)%Z).
        { destruct (Z.eq_dec (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          first [ rewrite Z.mod_small in Hc by lia; lia | lia ]. }
        clear Hc.
        replace (Z.of_nat j - 64 + 1)%Z with (Z.of_nat (S j) - 64)%Z by lia.
        replace (8 * Z.of_nat j + 8)%Z with (8 * Z.of_nat (S j))%Z by lia.
        replace (Z_to_bv 64 (N - Z.of_nat j + -1)) with (Z_to_bv 64 (N - Z.of_nat (S j))) by (f_equal; lia).
        eapply (IH (S j) jk rar); try eassumption; try lia.
        { rewrite upd_length. exact Hcur. }
        unfold boxed in RI |- *. rewrite <- Hlimb. apply rip_inv_wrap; [exact RI | rewrite Hx0l; lia | lia].
      + (* [comment removed for export] *)
        assert (Hnw : (bv_unsigned w + 1 < 2^64)%Z).
        { destruct (Z.lt_ge_cases (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          change 18446744073709551616%Z with (2^64)%Z in Hc.
          rewrite <- (Z.mod_unique_pos (bv_unsigned w + 1) (2^64) 1 (bv_unsigned w + 1 - 2^64)) in Hc by lia. lia. }
        clear Hc.
        step. (* [comment removed for export] *)
        eapply EPI; try eassumption.
        * rewrite upd_length. exact Hcur.
        * lia.
        * unfold boxed in RI, HX0 |- *. rewrite <- Hlimb. replace (Z.to_nat N) with nN by lia.
          rewrite (rip_inv_stop x0 cur ys _ _ _ nN RI) by (rewrite ?Hx0l; lia).
          rewrite HX0, <- Hns. rewrite Hnl, Hny, !Nat2Z.id. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition tail_ok (k : nat) : Prop :=
    forall (i : nat) (jk : list byte) (rar t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s8r s9r t3 t4 t5 t6 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (ny - S i = k)%nat -> (S i <= ny)%nat ->
      FRAME jk m -> stk USEGS m (SP + -112) (SP + -112) ->
      u64arr USEGS m X cur -> length cur = 62%nat -> rw_cells USEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr USEGS m Y ys ->
      boxed (ladd_inv x0 cur ys ns (S i) c) ->
      munch W m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 xv (Z_to_bv 64 1)
                 a0 (Z_to_bv 64 ylen) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 start) (Z_to_bv 64 (Z.of_nat i)) NOTX (Z_to_bv 64 c) (Z_to_bv 64 (63 - start))
                 (Z_to_bv 64 (8 * (start + Z.of_nat i))) s8r s9r s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x275d0) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition add_ok (k : nat) : Prop :=
    forall (i : nat) (jk : list byte) (rar t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8r s9r t3 t4 t5 t6 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (ny - i = k)%nat -> (i < ny)%nat ->
      FRAME jk m -> stk USEGS m (SP + -112) (SP + -112) ->
      u64arr USEGS m X cur -> length cur = 62%nat -> rw_cells USEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr USEGS m Y ys ->
      boxed (ladd_inv x0 cur ys ns i c) ->
      munch W m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 xv (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 start) (Z_to_bv 64 (Z.of_nat i)) NOTX (Z_to_bv 64 c) (Z_to_bv 64 (63 - start))
                 (Z_to_bv 64 (8 * (start + Z.of_nat i))) s8r s9r s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27580) fc None m (seg_rom USEGS)).

  Lemma add_tail : epi_ok -> (forall k, rip_ok k) -> forall k, add_ok k -> tail_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI RIP k IH. unfold tail_ok.
    intros i jk rar t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s8r s9r t3 t4 t5 t6 c cur m Hk Hi FR ST XL Hcur XC YL LI MU WM; bounds.
    assert (LIc : c = 0%Z \/ c = 1%Z) by (unfold boxed in LI; destruct LI as (_ & _ & _ & Hc); exact Hc).
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - (* [comment removed for export] *)
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
      replace (8 * (start + Z.of_nat i) + 8)%Z with (8 * (start + Z.of_nat (S i)))%Z by lia.
      eapply (IH (S i) jk rar); try eassumption; try lia.
    - (* [comment removed for export] *)
      assert (Hn : S i = ny) by lia. clear Hb.
      step. (* [comment removed for export] *)
      destruct LIc as [Hc0 | Hc1]; subst c.
      + (* [comment removed for export] *)
        if_true.
        eapply EPI; try eassumption; try lia.
        unfold boxed in LI, HX0 |- *.
        pose proof (ladd_finish x0 cur ys _ _ _ nN LI ltac:(lia)) as HV.
        rewrite Hn, HX0, <- Hns in HV. rewrite Hnl, Hny, !Nat2Z.id.
        replace (Z.to_nat N) with nN by lia. lia.
      + (* [comment removed for export] *)
        if_false.
        step. (* [comment removed for export] *)
        rewrite zx16_lit by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit (ylen + start)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit N), (unsigned_lit (ylen + start)) by lia.
        rewrite (ripple_count N (ylen + start)) by lia.
        replace (Z_to_bv 64 ((ylen + start) * 2 ^ 3)) with (Z_to_bv 64 (8 * Z.of_nat (ny + ns))) by (f_equal; lia).
        replace (Z_to_bv 64 (N - (ylen + start))) with (Z_to_bv 64 (N - Z.of_nat (ny + ns))) by (f_equal; lia).
        replace (Z_to_bv 64 (18446744073709551552 + (ylen + start))) with (Z_to_bv 64 (Z.of_nat (ny + ns) - 64)).
        2:{ apply Z_to_bv_eqm.
            replace (18446744073709551552 + (ylen + start))%Z with ((Z.of_nat (ny + ns) - 64) + 1 * 2^64)%Z by lia.
            rewrite Z.mod_add by lia. reflexivity. }
        eapply (RIP (nN - (ny + ns))%nat (ny + ns)%nat jk rar); try eassumption; try lia.
        unfold boxed in LI |- *. replace (ny + ns)%nat with (ns + ny)%nat by lia.
        apply rip_inv_start. rewrite <- Hn. exact LI.
  Qed.

  Lemma add_loop : epi_ok -> (forall k, rip_ok k) -> forall k, add_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI RIP. induction k as [|k IH]; unfold add_ok;
      intros i jk rar t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8r s9r t3 t4 t5 t6 c cur m Hk Hi FR ST XL Hcur XC YL LI MU WM; bounds.
    { exfalso; lia. }
    pose proof (add_tail EPI RIP k IH) as TAIL.
    assert (LIc : c = 0%Z \/ c = 1%Z) by (unfold boxed in LI; destruct LI as (_ & _ & _ & Hc); exact Hc).
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    pose proof (rw_cells_bound _ _ _ _ FR) as BFR. cbn [cells_size csize Nat.add] in BFR.
    destruct (nth_error cur (ns + i)) as [wx|] eqn:Hnx. 2:{ exfalso. apply nth_error_None in Hnx. lia. }
    assert (Hwx : nth (ns + i) cur w0 = wx) by (apply nth_error_nth; exact Hnx).
    destruct (nth_error ys i) as [wy|] eqn:Hny'. 2:{ exfalso. apply nth_error_None in Hny'. lia. }
    assert (Hwy : nth i ys w0 = wy) by (apply nth_error_nth; exact Hny').
    pose proof (bv_unsigned_in_range 64 wx) as Rwx. unfold bv_modulus in Rwx.
    pose proof (bv_unsigned_in_range 64 wy) as Rwy. unfold bv_modulus in Rwy.
    assert (Ex : limbZ x0 (ns + i) = bv_unsigned wx).
    { unfold boxed in LI. destruct LI as (_ & LIag & _). unfold limbZ. rewrite <- (LIag (ns + i)%nat) by lia. rewrite Hwx. reflexivity. }
    assert (Ey : limbZ ys i = bv_unsigned wy) by (unfold limbZ; rewrite Hwy; reflexivity).
    assert (LI2 : forall cc, cc = c ->
              boxed (ladd_inv x0 (upd cur (ns + i) (Z_to_bv 64 (bv_unsigned wx + bv_unsigned wy + cc))) ys ns (S i)
                       (if bv_unsigned wx + bv_unsigned wy + cc <? 2 ^ 64 then 0 else 1)%Z)).
    { intros cc ->. unfold boxed in LI |- *. rewrite <- Ex, <- Ey. apply (ladd_inv_step x0 cur ys ns i c LI). rewrite Hx0l. lia. }
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    pose proof (u64arr_read USEGS m X cur (Z.of_nat (ns + i)) wx (Z_to_bv 64 (X + 8 * (start + Z.of_nat i))) XL
                  ltac:(rewrite Nat2Z.id; exact Hnx) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (rw_cells_read_at USEGS m (SP + -112) _ 8%nat (C8 yv) 8 (Z_to_bv 64 (SP + -104)) FR
                  ltac:(cells_cbv; reflexivity) eq_refl ltac:(unfold wa; f_equal; lia)) as RDY.
    cbn [cbytes] in RDY.
    step. (* [comment removed for export] *)
    call (span_index_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yv (Z.of_nat i)).
    { exact RDY. } { reflexivity. } { lia. } { exact YNZ. } { exact YAL. } { lia. }
    clear RDY.
    pose proof (u64arr_read USEGS m Y ys (Z.of_nat i) wy (Z_to_bv 64 (Y + 8 * Z.of_nat i)) YL
                  ltac:(rewrite Nat2Z.id; exact Hny') ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok USEGS m X cur (Z.of_nat (ns + i)) (Z_to_bv 64 (X + 8 * (start + Z.of_nat i))) XL
                  ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    destruct LIc as [Hc0 | Hc1]; subst c.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_false.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_write USEGS m X cur (Z.of_nat (ns + i)) (Z_to_bv 64 (bv_unsigned wx + bv_unsigned wy)) XL ltac:(lia)) as XL'.
      replace (wa (X + 8 * Z.of_nat (ns + i))) with (wa (X + 8 * (start + Z.of_nat i))) in XL' by (unfold wa; f_equal; lia).
      rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      rewrite (ladd_carry0 wx (bv_unsigned wy)) by lia.
      eapply TAIL; try eassumption; try lia.
      { rewrite upd_length. exact Hcur. }
      specialize (LI2 0%Z eq_refl). rewrite !Z.add_0_r in LI2. rewrite !Z.add_0_r. exact LI2.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_true.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_write USEGS m X cur (Z.of_nat (ns + i)) (Z_to_bv 64 (bv_unsigned wx + bv_unsigned wy + 1)) XL ltac:(lia)) as XL'.
      replace (wa (X + 8 * Z.of_nat (ns + i))) with (wa (X + 8 * (start + Z.of_nat i))) in XL' by (unfold wa; f_equal; lia).
      rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      rewrite (ladd_carry1 wx (bv_unsigned wy)) by lia.
      eapply TAIL; try eassumption; try lia.
      { rewrite upd_length. exact Hcur. }
      exact (LI2 1%Z eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma from_255a0 : epi_ok -> (forall k, add_ok k) ->
    forall (jk : list byte) (rar t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
      FRAME jk m -> stk USEGS m (SP + -112) (SP + -112) ->
      u64arr USEGS m X x0 -> rw_cells USEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr USEGS m Y ys ->
      munch W m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 xv s1i a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 start) (Z_to_bv 64 ylen) s4i s5i s6i s7i s8i s9i s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27554) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI ADD. intros until m. intros FR ST XL XC YL MU WM; bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hx0l in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - (* [comment removed for export] *)
      eapply EPI; try eassumption; try lia.
      unfold boxed in HX0 |- *. replace (Z.to_nat N) with nN by lia. rewrite HX0, Hnl, Hny, !Nat2Z.id.
      replace ny with 0%nat by lia. cbn [bval]. lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit start) by lia. rewrite (land_negmask (63 - start)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit start) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      replace (Z_to_bv 64 (start * 2 ^ 3)) with (Z_to_bv 64 (8 * (start + Z.of_nat 0))) by (f_equal; lia).
      change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat 0)) at 1.
      eapply (ADD ny 0%nat jk rar); try eassumption; try lia.
      unfold boxed. apply ladd_inv_init.
  Qed.
  End RS.

  (* [comment removed for export] *)
  Lemma from_25588 : epi_ok ->
    forall (jk : list byte) (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
      (len < ylen + start)%Z ->
      FRAME jk m -> stk USEGS m (SP + -112) (SP + -112) ->
      u64arr USEGS m X ws -> rw_cells USEGS m (X + 496) [C2 (Z_to_bv 64 len)] -> u64arr USEGS m Y ys ->
      munch W m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR ra (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 xv s1i a0 yv (Z_to_bv 64 ylen) a3 a4 a5 a6 a7
                 (Z_to_bv 64 start) (Z_to_bv 64 ylen) s4i s5i s6i s7i s8i s9i s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2753c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI. intros until m. intros HLT FR ST XL XC YL MU WM; bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hxl in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (resize_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ws len (ylen + start)%Z).
    { exact XL. } { exact Hxl. } { exact XC. } { lia. } { reflexivity. } { lia. }
    lazymatch goal with H : u64arr USEGS ?m' X (resize_ws ws len (ylen + start) (Z_to_bv 64 0)) |- _ => rename H into XL' end.
    unfold resize_ws in XL'. replace (ylen + start <=? len)%Z with false in XL' by (symmetry; apply Z.leb_gt; lia).
    set (k := (ny + ns - nl)%nat).
    rewrite (fill_from_zfill (Z.to_nat (ylen + start - len)) ws (Z.to_nat len)) in XL' by (rewrite Hxl; lia).
    replace (Z.to_nat len) with nl in XL' by lia. replace (Z.to_nat (ylen + start - len)) with k in XL' by lia.
    assert (Hx0l : length (zfill ws nl k (Z_to_bv 64 0)) = 62%nat) by (rewrite zfill_length; rewrite ?Hxl; lia).
    assert (HX0 : boxed (bval (zfill ws nl k (Z_to_bv 64 0)) (ny + ns)%nat = bval ws nl)).
    { unfold boxed. replace (ny + ns)%nat with (nl + k)%nat by lia. apply bval_zfill0. rewrite Hxl; lia. }
    assert (HnN : (ylen + start)%Z = Z.of_nat (ny + ns)) by lia.
    assert (HN : (ylen + start)%Z = Z.max len (ylen + start)) by lia.
    pose proof (rip_loop (ylen + start)%Z (ny + ns)%nat _ HnN HN Hx0l HX0 EPI) as RIP.
    pose proof (add_loop (ylen + start)%Z (ny + ns)%nat _ HnN HN Hx0l HX0 EPI RIP) as ADD.
    eapply (from_255a0 (ylen + start)%Z (ny + ns)%nat _ HnN HN Hx0l HX0 EPI ADD); eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma body_ok : epi_ok ->
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      stk USEGS m0 (SP - 112) SP ->
      u64arr USEGS m0 X ws -> rw_cells USEGS m0 (X + 496) [C2 (Z_to_bv 64 len)] -> u64arr USEGS m0 Y ys ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i xv yv (Z_to_bv 64 ylen) (Z_to_bv 64 start) a4 a5 a6 a7
                 s2i s3i s4i s5i s6i s7i s8i s9i s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x274e8) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI. intros until t6. intros ST XL XC YL. bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hxl in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl USEGS m0) as WM.
    carve_frame 112%nat ST.
    do 12 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite zx16_lit by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H1; cond_cleanup H1.
    2: { (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H2; cond_cleanup H2.
      { (* [comment removed for export] *)
        assert (HX0 : boxed (bval ws nl = bval ws nl)) by (unfold boxed; reflexivity).
        assert (HN : len = Z.max len (ylen + start)) by lia.
        pose proof (rip_loop len nl ws Hnl HN Hxl HX0 EPI) as RIP.
        pose proof (add_loop len nl ws Hnl HN Hxl HX0 EPI RIP) as ADD.
        eapply (from_255a0 len nl ws Hnl HN Hxl HX0 EPI ADD); eassumption. }
      eapply (from_25588 EPI); try eassumption. lia. }
    eapply (from_25588 EPI); try eassumption. lia.
  Qed.
End Proof.

Section Top.
  Hypothesis resize_spec : resize_stmt.
  Hypothesis span_index_spec : span_index_stmt.

  Lemma large_add_from_spec : large_add_from_stmt.
  Proof.
    unfold large_add_from_stmt. intros until start.
    intros ST ALIGN XL Hxl XC XLEN XAL YL Hyl Ha2 YLEN YAL YNZ YEND Ha3 START FIT CAP SEP1 SEP2 SEP3.
    subst a2 a3.
    eapply (body_ok resize_spec span_index_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m ws ys len ylen start
              (Z.to_nat len) (Z.to_nat ylen) (Z.to_nat start)); try eassumption; try lia.
    all: try exact CAP.
    eapply (epilogue resize_spec span_index_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m ws ys len ylen start
              (Z.to_nat len) (Z.to_nat ylen) (Z.to_nat start)); try eassumption; try lia.
    all: try exact CAP.
  Qed.
End Top.
