(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 317 of its 350 lines of code are new or changed and 668 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/Prog/RcBraidLib.v, with its module paths, module names and numbers changed; 642 of its 674 lines of code are new or changed and 318 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/reac_braid_encode_exact.v, with its module paths, addresses and numbers changed; 220 of its 468 lines of code are new or changed and 426 lines of the source are left out. *)
(* reac_braid_encode of the fuzz_decode asan image (A), entry 0x818d4, frame 48 bytes:
   reac_braid_encode_exact_holds proves reac_braid_encode_exact_contract of crt_braid_need.v.

   A relocation of the fuzz_ctrl asan proof (proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_braid_encode_exact.v of
   a working branch, commit c1fcc4ce0f4, entry 0x86e3c). The entry point: the fuzz_ctrl proof image is the patched
   build (internal path, the binaries cb uses for fuzz_ctrl), where reac_braid_encode STARTS at 0x86e3c
   (its nm.txt: 0x86e3c, size 0x1fc). The released fuzz_ctrl build puts it at 0x86e0c, so the +0x30 is only the
   difference between the two fuzz_ctrl builds, not a skipped prologue. In fuzz_decode the function starts at 0x818d4
   (nm.txt: 0x818d4, size 0x1fc), and both statements enter at the first instruction (addi sp, sp, -48) with the
   same premises, so the donor run applies from the start. The two functions are 127 instructions, 118 words equal;
   the 9 others are pc-relative only: auipc/ld of the GOT cell of the shadow offset (GOT_CELL_K 0x9fa10 -> 0x98d40,
   holding CELL_K 0xa87b8 -> 0xa0db8), auipc/flw of the float 8388607.0 (0x21a98 -> 0x20dac, both 0x4afffffe), and
   the five jal to the report stubs (__asan_report_load8/store1/load4), which the run does not reach.
   Moved numerals (pc in the function, old - 0x5568): 0x86e70 -> 0x81908 (+0x34), 0x86ebc -> 0x81954 (+0x80);
   690104 (CELL_K of fuzz_ctrl, 0xa87b8) -> 0xa0db8 (CELL_K of fuzz_decode). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import RcAsanRT crt_braid_need.
Import ListNotations.
Open Scope Z_scope.

Definition rbe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns : Z) (K : Z -> Z -> Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get F' k = reg_get F k) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp); (a, a + 3 * N * ns)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp - 48) (bv_unsigned sp) /\
    (forall x : word, outside [(bv_unsigned sp - 48, bv_unsigned sp)] (bv_unsigned x) ->
       m' x = rb_enc m (rb_rows a N K (Z.to_nat ns)) x).

Ltac join r CONT :=
  lazymatch goal with
  | |- evt ?S ?Qp (MS ?R ?Fr (if _ then _ else ?J) ?fc' ?sv ?mm' ?rom) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    assert (CONT : forall y : word, evt S Qp (MS (tset p y R) Fr J fc' sv mm' rom))
  end.
Ltac join_use CONT :=
  lazymatch type of CONT with forall y : word, evt _ _ (MS (tset ?p _ _) _ _ _ _ _ _) =>
  lazymatch goal with |- evt _ _ (MS ?R0 _ _ _ _ _ _) =>
    let v := eval cbv beta iota delta [tget] in (match tget p R0 with Some v => v | None => w0 end) in
    exact (CONT v) end end.

Lemma rbe_chk0 : forall X (k : byte), bv_signed k <> 0 -> (bv_signed k = 0 \/ X mod 8 < bv_signed k) ->
  bv_lts (Z_to_bv 64 (X mod 8)) (Z_to_bv 64 (bv_signed k)) = true.
Proof.
  intros X k H0 H. pose proof (Z.mod_pos_bound X 8 ltac:(lia)). pose proof (rc_byte_signed k).
  rewrite rc_lts_signed by lia. apply Z.ltb_lt. destruct H as [H|H]; [contradiction | exact H].
Qed.

Lemma rbe_chk3 : forall X (k : byte), bv_signed k <> 0 -> (bv_signed k = 0 \/ X mod 8 + 3 < bv_signed k) ->
  bv_lts (Z_to_bv 64 (X mod 8 + 3)) (Z_to_bv 64 (bv_signed k)) = true.
Proof.
  intros X k H0 H. pose proof (Z.mod_pos_bound X 8 ltac:(lia)). pose proof (rc_byte_signed k).
  rewrite rc_lts_signed by lia. apply Z.ltb_lt. destruct H as [H|H]; [contradiction | exact H].
Qed.

Lemma rbe_eqb0b : forall k : byte, bv_eqb (Z_to_bv 64 (bv_signed k)) (Z_to_bv 64 0) = (bv_signed k =? 0).
Proof. intros k. pose proof (rc_byte_signed k). apply rc_eqb0_signed. lia. Qed.

Lemma rbe_swrap32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

(* The register equations at a loop entry, in a context cleared down to the bounds they need. *)
Ltac rbe_aweq :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [bv_swrap 32 ?z] => rewrite (rbe_swrap32 z) by lia
  end;
  rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.pow_1_r;
  first [ reflexivity | f_equal; lia | f_equal; nia ].

Section Run.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns off : Z) (Q : Z -> Z) (V K : Z -> Z -> Z).
  Hypothesis HN : 2 <= N <= 127.
  Hypothesis HNe : N mod 2 = 0.
  Hypothesis Hns : 1 <= ns <= 12.
  Hypothesis FRM : frm0 fc.
  Hypothesis Ha : 0 < a.
  Hypothesis HaE : a + 3 * N * ns <= 2^64.
  Hypothesis HP0 : 0 < P.
  Hypothesis HP8m : P mod 8 = 0.
  Hypothesis HP8 : P + 8 * N <= 2^64.
  Hypothesis HQ : forall ch, 0 <= ch < N -> 0 < Q ch /\ Q ch mod 4 = 0 /\ Q ch + 4 * ns <= 2^64.
  Hypothesis HV : forall s ch, 0 <= s < ns -> 0 <= ch < N ->
    bytes_at rsegs m (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch))) /\ rb_sample (V s ch) (K s ch).
  Hypothesis HD1 : a + 3 * N * ns <= P \/ P + 8 * N <= a.
  Hypothesis HD2 : forall ch, 0 <= ch < N -> a + 3 * N * ns <= Q ch \/ Q ch + 4 * ns <= a.
  Hypothesis HD3 : a + 3 * N * ns <= bv_unsigned sp + -48 \/ bv_unsigned sp <= a.
  Hypothesis Hsp : 48 <= bv_unsigned sp.
  Hypothesis Hoff : 0 <= off < 2^63.
  Hypothesis HSRa : asan_shadow_rd rsegs m off a (3 * N * ns)
    [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)].
  Hypothesis HADa : asan_addressable rsegs m off a (3 * N * ns).
  Hypothesis HSRP : asan_shadow_rd rsegs m off P (8 * N)
    [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)].
  Hypothesis HADP : asan_addressable rsegs m off P (8 * N).
  Hypothesis HR3P : asan_rt3 rsegs m off P (8 * N).
  Hypothesis HSRQ : forall ch, 0 <= ch < N -> asan_shadow_rd rsegs m off (Q ch) (4 * ns)
    [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)].
  Hypothesis HADQ : forall ch, 0 <= ch < N -> asan_addressable rsegs m off (Q ch) (4 * ns).

  Lemma shP : forall mm ch, munch [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)] m mm ->
    0 <= ch < N -> ov_read_bytes rsegs mm (wa ((P + 8 * ch) / 8 + off)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros mm ch HM Hch.
    pose proof (asan_shadow_rd_munch rsegs m mm off P (8 * N) _ _ HSRP HM (fun x Hx => Hx)) as HS.
    pose proof (asan_addressable_munch rsegs m mm off P (8 * N) _ _ HADP HSRP HM (fun x Hx => Hx)) as HA.
    pose proof (asan_rt3_munch rsegs m mm off P (8 * N) _ _ HR3P HSRP HM (fun x Hx => Hx)) as H3.
    destruct (asan_shadow_read rsegs mm off P (8 * N) _ (8 * ch) HS ltac:(lia)) as (k & RK & BK).
    assert (HM8 : (P + 8 * ch) mod 8 = 0).
    { replace (P + 8 * ch) with (P + ch * 8) by ring. rewrite Z_mod_plus_full. exact HP8m. }
    pose proof (asan_check_8 rsegs mm off P (8 * N) (8 * ch) k HA H3 ltac:(lia) ltac:(lia) HM8 BK) as K0.
    assert (E : k = Z_to_bv 8 0) by (apply bv_eq; rewrite (rc_signed0_unsigned0 k K0); reflexivity).
    subst k. exact RK.
  Qed.

  Lemma shQ : forall mm s ch, munch [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)] m mm ->
    0 <= s < ns -> 0 <= ch < N ->
    exists k : byte, ov_read_bytes rsegs mm (wa ((Q ch + 4 * s) / 8 + off)) 1 = Some [k] /\
      (bv_signed k = 0 \/ (Q ch + 4 * s) mod 8 + 3 < bv_signed k).
  Proof.
    intros mm s ch HM Hs Hch. destruct (HQ ch Hch) as (HQ0 & HQ4 & HQE).
    pose proof (asan_shadow_rd_munch rsegs m mm off (Q ch) (4 * ns) _ _ (HSRQ ch Hch) HM (fun x Hx => Hx)) as HS.
    pose proof (asan_addressable_munch rsegs m mm off (Q ch) (4 * ns) _ _ (HADQ ch Hch) (HSRQ ch Hch) HM
                  (fun x Hx => Hx)) as HA.
    destruct (asan_shadow_read rsegs mm off (Q ch) (4 * ns) _ (4 * s) HS ltac:(lia)) as (k & RK & BK).
    exists k. split; [exact RK|].
    assert (HW4 : (Q ch + 4 * s) mod 8 + 4 <= 8) by (clear - HQ4; Z.div_mod_to_equations; lia).
    exact (asan_check_lt rsegs mm off (Q ch) (4 * ns) (4 * s) 4 k HA ltac:(lia) ltac:(lia) ltac:(lia) HW4 BK).
  Qed.

  Lemma shA : forall mm X, munch [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)] m mm ->
    a <= X < a + 3 * N * ns ->
    exists k : byte, ov_read_bytes rsegs mm (wa (X / 8 + off)) 1 = Some [k] /\
      (bv_signed k = 0 \/ X mod 8 < bv_signed k).
  Proof.
    intros mm X HM HX.
    pose proof (asan_shadow_rd_munch rsegs m mm off a (3 * N * ns) _ _ HSRa HM (fun x Hx => Hx)) as HS.
    pose proof (asan_addressable_munch rsegs m mm off a (3 * N * ns) _ _ HADa HSRa HM (fun x Hx => Hx)) as HA.
    destruct (asan_shadow_read rsegs mm off a (3 * N * ns) _ (X - a) HS ltac:(lia)) as (k & RK & BK).
    replace (a + (X - a)) with X in RK, BK by lia.
    exists k. split; [exact RK|].
    pose proof (HA (X - a) k ltac:(lia)) as OK. replace (a + (X - a)) with X in OK by lia.
    exact (OK BK).
  Qed.

  Definition INV (mm : word -> option byte) (L : list (Z * byte)) : Prop :=
    (forall ch, 0 <= ch < N -> bytes_at rsegs mm (P + 8 * ch) (le8 (Z_to_bv 64 (Q ch)))) /\
    (forall s ch, 0 <= s < ns -> 0 <= ch < N -> bytes_at rsegs mm (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch)))) /\
    wr_at rsegs mm a (3 * N * ns) /\ mem_inv rsegs mm /\
    (forall x, outside [(bv_unsigned sp + -48, bv_unsigned sp)] (bv_unsigned x) -> mm x = rb_enc m L x) /\
    munch [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)] m mm /\ wmono rsegs m mm.

  Lemma INV_store : forall mm L X b, INV mm L -> a <= X < a + 3 * N * ns ->
    INV (write_to_mem mm (wa X) [b]) (L ++ [(X, b)]).
  Proof.
    intros mm L X b (I1 & I2 & I3 & I4 & I5 & I6 & I7) HX.
    assert (HL : X + Z.of_nat (length [b]) <= 2^64) by (cbn [length Z.of_nat]; lia).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros ch Hch. apply bytes_at_write_other; [apply I1; exact Hch | lia | exact HL |].
      rewrite length_le8. cbn [length Z.of_nat]. destruct HD1; lia.
    - intros s ch Hs Hch. apply bytes_at_write_other; [apply I2; assumption | lia | exact HL |].
      rewrite length_le4. cbn [length Z.of_nat]. destruct (HD2 ch Hch); lia.
    - apply wr_at_write. exact I3.
    - apply mem_inv_store; [exact I4|]. cbn [length].
      replace (wa X) with (wa (a + (X - a))) by (f_equal; lia).
      apply (wr_at_store_ok rsegs mm a (3 * N * ns) (X - a) 1 I3); lia.
    - intros x Hx. rewrite rb_enc_app.
      change (rb_enc (rb_enc m L) [(X, b)]) with (write_to_mem (rb_enc m L) (wa X) [b]).
      apply (rbe_wr_agree [(bv_unsigned sp + -48, bv_unsigned sp)]); [lia | exact I5 | exact Hx].
    - apply munch_write; [exact I6 | lia | exact HL | cbn [inside length Z.of_nat]; lia].
    - apply wmono_write. exact I7.
  Qed.

  Lemma FR_store : forall mm cs X b, rw_cells rsegs mm (bv_unsigned sp + -48) cs -> cells_size cs = 48%nat ->
    a <= X < a + 3 * N * ns -> rw_cells rsegs (write_to_mem mm (wa X) [b]) (bv_unsigned sp + -48) cs.
  Proof.
    intros mm cs X b H Hs HX. apply rw_cells_frame; [exact H | lia | cbn [length Z.of_nat]; lia |].
    rewrite Hs. cbn [length Z.of_nat]. destruct HD3; lia.
  Qed.

  Lemma INV_list : forall mm L L', INV mm L -> L = L' -> INV mm L'.
  Proof. intros mm L L' H ->. exact H. Qed.

  Lemma INV_mu : forall mm L, INV mm L -> munch [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)] m mm.
  Proof. intros mm L H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.

  Lemma INV_wr : forall mm L, INV mm L -> wr_at rsegs mm a (3 * N * ns).
  Proof. intros mm L H. exact (proj1 (proj2 (proj2 H))). Qed.

  Lemma rbe_loop : forall (n : nat) (s ch : Z) (mm : word -> option byte) (G : bvmap 5 word)
      (x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
    n = Z.to_nat ((ns - s) * N - ch) -> 0 <= s < ns -> 0 <= ch < N ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -48) -> x5 = Z_to_bv 64 s -> x6 = Z_to_bv 64 off -> x7 = Z_to_bv 64 N ->
    x8 = Z_to_bv 64 (P + 8 * ch) -> x14 = Z_to_bv 64 ns -> x15 = Z_to_bv 64 (P + 8 * ch) ->
    x28 = Z_to_bv 64 2147483646 -> x29 = Z_to_bv 64 ch -> x30 = Z_to_bv 64 (s * N) -> x31 = Z_to_bv 64 (4 * s) ->
    INV mm (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) ->
    rw_cells rsegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get G k = reg_get F k) ->
    evt rsegs (rbe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
               x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          (bvmap_set 12 (Z_to_bv 64 18446744072820359168) (bvmap_set 13 (Z_to_bv 64 18446744070672875518)
            (bvmap_set 14 (Z_to_bv 64 18446744070672875520) (bvmap_set 15 (Z_to_bv 64 18446744069414584320) G))))
          (Z_to_bv 64 0x81954) fc None mm (seg_rom rsegs)).
  Proof.
    induction n as [|n IH];
      intros s ch mm G x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
        Hn Hs Hch E2 E5 E6 E7 E8 E14 E15 E28 E29 E30 E31 HI FR HG.
    { exfalso. clear - Hn Hs Hch HN. assert (s * N <= ns * N - N) by nia. lia. }
    subst x2 x5 x6 x7 x8 x14 x15 x28 x29 x30 x31.
    destruct (HQ ch Hch) as (HQ0 & HQ4 & HQE).
    destruct (HV s ch Hs Hch) as [_ HVs].
    destruct (rbe_pipe (V s ch) (K s ch) HVs) as (Hv & w & Hw & HM & HL1 & HL2 & HC).
    destruct HVs as [HK _].
    unfold F2P23, FCLAMP_HI, FCLAMP_LO in HM, HL1, HL2.
    pose proof (rbe_pos_bound N s ch ns Hs Hch HNe) as HB.
    assert (HsN : 0 <= s * N <= 1524) by (clear - Hs Hns HN; nia).
    pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hc2.
    assert (RP : ov_read_bytes rsegs mm (wa (P + 8 * ch)) 8 = Some (le8 (Z_to_bv 64 (Q ch))))
      by (apply rbe_rd8; apply (proj1 HI); exact Hch).
    assert (RV : ov_read_bytes rsegs mm (wa (Q ch + 4 * s)) 4 = Some (le4 (Z_to_bv 64 (V s ch))))
      by (apply rbe_rd4; apply (proj1 (proj2 HI)); assumption).
    pose proof (shP mm ch (INV_mu _ _ HI) Hch) as RKP.
    rbe_st. rbe_st.
    rewrite (rbe_eqb P 0) by lia. if_false.
    rbe_st. rbe_st.
    rewrite (rbe_lts ch N) by lia. if_false.
    step.
    rewrite (unsigned_lit (P + 8 * ch)) by lia. rewrite rc_shr3.
    step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). rbe_st.
    rbe_st. rbe_st. rbe_st.
    rewrite (rbe_eqb (Q ch) 0) by lia. if_false.
    rbe_st.
    step.
    rewrite (unsigned_lit (Q ch + 4 * s)) by lia. rewrite rc_shr3.
    step.
    destruct (shQ mm s ch (INV_mu _ _ HI) Hs Hch) as (k & RKQ & OKQ).
    pose proof (rc_byte_signed k) as KR.
    step. clear RKQ.
    step.
    join 9 CONTQ.
    { intros y. map_cbv_set.
      rbe_st. rewrite (rbe_ld4 (V s ch)) by lia.
      step. rbe_fpc. rewrite (rbe_u32 (V s ch)) by lia. rewrite HM. cbn [fst snd]. rewrite rbe_fc_same.
      step. rbe_fpc. rewrite (rbe_u32 w) by lia. rewrite HL1. cbn [fst snd]. rewrite rbe_fc_same.
      rbe_st. rbe_st. rbe_st.
      step. rbe_fpc. rewrite (rbe_u32 w) by lia. rewrite HL2. cbn [fst snd]. rewrite rbe_fc_same.
      rbe_st. rbe_st. rbe_st.
      do 8 rbe_st.
      rewrite (unsigned_lit ch) by lia. rewrite (rbe_land_even ch) by lia. rewrite (rbe_land1 ch) by lia.
      rewrite (unsigned_lit (ch - ch mod 2 + s * N)) by lia.
      rewrite (Z.shiftl_mul_pow2 _ 1) by lia.
      replace (a + ch mod 2 + ((ch - ch mod 2 + s * N) * 2 ^ 1 + (ch - ch mod 2 + s * N)) + 3)
        with (a + rb_lo N s ch) by (unfold rb_lo, rb_G; ring).
      destruct HB as [HB0 HB1].
      assert (HX1 : a <= a + rb_lo N s ch < a + 3 * N * ns) by (unfold rb_lo; lia).
      assert (HX2 : a <= a + rb_mid N s ch < a + 3 * N * ns) by (unfold rb_mid; lia).
      assert (HX3 : a <= a + rb_hi N s ch < a + 3 * N * ns) by (unfold rb_hi; lia).
      step. rewrite (unsigned_lit (a + rb_lo N s ch)) by lia. rewrite rc_shr3.
      step.
      destruct (shA mm (a + rb_lo N s ch) (INV_mu _ _ HI) HX1) as (k1 & RK1 & OK1).
      pose proof (rc_byte_signed k1) as KR1.
      step. clear RK1.
      step.
      join 20 CONTL.
      { intros y4. map_cbv_set.
        step. rbe_fpc. rewrite (rbe_u32 w) by lia. rewrite HC. cbn [fst snd]. rewrite rbe_fc_same.
        rbe_st. rbe_st.
        rewrite (unsigned_lit (ch mod 2)) by lia. rewrite (rbe_neg5 (ch mod 2)) by lia.
        set (L := rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) in *.
        set (b1 := Z_to_bv 8 ((K s ch mod 2 ^ 24) mod 256)).
        set (b2 := Z_to_bv 8 ((K s ch mod 2 ^ 24) / 256 mod 256)).
        set (b3 := Z_to_bv 8 ((K s ch mod 2 ^ 24) / 65536)).
        assert (HS1 : store_ok rsegs mm (wa (a + rb_lo N s ch)) 1 = true).
        { apply (wr_at_store_ok rsegs mm a (3 * N * ns) (rb_lo N s ch) 1 (INV_wr _ _ HI)); cbn [Z.of_nat]; lia. }
        step.
        rewrite rbe_le1, rbe_b0. fold b1.
        change (Z_to_bv 64 (a + rb_lo N s ch)) with (wa (a + rb_lo N s ch)).
        pose proof (INV_store mm L (a + rb_lo N s ch) b1 HI HX1) as HI1.
        pose proof (FR_store mm _ (a + rb_lo N s ch) b1 FR eq_refl HX1) as FR1.
        set (mm1 := write_to_mem mm (wa (a + rb_lo N s ch)) [b1]) in *. clearbody mm1.
        clear HS1.
        rbe_st. rbe_st.
        replace (a + 5 * (ch mod 2) + ((ch - ch mod 2 + s * N) * 2 ^ 1 + (ch - ch mod 2 + s * N)))
          with (a + rb_mid N s ch) by (unfold rb_mid, rb_G; ring).
        step. rewrite (unsigned_lit (a + rb_mid N s ch)) by lia. rewrite rc_shr3.
        step.
        destruct (shA mm1 (a + rb_mid N s ch) (INV_mu _ _ HI1) HX2) as (k2 & RK2 & OK2).
        pose proof (rc_byte_signed k2) as KR2.
        step. clear RK2.
        step.
        join 19 CONTM.
        { intros y3. map_cbv_set.
          step. rewrite (unsigned_lit (K s ch mod 2^64)) by (pose proof (Z.mod_pos_bound (K s ch) (2^64)); lia).
          step.
          replace (a + ch mod 2 + ((ch - ch mod 2 + s * N) * 2 ^ 1 + (ch - ch mod 2 + s * N)) + 1)
            with (a + rb_hi N s ch) by (unfold rb_hi, rb_G; ring).
          assert (HS2 : store_ok rsegs mm1 (wa (a + rb_mid N s ch)) 1 = true).
          { apply (wr_at_store_ok rsegs mm1 a (3 * N * ns) (rb_mid N s ch) 1 (INV_wr _ _ HI1)); cbn [Z.of_nat]; lia. }
          step.
          rewrite rbe_le1, rbe_b1. fold b2.
          change (Z_to_bv 64 (a + rb_mid N s ch)) with (wa (a + rb_mid N s ch)).
          pose proof (INV_store mm1 _ (a + rb_mid N s ch) b2 HI1 HX2) as HI2.
          pose proof (FR_store mm1 _ (a + rb_mid N s ch) b2 FR1 eq_refl HX2) as FR2.
          set (mm2 := write_to_mem mm1 (wa (a + rb_mid N s ch)) [b2]) in *. clearbody mm2.
          clear HS2.
          step. rewrite (unsigned_lit (a + rb_hi N s ch)) by lia. rewrite rc_shr3.
          step.
          destruct (shA mm2 (a + rb_hi N s ch) (INV_mu _ _ HI2) HX3) as (k3 & RK3 & OK3).
          pose proof (rc_byte_signed k3) as KR3.
          step. clear RK3.
          step.
          join 18 CONTH.
          { intros y2. map_cbv_set.
            step. rewrite (unsigned_lit (K s ch mod 2^64)) by (pose proof (Z.mod_pos_bound (K s ch) (2^64)); lia).
            step. step.
            assert (HS3 : store_ok rsegs mm2 (wa (a + rb_hi N s ch)) 1 = true).
            { apply (wr_at_store_ok rsegs mm2 a (3 * N * ns) (rb_hi N s ch) 1 (INV_wr _ _ HI2)); cbn [Z.of_nat]; lia. }
            step.
            rewrite rbe_le1, rbe_b2. fold b3.
            change (Z_to_bv 64 (a + rb_hi N s ch)) with (wa (a + rb_hi N s ch)).
            pose proof (INV_store mm2 _ (a + rb_hi N s ch) b3 HI2 HX3) as HI3.
            pose proof (FR_store mm2 _ (a + rb_hi N s ch) b3 FR2 eq_refl HX3) as FR3.
            set (mm3 := write_to_mem mm2 (wa (a + rb_hi N s ch)) [b3]) in *. clearbody mm3.
            assert (HI4 : INV mm3 (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat (ch + 1)))).
            { apply (INV_list mm3 _ _ HI3). subst L. rewrite rb_row_succ by lia. unfold rb_turn. subst b1 b2 b3.
              rewrite <- !app_assoc. reflexivity. }
            clear HI HI1 HI2 HI3 FR FR1 FR2 HS3 RP RV.
            rbe_st. step.
            rewrite (rbe_eqb N (ch + 1)) by (clear - HN Hch; lia).
            destruct (Z.eq_dec (ch + 1) N) as [Hlast|Hmore].
            - replace (N =? ch + 1) with true by (symmetry; apply Z.eqb_eq; clear - Hlast; lia). cbn [negb]. rbe_rif.
              step. rbe_st. step.
              rewrite (rbe_eqb (s + 1) ns) by (clear - Hs Hns; lia).
              destruct (Z.eq_dec (s + 1) ns) as [Hend|Hnext].
              + replace (s + 1 =? ns) with true by (symmetry; apply Z.eqb_eq; exact Hend). cbn [negb]. rbe_rif.
                do 7 rbe_st.
                assert (ST : stk rsegs mm3 (bv_unsigned sp + -48) (bv_unsigned sp + -48)).
                { pose proof (bv_unsigned_in_range 64 sp) as R; change (bv_modulus 64) with (2^64) in R.
                  clear - R Hsp. split; [lia|]. split; [lia|]. intros x Hx; lia. }
                release_frame FR3 ST (bv_unsigned sp).
                step.
                destruct HI4 as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
                apply evt_done. unfold rbe_post. do 13 eexists. split; [reflexivity|].
                split; [intros k0 Hk; rewrite rbe_fget6 by (first [exact Hk | reflexivity]); apply HG; exact Hk|].
                split; [exact I6|]. split; [exact I7|]. split; [exact I4|]. split; [exact ST|].
                intros x Hx. rewrite (I5 x Hx). rewrite <- Hend, rb_rows_succ by (clear - Hs; lia). rewrite <- Hlast. reflexivity.
              + replace (s + 1 =? ns) with false by (symmetry; apply Z.eqb_neq; exact Hnext). cbn [negb]. rbe_rif.
                step. rewrite (rbe_lts 0 N) by (clear - HN; lia). if_false.
                do 5 rbe_st.
                rewrite rbe_frot by reflexivity.
                eapply (IH (s + 1) 0 mm3).
                all: lazymatch goal with
                     | |- INV _ _ => apply (INV_list mm3 _ _ HI4); rewrite rb_rows_succ by (clear - Hs; lia); rewrite <- Hlast;
                                     cbn [Z.to_nat rb_row]; rewrite app_nil_r; reflexivity
                     | |- rw_cells _ _ _ _ => exact FR3
                     | |- forall k, _ -> _ => intros k0 Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
                     | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hsp Hoff Ha HaE HP0 HP8 Hlast Hnext; rbe_aweq
                     | |- _ => clear - Hn Hs Hch HN Hns Hlast Hnext; nia
                     end.
            - replace (N =? ch + 1) with false by (symmetry; apply Z.eqb_neq; clear - Hmore; lia). cbn [negb]. rbe_rif.
              rewrite rbe_frot by reflexivity.
              eapply (IH s (ch + 1) mm3).
              all: lazymatch goal with
                   | |- INV _ _ => exact HI4
                   | |- rw_cells _ _ _ _ => exact FR3
                   | |- forall k, _ -> _ => intros k0 Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
                   | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hsp Hoff Ha HaE HP0 HP8 Hmore; rbe_aweq
                   | |- _ => clear - Hn Hs Hch HN Hns Hmore; nia
                   end. }
          unfold sxb. rewrite (rbe_eqb0b k3).
          destruct (Z.eqb_spec (bv_signed k3) 0) as [K3|K3]; cbn [negb].
          - join_use CONTH.
          - step. rewrite (unsigned_lit (a + rb_hi N s ch)) by lia. rewrite rc_land7.
            step.
            rewrite (rbe_chk0 (a + rb_hi N s ch) k3 K3 OK3).
            cbn [negb]. step. join_use CONTH. }
        unfold sxb. rewrite (rbe_eqb0b k2).
        destruct (Z.eqb_spec (bv_signed k2) 0) as [K2|K2]; cbn [negb].
        - join_use CONTM.
        - step. rewrite (unsigned_lit (a + rb_mid N s ch)) by lia. rewrite rc_land7.
          step.
          rewrite (rbe_chk0 (a + rb_mid N s ch) k2 K2 OK2).
          cbn [negb]. step. join_use CONTM. }
      unfold sxb. rewrite (rbe_eqb0b k1).
      destruct (Z.eqb_spec (bv_signed k1) 0) as [K1|K1]; cbn [negb].
      - join_use CONTL.
      - step. rewrite (unsigned_lit (a + rb_lo N s ch)) by lia. rewrite rc_land7.
        step.
        rewrite (rbe_chk0 (a + rb_lo N s ch) k1 K1 OK1).
        cbn [negb]. step. join_use CONTL. }
    unfold sxb. rewrite (rbe_eqb0b k).
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - join_use CONTQ.
    - step. rewrite (unsigned_lit (Q ch + 4 * s)) by lia. rewrite rc_land7.
      step. step.
      rewrite (rbe_chk3 (Q ch + 4 * s) k K0 OKQ).
      cbn [negb]. step. join_use CONTQ.
  Qed.
End Run.

(* slli a5,a1,32 then srli t2,a5,32: the zero extension of N. *)
Lemma rbe_zx32 : forall N, 0 <= N < 2^32 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 N)) 32))) 32) = Z_to_bv 64 N.
Proof.
  intros N HN. rewrite (unsigned_lit N) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (N * 2^32))
    by (change (2^32) with 4294967296; change (2^64) with 18446744073709551616; change (2^32) with 4294967296 in HN; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Theorem reac_braid_encode_exact_holds : reac_braid_encode_exact_contract.
Proof.
  unfold reac_braid_encode_exact_contract, REAC_BRAID_ENCODE, REAC_BRAID_ENCODE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    a N P ns Q V K -> -> -> -> -> HN HNe Hns FRM HI ST Ha HaE HW HP0 HP8m HP8 HPb HQ HV HD1 HD2 HD3 HD4 HD5
    HCE HSW HAa HAP HAQ HWO.
  change (evt rsegs ?Qx ?ms) with
    (evt rsegs (rbe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K) ms).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (Hsp : 48 <= bv_unsigned sp) by lia.
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in HD3, HD4, HD5, HWO by lia.
  (* the runtime facts on m: the cell of the shadow offset, and the shadow of a, P and each Q ch *)
  pose proof (rt_asan_rt m _ HCE HWO) as HRT.
  assert (HWs : forall x, in_shadow x -> outside [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)] x)
    by (intros x Hx; apply HWO; right; right; exact Hx).
  pose proof (rt_shadow_rd m a (3 * N * ns) _ HAa HWs) as HSRa.
  pose proof (rt_addressable m a (3 * N * ns) HAa) as HADa.
  pose proof (rt_shadow_rd m P (8 * N) _ HAP HWs) as HSRP.
  pose proof (rt_addressable m P (8 * N) HAP) as HADP.
  pose proof (rt_rt3 m P (8 * N) HAP) as HR3P.
  assert (HSRQ : forall ch, 0 <= ch < N -> asan_shadow_rd rsegs m ASAN_K (Q ch) (4 * ns)
                   [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)])
    by (intros ch Hch; apply rt_shadow_rd; [apply HAQ; exact Hch | exact HWs]).
  assert (HADQ : forall ch, 0 <= ch < N -> asan_addressable rsegs m ASAN_K (Q ch) (4 * ns))
    by (intros ch Hch; apply rt_addressable, HAQ, Hch).
  assert (Hoff : 0 <= ASAN_K < 2^63) by (unfold ASAN_K; lia).
  clear HCE HSW HAa HAP HAQ HWs.
  set (off := ASAN_K) in *. clearbody off.
  (* +0x0 .. +0x18: addi sp and the six callee-saved stores *)
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.
  (* +0x1c: ns > 0 *)
  step. rewrite (rbe_lts 0 ns) by lia. if_false.
  (* +0x20 .. +0x2c: the GOT cell of the shadow offset, and min (ns, 12) *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (HRT1 : asan_rt rsegs mc GOT_CELL_K CELL_K off [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 3 * N * ns)])
      by (apply (asan_rt_munch rsegs m mc _ _ _ _ _ HRT MU); intros x [H1 _]; split; [exact H1 | exact I])
  end.
  pose proof (asan_rt_got_read rsegs _ _ _ _ _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs _ _ _ _ _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
  assert (PRO : forall x14 : word, x14 = Z_to_bv 64 ns ->
    evt rsegs (rbe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N)
               (Z_to_bv 64 P) (Z_to_bv 64 N) x14 (Z_to_bv 64 0xa0db8) (Z_to_bv 64 12) a7 s2 s3 s4 s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81908) fc None m3 (seg_rom rsegs)))
  end.
  { intros x14 ->.
    (* +0x34 .. +0x64: the shadow offset and the float constants *)
    do 13 rbe_st.
    (* +0x68 .. +0x7c: N > 0, the first row *)
    step. rewrite (rbe_lts 0 N) by lia. if_false.
    do 5 rbe_st.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
      assert (HI0 : INV sp m a N P ns Q V m4 (rb_rows a N K (Z.to_nat 0) ++ rb_row a N K 0 (Z.to_nat 0)))
    end.
    { unfold INV. cbn [rb_rows rb_row Z.to_nat app].
      split.
      { intros ch Hch. eapply bytes_at_transport; [apply HPb; exact Hch | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le8. destruct HD4; lia. }
      split.
      { intros s' ch Hs' Hch. eapply bytes_at_transport; [apply (proj1 (HV s' ch Hs' Hch)) | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le4. destruct (HD5 ch Hch); lia. }
      split; [exact HW|].
      split; [exact HI|].
      split; [intros x Hx; exact (MU x Hx)|].
      split; [eapply munch_weaken; [|exact MU]; intros x [H1 [H2 _]]; split; [exact H1|exact I]|].
      exact WM. }
    eapply rbe_loop with (n := Z.to_nat ((ns - 0) * N - 0)) (s := 0) (ch := 0).
    all: first
      [ exact HI0
      | match goal with |- forall k, _ -> _ => intros k Hk; reflexivity end
      | eassumption
      | reflexivity
      | apply rbe_zx32; lia
      | f_equal; lia
      | lia ]. }
  if_cases HC12.
  - apply (PRO (Z_to_bv 64 ns)). reflexivity.
  - rbe_rif. step. apply (PRO (Z_to_bv 64 12)).
    unfold bv_ltu in HC12. rewrite !unsigned_lit in HC12 by lia. apply Z.ltb_ge in HC12.
    f_equal. lia.
Qed.
