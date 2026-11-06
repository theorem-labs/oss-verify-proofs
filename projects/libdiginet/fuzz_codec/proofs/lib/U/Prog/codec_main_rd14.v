(** Segment RD14 of the UBSan LLVMFuzzerTestOneInput walk: MASKS, the default of the reader switch
    (fuzz_codec.c:648-653): n = fuzz_u32, mask = fuzz_u16, check_text_masks(n, mask), then the MASKS
    copy of the latch at 0x14b1c. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  check_text_masks_c codec_main_inv codec_main_lib codec_main_rdlib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the two arguments of check_text_masks ---- *)

(** Disjoint bits: a value below [2 ^ n] or-ed with a multiple of [2 ^ n] is their sum. *)
Lemma lor_hi : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b -> Z.lor a (2 ^ k * b) = a + 2 ^ k * b.
Proof.
  intros a b k Hk Ha Hb.
  assert (Hd : Z.land a (2 ^ k * b) = 0).
  { apply Z.bits_inj'. intros j Hj.
    rewrite Z.land_spec, Z.bits_0, (Z.mul_comm (2 ^ k)), Z.mul_pow2_bits by lia.
    destruct (Z_lt_le_dec j k).
    - rewrite (Z.testbit_neg_r b) by lia. apply andb_false_r.
    - destruct (Z.eq_dec a 0) as [-> | Ha0]; [rewrite Z.bits_0; reflexivity |].
      rewrite (Z.bits_above_log2 a j); [reflexivity | lia |].
      apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by exact Hd. symmetry. apply Z.add_nocarry_lxor. exact Hd.
Qed.

(** 0x14b00-0x14b10: the low half or-ed with [slliw] of the high half is n sign-extended from bit 31. *)
Lemma u32_sx : forall lo hi, 0 <= lo < 2 ^ 16 -> 0 <= hi < 2 ^ 16 ->
  Z_to_bv 64 (Z.lor lo (bv_swrap 32 (Z.shiftl hi 16) mod 18446744073709551616)) =
  Z_to_bv 64 (s32 (lo + 65536 * hi)).
Proof.
  intros lo hi Hl Hh. apply Z_to_bv_eqm. change (2 ^ 64) with 18446744073709551616.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mul_comm hi).
  unfold s32.
  destruct (Z.ltb_spec hi 32768) as [HA | HB].
  - rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
    rewrite (Z.mod_small (2 ^ 16 * hi)) by lia.
    rewrite lor_hi by lia.
    replace (lo + 65536 * hi <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
    f_equal; lia.
  - rewrite bv_swrap_hi by (first [ discriminate | change (bv_half_modulus 32) with (2 ^ 31); lia
                                  | change (bv_modulus 32) with (2 ^ 32); lia ]).
    change (bv_modulus 32) with (2 ^ 32).
    rewrite <- (Z.mod_unique (2 ^ 16 * hi - 2 ^ 32) 18446744073709551616 (-1) (2 ^ 16 * (hi + 2 ^ 48 - 2 ^ 16)))
      by lia.
    rewrite lor_hi by lia.
    replace (lo + 65536 * hi <? 2 ^ 31) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite <- (Z.mod_add (lo + 65536 * hi - 2 ^ 32) 1 18446744073709551616) by lia.
    f_equal; lia.
Qed.

Lemma arg_u32_hl : forall lo hi, 0 <= lo < 2 ^ 16 -> 0 <= hi < 2 ^ 16 ->
  arg_u32 (Z_to_bv 64 (Z.lor lo (bv_swrap 32 (Z.shiftl hi 16) mod 18446744073709551616))) (lo + 65536 * hi).
Proof. intros lo hi Hl Hh. split; [lia | apply u32_sx; assumption]. Qed.

(** When the high half is 0 the stepper folds it away: the value is the low half. *)
Lemma arg_u32_l : forall lo, 0 <= lo < 2 ^ 16 -> arg_u32 (Z_to_bv 64 lo) lo.
Proof.
  intros lo Hl. split; [lia |]. unfold s32.
  replace (lo <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma arg_zx16_of : forall v, 0 <= v < 2 ^ 16 -> arg_zx 16 (Z_to_bv 64 v) v.
Proof. intros v Hv. split; [exact Hv | reflexivity]. Qed.

(** The bytes left when MASKS starts: each of the six reads sees a byte or the end. *)
Lemma rem7_cases : forall rem, 0 <= rem ->
  rem = 0 \/ rem = 1 \/ rem = 2 \/ rem = 3 \/ rem = 4 \/ rem = 5 \/ 6 <= rem.
Proof. intros. lia. Qed.

Section RD14.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis CTM : check_text_masks_contract.
Hypothesis LATCH : latch_ok E n 0x14b1c.

(** 0x14b18: check_text_masks(n, mask), then the latch copy at 0x14b1c. *)
Lemma rd14_call : forall (kc : list cell) (a0 a1 : word) (nv mv cz rz ops : Z)
    (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  arg_u32 a0 nv -> arg_zx 16 a1 mv ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  fr E m1 kc (Z_to_bv 64 cz) (Z_to_bv 64 rz) u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0 a1 a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x14b18 m1).
Proof.
  intros kc a0 a1 nv mv cz rz ops ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
    u0 pj tj plj m1 HA0 HA1 Ho1 Ho2 Hcz Hrz Hcr FR ST MU WM HMI.
  unfold rd_st.
  pose proof ENV as (_ & _ & _ & HLO & _ & _ & HPB & _ & _ & _).
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (c_p E)) as Rp. unfold bv_modulus in Rp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Rp.
  pose proof ST as (Hlo0 & _).
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) = bv_unsigned (c_sp E) + -416)
    by (apply u_frame; lia).
  pose proof HA0 as [HN0 _]. pose proof HA1 as [HM0 _].
  zstep.
  unfold check_text_masks_contract, CHECK_TEXT_MASKS, CHECK_TEXT_MASKS_DEPTH in CTM.
  eapply evt_cut;
    [ eapply CTM with (lo := c_lo E) (n := nv) (mask := mv)
    | intros ms' (a0x & a1x & a2x & a3x & m2 & -> & MU2 & WM2 & MI2 & ST2) ].
  { unfold check_text_masks_pre, CHECK_TEXT_MASKS_DEPTH. rewrite U416.
    split; [exact HA0 |]. split; [exact HA1 |]. split; [exact HMI |]. split; [exact ST |].
    split; [lia |].
    exact (masks_agree nv mv HN0 HM0). }
  fix_ret.
  rewrite U416 in MU2, ST2.
  pose proof (fr_munch _ _ _ _ _ _ _ _ _ _ _ FR MU2 WM2) as FR2.
  assert (MU2' : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m2)
    by (eapply munch_frame; [exact MU | exact MU2 | lia]).
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM2'.
  unfold latch_ok in LATCH.
  eapply LATCH with (cur := Z_to_bv 64 cz) (rem := Z_to_bv 64 rz) (c := cz - bv_unsigned (c_p E));
    [ exact Ho1 | exact Ho2 | rewrite unsigned_lit by lia; lia | lia | rewrite unsigned_lit by lia; lia
    | exact FR2 | exact ST2 | exact MU2' | exact WM2' | exact MI2 ].
Qed.

(** 0x13b68-0x14b14: n = fuzz_u32, mask = fuzz_u16 (six fuzz_u8 with their zero paths and the
    group A trap edges), assembled into the two argument registers. *)
Lemma rd14_read : forall (i cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (k_head 14 i)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13b68 m1).
Proof.
  intros i cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem7_cases rz Hrz) as [R | [R | [R | [R | [R | [R | R]]]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14b18.
  all: match goal with
       | FC : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)] |- _ =>
           eapply (rd14_call (kcall_cells (k_head 14 i)) _ _ _ _ CZ RZ)
       end.
  all: first [ (first [ apply arg_u32_hl | apply arg_u32_l ]; bnd)
             | (apply arg_zx16_of; bnd)
             | eassumption
             | lia
             | (unfold fr; exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD
                                      (conj FTX (conj FPL FSV)))))))))].
Qed.

(** T1 has no entry for 14: the switch's default 0x13b68. *)
Lemma rd14_ok : forall i, 0 <= i <= 2 -> rd_ok E n 14 i.
Proof.
  intros i HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC1 HCN FR ST MU WM HMI.
  change (pc_rd 14) with 0x13b68.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  exact (rd14_read i (bv_unsigned cur) (bv_unsigned rem) ops
           ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
           u0 pj tj plj m1 Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
           F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD14.

Lemma codec_main_rd14 : seg_rd14_stmt.
Proof.
  unfold seg_rd14_stmt. intros E n ENV CTM LATCH i HI.
  exact (rd14_ok E n ENV CTM LATCH i HI).
Qed.
