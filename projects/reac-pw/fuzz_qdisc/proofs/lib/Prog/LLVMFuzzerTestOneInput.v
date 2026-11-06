(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 269 of its 286 lines of code are new or changed and 43 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec reac_qdisc_etf_catchup_slots_c
  check_slots_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of reac-pw/fuzz_qdisc (fuzz_qdisc.c:89-102; 312 bytes at 0x12ac8 in the plain image,
    frame 80 bytes) against qdisc_main_contract, given the contracts of its two callees. The walk is ported from
    libreac/fuzz_knock's released Prog/LLVMFuzzerTestOneInput.v (ossv/recipes 25e3d17bdb50): a Section with the
    frame hypotheses, the [saved] cells of the prologue, an exit lemma, and a fuel-indexed loop lemma over the
    budget count with the cursor invariant c + rem = length data. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma qd_bytes_at_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma dec_small : forall x, 1 <= x <= 7 -> bv_swrap 32 (x + -1) = x - 1.
Proof. intros x Hx. apply bv_swrap_small. replace (bv_half_modulus 32) with (2^31) by reflexivity. lia. Qed.

Lemma lead_bound : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (Z.shiftl x 8 mod 18446744073709551616) y)) <= 65535.
Proof.
  intros x y Hx Hy.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (x * 2 ^ 8)) by lia.
  assert (L : 0 <= Z.lor (x * 2 ^ 8) y < 2 ^ 16) by (apply lor_lt_pow2; lia).
  rewrite unsigned_lit by lia. lia.
Qed.

Lemma sel_bound_gen : forall (g : Z -> Z),
  forallb (fun x => (0 <=? g x) && (g x <? 6)) (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> 0 <= g x < 6.
Proof.
  intros g H x Hx. rewrite forallb_forall in H.
  assert (Hin : In x (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia. }
  specialize (H x Hin). apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Ltac sel_tac :=
  lazymatch goal with
  | |- 0 <= ?E < 6 =>
    lazymatch E with context [bv_unsigned (nth ?i ?d ?z)] =>
      let X := constr:(bv_unsigned (nth i d z)) in
      let g := lazymatch eval pattern X in E with ?g _ => g end in
      apply (sel_bound_gen g); [ vm_compute; reflexivity | ];
      pose proof (bv_unsigned_in_range 8 (nth i d z)) as RX; unfold bv_modulus in RX;
      change (2 ^ Z.of_N 8) with 256 in RX; lia
    end
  end.

Ltac lead_tac :=
  lazymatch goal with
  | |- bv_unsigned (Z_to_bv 64 (Z.lor (Z.shiftl (bv_unsigned ?b1) 8 mod 18446744073709551616) (bv_unsigned ?b0))) <= 65535 =>
      pose proof (bv_unsigned_in_range 8 b1) as RB1; pose proof (bv_unsigned_in_range 8 b0) as RB0;
      unfold bv_modulus in RB1, RB0; change (2 ^ Z.of_N 8) with 256 in RB1, RB0;
      apply lead_bound; lia
  end.

Ltac qside := first [ eassumption | lia | (rewrite unsigned_lit by lia; lia) | lead_tac | sel_tac ].

Section QRun.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z).
Hypothesis LO : lo + 80 <= bv_unsigned sp.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HMI0 : mem_inv rsegs m.
Hypothesis ST0 : stk rsegs m lo (bv_unsigned sp).

Definition saved : list cell :=
  [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Qk (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Lemma q_exit : forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
                       x18 x19 x20 x21 x22 x23 x24 t3' t4' t5' t6' : word)
                       (m1 : word -> option byte),
  rw_cells rsegs m1 (bv_unsigned sp + -80) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -80) ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 ->
  wmono rsegs m m1 ->
  mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12bcc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24
         t3' t4' t5' t6' m1 FR ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  unfold saved in FR.
  do 12 zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -80 + Z.of_nat 80) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

Variables (p : word) (data : list byte).
Hypothesis DJ : bv_unsigned p + Z.of_nat (length data) <= lo \/ bv_unsigned sp <= bv_unsigned p.
Hypothesis HPB : bv_unsigned p + Z.of_nat (length data) < 2 ^ 63.

Definition loop_ok (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (bw cur rem : word) (c : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned bw) <= fuel)%nat ->
  1 <= bv_unsigned bw <= 7 ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  rw_cells rsegs m1 (bv_unsigned sp + -80) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -80) ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             bw (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 66536) (Z_to_bv 64 171) rem cur s9 s10 s11
             t3' t4' t5' t6')
        F (Z_to_bv 64 0x12b2c) fc None m1 (seg_rom rsegs)).

Hypothesis SLOTS : qdisc_slots_contract.
Hypothesis CHECK : qdisc_check_contract.

Lemma q_calls : forall (fuel : nat), loop_ok fuel ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (lw bw cur rem : word) (f c : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned bw) <= S fuel)%nat ->
  1 <= bv_unsigned bw <= 7 ->
  bv_unsigned lw <= 65535 ->
  -2^31 <= f < 2^31 ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  rw_cells rsegs m1 (bv_unsigned sp + -80) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -80) ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' lw (Z_to_bv 64 f) a0' a1' a2' a3' a4' a5' a6' a7'
             bw (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 66536) (Z_to_bv 64 171) rem cur s9 s10 s11
             t3' t4' t5' t6')
        F (Z_to_bv 64 0x12b44) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' lw bw cur rem f c m1
    HF HB HL Hf HC HC0 HCN FR HD ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 lw) as Rlw. unfold bv_modulus in Rlw.
  unfold qdisc_slots_contract, QDISC_SLOTS in SLOTS.
  unfold qdisc_check_contract, QDISC_CHECK in CHECK.
  zstep. zstep. zstep.
  eapply evt_cut; [ eapply SLOTS with (lead := bv_unsigned lw) (fps := f);
                    first [ lia | reflexivity | exact HMI ] | ].
  intros ms' [a1x [a2x [a3x ->]]].
  replace (ret_pc (Z_to_bv 64 76624)) with (Z_to_bv 64 76624) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  zstep. zstep. zstep.
  eapply evt_cut; [ eapply CHECK with (lead := bv_unsigned lw) (fps := f);
                    first [ lia | reflexivity | exact HMI ] | ].
  intros ms' [a1y [a2y [a3y ->]]].
  replace (ret_pc (Z_to_bv 64 76636)) with (Z_to_bv 64 76636) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  zstep. zstep.
  rewrite (dec_small (bv_unsigned bw) HB).
  if_cases EZ.
  - zify_cond EZ.
    eapply LOOP; first [ eassumption | (rewrite unsigned_lit by lia; lia) ].
  - zstep.
    eapply q_exit; eassumption.
Qed.

Lemma q_join : forall (fuel : nat), loop_ok fuel ->
  forall (ra' t0' t1' t2' x9 a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (lw bw cur rem : word) (k c : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned bw) <= S fuel)%nat ->
  1 <= bv_unsigned bw <= 7 ->
  bv_unsigned lw <= 65535 ->
  0 <= k < 6 ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  rw_cells rsegs m1 (bv_unsigned sp + -80) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -80) ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' lw x9 (Z_to_bv 64 k) a1' a2' a3' a4' a5' a6' a7'
             bw (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 66536) (Z_to_bv 64 171) rem cur s9 s10 s11
             t3' t4' t5' t6')
        F (Z_to_bv 64 0x12b38) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' x9 a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' lw bw cur rem k c m1
    HF HB HL Hk HC HC0 HCN FR HD ST MU WM HMI.
  assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
  destruct Ek as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  all: zstep; zstep; zstep.
  4: replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
  all: eapply (q_calls fuel LOOP); first [ eassumption | lia ].
Qed.

Lemma q_loop : forall fuel, loop_ok fuel.
Proof.
  induction fuel as [|fuel IH]; unfold loop_ok;
    intros ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' bw cur rem c m1
      HF HB HC HC0 HCN FR HD ST MU WM HMI.
  { exfalso. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur.
  pose proof (bv_unsigned_in_range 64 p) as Rp.
  pose proof (bytes_at_bound rsegs m1 (bv_unsigned p) data HD) as Bd.
  unfold bv_modulus in Rsp, Rrem, Rcur, Rp.
  zstep.
  if_cases R0.
  - zify_cond R0.
    assert (HB0 : ov_read_bytes rsegs m1 cur 1 = Some [nth (Z.to_nat c) data (Z_to_bv 8 0)]).
    { rewrite <- (Z_to_bv_bv_unsigned cur). rewrite HC. apply (qd_bytes_at_byte m1 (bv_unsigned p) data c); [exact HD | lia]. }
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat c) data (Z_to_bv 8 0))) as Rb0. unfold bv_modulus in Rb0.
    zstep. zstep.
    if_cases R1.
    + zify_cond R1.
      assert (HB1 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned cur + 1)) 1
                    = Some [nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0)]).
      { rewrite HC. replace (bv_unsigned p + c + 1) with (bv_unsigned p + (c + 1)) by lia.
        apply qd_bytes_at_byte; [exact HD | lia]. }
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0))) as Rb1. unfold bv_modulus in Rb1.
      zstep. zstep. zstep. zstep.
      if_cases R2.
      * zify_cond R2.
        assert (HB2 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned cur + 2)) 1
                      = Some [nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0)]).
        { rewrite HC. replace (bv_unsigned p + c + 2) with (bv_unsigned p + (c + 2)) by lia.
          apply qd_bytes_at_byte; [exact HD | lia]. }
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0))) as Rb2. unfold bv_modulus in Rb2.
        do 11 zstep.
        eapply (q_join fuel IH) with (c := c + 3); qside.
      * zify_cond R2. do 4 zstep.
        eapply (q_join fuel IH) with (c := c + 2); qside.
    + zify_cond R1. do 4 zstep.
      eapply (q_join fuel IH) with (c := c + 1); qside.
  - zify_cond R0. do 2 zstep.
    eapply (q_join fuel IH); qside.
Qed.

Lemma q_entry : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m (bv_unsigned p) data ->
  bv_unsigned a1 = Z.of_nat (length data) ->
  evt rsegs Qk
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12ac8) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HD HN.
  pose proof HMI0 as HMI. pose proof ST0 as ST.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  pose proof (bv_unsigned_in_range 64 p) as Rp.
  pose proof ST0 as [Hlo _].
  unfold bv_modulus in Rsp, Ra1, Rp.
  do 4 zstep.
  if_cases EBIG.
  - zify_cond EBIG. zstep. zstep. finish; first [apply munch_refl | apply wmono_refl].
  - zify_cond EBIG.
    carve_frame 80%nat ST.
    assert (MU : munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m) by apply munch_refl.
    assert (WM : wmono rsegs m m) by apply wmono_refl.
    do 11 zstep.
    assert (EN : 1 <= bv_unsigned a1 < 2 ^ 26) by (Z.div_mod_to_equations; lia).
    match goal with HDm : bytes_at rsegs ?mm (bv_unsigned p) data |- _ =>
      assert (HB0 : ov_read_bytes rsegs mm p 1 = Some [nth (Z.to_nat 0) data (Z_to_bv 8 0)])
        by (rewrite <- (Z_to_bv_bv_unsigned p) at 1; rewrite <- (Z.add_0_r (bv_unsigned p));
            apply qd_bytes_at_byte; [exact HDm | lia])
    end.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 0) data (Z_to_bv 8 0))) as Rb0.
    unfold bv_modulus in Rb0. change (2 ^ Z.of_N 8) with 256 in Rb0.
    zstep. zstep. zstep.
    if_cases EB.
    + zify_cond EB.
      eapply q_exit; eassumption.
    + zify_cond EB.
      assert (L7 : 0 <= Z.land (bv_unsigned (nth (Z.to_nat 0) data (Z_to_bv 8 0))) 7 <= 7).
      { replace (Z.land (bv_unsigned (nth (Z.to_nat 0) data (Z_to_bv 8 0))) 7)
          with (bv_unsigned (nth (Z.to_nat 0) data (Z_to_bv 8 0)) mod 8)
          by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
        pose proof (Z.mod_pos_bound (bv_unsigned (nth (Z.to_nat 0) data (Z_to_bv 8 0))) 8 ltac:(lia)). lia. }
      do 7 zstep.
      eapply (q_loop 7) with (c := 1); qside.
Qed.

End QRun.

Theorem qdisc_main_holds : qdisc_slots_contract -> qdisc_check_contract -> qdisc_main_contract.
Proof.
  intros SL CK. unfold qdisc_main_contract, LLVM_QDISC, LLVM_QDISC_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo data HD HN HMI ST LO SPA DJ HPB.
  change (evt rsegs (Qk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12ac8) fc None m (seg_rom rsegs))).
  eapply q_entry; eassumption.
Qed.
