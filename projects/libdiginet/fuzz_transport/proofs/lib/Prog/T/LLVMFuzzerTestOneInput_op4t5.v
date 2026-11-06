(* Case 4 of the plain op loop, the tagged arm's last stretch: 0x14260-0x1427c (fuzz_transport.c:1117 g_ncmd++, the
   cursor after the take of :1089 into s0 / s6, s2 = 0x39 and s1 = 7 back for the loop) and llvm_op4_tail (0x14280:
   settle(0) of :1118, the latch). *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4k.
Import ListNotations.
Open Scope Z_scope.

(* :1120 g_ncmd++ as the machine does it: lw (signed), +1, sw. From the ubsan twin
   (lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_lib.v t4_put4_mod, lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_m.v
   t4_s32_mod / t4_put4_cong / t4_put4_s32 / t4_ncmdw): build-independent. *)
Lemma o4t5_put4_mod : forall x, put 4 (x mod 2 ^ 32) = put 4 x.
Proof. intros x. unfold put. rewrite <- (Z_to_le_bytes_mod 4 x 32) by lia. reflexivity. Qed.

Lemma o4t5_s32_mod : forall B k, s32_at B k mod 2 ^ 32 = u_at B k 4 mod 2 ^ 32.
Proof.
  intros B k. unfold s32_at, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma o4t5_put4_s32 : forall B k d, put 4 (s32_at B k + d) = put 4 (u_at B k 4 + d).
Proof.
  intros B k d. rewrite <- (o4t5_put4_mod (s32_at B k + d)), <- (o4t5_put4_mod (u_at B k 4 + d)).
  rewrite <- (Zplus_mod_idemp_l (s32_at B k)), <- (Zplus_mod_idemp_l (u_at B k 4)), o4t5_s32_mod.
  reflexivity.
Qed.

Lemma o4t5_ncmdw : forall B6, upd B6 OFF_g_ncmd (put 4 (s32_at B6 OFF_g_ncmd + 1))
  = set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32).
Proof.
  intros B6. unfold set_g_ncmd, g_ncmd.
  rewrite (o4t5_put4_mod (u_at B6 OFF_g_ncmd 4 + 1)). rewrite o4t5_put4_s32. reflexivity.
Qed.

Section T5.
Context (data : Z) (D : list byte).

(* the cursor after a byte read and after a take is still a cursor of D (fuzz.h:40-46, the take of :1089) *)
Lemma o4t5_cursor_u8 : forall c, llvm_cursor D c -> llvm_cursor D (fst (fuzz_u8_m D c)).
Proof.
  intros c (H1 & H2 & H3 & H4). unfold fuzz_u8_m.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|E]; unfold llvm_cursor; cbn [fst fi_off fi_n]; lia.
Qed.

Lemma o4t5_cursor_take : forall c w, llvm_cursor D c -> 0 <= w -> llvm_cursor D (fst (fst (fuzz_take_m c w))).
Proof.
  intros c w (H1 & H2 & H3 & H4) Hw. unfold fuzz_take_m.
  destruct (Z.ltb_spec w (fi_n c)) as [E|E]; unfold llvm_cursor; cbn [fst fi_off fi_n]; lia.
Qed.

(* o4_n (the bytes the take moves) is at most the cursor's n after lb, and at most 21 *)
Lemma o4t5_n_rng : forall c3, llvm_cursor D c3 -> 0 <= o4_n D c3 <= fi_n (o4_c4 D c3) /\ o4_n D c3 <= 21.
Proof.
  intros c3 HC. pose proof (o4t5_cursor_u8 c3 HC) as HC4. fold (o4_c4 D c3) in HC4.
  destruct HC4 as (_ & H2 & _).
  assert (HL : 0 <= snd (fuzz_u8_m D c3) mod 22 < 22) by (apply Z.mod_pos_bound; lia).
  unfold o4_n, o4_tk, fuzz_take_m, o4_len. cbn [snd].
  destruct (Z.ltb_spec (snd (fuzz_u8_m D c3) mod 22 + 3 - 3) (fi_n (o4_c4 D c3))); lia.
Qed.

Lemma o4t5_cursor5 : forall c3, llvm_cursor D c3 -> llvm_cursor D (o4_c5 D c3).
Proof.
  intros c3 HC. unfold o4_c5, o4_tk. apply o4t5_cursor_take; [apply o4t5_cursor_u8; exact HC|].
  unfold o4_len. pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c3)) 22 ltac:(lia)). lia.
Qed.

Lemma op4_tag5 : op4_tag5_stmt data D.
Proof.
  intros Sp lo ops c3 B1 before display key B6 B8 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    STC H HB8 HK.
  destruct H as (rr & t0 & t1 & t2 & x8 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x18 & x20 & x23 &
                 t3 & t4 & t5 & t6 & m & -> & HOK & (j30 & j70 & HM)).
  destruct HOK as ((HOPS & HC & _ & _ & _) & _).
  pose proof HM as HM0.
  unfold op4_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B6) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  unfold op4_fr in HRW. cbn [app] in HRW.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_ncmd. wk_eq_fact OFF_g_s. wk_eq_fact OFF_M.
  pose proof (o4t5_n_rng c3 HC) as (HN1 & HN2).
  pose proof (o4t5_cursor_u8 c3 HC) as HC4. fold (o4_c4 D c3) in HC4.
  pose proof (o4t5_cursor5 c3 HC) as HC5.
  destruct HC4 as (H41 & H42 & H43 & H44).
  unfold FUZZ_INPUT_MAX in H44.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU6.
  pose proof (wmono_refl rsegs m) as WMO6.
  (* 0x14260 lw a0, 0x10(s9) (g_ncmd, signed: 0x10(s9) = W_BASE_PLAIN + OFF_g_ncmd); 0x14264 add s0, s3, s6;
     0x14268 ld a1, 0x10(sp) (the cursor's n after lb); 0x1426c sub s6, a1, s6; 0x14270 addiw-free addi a0, 1;
     0x14274 sw a0, 0x10(s9); 0x14278 li s2, 0x39; 0x1427c li s1, 7 *)
  do 8 zstep.
  (* the cursor after the take (o4_c5 = fuzz_take_m's cursor, TOps.v:64-66) *)
  assert (EO : fi_off (o4_c5 D c3) = fi_off (o4_c4 D c3) + o4_n D c3) by reflexivity.
  assert (EN : fi_n (o4_c5 D c3) = fi_n (o4_c4 D c3) - o4_n D c3) by reflexivity.
  replace (Z_to_bv 64 (data + fi_off (o4_c4 D c3) + o4_n D c3)) with (Z_to_bv 64 (data + fi_off (o4_c5 D c3)))
    by (f_equal; lia).
  try rewrite (Z.mod_small (fi_n (o4_c4 D c3)) 18446744073709551616) by lia.
  try rewrite (Z.mod_small (o4_n D c3) 18446744073709551616) by lia.
  try rewrite <- EN.
  (* the world: g_ncmd++ is the model's set_g_ncmd (64984 = OFF_g_ncmd) *)
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN _ |- _ =>
    change 64984 with OFF_g_ncmd in Hw; rewrite o4t5_ncmdw in Hw end.
  assert (FN7 : g_fail_next (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) = g_fail_next B6).
  { unfold set_g_ncmd. apply op4_fn_put; [exact LBz | unfold OFF_g_ncmd; lia | unfold OFF_g_ncmd, W_LEN; cbn [Z.of_nat]; lia
      | unfold OFF_g_ncmd, OFF_g_fail_next; cbn [Z.of_nat]; lia]. }
  lazymatch goal with Hr : rw_cells rsegs ?m7 Sp _ |- _ =>
    assert (HM7 : op4_mem data D Sp lo (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) m0 m7
      ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] ++
       [C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))] ++
       [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++
       [C8 (Z_to_bv 64 (bv_swrap 32 before)); CB 32 j30; CB 32 (o4_cs D B1 c3 display key); CB 8 j70] ++
       [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
  end.
  { eapply (op4_mem_after data D Sp lo 0 B6 _ m0 m); [exact HM0 | unfold LLVM_LOOP_K; lia | exact MU6 | exact WMO6
      | assumption | assumption | assumption | rewrite FN7; exact HFN | cbn [app]; assumption | reflexivity]. }
  eapply (llvm_op4_tail data D Sp lo ops (o4_c5 D c3) _ B8 m0 _ [C8 (Z_to_bv 64 (fi_n (o4_c4 D c3)))]
            [C8 (Z_to_bv 64 (bv_swrap 32 before)); CB 32 j30; CB 32 (o4_cs D B1 c3 display key); CB 8 j70]);
    [ exact STC | exact HM7 | reflexivity | reflexivity | exact HC5 | exact HOPS | exact HB8 | exact HK ].
Qed.

End T5.
