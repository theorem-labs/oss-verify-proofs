(* check_sent_frame_seg_tail: the footprint runs (lib/Lib/ExecF.v evtF) of check_sent_frame in image A from the
   second bcmp call's return (0x83f10) to the `ret` at 0x84110, each from one cut point of the code to the post
   csf_ret_post (ra, s0 .. s3 reloaded from the frame, sp given back, the memory unchanged):
     csf_ret2_F  0x83f10: the checks of fp + 48 and fp + 56, body = fa + 30 and body_len, the scan when body_len >= 4;
     csf_scan_F  0x83f68: the inlined spec_system_at, by induction on the turns left; a hit would reach the trap
                 (`bgez a4` at 0x83ff4), which the model's spec_system_at < 0 rules out;
     csf_n_F     0x83ff8: n = max (60, body_len + 30), and the padding loop when n < len;
     csf_pad_F   0x84028: the padding loop, every byte 0 (a5 stays 1);
     csf_k74_F   0x84074: len = n, no padding byte set, the check and the load of f->sum, the mode test;
     csf_sum_F   0x840b4: the body sum loop (the plain walk's csum);
     csf_end_F   0x840f4: f->sum = want, the epilogue and the `ret`.
   Every byte check passes: the struct's granules have shadow 0 and every frame byte's shadow byte is one the check
   accepts (csf_mem); the step / branch structure follows the plain walk lib/Prog/T/check_sent_frame.v (SUM, Kbc, ZL,
   K88, K74, LOOP) at image A's addresses. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require check_sent_frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_seg_base.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* What the `ret` at 0x84110 leaves: ra, s0 .. s3 reloaded from the frame, sp given back, gp, tp and s4 .. s11 kept, the
   memory the run started from (the tail stores nothing). *)
Definition csf_ret_post (cra cs0 cs1 cs2 cs3 gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp : word) (lo : Z) (ms' : machine_state) : Prop :=
  exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 spx : word),
    ms' = MS (mkR cra spx gp tp x5 x6 x7 cs0 cs1 x10 x11 x12 x13 x14 x15 x16 x17 cs2 cs3 s4 s5 s6 s7 s8 s9 s10 s11
                  x28 x29 x30 x31) F (ret_pc cra) fc None m (seg_rom rsegs) /\
    bv_unsigned spx = bv_unsigned sp /\ stk rsegs m lo (bv_unsigned sp).

Section Tail.
Variable RNG : ExecF.footprint.
Variables sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 cs0 cs1 cs2 cs3 cra : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variable lo : Z.
Variable junk : list byte.
Variables fa fp blen sum : Z.
Variables frame SB Bw : list byte.
Hypothesis MEM : csf_mem m fa fp frame SB Bw.
Hypothesis RNGH : csf_rng RNG (bv_unsigned sp) fa fp (Z.of_nat (length frame)).
Hypothesis BND : csf_bnd fa fp (Z.of_nat (length frame)).
Hypothesis FX : csf_fx fa frame SB Bw blen sum.
Hypothesis STK : stk rsegs m lo (bv_unsigned sp + -48).
Hypothesis HLO : lo <= bv_unsigned sp + -48.
Hypothesis FRM : rw_cells rsegs m (bv_unsigned sp + -48) (csf_fr junk cs3 cs2 cs1 cs0 cra).

Local Abbreviation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

(* Two words of equal value. *)
Ltac weq := first [ reflexivity | (f_equal; lia) | (rewrite !unsigned_lit by lia; first [reflexivity | (f_equal; lia)]) ].

(* The facts every piece opens: the bundles under the names of csf_prep, the model's facts, the sp bounds. *)
Ltac tail_prep :=
  pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp;
  pose proof (stk_lo_nonneg _ _ _ _ STK) as L0;
  pose proof FX as (LSB & FC0 & F8 & F16 & F48 & F56 & F28 & FDK & FB0 & FBL & FB16 & FSYS & FN & FZ & FSUM & FLB);
  let M := fresh "M" in let R := fresh "R" in let Bd := fresh "Bd" in
  pose proof MEM as M; pose proof RNGH as R; pose proof BND as Bd;
  csf_prep M R Bd; repeat match goal with H : ro_cells rsegs _ _ _ |- _ => clear H end.
Local Abbreviation RET := (csf_ret_post cra cs0 cs1 cs2 cs3 gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m sp lo).
Local Abbreviation ST pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31 :=
  (MS (mkR x1 SP gp tp x5 x6 x7 (Z_to_bv 64 fp) (Z_to_bv 64 (Z.of_nat (length frame))) x10 x11 x12 x13 x14 x15 x16
           x17 y2 (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x840f4: f->sum against the sum the code computed (a1, a0), then the epilogue and the `ret`. *)
Lemma csf_end_F : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31 : word),
  x10 = Z_to_bv 64 sum -> x11 = Z_to_bv 64 sum ->
  ExecF.evtF rsegs RNG RET (ST (CSF_AT 0x28c) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31 -> ->.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ STK) as L0.
  pose proof FRM as FR. pose proof STK as ST. unfold csf_fr in FR.
  pose proof FX as (_ & _ & _ & _ & _ & _ & F28 & _).
  pose proof (TWorldLemmas.u_at_range SB 28 2) as RS. rewrite F28 in RS. change (2 ^ (8 * Z.of_nat 2)) with 65536 in RS.
  pose proof RNGH as (RFR & _).
  csf_pc.
  step. brP false ltac:(rewrite bv_eqb_refl; reflexivity).
  do 7 step.
  apply evtF_done. unfold csf_ret_post. do 16 eexists. split; [reflexivity|]. split.
  { rewrite ?unsigned_lit_wrap. Z.div_mod_to_equations. lia. }
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

(* 0x840b4: the body sum loop, j bytes added (a0 = a3 = fa + 30 + j, a2 = blen - j, a4 = the sum so far). *)
Lemma csf_sum_F : forall k j (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31 : word),
  Z.of_nat k = blen - j -> 0 <= j < blen -> TW.Cfg_sum_mode Bw <> 1 ->
  x10 = Z_to_bv 64 (fa + 30 + j) -> x12 = Z_to_bv 64 (blen - j) ->
  x13 = Z_to_bv 64 (fa + 30 + j) -> x14 = Z_to_bv 64 (PCSF.csum frame 30 (Z.to_nat j)) ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x24c) x1 x5 x6 x7 x10 (Z_to_bv 64 sum) x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31).
Proof.
  induction k as [|k IH];
    intros j x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31 Hk Hj HM -> -> -> ->; [lia|].
  tail_prep.
  assert (HS : sum = PCSF.csum frame 30 (Z.to_nat blen) mod 65536)
    by (rewrite FSUM; replace (TW.Cfg_sum_mode Bw =? 1) with false by (symmetry; apply Z.eqb_neq; exact HM);
        reflexivity).
  pose proof (TWorldLemmas.u_at_range SB 28 2) as RS. rewrite F28 in RS. change (2 ^ (8 * Z.of_nat 2)) with 65536 in RS.
  pose proof (PCSF.csum_range frame 30 (Z.to_nat j)) as CR.
  pose proof (PCSF.csf_u1_range frame (30 + j)) as UR.
  destruct (SHf (30 + j) ltac:(lia)) as (kb & Mk & Ck).
  pose proof (RSf (30 + j) ltac:(lia)) as Rk.
  replace (fa + (30 + j)) with (fa + 30 + j) in Mk, Ck, Rk by lia.
  pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
  pose proof (Z.mod_pos_bound (fa + 30 + j) 8 ltac:(lia)) as MB.
  pose proof (byte_signed_range kb) as KR.
  (* 0x840c4: the load of body[j] and the bookkeeping *)
  assert (K : forall y15 y16 : word,
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x25c) x1 x5 x6 x7 (Z_to_bv 64 (fa + 30 + j)) (Z_to_bv 64 sum) (Z_to_bv 64 (blen - j))
          (Z_to_bv 64 (fa + 30 + j)) (Z_to_bv 64 (PCSF.csum frame 30 (Z.to_nat j))) y15 y16 x17 y2
          x28 x29 x30 x31)).
  { intros y15 y16. csf_pc.
    pose proof (csf_rd m fa frame (30 + j) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_world.
    do 5 step.
    rewrite (PCSF.csf_eqb (blen - j + -1) 0) by lia.
    destruct (Z.eqb_spec (blen - j + -1) 0) as [E|E]; cbn [negb]; cbv iota.
    - (* the last byte: 0x840dc j 0x840ec ; slli a0,a4,48 ; srli a0,a0,48 *)
      step. step. step.
      eapply csf_end_F; [|reflexivity].
      rewrite PCSF.csf_shift by lia. f_equal. rewrite HS. f_equal.
      replace (Z.to_nat blen) with (S (Z.to_nat j)) by lia. cbn [PCSF.csum]. rewrite Z2Nat.id by lia. reflexivity.
    - apply (IH (j + 1)); [lia | lia | exact HM | f_equal; lia | f_equal; lia | f_equal; lia |].
      f_equal. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. cbn [PCSF.csum].
      rewrite Z2Nat.id by lia. reflexivity. }
  csf_pc.
  step. rewrite (csf_shr3 (fa + 30 + j)) by lia.
  step. step. step. rewrite sxb_eq0.
  destruct Ck as [C|C].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. apply K.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb].
    step. rewrite land7, (unsigned_lit (fa + 30 + j)) by lia.
    step. rewrite (lts_low ((fa + 30 + j) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbv iota.
    apply K.
Qed.

(* 0x84074: len against n (a1), the padding verdict (a0), then f->sum, the mode and the sum loop. *)
Lemma csf_k74_F : forall (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 y2 x28 x29 x30 x31 : word),
  x10 = Z_to_bv 64 0 -> x11 = Z_to_bv 64 (Z.of_nat (length frame)) ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x20c) x1 x5 x6 x7 x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17 y2
        x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 y2 x28 x29 x30 x31 -> ->.
  tail_prep.
  pose proof (TWorldLemmas.u_at_range SB 28 2) as RS. rewrite F28 in RS. change (2 ^ (8 * Z.of_nat 2)) with 65536 in RS.
  assert (L4 : length (TW.sub Bw TW.A_Cfg_sum_mode 4) = 4%nat)
    by (apply TWorldLemmas.length_sub; [unfold TW.A_Cfg_sum_mode, TW.OFF_g_cfg; lia|];
        rewrite FLB; unfold TW.A_Cfg_sum_mode, TW.OFF_g_cfg, TW.W_LEN; lia).
  pose proof (csf_rd_all m _ _ 4 MSM L4) as RMS.
  pose proof (TWorldLemmas.s32_range Bw TW.A_Cfg_sum_mode) as RMR.
  csf_pc.
  (* 0x84074 bne s1,a1 ; 0x84078 bnez a0 *)
  step. brP false ltac:(rewrite bv_eqb_refl; reflexivity).
  step. brF false.
  (* 0x8407c addi a0,s0,28 ; srli ; add ; lb a1 : the shadow byte of fp + 28 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 28) 28.
  step. step. brF false.
  (* 0x84090 lhu a1,0(a0) : f->sum *)
  pose proof (csf_rd m fp SB 28 2 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD28.
  step. clear RD28. rewrite lhu_world, F28.
  (* 0x84094 li a0,0 ; beqz a2 *)
  step. step.
  rewrite (PCSF.csf_eqb blen 0) by lia.
  destruct (Z.eqb_spec blen 0) as [E0|E0]; cbv iota.
  { (* no body: want = 0 *)
    eapply csf_end_F; [|reflexivity].
    f_equal. rewrite FSUM, E0. destruct (TW.Cfg_sum_mode Bw =? 1); reflexivity. }
  (* 0x8409c auipc a4 ; lw a4 : g_cfg.sum_mode ; li a5,1 ; beq a4,a5 *)
  step. step. clear RMS. rewrite lw_world.
  step. step.
  rewrite (PCSF.csf_eqb_sgn (TW.s32_at Bw TW.A_Cfg_sum_mode) 1) by lia.
  change (TW.s32_at Bw TW.A_Cfg_sum_mode) with (TW.Cfg_sum_mode Bw).
  destruct (Z.eqb_spec (TW.Cfg_sum_mode Bw) 1) as [E1|E1]; cbv iota.
  { (* the zero-sum mode: want = 0 *)
    eapply csf_end_F; [|reflexivity]. f_equal. rewrite FSUM. try rewrite (proj2 (Z.eqb_eq _ _) E1). reflexivity. }
  (* 0x840ac li a4,0 ; mv a0,a3 : the sum loop at j = 0 *)
  step. step.
  apply (csf_sum_F (Z.to_nat blen) 0); [lia | lia | exact E1 | f_equal; lia | f_equal; lia | f_equal; lia | reflexivity].
Qed.

(* 0x84028: the padding loop, j bytes checked (a0 = s2 = fa + blen + 30 + j, a4 = the count left, a5 = 1). *)
Lemma csf_pad_F : forall k j (x1 x5 x6 x7 x10 x14 x15 x16 x17 y2 x28 x29 x30 x31 : word),
  Z.of_nat k = Z.of_nat (length frame) - (30 + blen) - j -> 0 <= j < Z.of_nat (length frame) - (30 + blen) ->
  x10 = Z_to_bv 64 (fa + (blen + 30) + j) -> x14 = Z_to_bv 64 (Z.of_nat (length frame) - (30 + blen) - j) ->
  x15 = Z_to_bv 64 1 -> y2 = Z_to_bv 64 (fa + (blen + 30) + j) ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x1c0) x1 x5 x6 x7 x10 (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 blen)
        (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17 y2 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros j x1 x5 x6 x7 x10 x14 x15 x16 x17 y2 x28 x29 x30 x31 Hk Hj -> -> -> ->; [lia|].
  tail_prep.
  destruct (SHf (blen + 30 + j) ltac:(lia)) as (kb & Mk & Ck).
  pose proof (RSf (blen + 30 + j) ltac:(lia)) as Rk.
  replace (fa + (blen + 30 + j)) with (fa + (blen + 30) + j) in Mk, Ck, Rk by lia.
  pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
  pose proof (Z.mod_pos_bound (fa + (blen + 30) + j) 8 ltac:(lia)) as MB.
  pose proof (byte_signed_range kb) as KR.
  pose proof (FZ (blen + 30 + j) ltac:(lia)) as Z0.
  (* 0x84038: the load of frame[blen + 30 + j] and the bookkeeping *)
  assert (K : forall y16 y17 : word, ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x1d0) x1 x5 x6 x7 (Z_to_bv 64 (fa + (blen + 30) + j)) (Z_to_bv 64 (Z.of_nat (length frame)))
          (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 (Z.of_nat (length frame) - (30 + blen) - j))
          (Z_to_bv 64 1) y16 y17 (Z_to_bv 64 (fa + (blen + 30) + j)) x28 x29 x30 x31)).
  { intros y16 y17. csf_pc.
    pose proof (csf_rd m fa frame (blen + 30 + j) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_world, Z0.
    do 6 step.
    (* 0x84054 beqz a4 : the last byte, or on to j + 1 *)
    step.
    rewrite (PCSF.csf_eqb (Z.of_nat (length frame) - (30 + blen) - j + -1) 0) by lia.
    destruct (Z.eqb_spec (Z.of_nat (length frame) - (30 + blen) - j + -1) 0) as [E|E]; cbv iota.
    - (* 0x84070 seqz a0,a5 : every byte was 0 *)
      step.
      apply csf_k74_F; [vm_compute; reflexivity | reflexivity].
    - (* 0x84058 j 0x84028 *)
      step.
      apply (IH (j + 1)); [lia | lia | f_equal; lia | f_equal; lia | vm_compute; reflexivity | f_equal; lia]. }
  csf_pc.
  step. rewrite (csf_shr3 (fa + (blen + 30) + j)) by lia.
  step. step. step. rewrite sxb_eq0.
  destruct Ck as [C|C].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. apply K.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb].
    step. rewrite land7, (unsigned_lit (fa + (blen + 30) + j)) by lia.
    step. rewrite (lts_low ((fa + (blen + 30) + j) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbv iota.
    apply K.
Qed.

(* 0x83ff8: n = max (60, body_len + 30) in a1, then the padding loop when body_len + 30 < len. *)
Lemma csf_n_F : forall (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x190) x1 x5 x6 x7 x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17
        (Z_to_bv 64 fa) x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31.
  tail_prep.
  (* 0x8400c: the padding test, with a1 = n = len *)
  assert (K : forall (y11 y14 : word), y11 = Z_to_bv 64 (Z.of_nat (length frame)) ->
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x1a4) x1 x5 x6 x7 (Z_to_bv 64 (blen + 30)) y11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) y14
          x15 x16 x17 (Z_to_bv 64 fa) x28 x29 x30 x31)).
  { intros y11 y14 ->. csf_pc.
    step.
    rewrite (PCSF.csf_ltu (blen + 30) (Z.of_nat (length frame))) by lia.
    destruct (Z.ltb_spec (blen + 30) (Z.of_nat (length frame))) as [L|L]; cbn [negb]; cbv iota.
    - (* 0x84010: the padding loop's set-up (a4 = len - n, a0 = s2 = fa + n, a5 = 1) *)
      do 6 step.
      apply (csf_pad_F (Z.to_nat (Z.of_nat (length frame) - (30 + blen))) 0); [lia | lia | weq | weq | weq | weq].
    - (* 0x84068 li a0,0 ; j 0x84074 : no padding *)
      step. step.
      apply csf_k74_F; weq. }
  csf_pc.
  (* 0x83ff8 addi a0,a2,30 ; li a4,60 ; mv a1,a0 ; bltu a4,a0 *)
  step. step. step. step.
  rewrite (PCSF.csf_ltu 60 (blen + 30)) by lia.
  destruct (Z.ltb_spec 60 (blen + 30)) as [L|L]; cbv iota.
  - apply K. f_equal. lia.
  - step. apply K. f_equal. lia.
Qed.

(* 0x83f68: the system-family scan of the body (spec_system_at, inlined), at offset i (a0 = fa + 30 + i, a4 = i,
   a5 = fa + 31 + i, a6 = body_len - 3, a7 / t0 / t1 = 240 / 19 / 112). A hit (F0 13 xx 70) would go to the trap through
   `bgez a4` at 0x83ff4; the model's spec_system_at < 0 rules it out (lib/Prog/T/check_sent_frame.v csf_sys). *)
Lemma csf_scan_F : forall k i (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Z.of_nat k = blen - 3 - i -> 0 <= i < blen - 3 ->
  x5 = Z_to_bv 64 19 -> x6 = Z_to_bv 64 112 ->
  x10 = Z_to_bv 64 (fa + 30 + i) -> x14 = Z_to_bv 64 i -> x15 = Z_to_bv 64 (fa + 30 + i + 1) ->
  x16 = Z_to_bv 64 (blen - 3) -> x17 = Z_to_bv 64 240 ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x100) x1 x5 x6 x7 x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17
        (Z_to_bv 64 fa) x28 x29 x30 x31).
Proof.
  induction k as [|k IH];
    intros i x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi -> -> -> -> -> -> ->; [lia|].
  tail_prep.
  (* 0x83fb8: no hit at i; on to i + 1, or out of the scan *)
  assert (NEXT : forall y1 y7 y28 : word,
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x150) x1 (Z_to_bv 64 19) (Z_to_bv 64 112) y7 (Z_to_bv 64 (fa + 30 + i)) y1 (Z_to_bv 64 blen)
          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 i) (Z_to_bv 64 (fa + 30 + i + 1)) (Z_to_bv 64 (blen - 3))
          (Z_to_bv 64 240) (Z_to_bv 64 fa) y28 x29 x30 x31)).
  { intros y1 y7 y28. csf_pc.
    do 3 step. step.
    rewrite (PCSF.csf_eqb (blen - 3) (i + 1)) by lia.
    destruct (Z.eqb_spec (blen - 3) (i + 1)) as [E|E]; cbn [negb]; cbv iota.
    - step. apply csf_n_F.
    - apply (IH (i + 1)); [lia | lia | reflexivity | reflexivity | weq | weq | weq | reflexivity | reflexivity]. }
  pose proof (PCSF.csf_u1_range frame (30 + i)) as U0.
  pose proof (PCSF.csf_u1_range frame (30 + i + 1)) as U1.
  pose proof (PCSF.csf_u1_range frame (30 + i + 3)) as U3.
  (* 0x83fb0: the load of body[i + 3] and its compare with 112; a hit is impossible *)
  assert (K3 : TW.u_at frame (30 + i) 1 = 240 -> TW.u_at frame (30 + i + 1) 1 = 19 ->
    forall y1 y7 y28 : word,
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x148) x1 (Z_to_bv 64 19) (Z_to_bv 64 112) y7 (Z_to_bv 64 (fa + 30 + i)) y1 (Z_to_bv 64 blen)
          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 i) (Z_to_bv 64 (fa + 30 + i + 1)) (Z_to_bv 64 (blen - 3))
          (Z_to_bv 64 240) (Z_to_bv 64 fa) y28 x29 x30 x31)).
  { intros E0 E1 y1 y7 y28. csf_pc.
    pose proof (csf_rd m fa frame (30 + i + 3) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_world.
    step.
    rewrite (PCSF.csf_eqb (TW.u_at frame (30 + i + 3) 1) 112) by lia.
    destruct (Z.eqb_spec (TW.u_at frame (30 + i + 3) 1) 112) as [E3|E3]; cbv iota.
    - exfalso. apply (PCSF.csf_sys frame blen i FSYS); lia.
    - apply NEXT. }
  (* 0x83f94: the load of body[i + 1] and its compare with 19, then the check of body + i + 3 *)
  assert (K2 : TW.u_at frame (30 + i) 1 = 240 -> forall y7 y28 : word,
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x12c) x1 (Z_to_bv 64 19) (Z_to_bv 64 112) y7 (Z_to_bv 64 (fa + 30 + i)) (Z_to_bv 64 (fa + 30 + i + 1))
          (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 i) (Z_to_bv 64 (fa + 30 + i + 1))
          (Z_to_bv 64 (blen - 3)) (Z_to_bv 64 240) (Z_to_bv 64 fa) y28 x29 x30 x31)).
  { intros E0 y7 y28. csf_pc. unfold ASAN_K.
    pose proof (csf_rd m fa frame (30 + i + 1) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_world.
    step.
    rewrite (PCSF.csf_eqb (TW.u_at frame (30 + i + 1) 1) 19) by lia.
    destruct (Z.eqb_spec (TW.u_at frame (30 + i + 1) 1) 19) as [E1|E1]; cbn [negb]; cbv iota; [|apply NEXT].
    (* 0x83f9c addi a1,a0,3 ; srli t2,a1,3 ; add t2,t2,s3 ; lb t2 ; bnez t2 *)
    destruct (SHf (30 + i + 3) ltac:(lia)) as (kb & Mk & Ck).
    pose proof (RSf (30 + i + 3) ltac:(lia)) as Rk.
    replace (fa + (30 + i + 3)) with (fa + 30 + i + 3) in Mk, Ck, Rk by lia.
    pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
    pose proof (Z.mod_pos_bound (fa + 30 + i + 3) 8 ltac:(lia)) as MB.
    pose proof (byte_signed_range kb) as KR.
    step. step. rewrite (csf_shr3 (fa + 30 + i + 3)) by lia.
    step. step. step. rewrite sxb_eq0.
    destruct Ck as [C|C].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply (K3 E0 E1).
    - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
      step. rewrite land7, (unsigned_lit (fa + 30 + i + 3)) by lia.
      step. rewrite (lts_low ((fa + 30 + i + 3) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbv iota.
      apply (K3 E0 E1). }
  (* 0x83f78: the load of body[i] and its compare with 240, then the check of body + i + 1 *)
  assert (K1 : forall y1 y7 : word,
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x110) x1 (Z_to_bv 64 19) (Z_to_bv 64 112) y7 (Z_to_bv 64 (fa + 30 + i)) y1 (Z_to_bv 64 blen)
          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 i) (Z_to_bv 64 (fa + 30 + i + 1)) (Z_to_bv 64 (blen - 3))
          (Z_to_bv 64 240) (Z_to_bv 64 fa) x28 x29 x30 x31)).
  { intros y1 y7. csf_pc. unfold ASAN_K.
    pose proof (csf_rd m fa frame (30 + i) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_world.
    step.
    rewrite (PCSF.csf_eqb (TW.u_at frame (30 + i) 1) 240) by lia.
    destruct (Z.eqb_spec (TW.u_at frame (30 + i) 1) 240) as [E0|E0]; cbn [negb]; cbv iota; [|apply NEXT].
    (* 0x83f80 addi a1,a0,1 ; srli t2,a1,3 ; add t2,t2,s3 ; lb t2 ; bnez t2 *)
    destruct (SHf (30 + i + 1) ltac:(lia)) as (kb & Mk & Ck).
    pose proof (RSf (30 + i + 1) ltac:(lia)) as Rk.
    replace (fa + (30 + i + 1)) with (fa + 30 + i + 1) in Mk, Ck, Rk by lia.
    pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
    pose proof (Z.mod_pos_bound (fa + 30 + i + 1) 8 ltac:(lia)) as MB.
    pose proof (byte_signed_range kb) as KR.
    step. step. rewrite (csf_shr3 (fa + 30 + i + 1)) by lia.
    step. step. step. rewrite sxb_eq0.
    destruct Ck as [C|C].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply (K2 E0).
    - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
      step. rewrite land7, (unsigned_lit (fa + 30 + i + 1)) by lia.
      step. rewrite (lts_low ((fa + 30 + i + 1) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply (K2 E0). }
  (* 0x83f68 srli a1,a0,3 ; add a1,a1,s3 ; lb a1 ; bnez a1 : the check of body + i *)
  destruct (SHf (30 + i) ltac:(lia)) as (kb & Mk & Ck).
  pose proof (RSf (30 + i) ltac:(lia)) as Rk.
  replace (fa + (30 + i)) with (fa + 30 + i) in Mk, Ck, Rk by lia.
  pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
  pose proof (Z.mod_pos_bound (fa + 30 + i) 8 ltac:(lia)) as MB.
  pose proof (byte_signed_range kb) as KR.
  csf_pc.
  step. rewrite (csf_shr3 (fa + 30 + i)) by lia.
  step. step. step. rewrite sxb_eq0.
  destruct Ck as [C|C].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply K1.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
    step. rewrite land7, (unsigned_lit (fa + 30 + i)) by lia.
    step. rewrite (lts_low ((fa + 30 + i) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
    step. apply K1.
Qed.

(* 0x83f10: from the second bcmp's return (a0 = 0) to the `ret`: the checks of fp + 48 and fp + 56, body_len and
   body, the scan when body_len >= 4, then n, the padding, the sum. *)
Lemma csf_ret2_F : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0xa8) x1 x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fa) x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  tail_prep.
  csf_pc.
  (* 0x83f10 bnez a0 *)
  step. brF false.
  (* 0x83f14 addi a0,s0,48 ; srli ; add ; lbu a1 : the shadow byte of fp + 48 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 48) 48.
  step. step. brF false.
  (* 0x83f28 addi a0,s0,56 ; srli ; add ; lbu a1 : the shadow byte of fp + 56 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 56) 56.
  step. step. brF false.
  (* 0x83f3c ld a2,0(a0) : f->body_len ; ld a3,48(s0) : f->body *)
  pose proof (csf_rd m fp SB 56 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD56.
  step. clear RD56. rewrite ld_world, F56.
  pose proof (csf_rd m fp SB 48 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD48.
  step. clear RD48. rewrite ld_world, F48.
  (* 0x83f44 li a0,4 ; bltu a2,a0 *)
  step. step.
  rewrite (PCSF.csf_ltu blen 4) by lia.
  destruct (Z.ltb_spec blen 4) as [L4|L4]; cbv iota.
  - apply csf_n_F.
  - (* 0x83f4c: the scan's set-up *)
    do 7 step.
    apply (csf_scan_F (Z.to_nat (blen - 3)) 0); [lia | lia | weq | weq | weq | weq | weq | weq | weq].
Qed.

End Tail.
