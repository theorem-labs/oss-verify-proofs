(* check_sent_frame_seg_tail: the footprint runs (lib/Lib/ExecF.v evtF) of check_sent_frame in image B
   (fuzz_transport.asan-ubsan, entry 0x84080) from the second bcmp call's return (0x84130) to the `ret` at 0x84380, each
   from one cut point of the code to the post csf_ret_post of lib/B/Prog/check_sent_frame_seg_defs.v (ra, s0 .. s3
   reloaded from the frame, sp given back, the memory unchanged). Image B's twin of
   lib/A/Prog/check_sent_frame_seg_tail.v:
     csf_ret2_F  0x84130: the checks of fp + 48 and fp + 56, body = fa + 30 and body_len, the scan when body_len >= 4;
     csf_scan_F  0x84188: the inlined spec_system_at, by induction on the turns left; a hit would reach the trap
                 (`bgez t4` at 0x84230), which the model's spec_system_at < 0 rules out;
     csf_n_F     0x84234: n = max (60, body_len + 30), and the padding loop when n < len;
     csf_pad_F   0x84268: the padding loop, every byte 0 (a4 stays 1);
     csf_k74_F   0x842c8: len = n, no padding byte set, the check and the load of f->sum, the mode test;
     csf_sum_F   0x84310: the body sum loop (the plain walk's csum);
     csf_end_F   0x84364: f->sum = want, the epilogue and the `ret`.
   csf_tail_all is the statement csf_tail_stmt of seg_defs.
   What the ubsan build adds to image A's code: the pointer checks of the scan, the padding loop and the sum loop
   (`bltu p,base`, `seqz; xor; beqz`, `beqz base` go to the unimp word at 0x84384; the pointers are at or above their
   base, not 0 and below 2^63) and the scan's index checks (`bgeu i,~body`, `bltu ~body,i + 3`). Every byte check passes:
   the struct's granules have shadow 0, and every frame byte's shadow byte k is 0 or above the byte's offset in its
   granule (csf_mem), so `bge (a mod 8),k` never goes to its report call and `blt (a mod 8),k` always goes back. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require check_sent_frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_seg_defs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

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

(* A register value Z_to_bv 64 x of the goal, rewritten to Z_to_bv 64 e when x = e is a ring identity; nothing when
   Z_to_bv 64 e is in the goal already. *)
Ltac zc e :=
  lazymatch goal with
  | |- context [Z_to_bv 64 e] => idtac
  | _ => match goal with
         | |- context [Z_to_bv 64 ?x] =>
             let ZC := fresh "ZC" in
             assert (ZC : x = e) by ring; rewrite ZC; clear ZC
         end
  end.

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
(* The scan's registers at offset i: t0 / t1 / t2 = 240 / 19 / 112, a2 = body_len, a3 = body = fa + 30,
   a4 = 2^64 - 1 - body, a5 = body + 1, a6 = i + 3, a7 = 1, s2 = fa. *)
Local Abbreviation SCAN pc i x1 x10 x11 x28 x29 x30 x31 :=
  (ST pc x1 (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30))
      (Z_to_bv 64 (18446744073709551615 - (fa + 30))) (Z_to_bv 64 (fa + 31)) (Z_to_bv 64 (i + 3)) (Z_to_bv 64 1)
      (Z_to_bv 64 fa) x28 x29 x30 x31).

(* 0x84364: f->sum against the sum the code computed (a1, a0), then the epilogue and the `ret`. *)
Lemma csf_end_F : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31 : word),
  x10 = Z_to_bv 64 sum -> x11 = Z_to_bv 64 sum ->
  ExecF.evtF rsegs RNG RET (ST (CSF_AT 0x2e4) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 x28 x29 x30 x31 -> ->.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ STK) as L0.
  pose proof FRM as FR. pose proof STK as ST. unfold csf_fr in FR.
  pose proof FX as (_ & _ & _ & _ & _ & _ & F28 & _).
  pose proof (TWorldLemmas.u_at_range SB 28 2) as RS. rewrite F28 in RS. change (2 ^ (8 * Z.of_nat 2)) with 65536 in RS.
  pose proof RNGH as (RFR & _).
  csf_pc.
  (* 0x84364 bne a0,a1 *)
  step. brP false ltac:(rewrite bv_eqb_refl; reflexivity).
  (* 0x84368 .. 0x84380: ld ra, s0 .. s3 ; addi sp,sp,48 ; ret *)
  do 7 step.
  apply evtF_done. unfold csf_ret_post. do 16 eexists. split; [reflexivity|]. split.
  { rewrite ?unsigned_lit_wrap. Z.div_mod_to_equations. lia. }
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

(* 0x84310: the body sum loop, j bytes added (a0 = a6 = fa + 30 + j, a2 = blen - j, a4 = the sum so far, a5 = 1). *)
Lemma csf_sum_F : forall k j (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 y2 x28 x29 x30 x31 : word),
  Z.of_nat k = blen - j -> 0 <= j < blen -> TW.Cfg_sum_mode Bw <> 1 ->
  x10 = Z_to_bv 64 (fa + 30 + j) -> x12 = Z_to_bv 64 (blen - j) ->
  x14 = Z_to_bv 64 (PCSF.csum frame 30 (Z.to_nat j)) -> x15 = Z_to_bv 64 1 -> x16 = Z_to_bv 64 (fa + 30 + j) ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x290) x1 x5 x6 x7 x10 (Z_to_bv 64 sum) x12 (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17 y2
        x28 x29 x30 x31).
Proof.
  induction k as [|k IH];
    intros j x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 y2 x28 x29 x30 x31 Hk Hj HM -> -> -> -> ->; [lia|].
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
  (* 0x84334: the load of body[j] and the bookkeeping *)
  assert (K : forall y5 y17 : word,
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x2b4) x1 y5 x6 x7 (Z_to_bv 64 (fa + 30 + j)) (Z_to_bv 64 sum) (Z_to_bv 64 (blen - j))
          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 (PCSF.csum frame 30 (Z.to_nat j))) (Z_to_bv 64 1)
          (Z_to_bv 64 (fa + 30 + j)) y17 y2 x28 x29 x30 x31)).
  { intros y5 y17. csf_pc.
    pose proof (csf_rd m fa frame (30 + j) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    (* 0x84334 lbu a7,0(a6) *)
    step. clear RD. rewrite lbu_world.
    (* 0x84338 addi a2,a2,-1 ; addi a0,a0,1 ; add a4,a4,a7 ; addi a6,a6,1 ; bnez a2 *)
    do 5 step.
    rewrite (PCSF.csf_eqb (blen - j + -1) 0) by lia.
    destruct (Z.eqb_spec (blen - j + -1) 0) as [E|E]; cbn [negb]; cbv iota.
    - (* the last byte: 0x8434c j 0x8435c ; slli a0,a4,48 ; srli a0,a0,48 *)
      step. step. step.
      eapply csf_end_F; [|reflexivity].
      rewrite PCSF.csf_shift by lia. f_equal. rewrite HS. f_equal.
      replace (Z.to_nat blen) with (S (Z.to_nat j)) by lia. cbn [PCSF.csum]. rewrite Z2Nat.id by lia. reflexivity.
    - apply (IH (j + 1)); [lia | lia | exact HM | f_equal; lia | f_equal; lia | | reflexivity | f_equal; lia].
      f_equal. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. cbn [PCSF.csum].
      rewrite Z2Nat.id by lia. reflexivity. }
  csf_pc.
  (* 0x84310 bltu a0,a3 : body + j >= body, not to the unimp word *)
  step. brP false ltac:(rewrite PCSF.csf_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x84314 seqz a7,a0 ; xor a7,a5,a7 ; beqz a7 : body + j is not 0 *)
  step. step. step. brP false ltac:(rewrite csf_seqz_pos by lia; reflexivity).
  (* 0x84320 beqz a3 : body is not 0 *)
  step. brP false ltac:(rewrite PCSF.csf_eqb by lia; apply Z.eqb_neq; lia).
  (* 0x84324 srli a7,a0,3 ; add a7,a7,s3 ; lb a7 ; bnez a7 : the check of body + j *)
  step. rewrite (csf_shr3 (fa + 30 + j)) by lia.
  step. step. step. rewrite sxb_eq0.
  destruct Ck as [C|C].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply K.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
    (* 0x84350 andi t0,a0,7 ; 0x84354 blt t0,a7 *)
    step. rewrite land7, (unsigned_lit (fa + 30 + j)) by lia.
    step. rewrite (lts_low ((fa + 30 + j) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbv iota.
    apply K.
Qed.

(* 0x842c8: len against n (a1), the padding verdict (a0), then f->sum, the mode and the sum loop. *)
Lemma csf_k74_F : forall (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 y2 x28 x29 x30 x31 : word),
  x10 = Z_to_bv 64 0 -> x11 = Z_to_bv 64 (Z.of_nat (length frame)) ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x248) x1 x5 x6 x7 x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17 y2
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
  (* 0x842c8 bne s1,a1 ; 0x842cc bnez a0 *)
  step. brP false ltac:(rewrite bv_eqb_refl; reflexivity).
  step. brF false.
  (* 0x842d0 addi a0,s0,28 ; srli ; add ; lb a1 : the shadow byte of fp + 28 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 28) 28.
  step. step. brF false.
  (* 0x842e4 lhu a1,0(a0) : f->sum *)
  pose proof (csf_rd m fp SB 28 2 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD28.
  step. clear RD28. rewrite lhu_world, F28.
  (* 0x842e8 mv a0,zero ; beqz a2 *)
  step. step.
  rewrite (PCSF.csf_eqb blen 0) by lia.
  destruct (Z.eqb_spec blen 0) as [E0|E0]; cbv iota.
  { (* no body: want = 0 *)
    eapply csf_end_F; [|reflexivity].
    f_equal. rewrite FSUM, E0. destruct (TW.Cfg_sum_mode Bw =? 1); reflexivity. }
  (* 0x842f0 auipc a4 ; lw a4 : g_cfg.sum_mode ; li a5,1 ; beq a4,a5 *)
  step. step. clear RMS. rewrite lw_world.
  step. step.
  rewrite (PCSF.csf_eqb_sgn (TW.s32_at Bw TW.A_Cfg_sum_mode) 1) by lia.
  change (TW.s32_at Bw TW.A_Cfg_sum_mode) with (TW.Cfg_sum_mode Bw).
  destruct (Z.eqb_spec (TW.Cfg_sum_mode Bw) 1) as [E1|E1]; cbv iota.
  { (* the zero-sum mode: want = 0 *)
    eapply csf_end_F; [|reflexivity]. f_equal. rewrite FSUM. try rewrite (proj2 (Z.eqb_eq _ _) E1). reflexivity. }
  (* 0x84300 mv a4,zero ; snez a5,a3 ; mv a6,a3 ; mv a0,a3 : the sum loop at j = 0 *)
  do 4 step.
  apply (csf_sum_F (Z.to_nat blen) 0);
    [ lia | lia | exact E1 | weq | weq | reflexivity | (rewrite csf_snez_pos by lia; reflexivity) | weq ].
Qed.

(* 0x84268: the padding loop, j bytes checked (a0 = a5 = fa + blen + 30 + j, a6 = the count left, a4 = 1, a7 = 1). *)
Lemma csf_pad_F : forall k j (x1 x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Z.of_nat k = Z.of_nat (length frame) - (30 + blen) - j -> 0 <= j < Z.of_nat (length frame) - (30 + blen) ->
  x10 = Z_to_bv 64 (fa + (blen + 30) + j) -> x14 = Z_to_bv 64 1 ->
  x15 = Z_to_bv 64 (fa + (blen + 30) + j) -> x16 = Z_to_bv 64 (Z.of_nat (length frame) - (30 + blen) - j) ->
  x17 = Z_to_bv 64 1 ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x1e8) x1 x5 x6 x7 x10 (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 blen)
        (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17 (Z_to_bv 64 fa) x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros j x1 x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hj -> -> -> -> ->; [lia|].
  tail_prep.
  destruct (SHf (blen + 30 + j) ltac:(lia)) as (kb & Mk & Ck).
  pose proof (RSf (blen + 30 + j) ltac:(lia)) as Rk.
  replace (fa + (blen + 30 + j)) with (fa + (blen + 30) + j) in Mk, Ck, Rk by lia.
  pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
  pose proof (Z.mod_pos_bound (fa + (blen + 30) + j) 8 ltac:(lia)) as MB.
  pose proof (byte_signed_range kb) as KR.
  pose proof (FZ (blen + 30 + j) ltac:(lia)) as Z0.
  (* 0x8428c: the load of frame[blen + 30 + j] and the bookkeeping *)
  assert (K : forall y5 y6 : word, ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x20c) x1 y5 y6 x7 (Z_to_bv 64 (fa + (blen + 30) + j)) (Z_to_bv 64 (Z.of_nat (length frame)))
          (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 1) (Z_to_bv 64 (fa + (blen + 30) + j))
          (Z_to_bv 64 (Z.of_nat (length frame) - (30 + blen) - j)) (Z_to_bv 64 1) (Z_to_bv 64 fa)
          x28 x29 x30 x31)).
  { intros y5 y6. csf_pc.
    pose proof (csf_rd m fa frame (blen + 30 + j) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    (* 0x8428c lbu t0,0(a5) *)
    step. clear RD. rewrite lbu_world, Z0.
    (* 0x84290 addi a6,a6,-1 ; addi a0,a0,1 ; snez t0,t0 ; addiw t0,t0,-1 ; and a4,t0,a4 ; addi a5,a5,1 ;
       beqz a6 : the last byte, or on to j + 1 *)
    do 7 step.
    rewrite (PCSF.csf_eqb (Z.of_nat (length frame) - (30 + blen) - j + -1) 0) by lia.
    destruct (Z.eqb_spec (Z.of_nat (length frame) - (30 + blen) - j + -1) 0) as [E|E]; cbv iota.
    - (* 0x842c4 seqz a0,a4 : every byte was 0 *)
      step.
      apply csf_k74_F; [vm_compute; reflexivity | reflexivity].
    - (* 0x842ac j 0x84268 *)
      step.
      apply (IH (j + 1)); [lia | lia | weq | vm_compute; reflexivity | weq | weq | reflexivity]. }
  csf_pc.
  (* 0x84268 bltu a0,s2 : the pointer is not below fa *)
  step. brP false ltac:(rewrite PCSF.csf_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x8426c seqz t0,a0 ; xor t0,a7,t0 ; beqz t0 : the pointer is not 0 *)
  step. step. step. brP false ltac:(rewrite csf_seqz_pos by lia; reflexivity).
  (* 0x84278 beqz s2 : fa is not 0 *)
  step. brP false ltac:(rewrite PCSF.csf_eqb by lia; apply Z.eqb_neq; lia).
  (* 0x8427c srli t0,a0,3 ; add t0,t0,s3 ; lb t0 ; bnez t0 : the check of frame + blen + 30 + j *)
  step. rewrite (csf_shr3 (fa + (blen + 30) + j)) by lia.
  step. step. step. rewrite sxb_eq0.
  destruct Ck as [C|C].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply K.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
    (* 0x842b0 andi t1,a0,7 ; 0x842b4 blt t1,t0 *)
    step. rewrite land7, (unsigned_lit (fa + (blen + 30) + j)) by lia.
    step. rewrite (lts_low ((fa + (blen + 30) + j) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbv iota.
    apply K.
Qed.

(* 0x84234: n = max (60, body_len + 30) in a1, then the padding loop when body_len + 30 < len. *)
Lemma csf_n_F : forall (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x1b4) x1 x5 x6 x7 x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17
        (Z_to_bv 64 fa) x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31.
  tail_prep.
  (* 0x84248: the padding test, with a1 = n = len and a5 = body_len + 30 *)
  assert (K : forall (y10 y11 : word), y11 = Z_to_bv 64 (Z.of_nat (length frame)) ->
    ExecF.evtF rsegs RNG RET
      (ST (CSF_AT 0x1c8) x1 x5 x6 x7 y10 y11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) x14 (Z_to_bv 64 (blen + 30))
          x16 x17 (Z_to_bv 64 fa) x28 x29 x30 x31)).
  { intros y10 y11 ->. csf_pc.
    (* 0x84248 bgeu a5,s1 *)
    step.
    rewrite (PCSF.csf_ltu (blen + 30) (Z.of_nat (length frame))) by lia.
    destruct (Z.ltb_spec (blen + 30) (Z.of_nat (length frame))) as [L|L]; cbn [negb]; cbv iota.
    - (* 0x8424c: the padding loop's set-up (a6 = len - n, a0 = a5 = fa + n, a4 = 1, a7 = snez fa) *)
      do 7 step.
      apply (csf_pad_F (Z.to_nat (Z.of_nat (length frame) - (30 + blen))) 0);
        [ lia | lia | weq | weq | weq | weq | (rewrite csf_snez_pos by lia; reflexivity) ].
    - (* 0x842bc mv a0,zero ; j 0x842c8 : no padding *)
      step. step.
      apply csf_k74_F; weq. }
  csf_pc.
  (* 0x84234 addi a5,a2,30 ; li a0,60 ; mv a1,a5 ; bltu a0,a5 *)
  step. step. step. step.
  rewrite (PCSF.csf_ltu 60 (blen + 30)) by lia.
  destruct (Z.ltb_spec 60 (blen + 30)) as [L|L]; cbv iota.
  - apply K. f_equal. lia.
  - (* 0x84244 li a1,60 *)
    step. apply K. f_equal. lia.
Qed.

(* 0x84188: the system-family scan of the body (spec_system_at, inlined), at offset i (a6 = i + 3; a0 = body + i + 3
   and a1 = body + i are set at the top). A hit (F0 13 xx 70) would go to the trap through `bgez t4` at 0x84230; the
   model's spec_system_at < 0 rules it out (lib/Prog/T/check_sent_frame.v csf_sys). *)
Lemma csf_scan_F : forall k i (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Z.of_nat k = blen - 3 - i -> 0 <= i < blen - 3 ->
  x5 = Z_to_bv 64 240 -> x6 = Z_to_bv 64 19 -> x7 = Z_to_bv 64 112 ->
  x14 = Z_to_bv 64 (18446744073709551615 - (fa + 30)) -> x15 = Z_to_bv 64 (fa + 31) ->
  x16 = Z_to_bv 64 (i + 3) -> x17 = Z_to_bv 64 1 ->
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0x108) x1 x5 x6 x7 x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 (fa + 30)) x14 x15 x16 x17
        (Z_to_bv 64 fa) x28 x29 x30 x31).
Proof.
  induction k as [|k IH];
    intros i x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi -> -> -> -> -> -> ->; [lia|].
  tail_prep.
  (* 0x84200: no hit at i; on to i + 1, or out of the scan *)
  assert (NEXT : forall y10 y11 y28 y29 y30 y31 : word,
    ExecF.evtF rsegs RNG RET (SCAN (CSF_AT 0x180) i x1 y10 y11 y28 y29 y30 y31)).
  { intros y10 y11 y28 y29 y30 y31. csf_pc.
    (* 0x84200 addi a6,a6,1 ; 0x84204 bne a2,a6 *)
    step. step.
    rewrite (PCSF.csf_eqb blen (i + 4)) by lia.
    destruct (Z.eqb_spec blen (i + 4)) as [E|E]; cbn [negb]; cbv iota.
    - (* 0x84208 j 0x84234 *)
      step. apply csf_n_F.
    - apply (IH (i + 1));
        [lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | weq | reflexivity]. }
  pose proof (PCSF.csf_u1_range frame (30 + i)) as U0.
  pose proof (PCSF.csf_u1_range frame (30 + i + 1)) as U1.
  pose proof (PCSF.csf_u1_range frame (30 + i + 3)) as U3.
  (* 0x841f8: the load of body[i + 3] and its compare with 112; a hit is impossible *)
  assert (K3 : TW.u_at frame (30 + i) 1 = 240 -> TW.u_at frame (30 + i + 1) 1 = 19 ->
    forall y10 y11 y29 y30 y31 : word,
    ExecF.evtF rsegs RNG RET (SCAN (CSF_AT 0x178) i x1 y10 y11 (Z_to_bv 64 (fa + 30 + i + 4)) y29 y30 y31)).
  { intros E0 E1 y10 y11 y29 y30 y31. csf_pc.
    pose proof (csf_rd m fa frame (30 + i + 3) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    (* 0x841f8 lbu a0,-1(t3) *)
    step. clear RD. rewrite lbu_world.
    (* 0x841fc beq a0,t2 *)
    step.
    rewrite (PCSF.csf_eqb (TW.u_at frame (30 + i + 3) 1) 112) by lia.
    destruct (Z.eqb_spec (TW.u_at frame (30 + i + 3) 1) 112) as [E3|E3]; cbv iota.
    - exfalso. apply (PCSF.csf_sys frame blen i FSYS); lia.
    - apply NEXT. }
  (* 0x841dc: the load of body[i + 1] and its compare with 19, the index check, then the check of body + i + 3 *)
  assert (K2 : TW.u_at frame (30 + i) 1 = 240 -> forall y11 y29 y30 y31 : word,
    ExecF.evtF rsegs RNG RET
      (SCAN (CSF_AT 0x15c) i x1 (Z_to_bv 64 (fa + 30 + i + 3)) y11 (Z_to_bv 64 (fa + 30 + i + 4)) y29 y30 y31)).
  { intros E0 y11 y29 y30 y31. csf_pc. unfold ASAN_K.
    pose proof (csf_rd m fa frame (30 + i + 1) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    (* 0x841dc lbu a1,-3(t3) *)
    step. clear RD. rewrite lbu_world.
    (* 0x841e0 bne a1,t1 *)
    step.
    rewrite (PCSF.csf_eqb (TW.u_at frame (30 + i + 1) 1) 19) by lia.
    destruct (Z.eqb_spec (TW.u_at frame (30 + i + 1) 1) 19) as [E1|E1]; cbn [negb]; cbv iota; [|apply NEXT].
    (* 0x841e4 bltu a4,a6 : i + 3 <= 2^64 - 1 - body, not to the unimp word *)
    step. brP false ltac:(rewrite PCSF.csf_ltu by lia; apply Z.ltb_ge; lia).
    (* 0x841e8 srli a1,a0,3 ; add a1,a1,s3 ; lb a1 ; bnez a1 : the check of body + i + 3 *)
    destruct (SHf (30 + i + 3) ltac:(lia)) as (kb & Mk & Ck).
    pose proof (RSf (30 + i + 3) ltac:(lia)) as Rk.
    replace (fa + (30 + i + 3)) with (fa + 30 + i + 3) in Mk, Ck, Rk by lia.
    pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
    pose proof (Z.mod_pos_bound (fa + 30 + i + 3) 8 ltac:(lia)) as MB.
    pose proof (byte_signed_range kb) as KR.
    step. rewrite (csf_shr3 (fa + 30 + i + 3)) by lia.
    step. step. step. rewrite sxb_eq0.
    destruct Ck as [C|C].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply (K3 E0 E1).
    - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x84224 andi t5,a0,7 ; 0x84228 blt t5,a1 *)
      step. rewrite land7, (unsigned_lit (fa + 30 + i + 3)) by lia.
      step. rewrite (lts_low ((fa + 30 + i + 3) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbv iota.
      apply (K3 E0 E1). }
  (* 0x841b4: t3 = body + i + 4, the load of body[i] and its compare with 240, the index check, then the check of
     body + i + 1 *)
  assert (K1 : forall y11 y28 y29 y30 y31 : word,
    ExecF.evtF rsegs RNG RET (SCAN (CSF_AT 0x134) i x1 (Z_to_bv 64 (fa + 30 + i + 3)) y11 y28 y29 y30 y31)).
  { intros y11 y28 y29 y30 y31. csf_pc. unfold ASAN_K.
    (* 0x841b4 add t3,a5,a6 *)
    step. zc (fa + 30 + i + 4).
    pose proof (csf_rd m fa frame (30 + i) 1 MFR ltac:(lia) ltac:(lia)) as RD.
    (* 0x841b8 lbu a1,-4(t3) *)
    step. clear RD. rewrite lbu_world.
    (* 0x841bc bne a1,t0 *)
    step.
    rewrite (PCSF.csf_eqb (TW.u_at frame (30 + i) 1) 240) by lia.
    destruct (Z.eqb_spec (TW.u_at frame (30 + i) 1) 240) as [E0|E0]; cbn [negb]; cbv iota; [|apply NEXT].
    (* 0x841c0 addi t4,a6,-3 ; 0x841c4 bgeu t4,a4 : i < 2^64 - 1 - body, not to the unimp word *)
    step. step. brP false ltac:(rewrite PCSF.csf_ltu by lia; apply negb_false_iff, Z.ltb_lt; lia).
    (* 0x841c8 addi a1,a0,-2 ; srli t5,a1,3 ; add t5,t5,s3 ; lb t5 ; bnez t5 : the check of body + i + 1 *)
    step. zc (fa + 30 + i + 1).
    destruct (SHf (30 + i + 1) ltac:(lia)) as (kb & Mk & Ck).
    pose proof (RSf (30 + i + 1) ltac:(lia)) as Rk.
    replace (fa + (30 + i + 1)) with (fa + 30 + i + 1) in Mk, Ck, Rk by lia.
    pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
    pose proof (Z.mod_pos_bound (fa + 30 + i + 1) 8 ltac:(lia)) as MB.
    pose proof (byte_signed_range kb) as KR.
    step. rewrite (csf_shr3 (fa + 30 + i + 1)) by lia.
    step. step. step. rewrite sxb_eq0.
    destruct Ck as [C|C].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply (K2 E0).
    - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x84218 andi t6,a1,7 ; 0x8421c bge t6,t5 ; 0x84220 j 0x841dc *)
      step. rewrite land7, (unsigned_lit (fa + 30 + i + 1)) by lia.
      step. rewrite (lts_low ((fa + 30 + i + 1) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply (K2 E0). }
  (* 0x84188 add a0,a3,a6 ; 0x8418c addi a1,a0,-3 *)
  csf_pc.
  step. step. zc (fa + 30 + i + 3). zc (fa + 30 + i).
  (* 0x84190 bltu a1,a3 : body + i >= body, not to the unimp word *)
  step. brP false ltac:(rewrite PCSF.csf_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x84194 seqz t3,a1 ; xor t3,a7,t3 ; beqz t3 : body + i is not 0 *)
  step. step. step. brP false ltac:(rewrite csf_seqz_pos by lia; reflexivity).
  (* 0x841a0 beqz a3 : body is not 0 *)
  step. brP false ltac:(rewrite PCSF.csf_eqb by lia; apply Z.eqb_neq; lia).
  (* 0x841a4 srli t3,a1,3 ; add t3,t3,s3 ; lb t3 ; bnez t3 : the check of body + i *)
  destruct (SHf (30 + i) ltac:(lia)) as (kb & Mk & Ck).
  pose proof (RSf (30 + i) ltac:(lia)) as Rk.
  replace (fa + (30 + i)) with (fa + 30 + i) in Mk, Ck, Rk by lia.
  pose proof (rd1 _ _ _ Mk) as HRk. clear Mk.
  pose proof (Z.mod_pos_bound (fa + 30 + i) 8 ltac:(lia)) as MB.
  pose proof (byte_signed_range kb) as KR.
  step. rewrite (csf_shr3 (fa + 30 + i)) by lia.
  step. step. step. rewrite sxb_eq0.
  destruct Ck as [C|C].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply K1.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)). cbn [negb]. cbv iota.
    (* 0x8420c andi t4,a1,7 ; 0x84210 bge t4,t3 ; 0x84214 j 0x841b4 *)
    step. rewrite land7, (unsigned_lit (fa + 30 + i)) by lia.
    step. rewrite (lts_low ((fa + 30 + i) mod 8) kb MB), (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
    step. apply K1.
Qed.

(* 0x84130: from the second bcmp's return (a0 = 0) to the `ret`: the checks of fp + 48 and fp + 56, body_len and
   body, the scan when body_len >= 4, then n, the padding, the sum. *)
Lemma csf_ret2_F : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ExecF.evtF rsegs RNG RET
    (ST (CSF_AT 0xb0) x1 x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fa) x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  tail_prep.
  csf_pc.
  (* 0x84130 bnez a0 *)
  step. brF false.
  (* 0x84134 addi a0,s0,48 ; srli ; add ; lbu a1 : the shadow byte of fp + 48 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 48) 48.
  step. step. brF false.
  (* 0x84148 addi a0,s0,56 ; srli ; add ; lbu a1 : the shadow byte of fp + 56 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 56) 56.
  step. step. brF false.
  (* 0x8415c ld a2,0(a0) : f->body_len ; ld a3,48(s0) : f->body *)
  pose proof (csf_rd m fp SB 56 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD56.
  step. clear RD56. rewrite ld_world, F56.
  pose proof (csf_rd m fp SB 48 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD48.
  step. clear RD48. rewrite ld_world, F48.
  (* 0x84164 li a0,4 ; bltu a2,a0 *)
  step. step.
  rewrite (PCSF.csf_ltu blen 4) by lia.
  destruct (Z.ltb_spec blen 4) as [L4|L4]; cbv iota.
  - apply csf_n_F.
  - (* 0x8416c: the scan's set-up: not a4,a3 ; addi a5,a3,1 ; li a6,3 ; snez a7,a3 ; li t0,240 ; li t1,19 ;
       li t2,112 *)
    do 7 step.
    apply (csf_scan_F (Z.to_nat (blen - 3)) 0);
      [ lia | lia | weq | weq | weq | (rewrite csf_not by lia; reflexivity) | weq | weq
      | (rewrite csf_snez_pos by lia; reflexivity) ].
Qed.

End Tail.

(* From the second bcmp's return (a0 = 0) to the `ret`. *)
Lemma csf_tail_all : csf_tail_stmt.
Proof.
  unfold csf_tail_stmt.
  intros RNG sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 cs0 cs1 cs2 cs3 cra F fc m lo junk fa fp blen sum frame SB Bw
    MEM RNGH BND FX STK HLO FRM.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  eapply csf_ret2_F;
    lazymatch goal with
    | |- csf_mem _ _ _ _ _ _ => exact MEM
    | |- csf_rng _ _ _ _ _ => exact RNGH
    | |- csf_bnd _ _ _ => exact BND
    | |- csf_fx _ _ _ _ _ _ => exact FX
    | |- stk _ _ _ _ => exact STK
    | |- rw_cells _ _ _ _ => exact FRM
    | |- _ <= _ => exact HLO
    end.
Qed.
