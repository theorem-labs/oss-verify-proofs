(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_egress: the harness-body walk of LLVMFuzzerTestOneInput on the UBSan image
   (fuzz_egress.ubsan: entry 0x12c6c, frame 0xa0, memset 0x1b4b4, memcpy 0x1b0b0, malloc 0x14240,
   check_restamp 0x12e58, check_mute 0x12f50, check_gate 0x1304c, check_inject 0x130b0, free 0x14100), at the SR
   level of libreac/fuzz_decode's released walk: the instruction segments are lib/U/Prog/LLVMFuzzerTestOneInput_evt.v,
   the allocator and callee glue lib/U/Prog/LLVMFuzzerTestOneInput_gl.v. The body returns 0 on every path
   (fuzz_egress.c:146, :164); the size >= 64 MiB arm is lib/U/Prog/LLVMFuzzerTestOneInput_early.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import memset_c memcpy_c check_gate_c
  check_restamp_c check_mute_c check_inject_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_early LLVMFuzzerTestOneInput_evt LLVMFuzzerTestOneInput_gl.
Import ListNotations.
Open Scope Z_scope.

(* the state at malloc's entry, after the harness has built head[], slot, ctr and v[] *)
Definition q1 (F : bvmap 5 word) (fc : bv 32) (gp tp s6 s7 s8 s9 s10 s11 : word) (m0 : word -> option byte)
    (lo Sp n P : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m' nf src slot w3 jv,
    ms = MS R F (Z_to_bv 64 0x14240) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12dbc /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 n /\ reg_get R 9 = Z_to_bv 64 P /\
    reg_get R 10 = Z_to_bv 64 (if nf =? 0 then 1 else nf) /\
    reg_get R 18 = Z_to_bv 64 slot /\ reg_get R 19 = w3 /\ reg_get R 20 = Z_to_bv 64 nf /\
    reg_get R 21 = Z_to_bv 64 src /\ reg_get R 22 = s6 /\ reg_get R 23 = s7 /\ reg_get R 24 = s8 /\
    reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    nf = Z.min (Z.max (n - 53) 0) 1600 /\ src = (if n <? 54 then 0 else 53) + P /\ -2 <= slot <= 253 /\
    length jv = 48%nat /\
    munch [(Sp, Sp + 160)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    rw_cells rsegs m' Sp [CB 48 jv] /\ rw_cells rsegs m' (Sp + 104) sv.

(* 0x12c6c-0x12db8: the whole of the harness body before the allocator's first call *)
Lemma e1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo P n : Z) (pl : list byte),
    memset_contract -> memcpy_contract ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned sp < 2 ^ 63 -> 0 <= lo -> 0 <= n < 2 ^ 26 -> 0 <= P < 2 ^ 64 ->
    n = Z.of_nat (length pl) -> (0 < n -> bytes_at rsegs m P pl) -> (0 < n -> 4096 <= P /\ P + n <= lo) ->
    Exec.evt rsegs
      (q1 F fc gp tp s6 s7 s8 s9 s10 s11 m lo (bv_unsigned sp - 160) n P (lsv ra s0 s1 s2 s3 s4 s5))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12c6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo P n pl MSET MCPY ST LO MI H63 Hlo0 Hn HP Hlen HPB HPL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  eapply s1a; try eassumption; try lia.
  intros m1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 jv jp jh ST1 MI1 MU1 WM1 FV1 FP1 FH1 FS1.
  eapply (s1b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 160) lo P n pl jh);
    try eassumption; try lia.
  { intros Hn0. eapply bytes_at_transport; [apply HPB; exact Hn0 | exact MU1 |].
    destruct (HPL ltac:(lia)). cbn [disjoint_from]. split; [lia | exact I]. }
  intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 jh2 MI2 MU2 WM2 FH2.
  destruct (rwc_cb_inv rsegs m2 (bv_unsigned sp - 160 + 51) 53 jh2 FH2) as (Hjh2 & BH2 & WH2).
  eapply (s1c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (bv_unsigned sp - 160) n P jh2);
    try eassumption; try lia.
  intros w14 w15 w16 w17 w3 slot Hslot.
  assert (FV2 : rw_cells rsegs m2 (bv_unsigned sp - 160) [CB 48 jv]).
  { eapply rw_cells_transport; [exact FV1 | exact MU2 | exact WM2 |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  assert (FS2 : rw_cells rsegs m2 (bv_unsigned sp - 160 + 104) (lsv ra s0 s1 s2 s3 s4 s5)).
  { eapply rw_cells_transport; [exact FS1 | exact MU2 | exact WM2 |].
    cbn [disjoint_from cells_size csize lsv]. split; [lia | exact I]. }
  assert (ST2 : stk rsegs m2 lo (bv_unsigned sp - 160)).
  { eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  destruct (rwc_cb_inv rsegs m2 (bv_unsigned sp - 160) 48 jv FV2) as (Hjv2 & _ & _).
  eapply (s1loop 11%nat) with (s := 0%nat) (iz := 0) (az := bv_unsigned sp - 160 + 59) (jh := jh2) (jv := jv)
    (sv := lsv ra s0 s1 s2 s3 s4 s5) (m0 := m2) (lo := lo);
    [ lia | lia | lia | exact Hjh2 | | lia | lia | lia | exact Hjv2 | exact FV2 | exact BH2 | exact FS2
    | exact ST2 | exact MI2 | apply munch_refl | apply wmono_refl ].
  intros m3 jv3 z10 z11 z14 z15 z16 z17 Hjv3 FV3 BH3 FS3 ST3 MI3 MU3 WM3.
  eapply (s1d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (bv_unsigned sp - 160) lo n P);
    try eassumption; try lia.
  intros nf src y11 y12 y13 y14 y15 y16 y17 Hnf Hsrc.
  apply evt_done. unfold q1.
  do 2 eexists; exists nf, src, slot, w3, jv3.
  split; [reflexivity|].
  do 17 (split; [reflexivity|]).
  split; [exact Hnf|]. split; [exact Hsrc|]. split; [exact Hslot|]. split; [exact Hjv3|].
  split.
  { replace (bv_unsigned sp - 160 + 160) with (bv_unsigned sp) by lia.
    eapply munch_trans; [exact MU1|].
    eapply munch_trans.
    - eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside].
      intros x [Hx _]. split; [lia | exact I].
    - eapply munch_weaken; [| exact MU3]. unfold sub_fp. cbn [outside].
      intros x [Hx _]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 (wmono_trans rsegs _ _ _ WM2 WM3))|].
  split; [exact MI3|]. split; [exact ST3|]. split; [exact FV3 | exact FS3].
Qed.

(* the state at check_restamp's entry *)
Definition q2 (F : bvmap 5 word) (fc : bv 32) (gp tp s6 s7 s8 s9 s10 s11 w3 : word) (m0 : word -> option byte)
    (Sp n nf nf' f src slot : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m' junk',
    ms = MS R F (Z_to_bv 64 0x12e58) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12dec /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 n /\ reg_get R 9 = Z_to_bv 64 f /\ reg_get R 10 = Z_to_bv 64 f /\
    reg_get R 11 = Z_to_bv 64 nf /\ reg_get R 12 = w3 /\ reg_get R 18 = Z_to_bv 64 slot /\
    reg_get R 19 = w3 /\ reg_get R 20 = Z_to_bv 64 nf /\
    reg_get R 21 = Z_to_bv 64 src /\ reg_get R 22 = s6 /\ reg_get R 23 = s7 /\ reg_get R 24 = s8 /\
    reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    munch [(f, f + nf')] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' f [CB (Z.to_nat nf') junk'] /\ rw_cells rsegs m' (Sp + 104) sv.

(* the state at check_inject's entry *)
Definition q4 (F : bvmap 5 word) (fc : bv 32) (gp tp s6 s7 s8 s9 s10 s11 w3 : word) (m0 : word -> option byte)
    (Sp lo n nf f slot : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m',
    ms = MS R F (Z_to_bv 64 0x130b0) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12e1c /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 n /\ reg_get R 9 = Z_to_bv 64 f /\ reg_get R 10 = Z_to_bv 64 f /\
    reg_get R 11 = Z_to_bv 64 nf /\ reg_get R 12 = Z_to_bv 64 slot /\ reg_get R 13 = Z_to_bv 64 Sp /\
    reg_get R 18 = Z_to_bv 64 slot /\ reg_get R 19 = w3 /\ reg_get R 20 = Z_to_bv 64 nf /\
    reg_get R 22 = s6 /\ reg_get R 23 = s7 /\ reg_get R 24 = s8 /\ reg_get R 25 = s9 /\ reg_get R 26 = s10 /\
    reg_get R 27 = s11 /\
    munch [(Sp - 80, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    rw_cells rsegs m' (Sp + 104) sv.

(* the state at check_mute's entry: the memory is as check_restamp left it *)
Definition qmute (F : bvmap 5 word) (fc : bv 32) (gp tp s6 s7 s8 s9 s10 s11 w3 : word)
    (m : word -> option byte) (Sp n nf f slot : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R,
    ms = MS R F (Z_to_bv 64 0x12f50) fc None m (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12df8 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 n /\ reg_get R 9 = Z_to_bv 64 f /\ reg_get R 10 = Z_to_bv 64 f /\
    reg_get R 11 = Z_to_bv 64 nf /\ reg_get R 18 = Z_to_bv 64 slot /\ reg_get R 19 = w3 /\
    reg_get R 20 = Z_to_bv 64 nf /\ reg_get R 22 = s6 /\ reg_get R 23 = s7 /\ reg_get R 24 = s8 /\
    reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    rw_cells rsegs m (Sp + 104) sv.

(* the state at free's entry *)
Definition qfree (F : bvmap 5 word) (fc : bv 32) (gp tp s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 : word)
    (m : word -> option byte) (Sp f : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R,
    ms = MS R F (Z_to_bv 64 0x14100) fc None m (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12e24 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = s0 /\ reg_get R 9 = s1 /\ reg_get R 10 = Z_to_bv 64 f /\ reg_get R 18 = s2 /\
    reg_get R 19 = s3 /\ reg_get R 20 = s4 /\ reg_get R 22 = s6 /\ reg_get R 23 = s7 /\
    reg_get R 24 = s8 /\ reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    rw_cells rsegs m (Sp + 104) sv.

(* the state the epilogue returns in *)
Definition qret (F : bvmap 5 word) (fc : bv 32) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : word -> option byte) (Sx : Z) (ms : machine_state) : Prop :=
  exists R,
    ms = MS R F (ret_pc ra) fc None m (seg_rom rsegs) /\
    reg_get R 1 = ra /\ reg_get R 2 = Z_to_bv 64 Sx /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = s0 /\ reg_get R 9 = s1 /\ reg_get R 10 = Z_to_bv 64 0 /\ reg_get R 18 = s2 /\
    reg_get R 19 = s3 /\ reg_get R 20 = s4 /\ reg_get R 21 = s5 /\ reg_get R 22 = s6 /\ reg_get R 23 = s7 /\
    reg_get R 24 = s8 /\ reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11.

(* fuzz_uci's lib/U/Prog/LLVMFuzzerTestOneInput.v at bc49657c087aa7d6ab0af1ffb2cb67fa08b15de1 *)
Lemma lf_rw_cells_frame : forall m m' A cs,
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] HE.
  rewrite cells_bytes_length in H1 by exact Hwf.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [rewrite cells_bytes_length by exact Hwf; exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite cells_bytes_length in Hi by exact Hwf.
    change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
    exact (proj1 (HE (A + Z.of_nat i) ltac:(lia))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    apply (proj1 (proj2 (HE (A + i) ltac:(lia)))). exact (Hw i Hi).
Qed.

Lemma blk_bytes_at : forall B m A bs, ms_segs B = rsegs -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Lemma nth_firstn_lt : forall {X : Type} (l : list X) k i, (i < k)%nat -> nth_error (firstn k l) i = nth_error l i.
Proof.
  intros X l. induction l as [|x l IH]; intros [|k] [|i] H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma nth_skipn : forall {X : Type} (l : list X) a i, nth_error (skipn a l) i = nth_error l (a + i).
Proof.
  intros X l. induction l as [|x l IH]; intros [|a] i.
  - destruct i; reflexivity.
  - destruct i; reflexivity.
  - reflexivity.
  - cbn. apply IH.
Qed.

Lemma blk_slice : forall B m A bs a k, blk_data B m A bs -> 0 <= a -> 0 <= k -> a + k <= Z.of_nat (length bs) ->
  blk_data B m (A + a) (firstn (Z.to_nat k) (skipn (Z.to_nat a) bs)).
Proof.
  intros B m A bs a k HD Ha Hk Hak i Hi.
  rewrite firstn_length_le in Hi by (rewrite length_skipn; lia).
  rewrite nth_firstn_lt by lia. rewrite nth_skipn.
  replace (A + a + i) with (A + (a + i)) by lia. rewrite (HD (a + i) ltac:(lia)). f_equal. lia.
Qed.

(* reg_get facts of a machine state carried to the config registers it is equivalent to (fuzz_uci's idiom) *)
Ltac xr Hx Rk E := lazymatch type of Rk with reg_get _ ?k = ?v => lazymatch type of Hx with Regs6ss.xregs_eqv _ ?r' =>
  assert (E : reg_get r' k = v) by (rewrite <- (Hx k eq_refl); exact Rk) end end.
(* a callee-saved register across a call *)
Tactic Notation "pz" constr(Hrp) constr(E) constr(kz) ident(E') :=
  lazymatch type of E with _ ?r1 _ = ?v => lazymatch type of Hrp with regs_preserved r1 ?r2 =>
  assert (E' : YK11.getr r2 (Z_to_bv 5 kz) = v) by (rewrite (Hrp kz ltac:(unfold callee_saved; lia)); exact E) end end.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis BND : blocks_nodup B API.
Hypothesis CT : ctx_owned B API.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis CG : check_gate_contract.
Hypothesis CRS : forall fx' : YK11.FPState, @check_restamp_contract fx' rc B API.
Hypothesis CM : forall fx' : YK11.FPState, @check_mute_contract fx' rc B API.
Hypothesis CI : forall fx' : YK11.FPState, @check_inject_contract fx' rc B API.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).

(* libreac/fuzz_decode's lib/U/Prog/fd_seghelp.v at 25e3d17bdb5059606131377a3722d585415ab5d6 *)
Lemma blk_keep : forall stk Sw L A mem md LX AXX memX mdX x bs,
  lf_fr B API stk Sw L A mem md LX AXX memX mdX -> In (x, Z.of_nat (length bs)) (blocks L A) ->
  blk_data B mem x bs -> blk_data B memX x bs.
Proof.
  intros stk Sw L A mem md LX AXX memX mdX x bs (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _) Hin HD i Hi.
  rewrite (Hbyt x _ i Hin Hi). exact (HD i Hi).
Qed.

Lemma norm_blk : forall L A mem md x k, aa_MR API L A mem md -> In (x, k) (blocks L A) -> 0 < k ->
  ro_agree rsegs mem -> exists junk, rw_cells rsegs (normalize rsegs mem) x [CB (Z.to_nat k) junk].
Proof.
  intros L A mem md x k HM Hin Hk Hro. pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q k HM Hqin) as (R1 & R2). rewrite Hq in R1, R2.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (ST : Frame.stk rsegs (normalize rsegs mem) x (x + k)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (mr_blocks B _ (aa_laws API) L A mem md q k (a - x) HM Hqin ltac:(lia)) as ((v & Hv) & _).
    pose proof (ax_blocks_img AX L A mem md q k (a - x) HM Hqin ltac:(lia)) as Hni.
    rewrite Hq in Hv, Hni. replace (x + (a - x)) with a in Hv, Hni by lia.
    assert (E : normalize rsegs mem (Z_to_bv 64 a) = Some v).
    { rewrite (mem_rel_rw rsegs mem (normalize rsegs mem) (Z_to_bv 64 a) (mem_rel_normalize rsegs mem Hro)
        (lf_ro_addr_out B a SEGS Hni ltac:(lia))). exact Hv. }
    unfold wa. split.
    - unfold wview. rewrite E. discriminate.
    - exists v. unfold mrd. rewrite E. reflexivity. }
  destruct (stk_carve rsegs _ x (x + k) (Z.to_nat k) ST ltac:(rewrite Z2Nat.id by lia; lia)) as [_ [junk HR]].
  rewrite Z2Nat.id in HR by lia. replace (x + k - k) with x in HR by lia. exists junk. exact HR.
Qed.

Lemma disj_mid : forall b1 x b2 y, pairwise ranges_disjoint (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros b1 x b2 y HP Hin. destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H];
    unfold ranges_disjoint in H; lia.
Qed.

Section Run.
Variables (stk empty : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
  (md0 : Model) (ra p n : Z) (pl : list byte) (b : sbound) (j : nat).
Hypothesis BI : llvm_binds B API.
Hypothesis Hk : LLVM_K <= stk.
Hypothesis Hra : YK0s.ret_ok (Z_to_bv 64 ra).
Hypothesis Hpre : lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n.
Hypothesis Hlen : n = Z.of_nat (length pl).
Hypothesis Hpd : blk_data B mem0 p pl.
Hypothesis Hsn : sink_none B mem0 md0.
Hypothesis Hsp : spZ regs0 <= 2 ^ 47.
Hypothesis Hroom : llvm_room b.
Hypothesis Hro : ro_agree rsegs mem0.
Hypothesis Hn26 : n < 2 ^ 26.
Hypothesis Hres0 : res_ok_slots A0 b.

Lemma f_bounds : 8464 <= stk /\ YM05.alloc_ceiling + stk <= spZ regs0 /\ spZ regs0 mod 16 = 0 /\
  spZ regs0 <= 2 ^ 47 /\ LF_RES_TOP < YM05.alloc_ceiling /\ 0 <= n.
Proof.
  pose proof Hpre as (_ & _ & _ & _ & _ & Hal & Hceil & _).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  split; [lia|]. split; [exact Hceil|]. split; [exact Hal|]. split; [exact Hsp|]. split; [exact Hrt | lia].
Qed.

Lemma f_pay : 0 < n -> In (bv_unsigned (reg_get regs0 10), n) (blocks L0 A0) /\
  4096 <= bv_unsigned (reg_get regs0 10) /\ bv_unsigned (reg_get regs0 10) + n <= YM05.alloc_ceiling /\
  bv_unsigned (reg_get regs0 10) = p.
Proof.
  intros Hn0.
  pose proof Hpre as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
  pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
  assert (E : bv_unsigned (reg_get regs0 10) = p).
  { assert (E10 : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp. rewrite E10. apply MState.unsigned_lit. lia. }
  rewrite E. split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia.
Qed.

Lemma f_p'range : 0 <= bv_unsigned (reg_get regs0 10) < 2 ^ 64.
Proof.
  pose proof (bv_unsigned_in_range _ (reg_get regs0 10)) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R. exact R.
Qed.

Lemma f_stk : forall L A mem md hi, lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  spZ regs0 - stk <= hi <= spZ regs0 ->
  Frame.stk rsegs (normalize rsegs mem) (spZ regs0 - stk) hi.
Proof.
  intros L A mem md hi FR Hhi. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply lf_stk; [lia | lia |]. intros a Ha. unfold writable_at.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem MI)
             (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
  rewrite <- SEGS. exact (Hstw a ltac:(lia)).
Qed.

Lemma room_b : forall k, 0 <= k <= 1600 -> room_slots b k.
Proof.
  intros k Hkk. destruct Hroom as (R1 & R2 & R3). apply room_slots_big; unfold CAPMAX in *; lia.
Qed.

Lemma room_mb : forall k k', 0 <= k <= 1600 -> 0 <= k' <= 1600 -> room_slots (sb_malloc b k') k.
Proof.
  intros k k' Hkk Hkk'. destruct Hroom as (R1 & R2 & R3). apply room_slots_big;
    unfold sb_malloc, CAPMAX in *; cbn [sb_live sb_bytes sb_cap] in *; lia.
Qed.

Lemma room_cmute : forall k k', 0 <= k <= 1600 -> 0 <= k' <= 1600 ->
  sb_live (sb_malloc b k') + 1 <= sb_cap (sb_malloc b k') <= CAPMAX /\ 0 <= sb_bytes (sb_malloc b k') /\
  sb_bytes (sb_malloc b k') + Z.max k 1 <= 2 ^ 40.
Proof.
  intros k k' Hkk Hkk'. destruct Hroom as (R1 & R2 & R3).
  unfold sb_malloc, CAPMAX in *; cbn [sb_live sb_bytes sb_cap] in *. repeat split; lia.
Qed.

Lemma room_cinj : forall k k', 0 <= k <= 1600 -> 0 <= k' <= 1600 ->
  sb_live (sb_malloc b k') + 2 <= sb_cap (sb_malloc b k') <= CAPMAX /\ 0 <= sb_bytes (sb_malloc b k') /\
  sb_bytes (sb_malloc b k') + 2 * Z.max k 1 <= 2 ^ 40.
Proof.
  intros k k' Hkk Hkk'. destruct Hroom as (R1 & R2 & R3).
  unfold sb_malloc, CAPMAX in *; cbn [sb_live sb_bytes sb_cap] in *. repeat split; lia.
Qed.

Lemma en_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma f_norm : forall L A mem md Ac cs, lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  spZ regs0 - stk <= Ac -> Ac + Z.of_nat (cells_size cs) <= spZ regs0 ->
  rw_cells rsegs mem Ac cs -> rw_cells rsegs (normalize rsegs mem) Ac cs.
Proof.
  intros L A mem md Ac cs FR Hlo Hhi HC. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply (lf_rw_cells_norm B mem Ac cs SEGS MI); [|exact HC].
  intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia.
Qed.

Lemma f_present : forall L A mem md i, lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  0 <= i < 48 -> present mem (spZ regs0 - 160 + i).
Proof.
  intros L A mem md i FR Hi. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply (lf_present_of_writable B mem _ SEGS).
  - intros Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia.
  - lia.
  - rewrite <- SEGS. apply Hstw. lia.
Qed.

Local Notation Post := (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).

Lemma sr_entry : frm_zero (@fp_csr fx) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0) Post.
Proof.
  intros Hfrm.
  pose proof BI as (_ & HMAL & HFRE & HGG & HG & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof YM05.alloc_ceiling_value as Hac.
  pose proof f_p'range as HP'.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn11 &
    Hpl0 & Hrod0).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  assert (HPB : 0 < n -> bytes_at rsegs (normalize rsegs mem0) (bv_unsigned (reg_get regs0 10)) pl).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & E). rewrite E in *.
    apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  assert (HPL : 0 < n -> 4096 <= bv_unsigned (reg_get regs0 10) /\
                         bv_unsigned (reg_get regs0 10) + n <= spZ regs0 - stk).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia. }
  pose proof f_pay as PAY.
  remember (bv_unsigned (reg_get regs0 10)) as P' eqn:EP'.
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 P') by (rewrite EP'; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 n) by exact Hn11.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0 L0 A0
    (q1 (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
        (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem0)
        (spZ regs0 - stk) (spZ regs0 - 160) n P'
        (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
             (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR0. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    apply (e1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx) (@fp_csr fx)
             (normalize rsegs mem0) (spZ regs0 - stk) P' n pl MSET MCPY).
    - apply (f_stk L0 A0 mem0 md0 (spZ regs0) FR0). lia.
    - unfold spZ in *. lia.
    - exact (mem_inv_normalize rsegs mem0).
    - unfold spZ in *. lia.
    - lia.
    - lia.
    - exact HP'.
    - exact Hlen.
    - exact HPB.
    - exact HPL. }
  { intros ms (R & m' & nf & src & slot & w3 & jv & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & MU & WM & _).
    do 5 eexists. exists [(spZ regs0 - 160, spZ regs0 - 160 + 160)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (R' & m'' & nf & src & slot & w3 & jv & HE & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R18 & R19 & R20 &
    R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hnf & Hsrc & Hslot & Hjv & MU & WM & MI & ST & FV & FS).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  xr Hx1 R1 F1. xr Hx1 R2 F2. xr Hx1 R3 F3. xr Hx1 R4 F4. xr Hx1 R8 F8. xr Hx1 R9 F9. xr Hx1 R10 F10.
  xr Hx1 R18 F18. xr Hx1 R19 F19. xr Hx1 R20 F20. xr Hx1 R21 F21. xr Hx1 R22 F22. xr Hx1 R23 F23. xr Hx1 R24 F24.
  xr Hx1 R25 F25. xr Hx1 R26 F26. xr Hx1 R27 F27.
  clear R1 R2 R3 R4 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel1 FV) as FV1.
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel1 FS) as FS1.
  clear FV FS ST MI MU WM.
  assert (Hsp1 : spZ regs1 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs1 2) with (reg_get regs1 2); rewrite F2;
        apply MState.unsigned_lit; lia).
  assert (Hnf0 : 0 <= nf <= 1600) by lia.
  set (nf' := if nf =? 0 then 1 else nf) in *.
  assert (Hnf' : nf' = Z.max nf 1) by (unfold nf'; destruct (Z.eqb_spec nf 0); lia).
  rewrite <- SEGS. change (Z_to_bv 64 0x14240) with (Z_to_bv 64 LLVM_MALLOC).
  eapply (g_malloc B API SEGS AX ERRNO_LOW HMAL MALLOC stk (spZ regs0) L0 A0 mem0 md0
            (mkFP (@fp_regs fx) (@fp_csr fx)) regs1 m1 md0 L0 A0 nf' b).
  { exact FR1. } { lia. } { lia. }
  { change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite F1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp1. unfold ALLOC_STACK. pose proof Hk as Hk'.
    unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs1 4) with (reg_get regs1 4). rewrite F4. exact Htp0. }
  { exact F10. }
  { exact Hres0. }
  { apply room_b. unfold nf'. destruct (Z.eqb_spec nf 0); lia. }
  intros L1 A1 regs2 mem2 md2 f FR2 Hrp2 G210 Hf1 Hf2 Hf16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  (* the payload block and the fresh block are disjoint *)
  assert (MINE : forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + nf' <= a).
  { intros a k Hak.
    assert (PW : pairwise ranges_disjoint (b1 ++ (f, nf') :: b2)).
    { rewrite <- Eb1. pose proof FR2 as (HM2 & _).
      exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
    rewrite Eb2 in Hak. pose proof (disj_mid b1 (f, nf') b2 (a, k) PW Hak) as H. cbn [fst snd] in H. lia. }
  assert (Hfin : In (f, nf') (blocks L1 A1)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (Hnf'0 : 0 < nf' <= 1600) by (unfold nf' in *; destruct (Z.eqb_spec nf 0); lia).
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & Hblk2 & Hbyt2 & Hstw2 & Herr2 & _ & Hro2).
  destruct (norm_blk L1 A1 mem2 md2 f nf' HM2 Hfin ltac:(lia) Hro2) as [junk FB2].
  (* the slice of the payload the copy reads *)
  set (sbs := firstn (Z.to_nat nf) (skipn 53 pl)) in *.
  assert (Hsbs : Z.of_nat (length sbs) = nf).
  { unfold sbs. rewrite firstn_length_le; [lia|]. rewrite length_skipn.
    destruct (Z.eq_dec nf 0) as [E0|E0]; [lia|]. lia. }
  assert (HSB : 0 < nf -> bytes_at rsegs (normalize rsegs mem2) src sbs).
  { intros Hnfp.
    assert (Hn0 : 0 < n) by lia.
    destruct (PAY Hn0) as (Hin0 & P1 & P2 & Ep).
    assert (BD : blk_data B mem2 P' pl).
    { apply (blk_keep stk (spZ regs0) L0 A0 mem0 md0 L1 A1 mem2 md2 P' pl FR2); [| rewrite Ep; exact Hpd].
      rewrite <- Hlen. exact Hin0. }
    assert (BA : bytes_at rsegs (normalize rsegs mem2) P' pl).
    { apply bytes_at_normalize; [exact Hro2|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
    rewrite <- (firstn_skipn 53 pl) in BA. apply bytes_at_app in BA as [_ BA].
    rewrite firstn_length_le in BA by lia.
    unfold sbs. rewrite <- (firstn_skipn (Z.to_nat nf) (skipn 53 pl)) in BA.
    apply bytes_at_app in BA as [BA _].
    assert (Esrc : src = P' + Z.of_nat 53).
    { rewrite Hsrc. destruct (Z.ltb_spec n 54) as [H54|H54]; [lia | lia]. }
    rewrite Esrc. exact BA. }
  assert (FS2 : rw_cells rsegs mem2 (spZ regs0 - 160 + 104)
                  (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
                       (reg_get regs0 20) (reg_get regs0 21))).
  { apply (lf_rw_cells_frame m1); [exact FS1|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove2. rewrite Hsp1. lia. }
  pose proof (f_norm L1 A1 mem2 md2 (spZ regs0 - 160 + 104)
                (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
                     (reg_get regs0 20) (reg_get regs0 21)) FR2 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS2) as FS2n.
  pz Hrp2 F2 2 P2. pz Hrp2 F3 3 P3. pz Hrp2 F4 4 P4. pz Hrp2 F8 8 P8. pz Hrp2 F9 9 P9. pz Hrp2 F18 18 P18.
  pz Hrp2 F19 19 P19. pz Hrp2 F20 20 P20. pz Hrp2 F21 21 P21. pz Hrp2 F22 22 P22. pz Hrp2 F23 23 P23.
  pz Hrp2 F24 24 P24. pz Hrp2 F25 25 P25. pz Hrp2 F26 26 P26. pz Hrp2 F27 27 P27.
  assert (Q2 : reg_get regs2 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact P2.
  assert (Q3 : reg_get regs2 3 = reg_get regs0 3) by exact P3.
  assert (Q4 : reg_get regs2 4 = reg_get regs0 4) by exact P4.
  assert (Q8 : reg_get regs2 8 = Z_to_bv 64 n) by exact P8.
  assert (Q9 : reg_get regs2 9 = Z_to_bv 64 P') by exact P9.
  assert (Q18 : reg_get regs2 18 = Z_to_bv 64 slot) by exact P18.
  assert (Q19 : reg_get regs2 19 = w3) by exact P19.
  assert (Q20 : reg_get regs2 20 = Z_to_bv 64 nf) by exact P20.
  assert (Q21 : reg_get regs2 21 = Z_to_bv 64 src) by exact P21.
  assert (Q22 : reg_get regs2 22 = reg_get regs0 22) by exact P22.
  assert (Q23 : reg_get regs2 23 = reg_get regs0 23) by exact P23.
  assert (Q24 : reg_get regs2 24 = reg_get regs0 24) by exact P24.
  assert (Q25 : reg_get regs2 25 = reg_get regs0 25) by exact P25.
  assert (Q26 : reg_get regs2 26 = reg_get regs0 26) by exact P26.
  assert (Q27 : reg_get regs2 27 = reg_get regs0 27) by exact P27.
  assert (G22 : YK11.getr regs2 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact P2.
  assert (Hsp2 : spZ regs2 = spZ regs0 - 160)
    by (unfold spZ at 1; rewrite G22; apply MState.unsigned_lit; lia).
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx) (@fp_csr fx)) regs2
            (YK11.getr regs1 1) mem2 md2 L1 A1
    (q2 (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
        (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) w3
        (normalize rsegs mem2) (spZ regs0 - 160) n nf nf' f src slot (lsv (reg_get regs0 1) (reg_get regs0 8)
          (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR2. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite F1.
    assert (Q10 : reg_get regs2 10 = Z_to_bv 64 f) by exact G210.
    rewrite Q2, Q3, Q4, Q8, Q9, Q10, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
    apply (s1e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx) (@fp_csr fx)
             (normalize rsegs mem2) (spZ regs0 - 160) (spZ regs0 - stk) n P' nf nf' f src sbs junk _ MCPY).
    - lia.
    - lia.
    - lia.
    - exact Hnf'.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite Hsrc. destruct (n <? 54); lia.
    - rewrite Hsrc. destruct (Z.ltb_spec n 54) as [H54|H54]; [lia|].
      destruct (PAY ltac:(lia)) as (_ & _ & Pc & _). lia.
    - destruct (Z.eq_dec nf 0) as [E0|E0]; [lia|].
      destruct (PAY ltac:(lia)) as (Hin0 & P1 & Pc & _).
      destruct (MINE P' n Hin0); [left | right]; rewrite Hsrc;
        destruct (Z.ltb_spec n 54) as [H54|H54]; lia.
    - exact HSB.
    - exact Hsbs.
    - exact FB2.
    - exact (mem_inv_normalize rsegs mem2).
    - intros m4 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 junk' MU4 WM4 MI4 FB4.
      apply evt_done. unfold q2. do 2 eexists; exists junk'.
      split; [reflexivity|]. do 19 (split; [reflexivity|]).
      split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact FB4|].
      eapply rw_cells_transport; [exact FS2n | exact MU4 | exact WM4 |].
      cbn [disjoint_from cells_size csize lsv]. split; [lia | exact I]. }
  { intros ms (Rq & mq & junkq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      MU & WM & _ & _ & _).
    do 5 eexists. exists [(f, f + nf')].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. right. exists f, nf'. split; [| apply en_out1 in NO; lia].
    unfold lf_mine. split; [exact Hfin|]. split; [lia | exact MINE]. }
  intros R2 F2' pc2 fc2 m2' HQ2 regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ2 as (Ra & ma & junk2 & HEa & S1 & S2 & S3 & S4 & S8 & S9 & S10 & S11 & S12 & S18 & S19 & S20 & S21 &
    S22 & S23 & S24 & S25 & S26 & S27 & MUa & WMa & MIa & FBa & FSa).
  injection HEa as ERa EFa EPa ECa EMa. subst Ra F2' pc2 fc2 ma.
  xr Hx3 S1 T1. xr Hx3 S2 T2. xr Hx3 S3 T3. xr Hx3 S4 T4. xr Hx3 S8 T8. xr Hx3 S9 T9. xr Hx3 S10 T10.
  xr Hx3 S11 T11. xr Hx3 S12 T12. xr Hx3 S18 T18. xr Hx3 S19 T19. xr Hx3 S20 T20. xr Hx3 S21 T21. xr Hx3 S22 T22.
  xr Hx3 S23 T23. xr Hx3 S24 T24. xr Hx3 S25 T25. xr Hx3 S26 T26. xr Hx3 S27 T27.
  pose proof (lf_rw_cells_rel m3 _ _ _ Hrel3 FSa) as FS3.
  assert (Hsp3 : spZ regs3 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs3 2) with (reg_get regs3 2); rewrite T2;
        apply MState.unsigned_lit; lia).
  assert (Hib : in_block L1 A1 f nf) by (exists f, nf'; split; [exact Hfin | lia]).
  assert (HTP3 : YK11.getr regs3 4 = Z_to_bv 64 (ms_tp B))
    by (change (YK11.getr regs3 4) with (reg_get regs3 4); rewrite T4; exact Htp0).
  (* check_restamp *)
  rewrite <- SEGS. change (Z_to_bv 64 0x12e58) with (Z_to_bv 64 CHECK_RESTAMP).
  eapply (g_crs B API SEGS AX ERRNO_LOW stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx) (@fp_csr fx)) regs3 m3
            md2 L1 A1 f nf (bv_unsigned w3) (sb_malloc b nf')).
  { exact CRS. } { exact FR3. } { lia. } { lia. }
  { change (YK11.getr regs3 1) with (reg_get regs3 1). rewrite T1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp3. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp3. unfold CHECK_RESTAMP_STACK, CR_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. } { exact HTP3. }
  { change (YK11.getr regs3 10) with (reg_get regs3 10). exact T10. }
  { change (YK11.getr regs3 11) with (reg_get regs3 11). exact T11. }
  { change (YK11.getr regs3 12) with (reg_get regs3 12). rewrite T12. symmetry. apply Z_to_bv_bv_unsigned. }
  { lia. } { exact Hib. } { exact Hfrm. } { exact Hres2. } { apply room_mb; lia. }
  intros fx4 L2 A2 regs4 mem4 md4 Hfrm4 FR4 Hrp4 Eb4 Hres4 Habove4 Hkept4.
  (* check_mute *)
  pz Hrp4 T18 18 U18. pz Hrp4 T2 2 U2. pz Hrp4 T3 3 U3. pz Hrp4 T4 4 U4. pz Hrp4 T8 8 U8. pz Hrp4 T9 9 U9. pz Hrp4 T19 19 U19.
  pz Hrp4 T20 20 U20. pz Hrp4 T21 21 U21. pz Hrp4 T22 22 U22. pz Hrp4 T23 23 U23. pz Hrp4 T24 24 U24.
  pz Hrp4 T25 25 U25. pz Hrp4 T26 26 U26. pz Hrp4 T27 27 U27.
  assert (V2 : reg_get regs4 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact U2.
  assert (V3 : reg_get regs4 3 = reg_get regs0 3) by exact U3.
  assert (V4 : reg_get regs4 4 = reg_get regs0 4) by exact U4.
  assert (V8 : reg_get regs4 8 = Z_to_bv 64 n) by exact U8.
  assert (V9 : reg_get regs4 9 = Z_to_bv 64 f) by exact U9.
  assert (V19 : reg_get regs4 19 = w3) by exact U19.
  assert (V20 : reg_get regs4 20 = Z_to_bv 64 nf) by exact U20.
  assert (V21 : reg_get regs4 21 = Z_to_bv 64 src) by exact U21.
  assert (V22 : reg_get regs4 22 = reg_get regs0 22) by exact U22.
  assert (V23 : reg_get regs4 23 = reg_get regs0 23) by exact U23.
  assert (V24 : reg_get regs4 24 = reg_get regs0 24) by exact U24.
  assert (V25 : reg_get regs4 25 = reg_get regs0 25) by exact U25.
  assert (V26 : reg_get regs4 26 = reg_get regs0 26) by exact U26.
  assert (V27 : reg_get regs4 27 = reg_get regs0 27) by exact U27.
  assert (V18 : reg_get regs4 18 = Z_to_bv 64 slot) by exact U18.
  assert (FS4 : rw_cells rsegs mem4 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (lf_rw_cells_frame m3); [exact FS3|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove4. rewrite Hsp3. lia. }
  pose proof (f_norm L2 A2 mem4 md4 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR4 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS4) as FS4n.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx4 regs4 (YK11.getr regs3 1) mem4 md4 L2 A2
    (qmute (@fp_regs fx4) (@fp_csr fx4) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
       (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) w3 (normalize rsegs mem4)
       (spZ regs0 - 160) n nf f slot (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR4. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs3 1) with (reg_get regs3 1). rewrite T1.
    rewrite V2, V3, V4, V8, V9, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27.
    apply (s1f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx4) (@fp_csr fx4)
             (normalize rsegs mem4) (spZ regs0 - 160) nf f).
    apply evt_done. unfold qmute. eexists.
    split; [reflexivity|]. do 17 (split; [reflexivity|]). exact FS4n. }
  { intros ms (Rq & ->  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R5 Ff5 pc5 fc5 m5' HQ5 regs5 m5 Hx5 Hrel5 FR5.
  destruct HQ5 as (Rb & HEb & W1 & W2 & W3 & W4 & W8 & W9 & W10 & W11 & W18 & W19 & W20 & W22 & W23 & W24 & W25 &
    W26 & W27 & FSb).
  injection HEb as ERb EFb EPb ECb EMb. subst Rb Ff5 pc5 fc5 m5'.
  xr Hx5 W1 X1. xr Hx5 W2 X2. xr Hx5 W3 X3. xr Hx5 W4 X4. xr Hx5 W8 X8. xr Hx5 W9 X9. xr Hx5 W10 X10.
  xr Hx5 W11 X11. xr Hx5 W18 X18. xr Hx5 W19 X19. xr Hx5 W20 X20. xr Hx5 W22 X22. xr Hx5 W23 X23.
  xr Hx5 W24 X24. xr Hx5 W25 X25. xr Hx5 W26 X26. xr Hx5 W27 X27.
  pose proof (lf_rw_cells_rel m5 _ _ _ Hrel5 FSb) as FS5.
  assert (Hsp5 : spZ regs5 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs5 2) with (reg_get regs5 2); rewrite X2;
        apply MState.unsigned_lit; lia).
  assert (Hib5 : in_block L2 A2 f nf) by (exists f, nf'; split; [rewrite Eb4; exact Hfin | lia]).
  rewrite <- SEGS. change (Z_to_bv 64 0x12f50) with (Z_to_bv 64 CHECK_MUTE).
  eapply (g_cm B API SEGS AX ERRNO_LOW stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx4) (@fp_csr fx4)) regs5 m5
            md4 L2 A2 f nf (sb_malloc b nf')).
  { exact CM. } { exact FR5. } { lia. } { lia. }
  { change (YK11.getr regs5 1) with (reg_get regs5 1). rewrite X1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp5. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp5. unfold CHECK_MUTE_STACK, CHECK_MUTE_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs5 4) with (reg_get regs5 4). rewrite X4. exact Htp0. }
  { change (YK11.getr regs5 10) with (reg_get regs5 10). exact X10. }
  { change (YK11.getr regs5 11) with (reg_get regs5 11). exact X11. }
  { lia. } { exact Hib5. } { exact Hfrm4. } { exact Hres4. } { apply room_cmute; lia. }
  intros fx6 L3 A3 regs6 mem6 md6 Hfrm6 FR6 Hrp6 Eb6 Hres6 Habove6 Hkept6.
  (* check_gate (an evt leaf) and check_inject *)
  pz Hrp6 X2 2 Y2. pz Hrp6 X3 3 Y3. pz Hrp6 X4 4 Y4. pz Hrp6 X8 8 Y8. pz Hrp6 X9 9 Y9. pz Hrp6 X18 18 Y18.
  pz Hrp6 X19 19 Y19. pz Hrp6 X20 20 Y20. pz Hrp6 X22 22 Y22. pz Hrp6 X23 23 Y23. pz Hrp6 X24 24 Y24.
  pz Hrp6 X25 25 Y25. pz Hrp6 X26 26 Y26. pz Hrp6 X27 27 Y27.
  assert (Z2 : reg_get regs6 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact Y2.
  assert (Z3 : reg_get regs6 3 = reg_get regs0 3) by exact Y3.
  assert (Z4 : reg_get regs6 4 = reg_get regs0 4) by exact Y4.
  assert (Z8 : reg_get regs6 8 = Z_to_bv 64 n) by exact Y8.
  assert (Z9 : reg_get regs6 9 = Z_to_bv 64 f) by exact Y9.
  assert (Z18 : reg_get regs6 18 = Z_to_bv 64 slot) by exact Y18.
  assert (Z19 : reg_get regs6 19 = w3) by exact Y19.
  assert (Z20 : reg_get regs6 20 = Z_to_bv 64 nf) by exact Y20.
  assert (Z22 : reg_get regs6 22 = reg_get regs0 22) by exact Y22.
  assert (Z23 : reg_get regs6 23 = reg_get regs0 23) by exact Y23.
  assert (Z24 : reg_get regs6 24 = reg_get regs0 24) by exact Y24.
  assert (Z25 : reg_get regs6 25 = reg_get regs0 25) by exact Y25.
  assert (Z26 : reg_get regs6 26 = reg_get regs0 26) by exact Y26.
  assert (Z27 : reg_get regs6 27 = reg_get regs0 27) by exact Y27.
  assert (FS6 : rw_cells rsegs mem6 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (lf_rw_cells_frame m5); [exact FS5|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove6. rewrite Hsp5. lia. }
  pose proof (f_norm L3 A3 mem6 md6 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR6 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS6) as FS6n.
  assert (Hfin6 : In (f, nf') (blocks L3 A3)) by (rewrite Eb6, Eb4; exact Hfin).
  pose proof FR6 as (HM6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro6).
  destruct (norm_blk L3 A3 mem6 md6 f nf' HM6 Hfin6 ltac:(lia) Hro6) as [junk6 FB6].
  destruct (rwc_cb_inv rsegs (normalize rsegs mem6) f (Z.to_nat nf') junk6 FB6) as (Hj6 & BB6 & _).
  assert (BBn : bytes_at rsegs (normalize rsegs mem6) f (firstn (Z.to_nat nf) junk6)).
  { rewrite <- (firstn_skipn (Z.to_nat nf) junk6) in BB6. apply bytes_at_app in BB6 as [BB6 _]. exact BB6. }
  assert (Hbn : Z.of_nat (length (firstn (Z.to_nat nf) junk6)) = nf)
    by (rewrite firstn_length_le; lia).
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx6 regs6 (YK11.getr regs5 1) mem6 md6 L3 A3
    (q4 (@fp_regs fx6) (@fp_csr fx6) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
       (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) w3 (normalize rsegs mem6)
       (spZ regs0 - 160) (spZ regs0 - stk) n nf f slot (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR6. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs5 1) with (reg_get regs5 1). rewrite X1.
    rewrite Z2, Z3, Z4, Z8, Z9, Z18, Z19, Z20, Z22, Z23, Z24, Z25, Z26, Z27.
    apply (s1g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx6) (@fp_csr fx6)
             (normalize rsegs mem6) (spZ regs0 - 160) (spZ regs0 - stk) nf f slot
             (firstn (Z.to_nat nf) junk6) _ CG).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact BBn.
    - exact Hbn.
    - exact (mem_inv_normalize rsegs mem6).
    - apply (f_stk L3 A3 mem6 md6 (spZ regs0 - 160) FR6). lia.
    - intros m7 y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 MU7 WM7 MI7 ST7.
      apply evt_done. unfold q4. eexists; eexists.
      split; [reflexivity|]. do 19 (split; [reflexivity|]).
      split; [exact MU7|]. split; [exact WM7|]. split; [exact MI7|]. split; [exact ST7|].
      eapply rw_cells_transport; [exact FS6n | exact MU7 | exact WM7 |].
      cbn [disjoint_from cells_size csize lsv]. split; [lia | exact I]. }
  { intros ms (Rq & mq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM &
      _ & _ & _).
    do 5 eexists. exists [(spZ regs0 - 160 - 80, spZ regs0 - 160)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R7 Ff7 pc7 fc7 m7' HQ7 regs7 m7 Hx7 Hrel7 FR7.
  destruct HQ7 as (Rc & mc & HEc & C1 & C2 & C3 & C4 & C8 & C9 & C10 & C11 & C12 & C13 & C18 & C19 & C20 & C22 &
    C23 & C24 & C25 & C26 & C27 & MUc & WMc & MIc & STc & FSc).
  injection HEc as ERc EFc EPc ECc EMc. subst Rc Ff7 pc7 fc7 mc.
  xr Hx7 C1 D1. xr Hx7 C2 D2. xr Hx7 C3 D3. xr Hx7 C4 D4. xr Hx7 C8 D8. xr Hx7 C9 D9. xr Hx7 C10 D10.
  xr Hx7 C11 D11. xr Hx7 C12 D12. xr Hx7 C13 D13. xr Hx7 C18 D18. xr Hx7 C19 D19. xr Hx7 C20 D20.
  xr Hx7 C22 D22. xr Hx7 C23 D23. xr Hx7 C24 D24. xr Hx7 C25 D25. xr Hx7 C26 D26. xr Hx7 C27 D27.
  pose proof (lf_rw_cells_rel m7 _ _ _ Hrel7 FSc) as FS7.
  assert (Hsp7 : spZ regs7 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs7 2) with (reg_get regs7 2); rewrite D2;
        apply MState.unsigned_lit; lia).
  rewrite <- SEGS. change (Z_to_bv 64 0x130b0) with (Z_to_bv 64 CHECK_INJECT).
  eapply (g_ci B API SEGS AX ERRNO_LOW stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx6) (@fp_csr fx6)) regs7 m7
            md6 L3 A3 f nf slot (spZ regs0 - 160) (sb_malloc b nf')).
  { exact CI. } { exact FR7. } { lia. } { lia. }
  { change (YK11.getr regs7 1) with (reg_get regs7 1). rewrite D1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp7. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp7. unfold CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK. pose proof Hk as Hk'.
    unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs7 4) with (reg_get regs7 4). rewrite D4. exact Htp0. }
  { change (YK11.getr regs7 10) with (reg_get regs7 10). exact D10. }
  { change (YK11.getr regs7 11) with (reg_get regs7 11). exact D11. }
  { change (YK11.getr regs7 12) with (reg_get regs7 12). exact D12. }
  { change (YK11.getr regs7 13) with (reg_get regs7 13). exact D13. }
  { lia. } { lia. }
  { exists f, nf'. split; [rewrite Eb6, Eb4; exact Hfin | lia]. }
  { rewrite Hsp7. lia. }
  { lia. }
  { replace (spZ regs0 - 160) with (spZ regs0 + (-40) * 4) by lia.
    rewrite Z.mod_add by lia. Z.div_mod_to_equations. lia. }
  { intros i Hi. exact (f_present L3 A3 m7 md6 i FR7 Hi). }
  { exact Hfrm6. } { exact Hres6. } { apply room_cinj; lia. }
  intros fx8 L4 A4 regs8 mem8 md8 Hfrm8 FR8 Hrp8 Eb8 Hres8 Habove8 Hkept8.
  (* free(f) *)
  pz Hrp8 D2 2 Ea2. pz Hrp8 D3 3 Ea3. pz Hrp8 D4 4 Ea4. pz Hrp8 D8 8 Ea8. pz Hrp8 D9 9 Ea9.
  pz Hrp8 D18 18 Ea18. pz Hrp8 D19 19 Ea19. pz Hrp8 D20 20 Ea20. pz Hrp8 D22 22 Ea22. pz Hrp8 D23 23 Ea23.
  pz Hrp8 D24 24 Ea24. pz Hrp8 D25 25 Ea25. pz Hrp8 D26 26 Ea26. pz Hrp8 D27 27 Ea27.
  assert (Fa2 : reg_get regs8 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact Ea2.
  assert (Fa3 : reg_get regs8 3 = reg_get regs0 3) by exact Ea3.
  assert (Fa4 : reg_get regs8 4 = reg_get regs0 4) by exact Ea4.
  assert (Fa8 : reg_get regs8 8 = Z_to_bv 64 n) by exact Ea8.
  assert (Fa9 : reg_get regs8 9 = Z_to_bv 64 f) by exact Ea9.
  assert (Fa18 : reg_get regs8 18 = Z_to_bv 64 slot) by exact Ea18.
  assert (Fa19 : reg_get regs8 19 = w3) by exact Ea19.
  assert (Fa20 : reg_get regs8 20 = Z_to_bv 64 nf) by exact Ea20.
  assert (Fa22 : reg_get regs8 22 = reg_get regs0 22) by exact Ea22.
  assert (Fa23 : reg_get regs8 23 = reg_get regs0 23) by exact Ea23.
  assert (Fa24 : reg_get regs8 24 = reg_get regs0 24) by exact Ea24.
  assert (Fa25 : reg_get regs8 25 = reg_get regs0 25) by exact Ea25.
  assert (Fa26 : reg_get regs8 26 = reg_get regs0 26) by exact Ea26.
  assert (Fa27 : reg_get regs8 27 = reg_get regs0 27) by exact Ea27.
  assert (FS8 : rw_cells rsegs mem8 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (lf_rw_cells_frame m7); [exact FS7|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove8. rewrite Hsp7. lia. }
  pose proof (f_norm L4 A4 mem8 md8 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR8 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS8) as FS8n.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx8 regs8 (YK11.getr regs7 1) mem8 md8 L4 A4
    (qfree (@fp_regs fx8) (@fp_csr fx8) (reg_get regs0 3) (reg_get regs0 4) (Z_to_bv 64 n) (Z_to_bv 64 f)
       (Z_to_bv 64 slot) w3 (Z_to_bv 64 nf) (reg_get regs0 22) (reg_get regs0 23)
       (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem8)
       (spZ regs0 - 160) f (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR8. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs7 1) with (reg_get regs7 1). rewrite D1.
    rewrite Fa2, Fa3, Fa4, Fa8, Fa9, Fa18, Fa19, Fa20, Fa22, Fa23, Fa24, Fa25, Fa26, Fa27.
    apply (s1h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx8) (@fp_csr fx8)
             (normalize rsegs mem8) (spZ regs0 - 160) f).
    apply evt_done. unfold qfree. eexists.
    split; [reflexivity|]. do 16 (split; [reflexivity|]). exact FS8n. }
  { intros ms (Rq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R9 Ff9 pc9 fc9 m9' HQ9 regs9 m9 Hx9 Hrel9 FR9.
  destruct HQ9 as (Rd & HEd & I1 & I2 & I3 & I4 & I8 & I9 & I10 & I18 & I19 & I20 & I22 & I23 & I24 & I25 &
    I26 & I27 & FSd).
  injection HEd as ERd EFd EPd ECd EMd. subst Rd Ff9 pc9 fc9 m9'.
  xr Hx9 I1 J1. xr Hx9 I2 J2. xr Hx9 I3 J3. xr Hx9 I4 J4. xr Hx9 I8 J8. xr Hx9 I9 J9. xr Hx9 I10 J10.
  xr Hx9 I18 J18. xr Hx9 I19 J19. xr Hx9 I20 J20. xr Hx9 I22 J22. xr Hx9 I23 J23.
  xr Hx9 I24 J24. xr Hx9 I25 J25. xr Hx9 I26 J26. xr Hx9 I27 J27.
  pose proof (lf_rw_cells_rel m9 _ _ _ Hrel9 FSd) as FS9.
  assert (Hsp9 : spZ regs9 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs9 2) with (reg_get regs9 2); rewrite J2;
        apply MState.unsigned_lit; lia).
  rewrite <- SEGS. change (Z_to_bv 64 0x14100) with (Z_to_bv 64 LLVM_FREE).
  eapply (g_free B API SEGS AX ERRNO_LOW HFRE FREE stk (spZ regs0) L0 A0 mem0 md0
            (mkFP (@fp_regs fx8) (@fp_csr fx8)) regs9 m9 md8 L4 A4 f nf' (sb_malloc b nf')).
  { exact FR9. } { lia. } { lia. }
  { change (YK11.getr regs9 1) with (reg_get regs9 1). rewrite J1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp9. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp9. unfold ALLOC_STACK. pose proof Hk as Hk'.
    unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs9 4) with (reg_get regs9 4). rewrite J4. exact Htp0. }
  { change (YK11.getr regs9 10) with (reg_get regs9 10). exact J10. }
  { rewrite Eb8, Eb6, Eb4. exact Hfin. }
  { lia. }
  { exact MINE. }
  { exact Hres8. }
  intros L5 A5 regs10 mem10 md10 FR10 Hrp10 (c1 & c2 & Ec1 & Ec2) Hres10 Habove10 Hkept10.
  (* the epilogue *)
  pz Hrp10 J2 2 K2. pz Hrp10 J3 3 K3. pz Hrp10 J4 4 K4. pz Hrp10 J8 8 K8. pz Hrp10 J9 9 K9.
  pz Hrp10 J18 18 K18. pz Hrp10 J19 19 K19. pz Hrp10 J20 20 K20. pz Hrp10 J22 22 K22.
  pz Hrp10 J23 23 K23. pz Hrp10 J24 24 K24. pz Hrp10 J25 25 K25. pz Hrp10 J26 26 K26. pz Hrp10 J27 27 K27.
  assert (M2 : reg_get regs10 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact K2.
  assert (M3 : reg_get regs10 3 = reg_get regs0 3) by exact K3.
  assert (M4 : reg_get regs10 4 = reg_get regs0 4) by exact K4.
  assert (M22 : reg_get regs10 22 = reg_get regs0 22) by exact K22.
  assert (M23 : reg_get regs10 23 = reg_get regs0 23) by exact K23.
  assert (M24 : reg_get regs10 24 = reg_get regs0 24) by exact K24.
  assert (M25 : reg_get regs10 25 = reg_get regs0 25) by exact K25.
  assert (M26 : reg_get regs10 26 = reg_get regs0 26) by exact K26.
  assert (M27 : reg_get regs10 27 = reg_get regs0 27) by exact K27.
  assert (FS10 : rw_cells rsegs mem10 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (lf_rw_cells_frame m9); [exact FS9|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove10. rewrite Hsp9. lia. }
  pose proof (f_norm L5 A5 mem10 md10 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR10 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS10) as FS10n.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx8) (@fp_csr fx8)) regs10
            (YK11.getr regs9 1) mem10 md10 L5 A5
    (qret (@fp_regs fx8) (@fp_csr fx8) (reg_get regs0 1) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 8)
       (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)
       (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26)
       (reg_get regs0 27) (normalize rsegs mem10) (spZ regs0))).
  { exact FR10. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs9 1) with (reg_get regs9 1). rewrite J1.
    rewrite M2, M3, M4, M22, M23, M24, M25, M26, M27.
    apply (s1i (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
             (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 3) (reg_get regs0 4)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx8) (@fp_csr fx8)
             (normalize rsegs mem10) (spZ regs0 - 160) (spZ regs0 - stk)).
    - lia.
    - lia.
    - lia.
    - exact FS10n.
    - intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17.
      apply evt_done. unfold qret. eexists.
      replace (spZ regs0 - 160 + 160) with (spZ regs0) by lia.
      split; [reflexivity|]. do 16 (split; [reflexivity|]). reflexivity. }
  { intros ms (Rq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R11 Ff11 pc11 fc11 m11' HQ11 regs11 m11 Hx11 Hrel11 FR11.
  destruct HQ11 as (Re & HEe & N1 & N2 & N3 & N4 & N8 & N9 & N10 & N18 & N19 & N20 & N21 & N22 & N23 & N24 & N25 &
    N26 & N27).
  injection HEe as ERe EFe EPe ECe EMe. subst Re Ff11 pc11 fc11 m11'.
  apply SR_ret.
  assert (G10f : YK11.getr regs11 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx11); exact N10).
  assert (RP : regs_preserved regs0 regs11).
  { intros r Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                  r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
    rewrite (lf_getr_eqv _ _ _ Hx11).
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[-> | ->]]]]]]]]]]]]]].
    - transitivity (Z_to_bv 64 (spZ regs0)); [exact N2 | unfold spZ; apply Z_to_bv_bv_unsigned].
    - exact N3.
    - exact N4.
    - exact N8.
    - exact N9.
    - exact N18.
    - exact N19.
    - exact N20.
    - exact N21.
    - exact N22.
    - exact N23.
    - exact N24.
    - exact N25.
    - exact N26.
    - exact N27. }
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L5 A5 regs11 m11 md10 Hpre Hsn FR11 G10f RP)
    as (Hpost & Hsn' & Hpay & MI11).
  exists (mkFP (@fp_regs fx8) (@fp_csr fx8)), L5, A5, regs11, m11, md10.
  assert (E1r : YK11.getr regs0 1 = reg_get regs0 1) by reflexivity.
  split; [rewrite SEGS, <- E1r, Hra1, (lf_ret_pc _ Hra); reflexivity|].
  split; [exact Hfrm8|]. split; [exact Hpost|]. split; [exact Hsn'|].
  split; [rewrite sb_free_malloc in Hres10; exact Hres10|].
  split; [exact Hpay|]. split; [exact MI11 | exact I].
Qed.

End Run.

(* decode's llvm_n_bound: the payload size is that of a live block, or 0 *)
Lemma llvm_n_bound : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn11 & _).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  apply (sr_entry stk empty L A regs mem md ra p n pl b j); assumption.
Qed.

End M.
