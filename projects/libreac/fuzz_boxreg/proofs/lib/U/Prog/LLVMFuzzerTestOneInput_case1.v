From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregStep BoxregUpd
  bcmp_c reac_boxreg_find_c lowest_free_base_c reac_boxreg_add_c reac_boxreg_add_inv range_free_c read_mac_c
  reac_boxreg_find bcmp read_mac memcpy mac_is_zero.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require reac_boxreg_add lowest_free_base range_taken
  range_free memset.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_c1p LLVMFuzzerTestOneInput_case2.
Import ListNotations.
Open Scope Z_scope.

Section S.
Hypothesis BCMP_C : bcmp_contract.
Hypothesis FIND_C : reac_boxreg_find_contract.
Hypothesis ADD_C : reac_boxreg_add_contract.
Hypothesis RF_C : range_free_contract.
Hypothesis RM_C : read_mac_contract.

Lemma u1_bcmp : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (pa pb : Z)
    (ls rs : list byte),
  a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 pb -> a2 = Z_to_bv 64 6 ->
  bytes_at rsegs m pa ls -> bytes_at rsegs m pb rs -> length ls = 6%nat -> length rs = 6%nat -> mem_inv rsegs m ->
  (forall (v : Z) (m' : word -> option byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     -256 < v < 256 -> (v = 0 <-> ls = rs) -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 BCMP) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q pa pb ls rs E0 E1 E2 HA HB LA LB MI K. subst a0 a1 a2.
  pose proof (bytes_at_bound rsegs m pa ls HA) as RA. pose proof (bytes_at_bound rsegs m pb rs HB) as RB.
  rewrite LA in RA. rewrite LB in RB.
  destruct (memcmp_model_total ls rs 6 ltac:(lia) ltac:(lia)) as [v Hv].
  destruct (c1_memcmp 6 ls rs v LA LB Hv) as [Rv Iv].
  pose proof BCMP_C as BC. unfold bcmp_contract in BC.
  eapply evt_cut.
  - eapply BC with (ls := ls) (rs := rs) (v := v).
    + rewrite unsigned_lit by lia. exact HA.
    + rewrite unsigned_lit by lia. exact HB.
    + exact Hv.
    + exact MI.
  - intros ms' PO. unfold memcmp_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m'
                    & E & MU & WM & MI' & _ & _).
    subst ms'. apply K; assumption.
Qed.

Lemma u1_find : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (lo r p : Z)
    (bs M : list byte),
  a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 p ->
  bytes_at rsegs m r bs -> length bs = 288%nat -> boxreg_B1 bs -> bytes_at rsegs m p M -> length M = 6%nat ->
  r <> 0 -> r mod 4 = 0 -> p <> 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
  (r + 288 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= r) -> (p + 6 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= p) ->
  mem_inv rsegs m ->
  (forall (z : Z) (m' : word -> option byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     find_result bs M z -> munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> bytes_at rsegs m' r bs -> bytes_at rsegs m' p M ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 z) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOXREG_FIND) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q lo r p bs M E0 E1 HB HL H1 HM HLM Hr0 Hr4 Hp0 ST LO D1 D2 MI K.
  pose proof FIND_C as FC. unfold reac_boxreg_find_contract, REAC_BOXREG_FIND_FRAME in FC.
  eapply evt_cut.
  - eapply FC; eassumption.
  - intros ms' (x5 & x6 & x7 & res & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m'
                & E & MU & WM & MI' & ST' & HB' & HM' & z & Ez & HF).
    subst ms' res. apply K; assumption.
Qed.

Lemma u1_add : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (lo r p k : Z)
    (bs M : list byte),
  a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 k -> -2^31 <= k < 2^31 -> r mod 8 = 0 ->
  r <> 0 -> p <> 0 ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> boxreg_inv bs ->
  bytes_at rsegs m p M -> length M = 6%nat -> (p + 6 <= r \/ r + 288 <= p) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp ->
  (bv_unsigned sp <= r \/ r + 288 <= lo) -> (bv_unsigned sp <= p \/ p + 6 <= lo) -> mem_inv rsegs m ->
  (forall (z : Z) (bs' : list byte) (m' : word -> option byte)
          (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     add_out bs M k z bs' -> bytes_at rsegs m' r bs' ->
     munch [(lo, bv_unsigned sp); (r, r + 288)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 z) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOXREG_ADD) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q lo r p k bs M E0 E1 E2 Hk Hr8 Hr0 Hp0 HB WR HI HM HLM D0 ST LO D1 D2 MI K.
  pose proof ADD_C as AC. unfold reac_boxreg_add_contract, ADD_K in AC.
  eapply evt_cut.
  - eapply AC; eassumption.
  - intros ms' (x5 & x6 & x7 & a0' & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & z & bs'
                & E & Ea & HA & HB' & MU & WM & MI' & ST').
    subst ms' a0'. eapply K; eassumption.
Qed.

Lemma u1_rf : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (t b k f : Z)
    (bs : list byte),
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 k -> a3 = Z_to_bv 64 f ->
  -2^31 <= b < 2^31 -> 1 <= k <= 40 -> 1 <= f <= 40 ->
  bytes_at rsegs m t bs -> length bs = 288%nat -> boxreg_B1 bs -> boxreg_B2 bs -> boxreg_B3 bs -> t mod 4 = 0 ->
  (forall (w : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     (w = 1 /\ range_free_ok bs b k f) \/ (w = 0 /\ ~ range_free_ok bs b k f) ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 w) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RANGE_FREE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q t b k f bs E0 E1 E2 E3 Hb Hk Hf HB HL H1 H2 H3 Ht K.
  pose proof RF_C as RC. unfold range_free_contract in RC.
  eapply evt_cut.
  - eapply RC; eassumption.
  - intros ms' (x5 & x6 & x7 & w & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & E & HW).
    subst ms'.
    destruct HW as [(-> & HR) | (-> & HR)]; [apply (K 1) | apply (K 0)]; [left | right]; split; auto.
Qed.

Lemma u1_end :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c lf k want : Z) (bs ja M bs' : list byte),
  s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 want -> s5 = Z_to_bv 64 want -> s7 = Z_to_bv 64 fab ->
  s9 = Z_to_bv 64 (-1 - r) ->
  -1 <= want < 5 -> 0 <= bx_n bs <= 5 -> -2^31 <= lf < 2^31 ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs' -> wr_at rsegs m r 288 -> boxreg_inv bs' -> bx_fabric bs' = fab ->
  llvm_kept bs bs' (-1) -> (want = bx_n bs -> bx_base bs' want = lf /\ bx_pinned bs' want = 0) ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e -> 0 <= r -> r + 288 <= bv_unsigned sp ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab i e q0 q c lf k want bs ja M bs' E0 E1 E5 E7 E9 Hw Hnb Hlf FR HB WR HI HF HK HBP MU WM MI
    Hq0 Hc Hqe Hr0 Hr.
  subst s0 s1 s5 s7 s9.
  pose proof (c1_inv_len bs' HI) as HL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step. step. c1_if.
  step. step. step. step.
  destruct (Z.eq_dec want (bx_n bs)) as [Ew | Nw].
  - subst want. destruct (HBP eq_refl) as [Eb Ep].
    c1_if.
    step. step. c1_if.
    step. step. step. step. rewrite bx_off56 by lia.
    step. c1_if.
    step.
    pose proof (rd4_bytes_at m r bs' (56 * bx_n bs + 8) HB ltac:(lia) ltac:(rewrite HL; lia)) as R1.
    change (rd4 bs' (56 * bx_n bs + 8)) with (bx_base bs' (bx_n bs)) in R1. rewrite Eb in R1. apply bx_ov4 in R1.
    pose proof (rd4_bytes_at m r bs' (56 * bx_n bs + 20) HB ltac:(lia) ltac:(rewrite HL; lia)) as R2.
    change (rd4 bs' (56 * bx_n bs + 20)) with (bx_pinned bs' (bx_n bs)) in R2. rewrite Ep in R2. apply bx_ov4 in R2.
    step. rewrite ?bx_sx32 by lia.
    step. step. step. step. c1_if.
    step. rewrite ?bx_sx32 by lia. step. c1_if.
    apply evt_done; unfold llvm_case_Q.
    do 23 eexists; exists m, (le8 (Z_to_bv 64 lf) ++ []), (le8 (Z_to_bv 64 k) ++ []), (ja ++ M ++ []), q, c, bs'.
    split; [reflexivity|]. split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|].
    refine (conj MU (conj WM (conj MI (conj (c1_fr_fin _ _ _ _ _ _ _ _ _ _ _ _ _ FR)
              (conj Hq0 (conj Hc (conj Hqe (conj HB (conj WR (conj HI (conj HF HK))))))))))).
  - c1_if.
    apply evt_done; unfold llvm_case_Q.
    do 23 eexists; exists m, (le8 (Z_to_bv 64 lf) ++ []), (le8 (Z_to_bv 64 k) ++ []), (ja ++ M ++ []), q, c, bs'.
    split; [reflexivity|]. split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|].
    refine (conj MU (conj WM (conj MI (conj (c1_fr_fin _ _ _ _ _ _ _ _ _ _ _ _ _ FR)
              (conj Hq0 (conj Hc (conj Hqe (conj HB (conj WR (conj HI (conj HF HK))))))))))).
Qed.

Ltac u1_mac FR HMb :=
  lazymatch type of FR with
  | rw_cells _ ?mm ?A [?x0; ?x1; ?x2; ?x3; ?x4; ?x5; ?x6; ?x7; CB 6 ?M; ?x9; ?x10] =>
      pose proof (c1_cb_at mm A [x0; x1; x2; x3; x4; x5; x6; x7] 6 M [x9; x10] FR) as HMb;
      change (Z.of_nat (cells_size _)) with 338 in HMb
  end.

Ltac u1_box FR HBc :=
  lazymatch type of FR with
  | rw_cells _ ?mm ?A [?x0; ?x1; ?x2; ?x3; ?x4; ?x5; CB 288 ?bs; ?x7; ?x8; ?x9; ?x10] =>
      pose proof (c1_cb_at mm A [x0; x1; x2; x3; x4; x5] 288 bs [x7; x8; x9; x10] FR) as HBc;
      change (Z.of_nat (cells_size _)) with 48 in HBc
  end.

Lemma u1_chk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c lf k known z : Z) (bs ja M bs' : list byte),
  s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 z -> s4 = Z_to_bv 64 known -> s5 = Z_to_bv 64 z -> s7 = Z_to_bv 64 fab ->
  s9 = Z_to_bv 64 (-1 - r) ->
  0 <= k < 256 -> find_result bs M known -> -1 <= known < 5 -> add_out bs M k z bs' ->
  (z = bx_n bs -> bx_base bs' z = lf /\ bx_pinned bs' z = 0) -> -2^31 <= lf < 2^31 ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs' -> wr_at rsegs m r 288 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 4096 <= r -> r mod 16 = 0 -> r + 288 <= lo ->
  bv_unsigned sp + 464 <= 2 ^ 47 ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13378) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab i e q0 q c lf k known z bs ja M bs' E0 E1 E4 E5 E7 E9 Hk HFk Hkn HA HBP Hlf HI HF HM FR HB WR
    ST LO Hr4k Hr16 Hr HX MU WM MI Hq0 Hc Hqe.
  subst s0 s1 s4 s5 s7 s9.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn.
  pose proof (reac_boxreg_add_keeps_inv_holds bs M bs' k z HI HM HA) as HI'.
  pose proof (c1_inv_len bs' HI') as HL'. pose proof (c1_inv_n bs' HI') as Hn'.
  pose proof (c1_add_range bs M k z bs' HI HA) as Hz.
  pose proof (c1_add_fab bs M k z bs' HI HM HA) as HF'. rewrite HF in HF'.
  pose proof (c1_kept bs M k z bs' HI HM HA) as HK.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step.
  destruct (Z_lt_le_dec z 0) as [Hz0 | Hz0].
  - c1_if.
    eapply u1_end with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := lf)
      (k := k) (want := z) (bs := bs) (ja := ja) (M := M) (bs' := bs');
      first [ reflexivity | eassumption | lia ].
  - c1_if.
    destruct (c1_add_pos bs M k z bs' HI HM HA Hz0) as (HZ & Ao & _ & Hn5 & Hh' & Hcase).
    pose proof (rd4_bytes_at m r bs' 280 HB ltac:(lia) ltac:(rewrite HL'; lia)) as R280.
    change (rd4 bs' 280) with (bx_n bs') in R280. apply bx_ov4 in R280.
    pose proof Hh' as (Hzn & Hmz & _).
    step. rewrite ?bx_sx32 by lia.
    step. c1_if.
    step. step. c1_if.
    step. step. step. rewrite bx_off56 by lia.
    step. c1_if.
    step. step. step. step. step.
    u1_mac FR HMb.
    eapply u1_bcmp with (pa := r + 56 * z) (pb := bv_unsigned sp + 338) (ls := bx_mac bs' z) (rs := M);
      [ fnd_eq | fnd_eq | reflexivity
      | exact (bytes_at_bsub m r bs' (56 * z) 6 HB ltac:(lia) ltac:(lia) ltac:(rewrite HL'; lia))
      | exact HMb | apply c1_mac_len; [exact HL' | lia] | exact HM | exact MI | ].
    intros v1 m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv1 Iv1 MU1 WM1 MI1.
    c1_retpc.
    destruct (c1_tr0 m0 m m1 lo (bv_unsigned sp) r _ bs' MU WM FR WR ST HB MU1 WM1)
      as (MU' & WM' & FR' & WR' & ST' & HB').
    clear MU WM FR WR ST HB MU1 WM1 HMb MI R280.
    assert (V0 : v1 = 0) by (apply Iv1; exact Hmz). subst v1.
    step. c1_if.
    step. step. step.
    u1_mac FR' HMb.
    eapply u1_find with (lo := lo) (r := r) (p := bv_unsigned sp + 338) (bs := bs') (M := M);
      [ fnd_eq | fnd_eq | exact HB' | exact HL' | unfold boxreg_B1; lia | exact HMb | exact HM | lia | mlia | lia
      | exact ST' | lia | lia | lia | exact MI1 | ].
    intros z2 m2 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HF2 MU2 WM2 MI2 ST2 HB2 HM2.
    c1_retpc.
    pose proof (c1_find_held bs' M z z2 HZ Hh' HF2) as Ez2. subst z2.
    destruct (c1_tr1 m0 m1 m2 lo (bv_unsigned sp) r _ _ _ MU' WM' FR' WR' MU2 WM2 ltac:(lia) ltac:(lia))
      as (MU'' & WM'' & FR'' & WR'').
    clear MU' WM' FR' WR' MU2 WM2 MI1 ST' HB' HMb.
    step. c1_if.
    step. step. step. step.
    u1_mac FR'' HMb.
    eapply u1_add with (lo := lo) (r := r) (p := bv_unsigned sp + 338) (k := k) (bs := bs') (M := M);
      [ fnd_eq | fnd_eq | fnd_eq | lia | mlia | lia | lia | exact HB2 | exact WR'' | exact HI' | exact HMb
      | exact HM | lia | exact ST2 | lia | lia | lia | exact MI2 | ].
    intros z3 bs3 m3 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HA3 HB3 MU3 WM3 MI3 ST3.
    c1_retpc.
    destruct (c1_add_again bs' M k z z3 bs3 HZ ltac:(rewrite HF'; rewrite <- HF; exact Ao) Hh' HA3) as [Ez3 Eb3].
    subst z3 bs3.
    destruct (c1_tr2 m0 m2 m3 lo (bv_unsigned sp) r _ MU'' WM'' FR'' WR'' MU3 WM3 ltac:(lia) ltac:(lia))
      as (MU4 & WM4 & FR4 & WR4).
    clear MU'' WM'' FR'' WR'' MU3 WM3 MI2 ST2 HB2 HM2 HMb.
    step. c1_if.
    step. step.
    destruct (Z_lt_le_dec known 0) as [Kn | Kp].
    + c1_if.
      assert (Hnch : bx_nch bs' z = k).
      { destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso | exact Hk'].
        pose proof (c1_find_none bs M known HFk Kn HZ) as NH. destruct Hh as (Hi & Mi & _). exact (NH z Hi Mi). }
      pose proof (rd4_bytes_at m3 r bs' (56 * z + 12) HB3 ltac:(lia) ltac:(rewrite HL'; lia)) as R12.
      change (rd4 bs' (56 * z + 12)) with (bx_nch bs' z) in R12. rewrite Hnch in R12. apply bx_ov4 in R12.
      step. rewrite ?bx_sx32 by lia.
      step. step. c1_if.
      eapply u1_end with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := lf)
        (k := k) (want := z) (bs := bs) (ja := ja) (M := M) (bs' := bs');
        first [ reflexivity | eassumption | lia ].
    + c1_if.
      eapply u1_end with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := lf)
        (k := k) (want := z) (bs := bs) (ja := ja) (M := M) (bs' := bs');
        first [ reflexivity | eassumption | lia ].
Qed.

Lemma u1_main :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c lf k v want : Z) (bs ja M : list byte),
  s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 want -> s2 = Z_to_bv 64 (Z.b2z (c1_okb k fab)) -> s3 = Z_to_bv 64 v ->
  s7 = Z_to_bv 64 fab -> s9 = Z_to_bv 64 (-1 - r) ->
  0 <= k < 256 -> -256 < v < 256 -> (v = 0 <-> M = zero6) -> c1_wantP bs M k lf want -> -2^31 <= lf < 2^31 ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 4096 <= r -> r mod 16 = 0 -> r + 288 <= lo ->
  bv_unsigned sp + 464 <= 2 ^ 47 ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13334) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab i e q0 q c lf k v want bs ja M E0 E1 E2 E3 E7 E9 Hk Hv Iv HW Hlf HI HF HM FR HB WR
    ST LO Hr4k Hr16 Hr HX MU WM MI Hq0 Hc Hqe.
  subst s0 s1 s2 s3 s7 s9.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step. step. step.
  u1_mac FR HMb.
  eapply u1_find with (lo := lo) (r := r) (p := bv_unsigned sp + 338) (bs := bs) (M := M);
    [ fnd_eq | fnd_eq | exact HB | exact HL | unfold boxreg_B1; lia | exact HMb | exact HM | lia | mlia | lia
    | exact ST | lia | lia | lia | exact MI | ].
  intros known m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HF1 MU1 WM1 MI1 ST1 HB1 HM1.
  c1_retpc.
  destruct (c1_tr1 m0 m m1 lo (bv_unsigned sp) r _ _ _ MU WM FR WR MU1 WM1 ltac:(lia) ltac:(lia))
    as (MU' & WM' & FR' & WR').
  clear MU WM FR WR MU1 WM1 MI ST HB HMb.
  step. step. step. step. step.
  eapply u1_add with (lo := lo) (r := r) (p := bv_unsigned sp + 338) (k := k) (bs := bs) (M := M);
    [ fnd_eq | fnd_eq | fnd_eq | lia | mlia | lia | lia | exact HB1 | exact WR' | exact HI | exact HM1
    | exact HM | lia | exact ST1 | lia | lia | lia | exact MI1 | ].
  intros z bs' m2 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HA HB2 MU2 WM2 MI2 ST2.
  c1_retpc.
  destruct (c1_tr2 m0 m1 m2 lo (bv_unsigned sp) r _ MU' WM' FR' WR' MU2 WM2 ltac:(lia) ltac:(lia))
    as (MU3 & WM3 & FR3 & WR3).
  clear MU' WM' FR' WR' MU2 WM2 MI1 ST1 HB1 HM1.
  destruct (c1_add_want bs M k lf want z bs' HI HM HW HA) as [Ezw HBP]. subst want.
  pose proof (c1_add_range bs M k z bs' HI HA) as Hz.
  pose proof (c1_find_range bs M known HF1 Hn) as Hkn.
  step.
  destruct (Z.eq_dec v 0) as [Ev | Nv];
    [ assert (Ez : z = -1) by (apply Iv in Ev; subst M; exact (c1_add_zero _ _ _ _ HA));
      step; c1_if; step; step; c1_if
    | step; c1_if ].
  all: step; step; step; step.
  all: destruct (c1_okb k fab) eqn:OK; destruct (Z_lt_le_dec known 0) as [Kn | Kp].
  all: try (assert (Ao : add_width_ok k (bx_fabric bs)) by (rewrite HF; apply c1_okb_spec; exact OK);
            pose proof (c1_known bs M k known z bs' HF1 Kp Ao HA) as Ekz; subst known;
            c1_if; step; c1_if).
  all: try c1_if.
  all: eapply u1_chk with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := lf)
         (k := k) (z := z) (bs := bs) (ja := ja) (M := M) (bs' := bs');
    first [ reflexivity | eassumption | lia ].
Qed.

Ltac u1_weq := first [ reflexivity | fnd_eq | apply bv_eq; vm_compute; reflexivity
                     | apply bv_eq; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Ltac u1_st0 :=
  lazymatch goal with
  | FR : rw_cells rsegs ?mm (bv_unsigned ?sp) ?cs |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SO := fresh "SO" in
      assert (SO : store_ok rsegs mm sp 8 = true)
        by (eapply (rw_cells_store_ok_at rsegs mm (bv_unsigned sp) cs 0 _ 8 sp FR);
            [ first [ reflexivity | cells_cbv; reflexivity ] | first [ reflexivity | cells_cbv; reflexivity ]
            | symmetry; apply wa_of_var; lia ]);
      step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 sp ?bb) _) =>
          replace (write_to_mem m1 sp bb) with (write_to_mem m1 (wa (bv_unsigned sp + Z.of_nat 0)) bb)
            by (f_equal; apply wa_of_var; lia)
      end;
      clear SO; mem_after_store
  end.

Lemma u1_found :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c k v b : Z) (bs ja M : list byte),
  s0 = Z_to_bv 64 r -> s2 = Z_to_bv 64 (Z.b2z (c1_okb k fab)) -> s3 = Z_to_bv 64 v -> s4 = Z_to_bv 64 b ->
  s7 = Z_to_bv 64 fab -> s9 = Z_to_bv 64 (-1 - r) ->
  0 <= b -> c1_lfres bs k fab b ->
  add_width_ok k (bx_fabric bs) -> M <> zero6 -> add_none_held bs M -> add_none_unbound bs k -> bx_n bs < 5 ->
  0 <= k < 256 -> -256 < v < 256 -> (v = 0 <-> M = zero6) ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 4096 <= r -> r mod 16 = 0 -> r + 288 <= lo ->
  bv_unsigned sp + 464 <= 2 ^ 47 ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1351c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab i e q0 q c k v b bs ja M E0 E2 E3 E4 E7 E9 Hb0 Hlf Ao Mz Hnh Hnu Hn5 Hk Hv Iv HI HF HM FR HB WR
    ST LO Hr4k Hr16 Hr HX MU WM MI Hq0 Hc Hqe.
  subst s0 s2 s3 s4 s7 s9.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (c1_inv_fab bs HI) as Hfb. pose proof (c1_inv_len bs HI) as HL.
  assert (Hbf : b <= fab - k) by (destruct Hlf as [(E & _) | (H & _)]; lia).
  assert (HW : c1_wantP bs M k b (bx_n bs)).
  { right; right; right; right. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
    split; [exact Hnu|]. split; [lia|]. split; [reflexivity|]. split; [lia | rewrite HF; exact Hlf]. }
  u1_st0. step. step.
  eapply u1_main with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := b)
    (k := k) (v := v) (want := bx_n bs) (bs := bs) (ja := ja) (M := M);
    first [ reflexivity | eassumption | lia ].
Qed.

Lemma u1_lfl : forall (d : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c k v b : Z) (bs ja M : list byte),
  s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 (fab - k + 1) -> s2 = Z_to_bv 64 (Z.b2z (c1_okb k fab)) ->
  s3 = Z_to_bv 64 v -> s4 = Z_to_bv 64 b -> s7 = Z_to_bv 64 fab -> s9 = Z_to_bv 64 (-1 - r) ->
  fab - k - b = Z.of_nat d -> 0 <= b -> (forall b', 0 <= b' < b -> ~ range_free_ok bs b' k fab) ->
  add_width_ok k (bx_fabric bs) -> M <> zero6 -> add_none_held bs M -> add_none_unbound bs k -> bx_n bs < 5 ->
  0 <= k < 256 -> -256 < v < 256 -> (v = 0 <-> M = zero6) ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 4096 <= r -> r mod 16 = 0 -> r + 288 <= lo ->
  bv_unsigned sp + 464 <= 2 ^ 47 -> bv_unsigned sp mod 16 = 0 ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13310) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH]; intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m0 m lo r fab i e q0 q c k v b bs ja M E0 E1 E2 E3 E4 E7 E9 Hd Hb0 Hlow Ao Mz Hnh Hnu Hn5 Hk Hv Iv
    HI HF HM FR HB WR ST LO Hr4k Hr16 Hr HX Hsp16 MU WM MI Hq0 Hc Hqe.
  all: subst s0 s1 s2 s3 s4 s7 s9.
  all: pose proof (c1_inv_len bs HI) as HL; pose proof (c1_inv_n bs HI) as Hn; pose proof (c1_inv_fab bs HI) as Hfb;
       pose proof HI as ((_ & HB1 & HB2 & HB3 & _) & _); pose proof Ao as (_ & Ak & Akf);
       pose proof (bv_unsigned_in_range 64 sp) as Rsp; change (bv_modulus 64) with (2 ^ 64) in Rsp.
  all: u1_box FR HBc.
  all: step; step; step; step; step.
  all: eapply u1_rf with (t := bv_unsigned sp + 48) (b := b) (k := k) (f := fab) (bs := bs);
         [ u1_weq | u1_weq | u1_weq | u1_weq | lia | lia | lia | exact HBc | exact HL | exact HB1 | exact HB2
         | exact HB3 | mlia | ].
  all: intros w x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HW; c1_retpc; step.
  all: destruct HW as [(-> & Hok) | (-> & Hnok)]; c1_if;
       [ assert (HLF : c1_lfres bs k fab b) by (right; split; [lia|]; split; [exact Hok | exact Hlow]);
         eapply u1_found with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (k := k)
           (v := v) (b := b) (bs := bs) (ja := ja) (M := M);
         first [ reflexivity | eassumption | lia ]
       | step; rewrite ?fnd_addiw by lia; step ].
  all: assert (Hlow' : forall b', 0 <= b' < b + 1 -> ~ range_free_ok bs b' k fab)
         by (intros b' Hb'; destruct (Z.eq_dec b' b) as [-> | Nb]; [exact Hnok | apply Hlow; lia]).
  - assert (Eb : b = fab - k) by lia. c1_if. step.
    assert (HW : c1_wantP bs M k (-1) (-1)).
    { right; right; right; left. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
      split; [exact Hnu|]. split; [|reflexivity]. right. left. split; [reflexivity|].
      rewrite HF. intros b' Hb'. apply Hlow'. lia. }
    eapply u1_main with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := -1)
      (k := k) (v := v) (want := -1) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | eassumption | lia ].
  - c1_if.
    eapply IH with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (k := k) (v := v)
      (b := b + 1) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | eassumption | lia ].
Qed.

Lemma u1_decide :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c h u v k : Z) (bs ja M : list byte),
  s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 h -> s3 = Z_to_bv 64 v -> s4 = Z_to_bv 64 u -> s9 = Z_to_bv 64 (-1 - r) ->
  0 <= k < 256 -> -256 < v < 256 -> (v = 0 <-> M = zero6) ->
  c1_sh bs M v (bx_n bs) h -> c1_su bs k (bx_n bs) u ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 4096 <= r -> r mod 16 = 0 -> r + 288 <= lo ->
  bv_unsigned sp + 464 <= 2 ^ 47 -> bv_unsigned sp mod 16 = 0 ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13178) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab i e q0 q c h u v k bs ja M E0 E1 E3 E4 E9 Hk Hv Iv HSH SU HI HF HM FR HB WR
    ST LO Hr4k Hr16 Hr HX Hsp16 MU WM MI Hq0 Hc Hqe.
  subst s0 s1 s3 s4 s9.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn. pose proof (c1_inv_fab bs HI) as Hfb.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step. step. step. step. step. step. step. step. step. step.
  fold (c1_okx k fab). rewrite (c1_okb_val k fab) by lia.
  pose proof (c1_okb_spec k fab) as OKS.
  destruct (c1_okb k fab) eqn:OK; [change (Z.b2z true) with 1 | change (Z.b2z false) with 0].
  2: { step. c1_if. step.
       assert (HW : c1_wantP bs M k (-1) (-1)).
       { left. split; [|reflexivity]. intros (Ao & _). rewrite HF in Ao. apply OKS in Ao. discriminate. }
       eapply u1_main with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := -1)
         (k := k) (v := v) (want := -1) (bs := bs) (ja := ja) (M := M);
         first [ reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  assert (Ao : add_width_ok k (bx_fabric bs)) by (rewrite HF; apply OKS; reflexivity).
  pose proof Ao as (Ake & Ak & Akf).
  step. c1_if. step.
  destruct (Z.eq_dec v 0) as [Ev | Nv].
  { c1_if. step.
    assert (HW : c1_wantP bs M k (-1) (-1)).
    { left. split; [|reflexivity]. intros (_ & Az). apply Az. apply Iv. exact Ev. }
    eapply u1_main with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := -1)
      (k := k) (v := v) (want := -1) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  assert (Mz : M <> zero6) by (intros Ez; apply Nv; apply Iv; exact Ez).
  c1_if. step.
  destruct HSH as [(Eh & [Ev' | Hnh]) | (Hv0 & Hh & Hmh & Hnh)]; [contradiction | |].
  2: { c1_if.
       assert (HW : c1_wantP bs M k (-1) h).
       { right; left. split; [exact Ao|]. split; [exact Mz|]. split; [lia|]. split; [exact Hmh | exact Hnh]. }
       eapply u1_main with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := -1)
         (k := k) (v := v) (want := h) (bs := bs) (ja := ja) (M := M);
         first [ reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  subst h. c1_if. step.
  destruct SU as [(Eu & Hnu) | (Hu & Hmu & Hku & Hnu)].
  2: { c1_if. step. step.
       assert (HW : c1_wantP bs M k (-1) u).
       { right; right; left. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
         split; [lia|]. split; [exact Hmu|]. split; [exact Hku | exact Hnu]. }
       eapply u1_main with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := -1)
         (k := k) (v := v) (want := u) (bs := bs) (ja := ja) (M := M);
         first [ reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  subst u. c1_if. step. step. step.
  destruct (Z_lt_le_dec 4 (bx_n bs)) as [N5 | N4].
  { c1_if. step.
    assert (HW : c1_wantP bs M k (-1) (-1)).
    { right; right; right; left. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
      split; [exact Hnu|]. split; [left; lia | reflexivity]. }
    eapply u1_main with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (lf := -1)
      (k := k) (v := v) (want := -1) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  c1_if. step. step. step. step. step. step.
  rewrite ?(unsigned_lit fab), ?(unsigned_lit k) by lia.
  rewrite (c1_land (fab - k)) by lia.
  step. rewrite ?fnd_addiw by lia.
  eapply u1_lfl with (d := Z.to_nat (fab - k)) (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q)
    (c := c) (k := k) (v := v) (b := 0) (bs := bs) (ja := ja) (M := M);
    first [ reflexivity | (rewrite OK; reflexivity) | eassumption | lia | (intros; lia) ].
Qed.

Ltac u1_sh0 := left; split; [reflexivity | right; intros; exfalso; lia].
Ltac u1_su0 := left; split; [reflexivity | intros; exfalso; lia].

Lemma u1_body1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (i h v : Z)
    (bs M : list byte),
  s1 = Z_to_bv 64 h -> s2 = Z_to_bv 64 i -> s3 = Z_to_bv 64 v -> s6 = Z_to_bv 64 i -> s7 = Z_to_bv 64 (12 + 56 * i) ->
  s8 = Z_to_bv 64 (-1 - (bv_unsigned sp + 48)) -> s10 = Z_to_bv 64 (bv_unsigned sp + 48) ->
  0 <= i <= 4 -> length bs = 288%nat -> length M = 6%nat -> -256 < v < 256 -> c1_sh bs M v i h ->
  bytes_at rsegs m (bv_unsigned sp + 48) bs -> bytes_at rsegs m (bv_unsigned sp + 338) M -> mem_inv rsegs m ->
  bv_unsigned sp + 464 <= 2 ^ 47 ->
  (forall (h' : Z) (m' : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     c1_sh bs M v (i + 1) h' -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 h') a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13120) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x130e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q i h v bs M E1 E2 E3 E6 E7 E8 E10 Hi HL HLM Hv HSH HB HM MI HX K.
  subst s1 s2 s3 s6 s7 s8 s10.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (bytes_at_bsub m (bv_unsigned sp + 48) bs (56 * i) 6 HB ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia))
    as HBi.
  change (bsub bs (56 * i) 6) with (bx_mac bs i) in HBi.
  pose proof (c1_mac_len bs i HL Hi) as LBi.
  step.
  destruct HSH as [(Eh & Hvh) | (Hv0 & Hh & Hmh & Hnh)].
  - subst h. c1_if. step.
    destruct (Z.eq_dec v 0) as [Ev | Nv].
    + c1_if. eapply K; [apply c1_sh_v0; exact Ev | apply munch_refl | apply wmono_refl | exact MI].
    + c1_if. step. step. c1_if. step. step. c1_if. step. step. step. step. step.
      eapply u1_bcmp with (pa := bv_unsigned sp + 48 + 56 * i) (pb := bv_unsigned sp + 338) (ls := bx_mac bs i)
        (rs := M); [ u1_weq | u1_weq | u1_weq | exact HBi | exact HM | exact LBi | exact HLM | exact MI | ].
      intros v1 m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv1 Iv1 MU1 WM1 MI1.
      c1_retpc. step. step.
      destruct (Z.eq_dec v1 0) as [E1 | N1].
      * c1_if. step.
        eapply K; [ | exact MU1 | exact WM1 | exact MI1 ].
        apply c1_sh_hit; [left; split; [reflexivity | exact Hvh] | exact Nv | lia | apply Iv1; exact E1].
      * c1_if. step. step.
        eapply K; [ | exact MU1 | exact WM1 | exact MI1 ].
        apply c1_sh_miss; [left; split; [reflexivity | exact Hvh] | lia | intros E; apply N1; apply Iv1; exact E].
  - c1_if. eapply K; [ | apply munch_refl | apply wmono_refl | exact MI ].
    apply c1_sh_keep; [right; split; [exact Hv0|]; split; [exact Hh|]; split; [exact Hmh | exact Hnh] | lia].
Qed.

Lemma u1_body2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (i u k : Z)
    (w0 w1 w2 w4 w5 w9 w10 : word) (bs ja M : list byte),
  s2 = Z_to_bv 64 i -> s4 = Z_to_bv 64 u -> s6 = Z_to_bv 64 i -> s7 = Z_to_bv 64 (12 + 56 * i) ->
  s8 = Z_to_bv 64 (-1 - (bv_unsigned sp + 48)) -> s10 = Z_to_bv 64 (bv_unsigned sp + 48) ->
  0 <= i <= 4 -> length bs = 288%nat -> 0 <= k < 256 -> c1_su bs k i u ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 w0; C8 w1; C8 w2; C8 (Z_to_bv 64 k); C8 w4; C8 w5; CB 288 bs; CB 2 ja; CB 6 M; C8 w9; C8 w10] ->
  mem_inv rsegs m -> bv_unsigned sp + 464 <= 2 ^ 47 ->
  (forall (u' : Z) (m' : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     c1_su bs k (i + 1) u' -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 (Z_to_bv 64 u') s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13168) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13120) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q i u k w0 w1 w2 w4 w5 w9 w10 bs ja M E2 E4 E6 E7 E8 E10 Hi HL Hk SU FR MI HX K.
  subst s2 s4 s6 s7 s8 s10.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  u1_box FR HB.
  pose proof (bytes_at_bsub m (bv_unsigned sp + 48) bs (56 * i) 6 HB ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia))
    as HBi.
  change (bsub bs (56 * i) 6) with (bx_mac bs i) in HBi.
  pose proof (c1_mac_len bs i HL Hi) as LBi.
  step.
  destruct SU as [(Eu & Hnu) | (Hu & Hmu & Hku & Hnu)].
  - subst u. c1_if. step. step. c1_if. step. step. c1_if. step. step. step. step. step.
    eapply u1_bcmp with (pa := bv_unsigned sp + 48 + 56 * i) (pb := 0x10392) (ls := bx_mac bs i) (rs := zero6);
      [ u1_weq | u1_weq | u1_weq | exact HBi | exact (c1_zero m MI) | exact LBi | reflexivity | exact MI | ].
    intros v2 m2 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv2 Iv2 MU2 WM2 MI2.
    c1_retpc. step.
    destruct (Z.eq_dec v2 0) as [E2 | N2].
    + c1_if.
      pose proof (bytes_at_transport rsegs [] m m2 _ _ HB MU2 I) as HB2.
      pose proof (rw_cells_transport rsegs [] m m2 _ _ FR MU2 WM2 I) as FR2.
      clear FR HB HBi.
      pose proof (rd4_bytes_at m2 (bv_unsigned sp + 48) bs (56 * i + 12) HB2 ltac:(lia) ltac:(rewrite HL; lia))
        as R12.
      change (rd4 bs (56 * i + 12)) with (bx_nch bs i) in R12. apply bx_ov4 in R12.
      pose proof (rd4_range bs (56 * i + 12)) as Rn. change (rd4 bs (56 * i + 12)) with (bx_nch bs i) in Rn.
      step. step. rewrite ?bx_sx32 by lia. step. step. step.
      destruct (Z.eq_dec (bx_nch bs i) k) as [Ek | Nk].
      * c1_if. step.
        eapply K; [ | exact MU2 | exact WM2 | exact MI2 ].
        apply c1_su_hit; [left; split; [reflexivity | exact Hnu] | lia | apply Iv2; exact E2 | exact Ek].
      * c1_if. step. step.
        eapply K; [ | exact MU2 | exact WM2 | exact MI2 ].
        apply c1_su_miss; [left; split; [reflexivity | exact Hnu] | lia | intros (_ & E); exact (Nk E)].
    + c1_if.
      eapply K; [ | exact MU2 | exact WM2 | exact MI2 ].
      apply c1_su_miss; [left; split; [reflexivity | exact Hnu] | lia | intros (E & _); apply N2; apply Iv2; exact E].
  - c1_if. eapply K; [ | apply munch_refl | apply wmono_refl | exact MI ].
    apply c1_su_keep; [right; split; [exact Hu|]; split; [exact Hmu|]; split; [exact Hku | exact Hnu] | lia].
Qed.

Lemma u1_loop : forall (d : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (i h u v k : Z)
    (w0 w1 w2 w4 w5 w9 w10 : word) (bs ja M : list byte),
  s1 = Z_to_bv 64 h -> s2 = Z_to_bv 64 i -> s3 = Z_to_bv 64 v -> s4 = Z_to_bv 64 u -> s5 = Z_to_bv 64 (bx_n bs) ->
  s6 = Z_to_bv 64 i -> s7 = Z_to_bv 64 (12 + 56 * i) -> s8 = Z_to_bv 64 (-1 - (bv_unsigned sp + 48)) ->
  s10 = Z_to_bv 64 (bv_unsigned sp + 48) ->
  bx_n bs - i = Z.of_nat (S d) -> 0 <= i -> bx_n bs <= 5 -> length bs = 288%nat -> length M = 6%nat ->
  -256 < v < 256 -> 0 <= k < 256 -> c1_sh bs M v i h -> c1_su bs k i u ->
  rw_cells rsegs m (bv_unsigned sp)
    [C8 w0; C8 w1; C8 w2; C8 (Z_to_bv 64 k); C8 w4; C8 w5; CB 288 bs; CB 2 ja; CB 6 M; C8 w9; C8 w10] ->
  mem_inv rsegs m -> bv_unsigned sp + 464 <= 2 ^ 47 ->
  (forall (h' u' : Z) (m' : word -> option byte)
          (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s6' s7' t3' t4' t5' t6' : word),
     c1_sh bs M v (bx_n bs) h' -> c1_su bs k (bx_n bs) u' -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 h') a0' a1' a2' a3' a4' a5' a6' a7'
                          s2' s3 (Z_to_bv 64 u') s5 s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13178) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x130e4) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH]; intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Q i h u v k w0 w1 w2 w4 w5 w9 w10 bs ja M E1 E2 E3 E4 E5 E6 E7 E8 E10 Hd Hi Hn5 HL HLM Hv Hk
    HSH SU FR MI HX K;
    u1_box FR HB; u1_mac FR HM;
    (eapply u1_body1 with (i := i) (h := h) (v := v) (bs := bs) (M := M);
      [ exact E1 | exact E2 | exact E3 | exact E6 | exact E7 | exact E8 | exact E10 | lia | exact HL | exact HLM
      | exact Hv | exact HSH | exact HB | exact HM | exact MI | exact HX | ]);
    intros h1 m1 ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 SH1 MU1 WM1 MI1;
    pose proof (rw_cells_transport rsegs [] m m1 _ _ FR MU1 WM1 I) as FR1;
    (eapply u1_body2 with (i := i) (u := u) (k := k) (bs := bs) (ja := ja) (M := M);
      [ exact E2 | exact E4 | exact E6 | exact E7 | exact E8 | exact E10 | lia | exact HL | exact Hk | exact SU
      | exact FR1 | exact MI1 | exact HX | ]);
    intros u1 m2 ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 SU1 MU2 WM2 MI2;
    subst s1 s2 s3 s4 s5 s6 s7 s8 s10;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; change (bv_modulus 64) with (2 ^ 64) in Rsp;
    step; step; step; rewrite ?fnd_addiw by lia; step.
  - c1_if.
    replace (i + 1) with (bx_n bs) in SH1, SU1 by lia.
    eapply K; [ exact SH1 | exact SU1 | eapply munch_trans; [exact MU1 | exact MU2]
              | eapply wmono_trans; [exact WM1 | exact WM2] | exact MI2 ].
  - c1_if.
    pose proof (rw_cells_transport rsegs [] m1 m2 _ _ FR1 MU2 WM2 I) as FR2.
    eapply IH with (i := i + 1) (h := h1) (u := u1) (v := v) (k := k) (bs := bs) (ja := ja) (M := M);
      [ first [ reflexivity | u1_weq | exact SH1 | exact SU1 | exact FR2 | exact MI2 | exact HX | exact Hn5
              | exact HL | exact HLM | exact Hv | exact Hk | lia ] .. | ].
    intros h' u' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s6' s7' t3' t4' t5' t6' SH' SU' MU' WM' MI'.
    eapply K; [ exact SH' | exact SU' | | | exact MI' ].
    + eapply munch_trans; [exact MU1 | eapply munch_trans; [exact MU2 | exact MU']].
    + eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM']].
Qed.

Lemma u1_cmp :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c k : Z) (j0 bs ja M : list byte),
  s0 = Z_to_bv 64 r -> s8 = Z_to_bv 64 (-1 - (bv_unsigned sp + 48)) -> s9 = Z_to_bv 64 (-1 - r) ->
  s10 = Z_to_bv 64 (bv_unsigned sp + 48) ->
  0 <= k < 256 -> boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 4096 <= r -> r mod 16 = 0 -> r + 288 <= lo ->
  bv_unsigned sp + 464 <= 2 ^ 47 -> bv_unsigned sp mod 16 = 0 ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x130a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab i e q0 q c k j0 bs ja M E0 E8 E9 E10 Hk HI HF HM FR HB WR ST LO Hr4k Hr16 Hr HX Hsp16
    MU WM MI Hq0 Hc Hqe.
  subst s8 s10.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  u1_mac FR HMb.
  step. step. step. step. step.
  eapply u1_bcmp with (pa := bv_unsigned sp + 338) (pb := 0x10392) (ls := M) (rs := zero6);
    [ u1_weq | u1_weq | u1_weq | exact HMb | exact (c1_zero m MI) | exact HM | reflexivity | exact MI | ].
  intros v m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv Iv MU1 WM1 MI1.
  c1_retpc.
  destruct (c1_tr0 m0 m m1 lo (bv_unsigned sp) r _ bs MU WM FR WR ST HB MU1 WM1)
    as (MU' & WM' & FR' & WR' & ST' & HB').
  clear MU WM FR WR ST HB MU1 WM1 HMb MI.
  u1_box FR' HBc.
  step.
  pose proof (rd4_bytes_at m1 (bv_unsigned sp + 48) bs 280 HBc ltac:(lia) ltac:(rewrite HL; lia)) as R280.
  change (rd4 bs 280) with (bx_n bs) in R280. apply bx_ov4 in R280.
  match type of FR' with ?T => change T with (bx_keep T) in FR' end.
  step.
  unfold bx_keep in FR'.
  rewrite ?bx_sx32 by lia.
  clear R280.
  step.
  u1_st0.
  lazymatch type of FR' with rw_cells _ _ _ (C8 ?w :: _) => replace w with (Z_to_bv 64 (-1)) in FR' by u1_weq end.
  step. step. step.
  destruct (Z.eq_dec (bx_n bs) 0) as [N0 | N1].
  - c1_if.
    eapply u1_decide with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c)
      (h := -1) (u := -1) (v := v) (k := k) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | eassumption | lia | u1_sh0 | u1_su0 | u1_weq ].
  - c1_if. step. step. step. step. step.
    eapply (u1_loop (Z.to_nat (bx_n bs - 1))) with (i := 0) (h := -1) (u := -1) (v := v) (k := k) (bs := bs)
      (ja := ja) (M := M);
      [ first [ reflexivity | eassumption | lia | u1_sh0 | u1_su0 | u1_weq ] .. | ].
    intros h' u' mK ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s6' s7' t3' t4' t5' t6' SH' SU' MUK WMK MIK.
    destruct (c1_tr0 m0 _ mK lo (bv_unsigned sp) r _ bs MU' WM' FR' WR' ST' HB' MUK WMK)
      as (MU'' & WM'' & FR'' & WR'' & ST'' & HB'').
    eapply u1_decide with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c)
      (h := h') (u := u') (v := v) (k := k) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | exact SH' | exact SU' | exact MU'' | exact WM'' | exact FR'' | exact WR'' | exact ST''
            | exact HB'' | exact MIK | eassumption | lia ].
Qed.

Lemma u1_wid :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab i e q0 q c : Z) (j0 j1 bs ja M rest : list byte),
  s0 = Z_to_bv 64 r -> s6 = Z_to_bv 64 1 -> s8 = Z_to_bv 64 (-1 - (bv_unsigned sp + 48)) ->
  s9 = Z_to_bv 64 (-1 - r) -> s10 = Z_to_bv 64 (bv_unsigned sp + 48) ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i);
     C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 2 ja; CB 6 M; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m q rest -> Z.of_nat (length rest) = c ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 4096 <= r -> r mod 16 = 0 -> r + 288 <= lo ->
  bv_unsigned sp + 464 <= 2 ^ 47 -> bv_unsigned sp mod 16 = 0 ->
  munch [(lo, bv_unsigned sp + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 1 <= q -> q + c = e -> e <= lo ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab i e q0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12eec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab i e q0 q c j0 j1 bs ja M rest E0 E6 E8 E9 E10 HI HF HM FR HP HPl HB WR ST LO Hr4k Hr16 Hr
    HX Hsp16 MU WM MI Hq0 Hq1 Hqe Hel.
  subst s6.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step. step.
  destruct rest as [|x rest]; cbn [length] in HPl.
  - c1_if. step.
    eapply u1_cmp with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q) (c := c) (k := 0)
      (j0 := j0) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | eassumption | lia ].
  - c1_if. step. step. step. step. step. c1_if. step. rd_prep. step.
    pose proof (bx_byte_range x) as Rx.
    step. step.
    eapply u1_cmp with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := q0) (q := q + 1) (c := c + -1)
      (k := bv_unsigned x) (j0 := j0) (bs := bs) (ja := ja) (M := M);
      first [ reflexivity | eassumption | lia ].
Qed.

Lemma u1_skip : forall m q (rest : list byte) u, bytes_at rsegs m q rest -> 0 <= u <= Z.of_nat (length rest) ->
  bytes_at rsegs m (q + u) (skipn (Z.to_nat u) rest) /\
  Z.of_nat (length (skipn (Z.to_nat u) rest)) = Z.of_nat (length rest) - u.
Proof.
  intros m q rest u H Hu.
  rewrite <- (firstn_skipn (Z.to_nat u) rest) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. rewrite length_skipn.
  replace (q + Z.of_nat (Nat.min (Z.to_nat u) (length rest))) with (q + u) in H by lia.
  split; [exact H | lia].
Qed.

Lemma u1_evt : llvm_case_evt (llvm_case_pc 1).
Proof.
  intros F fc regs mem spv lo r fab ip inn op i e gp tp j0 j1 jm bs rest E2 E3 E4 E8 E9 E18 E19 E20 E21
    E22 E23 E24 E25 E26 E27 HS HR HI HF HP HL MI ST Hlo Hlo2 Hsp Hspa Hr4 Hr16 Hr Hip Hie Hel Hinn Hinn2 Hop Hi.
  change (llvm_case_pc 1) with 0x12edc.
  unfold Regs6ss.mkR_of.
  assert (G2 : reg_get regs 2 = Z_to_bv 64 spv) by exact E2.
  assert (G3 : reg_get regs 3 = gp) by exact E3.
  assert (G4 : reg_get regs 4 = tp) by exact E4.
  assert (G8 : reg_get regs 8 = Z_to_bv 64 r) by exact E8.
  assert (G9 : reg_get regs 9 = Z_to_bv 64 op) by exact E9.
  assert (G18 : reg_get regs 18 = Z_to_bv 64 inn) by exact E18.
  assert (G19 : reg_get regs 19 = Z_to_bv 64 (ip + 1)) by exact E19.
  assert (G20 : reg_get regs 20 = Z_to_bv 64 ip) by exact E20.
  assert (G21 : reg_get regs 21 = Z_to_bv 64 (inn - 1)) by exact E21.
  assert (G22 : reg_get regs 22 = Z_to_bv 64 1) by exact E22.
  assert (G23 : reg_get regs 23 = Z_to_bv 64 fab) by exact E23.
  assert (G24 : reg_get regs 24 = Z_to_bv 64 (-1 - (spv + 48))) by exact E24.
  assert (G25 : reg_get regs 25 = Z_to_bv 64 (-1 - r)) by exact E25.
  assert (G26 : reg_get regs 26 = Z_to_bv 64 (spv + 48)) by exact E26.
  assert (G27 : reg_get regs 27 = Z_to_bv 64 336) by exact E27.
  rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
  clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27.
  pose proof RM_C as RM. unfold read_mac_contract, READ_MAC, READ_MAC_FRAME in RM.
  assert (Hspv : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  pose proof (munch_refl [(lo, spv + 360); (r, r + 288)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  pose proof HI as ((Lbs & B1 & _) & _).
  pose proof HR as [[_ HB] WR]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  change (Z.of_nat (cells_size [CB 288 bs])) with 288 in WR. clear HR.
  lazymatch type of HS with rw_cells _ _ _ ?cs => split_for_access HS rsegs mem spv cs 338%nat 6%nat end.
  lazymatch type of HS with
  | rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; CB 2 ?ja; CB 6 ?jb; ?c9; ?c10] =>
      destruct (c2_split3 mem spv [c0; c1; c2; c3; c4; c5; c6; CB 2 ja] [CB 6 jb] [c9; c10] 338 6 HS
        eq_refl eq_refl) as (HS1 & HS2 & HS3);
      clear HS;
      replace (spv + 338 + 6) with (spv + 344) in HS3 by lia;
      step; step; step; step;
      eapply evt_cut;
      [ eapply RM with (lo := lo) (c := spv + 344) (p := ip + 1) (n := inn - 1) (mac := spv + 338) (pl := rest)
          (junk := jb);
        [ fnd_eq | fnd_eq | clear - Hspa; Z.div_mod_to_equations; lia | exact HS3 | exact HS2 | exact HP | exact HL
        | lia | exact MI | rewrite Hspv; exact ST | rewrite Hspv; lia
        | unfold apart; lia | unfold apart; lia | unfold apart; lia | unfold apart, MAC_BASE; unfold LF_RES_TOP in Hlo; lia
        | rewrite Hspv; unfold apart; lia | rewrite Hspv; unfold apart; lia | rewrite Hspv; unfold apart; lia ] | ]
  end.
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & E & MU1 & WM1 & ST1 & MI1 & HC1 & HM1).
  subst ms'.
  c1_retpc.
  rewrite Hspv in MU1, ST1.
  pose proof (rw_cells_transport rsegs _ mem m1 _ _ HS1 MU1 WM1
    ltac:(cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 338; repeat split; lia)) as HS1'.
  pose proof (bytes_at_transport rsegs _ mem m1 _ _ HB MU1
    ltac:(cbn [disjoint_from]; rewrite Lbs; repeat split; lia)) as HB1.
  pose proof (bytes_at_transport rsegs _ mem m1 _ _ HP MU1
    ltac:(cbn [disjoint_from]; repeat split; lia)) as HP1.
  assert (WR1 : wr_at rsegs m1 r 288) by (eapply wr_at_transport; [exact WR | exact WM1]).
  assert (MU1' : munch [(lo, spv + 360); (r, r + 288)] mem m1).
  { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros x Hx; repeat split; lia. }
  pose proof (munch_trans _ mem mem m1 MU MU1') as MU2. clear MU1'.
  pose proof (wmono_trans rsegs mem mem m1 WM WM1) as WM2.
  clear MU MU1 WM WM1 HS1 HB HP ST MI WR.
  destruct (c2_cb_bytes _ _ _ _ HM1) as [_ LM].
  lazymatch type of HS1' with
  | rw_cells _ _ _ ?cs1 =>
      lazymatch type of HM1 with
      | rw_cells _ _ _ ?cs2 =>
          lazymatch type of HC1 with
          | rw_cells _ _ _ ?cs3 =>
              pose proof (c2_join3 m1 spv cs1 cs2 cs3 338 6 HS1' HM1 ltac:(replace (spv + 338 + 6) with (spv + 344) by lia;
                  exact HC1) eq_refl eq_refl) as HSJ
          end
      end
  end.
  clear HS1' HM1 HC1.
  cbn [app] in HSJ.
  lazymatch type of HSJ with context [read_mac_used ?f ?nn] =>
    pose proof (c2_used f nn ltac:(lia)) as HU; set (u := read_mac_used f nn) in * end.
  lazymatch type of HSJ with context [CB 6 ?Mx] => set (M := Mx) in * end.
  lazymatch type of HSJ with context [CB 2 ?jx] => set (ja := jx) in * end.
  destruct (u1_skip m1 (ip + 1) rest u HP1 ltac:(lia)) as [HP2 HL2].
  eapply u1_wid with (lo := lo) (r := r) (fab := fab) (i := i) (e := e) (q0 := ip) (q := ip + 1 + u)
    (c := inn - 1 - u) (j0 := j0) (j1 := j1) (bs := bs) (ja := ja) (M := M) (rest := skipn (Z.to_nat u) rest);
    first [ reflexivity | eassumption | (rewrite Hspv; first [ reflexivity | eassumption | lia ]) | lia ].
Qed.

End S.

Section C1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Theorem llvm_case1_ok : llvm_case_ok B API 1.
Proof.
  exact (llvm_case_of_evt B API 1
    (u1_evt bcmp_holds (reac_boxreg_find_holds mac_is_zero_holds bcmp_holds)
       (reac_boxreg_add.reac_boxreg_add_holds mac_is_zero_holds (reac_boxreg_find_holds mac_is_zero_holds bcmp_holds)
          (lowest_free_base.lowest_free_base_holds range_taken.range_taken_holds) memset.memset_holds memcpy_holds)
       range_free.range_free_holds (read_mac_holds memcpy_holds))).
Qed.

End C1.
