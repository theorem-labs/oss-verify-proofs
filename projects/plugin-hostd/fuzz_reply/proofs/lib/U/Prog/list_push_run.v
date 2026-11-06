(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 684 of its 782 lines of code are new or changed and 919 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/arg_s.v, with its addresses and numbers changed; 1437 of its 1551 lines of code are new or changed and 668 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/hand_back.v, with its module paths, addresses and numbers changed; 256 of its 295 lines of code are new or changed and 1512 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import ListStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lpu_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma lpu_and7 : forall x, 0 <= x < 2 ^ 64 -> x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof. intros x R H. rewrite unsigned_lit by lia. exact (lpu_land7 x H). Qed.

Lemma lpu_addiw : forall z c, -2^31 <= z < 2^31 -> -2^31 <= z + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c)) = Z_to_bv 64 (z + c).
Proof.
  intros z c Hz Hzc. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz, Hzc.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lpu_snez : forall z, 0 < z < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z H. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt 0 z)) by lia. reflexivity.
Qed.

Lemma lpu_seqz : forall z, 0 < z < 2 ^ 64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z H. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge z 1)) by lia. reflexivity.
Qed.

Lemma lpu_slti0 : forall z, 0 <= z < 2 ^ 63 -> v_slti (Z_to_bv 64 z) 0 = Z_to_bv 64 0.
Proof.
  intros z H. unfold v_slti, zsig. rewrite (ls_signed z) by lia.
  rewrite (proj2 (Z.ltb_ge z 0)) by lia. reflexivity.
Qed.

Lemma lpu_sltu_ge : forall x y, 0 <= y <= x -> x < 2 ^ 64 -> v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 0.
Proof.
  intros x y H1 H2. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_ge x y)) by lia. reflexivity.
Qed.

Open Scope bv_scope.

Definition lpu_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 b1 b2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0,
    ms' = MS (mkR (Z_to_bv 64 0x148c0) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a0 a2
                  (Z_to_bv 64 (bv_unsigned a2 + 1)) b1 b2 a3 a4 a5 a6 a7 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1608c) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 48)%Z [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma lpu_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N CAP : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z ->
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  (bv_unsigned a0 + 16 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 mod 8 = 0)%Z ->
  (0 <= N < CAP)%Z -> (CAP < 2 ^ 30)%Z -> (bv_unsigned a2 + 1 < 2 ^ 64)%Z ->
  evt rsegs (lpu_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1484c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V N CAP ST LO LC DJ AL NC CB N1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 a2) as RA2. unfold bv_modulus in RA2. cbn in RA2.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  rewrite (lpu_land7 (bv_unsigned a0) AL).
  step. br false.
  do 4 step.
  rewrite ?ls_sx32 by lia.
  step. br true.
  do 2 step.
  apply evt_done. unfold lpu_mid1.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. exact FR.
Qed.

Definition lpu_mid1g (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (V G : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 b2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0,
    ms' = MS (mkR (Z_to_bv 64 0x148ac) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a0 a2
                  (Z_to_bv 64 V) (Z_to_bv 64 (16 * G)) b2 a3 a4 a5 a6 a7 a1 (Z_to_bv 64 G)
                  s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x178f8) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 48)%Z [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma lpu_run1g : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N G : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z ->
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 N)] ->
  (bv_unsigned a0 + 16 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 mod 8 = 0)%Z ->
  (0 <= N < 2 ^ 29)%Z -> G = (if (N =? 0)%Z then 8 else 2 * N)%Z ->
  evt rsegs (lpu_mid1g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 V G m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1484c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V N G ST LO LC DJ AL NC EG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  rewrite (lpu_land7 (bv_unsigned a0) AL).
  step. br false.
  do 4 step.
  rewrite ?ls_sx32 by lia.
  step. br false.
  step.
  destruct (Z.eq_dec N 0) as [N0|N0].
  - subst N. cbn in EG. subst G. br true.
    step. step. step. step.
    apply evt_done. unfold lpu_mid1g.
    do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. exact FR.
  - rewrite (proj2 (Z.eqb_neq N 0) N0) in EG. subst G. br false.
    step. step.
    rewrite (lpu_addiw N 1073741824) by lia.
    step. br false.
    step.
    rewrite (ls_slliw1 N) by lia.
    step. step. step.
    rewrite (ls_slli4 (2 * N)) by lia.
    step.
    apply evt_done. unfold lpu_mid1g.
    do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. exact FR.
Qed.

Definition lpu_mid2 (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp1 : word) (LA V N G : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x148c0) sp1 gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 (bv_unsigned s1 + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1608c) fc None m' (seg_rom rsegs)
    /\ munch [(LA, LA + 16)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 G)].

Lemma lpu_run2 : forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp1 : word) (LA V0 V N CAP G : Z),
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V0); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  (0 < V < 2 ^ 64)%Z -> (0 <= LA)%Z -> (LA + 16 <= 2 ^ 64)%Z -> (0 <= G < 2 ^ 31)%Z ->
  (bv_unsigned s1 + 1 < 2 ^ 64)%Z ->
  evt rsegs (lpu_mid2 gp tp (Z_to_bv 64 LA) s1 s2 (Z_to_bv 64 G) s4 s5 s6 s7 s8 s9 s10 s11 F fc sp1 LA V N G m)
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 LA) s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 G)
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x148ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp1 LA V0 V N CAP G LC RV RL RL2 RG RS.
  pose proof (munch_refl [(LA, LA + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. br false.
  step. step.
  step. step.
  apply evt_done. unfold lpu_mid2.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition lpu_end (ra0 sp0 gp tp s00 s01 s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LA V N G d n : Z) (x : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                  s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp0 - 48, bv_unsigned sp0); (LA, LA + 16); (V + 16 * N, V + 16 * N + 16); (d, d + n + 1)]%Z m m'
    /\ wmono rsegs m m'
    /\ rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (N + 1)); C4 (Z_to_bv 64 G)]
    /\ rw_cells rsegs m' (V + 16 * N)%Z [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n)]
    /\ rw_cells rsegs m' d [CB (length x) x]
    /\ rw_cells rsegs m' (d + n)%Z [C1 (Z_to_bv 8 0)].

Lemma lpu_run3 : memcpy_contract ->
  forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 : word)
    (LA SRC V N G d n : Z) (x junk1 junk2 j1 j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 j0; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 G)] ->
  rw_cells rsegs m (V + 16 * N)%Z [CB 16 junk1] ->
  rw_cells rsegs m d [CB (length x) junk2] ->
  rw_cells rsegs m (d + n)%Z [CB 1 j1] ->
  bytes_at rsegs m SRC x -> Z.of_nat (length x) = n ->
  (0 <= N < 2 ^ 30)%Z -> (0 < V)%Z -> (V mod 8 = 0)%Z -> (V + 16 * N + 16 <= 2 ^ 64)%Z -> (0 < d)%Z ->
  (d + n + 1 <= 2 ^ 64)%Z ->
  (0 <= LA)%Z -> (LA + 16 <= 2 ^ 64)%Z -> (0 <= SRC < 2 ^ 64)%Z -> (48 <= bv_unsigned sp0)%Z ->
  (LA + 16 <= V + 16 * N \/ V + 16 * N + 16 <= LA)%Z ->
  (LA + 16 <= d \/ d + n + 1 <= LA)%Z ->
  (V + 16 * N + 16 <= d \/ d + n + 1 <= V + 16 * N)%Z ->
  (SRC + n <= d \/ d + n <= SRC)%Z ->
  (SRC + n <= LA \/ LA + 16 <= SRC)%Z ->
  (SRC + n <= V + 16 * N \/ V + 16 * N + 16 <= SRC)%Z ->
  (LA + 16 <= bv_unsigned sp0 - 48 \/ bv_unsigned sp0 <= LA)%Z ->
  (V + 16 * N + 16 <= bv_unsigned sp0 - 48 \/ bv_unsigned sp0 <= V + 16 * N)%Z ->
  (d + n + 1 <= bv_unsigned sp0 - 48 \/ bv_unsigned sp0 <= d)%Z ->
  mem_inv rsegs m ->
  evt rsegs (lpu_end ra0 sp0 gp tp s00 s01 s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 F fc LA V N G d n x m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 (Z_to_bv 64 LA) (Z_to_bv 64 n)
             (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SRC) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x148c0) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 LA SRC V N G d n x junk1 junk2 j1 j0
    FR LC SL DST DZ SRCB LX RN RV0 RV8 RV2 RD RD2 RL RL2 RS RSP D1 D2 D3 D4 D5 D6 D7 D8 D9 MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
  pose proof (munch_refl [(bv_unsigned sp0 - 48, bv_unsigned sp0); (LA, LA + 16); (V + 16 * N, V + 16 * N + 16); (d, d + n + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (US : bv_unsigned (Z_to_bv 64 SRC) = SRC) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (TN : Z.to_nat n = length x) by lia.
  assert (PM8 : ((V + 16 * N) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
  step.
  rewrite ?ls_sx32 by lia.
  step. step. step.
  rewrite (ls_idx V N) by lia.
  remember (V + 16 * N)%Z as P eqn:HP.
  step. rewrite (lpu_snez V) by lia.
  step. rewrite (lpu_seqz P) by lia.
  step. br false.
  step. rewrite (lpu_slti0 N) by lia.
  step. rewrite (lpu_sltu_ge P V) by lia.
  step. step.
  step. br false.
  step. br false.
  step. rewrite (lpu_and7 P ltac:(lia) PM8).
  step. br false.
  step.
  step. br false.
  step. br false.
  step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x junk2);
      [ rewrite US; exact SRCB | rewrite UN, TN; reflexivity | rewrite UD, UN, TN; exact DST
      | rewrite US, UD, UN; lia | assumption ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?US, ?UD, ?UN, ?TN in PO; revert ms' PO;
      post_call rsegs mm ]
  end.
  cbv delta [mkR].
  step.
  rewrite ?ls_sx32 by lia.
  step. step. step.
  rewrite (ls_idx V N) by lia. rewrite <- HP.
  step. rewrite (lpu_snez V) by lia.
  step. rewrite (lpu_seqz P) by lia.
  step. br false.
  step. rewrite (lpu_slti0 N) by lia.
  step. rewrite (lpu_sltu_ge P V) by lia.
  step. step.
  step. br false.
  step. br false.
  step. rewrite (lpu_and7 P ltac:(lia) PM8).
  step. br false.
  step.
  step.
  remember (d + n)%Z as Dn eqn:HDn.
  step. br false.
  step. rewrite (lpu_snez d) by lia.
  step. rewrite (lpu_seqz Dn) by lia.
  step.
  step. br false.
  step. br false.
  step.
  change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))). mem_after_store.
  step.
  rewrite ?ls_sx32 by lia.
  step. step. step.
  rewrite (ls_idx V N) by lia. rewrite <- HP.
  step. rewrite (lpu_snez V) by lia.
  step. rewrite (lpu_seqz P) by lia.
  step. br false.
  step. rewrite (lpu_slti0 N) by lia.
  step. rewrite (lpu_sltu_ge P V) by lia.
  step. step.
  step. br false.
  step. br false.
  step. rewrite (lpu_and7 P ltac:(lia) PM8).
  step. br false.
  step. rewrite (lpu_addiw N 1) by lia.
  step.
  step. br false.
  step.
  do 7 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. unfold lpu_end. subst P Dn.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; eassumption.
Qed.
