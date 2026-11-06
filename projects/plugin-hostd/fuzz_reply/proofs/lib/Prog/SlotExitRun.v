From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09
  YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ex_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Definition exit_pre_writes (b : Z) : list (Z * Z) :=
  [(b + 16, b + 24); (b + 40, b + 56); (0x31000, 0x31008)].

Ltac ex_sx :=
  repeat match goal with H : context [sx32 (Z_to_bv 64 ?z)] |- _ => rewrite (ex_sx32 z) in H by lia end.

Ltac ex_pre_fin :=
  ex_sx; apply evt_done; do 6 eexists;
  split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  repeat (split; [first [eassumption | intros; lia | intros _; eassumption | intros _; reflexivity]|]);
  first [eassumption | intros; lia | intros _; eassumption].

Lemma exit_pre_run : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b G N (f0 f1 f2 f3 : Z) (nw : word)
    (j16 j40 j44 j48 j52 : list byte),
  sp = Z_to_bv 64 b -> s4 = Z_to_bv 64 0x30fc0 -> 0x100000 <= b -> b + 192 < 2 ^ 64 ->
  4096 <= G -> G + 896 <= b -> mem_inv rsegs m -> 0 <= N <= 4 ->
  0 <= f0 < 2 ^ 31 -> 0 <= f1 < 2 ^ 31 -> 0 <= f2 < 2 ^ 31 -> 0 <= f3 < 2 ^ 31 ->
  (G + 896 <= 0x30fc0 \/ 0x311c0 <= G) ->
  rw_cells rsegs m 0x30fd8 [C4 (Z_to_bv 64 N)] -> rw_cells rsegs m 0x30ff0 [C8 (Z_to_bv 64 G)] ->
  rw_cells rsegs m 0x31000 [C8 nw] ->
  rw_cells rsegs m (b + 16) [CB 8 j16] ->
  rw_cells rsegs m (b + 40) [CB 4 j40] -> rw_cells rsegs m (b + 44) [CB 4 j44] ->
  rw_cells rsegs m (b + 48) [CB 4 j48] -> rw_cells rsegs m (b + 52) [CB 4 j52] ->
  (0 < N -> rw_cells rsegs m G [C4 (Z_to_bv 64 f0)]) -> (1 < N -> rw_cells rsegs m (G + 56) [C4 (Z_to_bv 64 f1)]) ->
  (2 < N -> rw_cells rsegs m (G + 112) [C4 (Z_to_bv 64 f2)]) ->
  (3 < N -> rw_cells rsegs m (G + 168) [C4 (Z_to_bv 64 f3)]) ->
  evt rsegs
    (fun ms => exists x10 x11 x12 x13 x19 m',
      ms = MS (mkR (Z_to_bv 64 (if N =? 0 then 0x1418c else 0x14120)) sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13
        a4 a5 a6 a7 s2 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1300c) fc None m' (seg_rom rsegs) /\
      munch (exit_pre_writes b) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      (0 < N -> x19 = Z_to_bv 64 N) /\
      rw_cells rsegs m' (b + 16) [C8 (Z_to_bv 64 0)] /\ rw_cells rsegs m' 0x31000 [C8 (Z_to_bv 64 0)] /\
      (0 < N -> rw_cells rsegs m' (b + 40) [C4 (Z_to_bv 64 f0)]) /\
      (1 < N -> rw_cells rsegs m' (b + 44) [C4 (Z_to_bv 64 f1)]) /\
      (2 < N -> rw_cells rsegs m' (b + 48) [C4 (Z_to_bv 64 f2)]) /\
      (3 < N -> rw_cells rsegs m' (b + 52) [C4 (Z_to_bv 64 f3)]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x140d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b G N f0 f1 f2 f3 nw j16 j40 j44 j48 j52 -> -> HB HEND HG0 HG1 MI HN R0 R1 R2 R3 HGD
    WN WG WO W16 W40 W44 W48 W52 T0 T1 T2 T3.
  pose proof (munch_refl (exit_pre_writes b) m) as MU. unfold exit_pre_writes in MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (CN : N = 0 \/ N = 1 \/ N = 2 \/ N = 3 \/ N = 4) by lia.
  destruct CN as [EN|[EN|[EN|[EN|EN]]]]; subst N.
  - clear T0 T1 T2 T3. step. step. step. if_true. step. step. ex_pre_fin.
  - specialize (T0 ltac:(lia)). clear T1 T2 T3.
    step. step. step. if_false. step. step. step. if_true. do 4 step.
    do 6 step. if_false. step. step. ex_pre_fin.
  - specialize (T0 ltac:(lia)). specialize (T1 ltac:(lia)). clear T2 T3.
    step. step. step. if_false. step. step. step. if_true. do 4 step.
    do 6 step. if_true. do 6 step. if_false. step. step. ex_pre_fin.
  - specialize (T0 ltac:(lia)). specialize (T1 ltac:(lia)). specialize (T2 ltac:(lia)). clear T3.
    step. step. step. if_false. step. step. step. if_true. do 4 step.
    do 6 step. if_true. do 6 step. if_true. do 6 step. if_false. step. step. ex_pre_fin.
  - specialize (T0 ltac:(lia)). specialize (T1 ltac:(lia)). specialize (T2 ltac:(lia)). specialize (T3 ltac:(lia)).
    step. step. step. if_false. step. step. step. if_false. do 5 step.
    do 6 step. if_true. do 6 step. if_true. do 6 step. if_true. do 6 step. if_false. step. step. ex_pre_fin.
Qed.

Lemma ex_swrap0 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 (z + 0) = z.
Proof.
  intros z Hz. rewrite Z.add_0_r. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2^31) with 2147483648 in Hz. Z.div_mod_to_equations. lia.
Qed.
Ltac ex_sxg :=
  repeat match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (ex_sx32 z) by lia end.
Lemma exit_scan_init : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b N,
  sp = Z_to_bv 64 b -> s3 = Z_to_bv 64 N -> s4 = Z_to_bv 64 0x30fc0 -> 0 <= b -> b + 192 < 2 ^ 64 -> 0 < N <= 4 ->
  evt rsegs
    (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x102e9) (Z_to_bv 64 0x31040) (Z_to_bv 64 0x10134)
        a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 N) s4 (Z_to_bv 64 (b + 40)) (Z_to_bv 64 0x31040)
        (Z_to_bv 64 0x311c0) (Z_to_bv 64 (b + 40)) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14148) fc None m
        (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14120) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b N -> -> -> HB HEND HN.
  do 10 step. rewrite unsigned_lit, ex_swrap0 by lia. apply evt_done. reflexivity.
Qed.

Lemma exit_scan_test : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b HA P8 fd o fi,
  sp = Z_to_bv 64 b -> s0 = Z_to_bv 64 0x102e9 -> s1 = Z_to_bv 64 HA -> s8 = Z_to_bv 64 P8 ->
  0 <= b -> b + 192 < 2 ^ 64 -> 0 <= HA -> HA + 8 < 2 ^ 64 -> 0 <= P8 -> P8 + 4 < 2 ^ 64 -> mem_inv rsegs m ->
  0 <= fd < 2 ^ 31 -> 0 <= o < 2 ^ 31 -> 0 <= fi < 2 ^ 31 ->
  rw_cells rsegs m HA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 o)] -> rw_cells rsegs m P8 [C4 (Z_to_bv 64 fi)] ->
  evt rsegs
    (fun ms =>
      (o <> 0 /\ fd = fi /\
       ms = MS (mkR (Z_to_bv 64 0x1416c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 HA) (Z_to_bv 64 0x102e9)
         (Z_to_bv 64 (b + 16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143c0)
         fc None m (seg_rom rsegs)) \/
      ((o = 0 \/ fd <> fi) /\ exists x10 x11,
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x1416c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14148) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b HA P8 fd o fi -> -> -> -> HB HEND H0 H1 P0 P1 MI Rfd Ro Rfi CH CF.
  step. ex_sxg. step. if_cases Q0.
  { apply evt_done. right. split; [left; zify_cond Q0; lia|]. do 2 eexists. reflexivity. }
  step. ex_sxg. step. ex_sxg. step. if_cases Q1.
  { apply evt_done. right. split; [right; zify_cond Q1; lia|]. do 2 eexists. reflexivity. }
  do 4 step. apply evt_done. left. split; [zify_cond Q0; lia|]. split; [zify_cond Q1; lia|].
  reflexivity.
Qed.

Lemma exit_done_call : check_shape_done_contract -> forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  s4 = Z_to_bv 64 0x30fc0 -> bytes_at rsegs m 0x31000 (le8 a0) ->
  evt rsegs
    (fun ms => exists x11,
      ms = MS (mkR (Z_to_bv 64 0x141a4) sp gp tp t0 t1 t2 (Z_to_bv 64 0x31040) (Z_to_bv 64 0x311c0)
        (Z_to_bv 64 0x31040) x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145fc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14190) fc None m (seg_rom rsegs)).
Proof.
  intros CSD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> HN.
  step. eapply evt_cut.
  { apply CSD. unfold G_NOUT. exact HN. }
  intros ms (x11 & ->).
  rewrite ret_pc_even by lia.
  do 4 step. apply evt_done. eexists. reflexivity.
Qed.

Lemma exit_scan_next : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b HA i N acc,
  sp = Z_to_bv 64 b -> s1 = Z_to_bv 64 HA -> s2 = Z_to_bv 64 i -> s3 = Z_to_bv 64 N ->
  s5 = Z_to_bv 64 (b + 40) -> s6 = Z_to_bv 64 0x31040 -> s7 = Z_to_bv 64 0x311c0 ->
  0 <= b -> b + 192 < 2 ^ 64 -> 0x31040 <= HA -> HA + 96 <= 0x311c0 -> 0 <= i < N -> N <= 4 -> mem_inv rsegs m ->
  rw_cells rsegs m (b + 16) [C8 acc] ->
  evt rsegs
    (fun ms =>
      (HA + 96 < 0x311c0 /\
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (HA + 96)) a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14148) fc None m (seg_rom rsegs)) \/
      (HA + 96 = 0x311c0 /\ i + 1 < N /\
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x31040) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (i + 1)) s3 s4 s5 s6 s7 (Z_to_bv 64 (b + 40 + 4 * (i + 1))) s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14148) fc None m (seg_rom rsegs)) \/
      (HA + 96 = 0x311c0 /\ i + 1 = N /\
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x311c0) acc a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (i + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14190) fc None m
         (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1416c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b HA i N acc -> -> -> -> -> -> -> HB HEND HA0 HA1 Hi HN MI CA.
  step. step. if_cases Q0.
  { apply evt_done. left. split; [zify_cond Q0; lia|]. reflexivity. }
  step. step. if_cases Q1.
  { do 3 step. apply evt_done. right. left. split; [zify_cond Q0; lia|]. split; [zify_cond Q1; lia|].
    replace (Z.shiftl (bv_unsigned (Z_to_bv 64 (i + 1))) 2) with (4 * (i + 1))
      by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
    reflexivity. }
  step. step. apply evt_done. right. right. split; [zify_cond Q0; lia|]. split; [zify_cond Q1; lia|].
  replace (HA + 96) with 0x311c0 by (zify_cond Q0; lia). reflexivity.
Qed.

Lemma exit_zero_next : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs
    (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14190) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1418c) fc None m (seg_rom rsegs)).
Proof.
  intros. step. apply evt_done. reflexivity.
Qed.

Lemma exit_reset_next : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b HA
    (rra rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 : word),
  sp = Z_to_bv 64 b -> s0 = Z_to_bv 64 HA -> s1 = Z_to_bv 64 0x311c0 ->
  0 <= b -> b + 192 < 2 ^ 64 -> 0x31040 <= HA -> HA + 96 <= 0x311c0 ->
  rw_cells rsegs m (b + 88)
    [C8 rs11; C8 rs10; C8 rs9; C8 rs8; C8 rs7; C8 rs6; C8 rs5; C8 rs4; C8 rs3; C8 rs2; C8 rs1; C8 rs0; C8 rra] ->
  evt rsegs
    (fun ms =>
      (HA + 96 < 0x311c0 /\
       ms = MS (mkR (Z_to_bv 64 0x141a4) sp gp tp t0 t1 t2 (Z_to_bv 64 (HA + 96)) s1 (Z_to_bv 64 (HA + 96))
         a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x145fc) fc None m
         (seg_rom rsegs)) \/
      (HA + 96 = 0x311c0 /\
       ms = MS (mkR rra (Z_to_bv 64 (b + 192)) gp tp t0 t1 t2 rs0 rs1 (Z_to_bv 64 0)
         a1 a2 a3 a4 a5 a6 a7 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 t3 t4 t5 t6)
         F (ret_pc rra) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x141a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b HA rra rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 -> -> -> HB HEND HA0 HA1 SAVED.
  step. step. if_cases Q0.
  - step. step. apply evt_done. left. split; [zify_cond Q0; lia|]. reflexivity.
  - do 16 step. apply evt_done. right. split; [zify_cond Q0; lia|]. reflexivity.
Qed.
