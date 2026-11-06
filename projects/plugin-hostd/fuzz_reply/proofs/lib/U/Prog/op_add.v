From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import CheckRep.
Import ListNotations.
Open Scope Z_scope.

Lemma oa_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma oa_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma oa_addiw : forall z c, -2^31 <= z < 2^31 -> -2^31 <= z + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c)) = Z_to_bv 64 (z + c).
Proof.
  intros z c Hz Hzc. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz, Hzc.
  Z.div_mod_to_equations. lia.
Qed.

Definition oa_scan_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (os : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    ((first_zero os = None /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)) \/
     (exists i, first_zero os = Some i /\
      ms' = MS (mkR (Z_to_bv 64 0x147e8) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2
                    (Z_to_bv 64 (0x31920 + 96 * Z.of_nat i)) (Z_to_bv 64 0x318a0)
                    (Z_to_bv 64 (0x31920 + 96 * Z.of_nat i)) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14cc0) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] /\
      stk rsegs m' lo (bv_unsigned sp + -32))).

Lemma oa_scan : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo o0 o1 o2 o3 : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x100000 <= lo -> mem_inv rsegs m ->
  - 2 ^ 31 <= o0 < 2 ^ 31 -> - 2 ^ 31 <= o1 < 2 ^ 31 -> - 2 ^ 31 <= o2 < 2 ^ 31 -> - 2 ^ 31 <= o3 < 2 ^ 31 ->
  rw_cells rsegs m 0x31924 [C4 (Z_to_bv 64 o0)] -> rw_cells rsegs m 0x31984 [C4 (Z_to_bv 64 o1)] ->
  rw_cells rsegs m 0x319e4 [C4 (Z_to_bv 64 o2)] -> rw_cells rsegs m 0x31a44 [C4 (Z_to_bv 64 o3)] ->
  evt rsegs (oa_scan_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [o0; o1; o2; o3] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147a8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    o0 o1 o2 o3 ST LO HI MI R0 R1 R2 R3 W0 W1 W2 W3.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 8 step.
  step. rewrite (oa_sx32 o0) by lia.
  step. if_cases Q0.
  { zify_cond Q0. assert (E0 : o0 = 0) by (Z.div_mod_to_equations; lia).
    do 2 step.
    apply evt_done. unfold oa_scan_post. do 3 eexists. exists (Z_to_bv 64 0). do 13 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. exists 0%nat. split; [cbn [first_zero]; rewrite E0; reflexivity|].
    split; [reflexivity|]. split; eassumption. }
  assert (N0 : o0 <> 0) by (intro X; zify_cond Q0; apply Q0; rewrite X; reflexivity).
  step. step. step. if_false. step.
  step. rewrite (oa_sx32 o1) by lia. step. if_cases Q1.
  { zify_cond Q1. assert (E1 : o1 = 0) by (Z.div_mod_to_equations; lia).
    do 2 step.
    apply evt_done. unfold oa_scan_post. do 3 eexists. exists (Z_to_bv 64 0). do 13 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. exists 1%nat. split; [cbn [first_zero]; rewrite (proj2 (Z.eqb_neq _ _) N0), E1; reflexivity|].
    split; [reflexivity|]. split; eassumption. }
  assert (N1 : o1 <> 0) by (intro X; zify_cond Q1; apply Q1; rewrite X; reflexivity).
  step. step. step. if_false. step.
  step. rewrite (oa_sx32 o2) by lia. step. if_cases Q2.
  { zify_cond Q2. assert (E2 : o2 = 0) by (Z.div_mod_to_equations; lia).
    do 2 step.
    apply evt_done. unfold oa_scan_post. do 3 eexists. exists (Z_to_bv 64 0). do 13 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. exists 2%nat.
    split; [cbn [first_zero]; rewrite (proj2 (Z.eqb_neq _ _) N0), (proj2 (Z.eqb_neq _ _) N1), E2; reflexivity|].
    split; [reflexivity|]. split; eassumption. }
  assert (N2 : o2 <> 0) by (intro X; zify_cond Q2; apply Q2; rewrite X; reflexivity).
  step. step. step. if_false. step.
  step. rewrite (oa_sx32 o3) by lia. step. if_cases Q3.
  { zify_cond Q3. assert (E3 : o3 = 0) by (Z.div_mod_to_equations; lia).
    do 2 step.
    apply evt_done. unfold oa_scan_post. do 3 eexists. exists (Z_to_bv 64 0). do 13 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. exists 3%nat.
    split; [cbn [first_zero]; rewrite (proj2 (Z.eqb_neq _ _) N0), (proj2 (Z.eqb_neq _ _) N1),
              (proj2 (Z.eqb_neq _ _) N2), E3; reflexivity|].
    split; [reflexivity|]. split; eassumption. }
  assert (N3 : o3 <> 0) by (intro X; zify_cond Q3; apply Q3; rewrite X; reflexivity).
  step. step. step. if_true.
  do 5 step.
  apply evt_done. unfold oa_scan_post. do 16 eexists. exists [].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  left. split; [|reflexivity].
  cbn [first_zero]. rewrite (proj2 (Z.eqb_neq _ _) N0), (proj2 (Z.eqb_neq _ _) N1),
    (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3). reflexivity.
Qed.

Lemma oa_mid1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (HA n0 : Z) (w : word),
  s0 = Z_to_bv 64 HA -> s1 = Z_to_bv 64 0x318a0 -> 0x31920 <= HA <= 0x31a40 ->
  0 <= n0 <= 512 -> mem_inv rsegs m ->
  rw_cells rsegs m 0x318c0 [C4 (Z_to_bv 64 n0)] -> rw_cells rsegs m HA [C4 w] ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x14810) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 6000) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1608c) fc None m' (seg_rom rsegs) /\
      munch [(0x318c0, 0x318c4); (HA, HA + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' 0x318c0 [C4 (Z_to_bv 64 (n0 + 1))] /\ rw_cells rsegs m' HA [C4 (Z_to_bv 64 (n0 + 100))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HA n0 w -> -> HHA HN MI GN GH.
  pose proof (munch_refl [(0x318c0, 0x318c4); (HA, HA + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (oa_sx32 n0) by lia.
  step. rewrite (oa_addiw n0 1) by lia.
  step. if_cases K1; [exfalso; unfold bv_lts in K1; rewrite (oa_signed (n0 + 1)), (oa_signed n0) in K1 by lia;
    apply Z.ltb_lt in K1; lia|].
  step. rewrite (oa_addiw n0 100) by lia.
  step.
  step. if_cases K2; [exfalso; unfold bv_lts in K2; rewrite (oa_signed (n0 + 100)), (oa_signed n0) in K2 by lia;
    apply Z.ltb_lt in K2; lia|].
  do 4 step.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma oa_mid2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (HA fd q : Z) (w1 w8 : word),
  s0 = Z_to_bv 64 HA -> a0 = Z_to_bv 64 q -> 0 < q < 2 ^ 64 -> 0x31920 <= HA <= 0x31a40 ->
  - 2 ^ 31 <= fd < 2 ^ 31 -> mem_inv rsegs m ->
  rw_cells rsegs m HA [C4 (Z_to_bv 64 fd); C4 w1] -> rw_cells rsegs m (HA + 40) [C8 w8] ->
  evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x14828) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 fd) (Z_to_bv 64 1)
                    a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13504) fc None m' (seg_rom rsegs) /\
      munch [(HA, HA + 8); (HA + 40, HA + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' HA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1)] /\
      rw_cells rsegs m' (HA + 40) [C8 (Z_to_bv 64 q)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14810) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HA fd q w1 w8 -> -> HQ HHA HF MI GH G40.
  pose proof (munch_refl [(HA, HA + 8); (HA + 40, HA + 48)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia|].
  step. rewrite (oa_sx32 fd) by lia.
  do 3 step.
  apply evt_done. do 14 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma oa_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (B : Z) (s0v s1v rav : word) (junk : list byte),
  sp = Z_to_bv 64 B -> a0 = Z_to_bv 64 0 -> 0 <= B -> B + 32 < 2 ^ 64 ->
  rw_cells rsegs m B [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (B + 32)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14828) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    B s0v s1v rav junk -> -> HB0 HB1 FR.
  step. if_false.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep ListTr HarnessTr TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c relay_event_c relay_add_b_c
  source_reset_c op_add_c KindB HarnessGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.

Lemma first_zero_some : forall os i, first_zero os = Some i -> (i < length os)%nat /\ nth i os 0 = 0 /\
  forall j, (j < i)%nat -> nth j os 0 <> 0.
Proof.
  induction os as [|o os IH]; intros i H; cbn [first_zero] in H; [discriminate|].
  destruct (Z.eqb_spec o 0) as [E|E].
  - injection H as <-. cbn. split; [lia|]. split; [exact E | intros j Hj; lia].
  - destruct (first_zero os) as [i'|] eqn:F; cbn in H; [|discriminate]. injection H as <-.
    destruct (IH i' eq_refl) as (H1 & H2 & H3). cbn [length nth]. split; [lia|]. split; [exact H2|].
    intros [|j] Hj; [exact E | cbn; apply H3; lia].
Qed.

Lemma oa_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma oa_ro_glob : forall a, 0x318a0 <= a < 0x31aa0 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha.
  assert (C : forallb (fun i => negb (ro_addr rsegs (wa (0x318a0 + Z.of_nat i)))) (seq 0 512) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat (a - 0x318a0))).
  rewrite Z2Nat.id in C by lia. replace (0x318a0 + (a - 0x318a0)) with a in C by lia.
  apply negb_true_iff. apply C. apply in_seq. lia.
Qed.

Section OA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable Fr : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis BW : blocks_writable Bm API.
Hypothesis NDB : blocks_nodup Bm API.
Hypothesis HMAL : ms_malloc Bm = 0x1608c.

Lemma zero_not_src : forall L A mem HA h, rw_cells (ms_segs Bm) mem HA [CB 96%nat (nulbytes 96)] ->
  ~ src_at Bm L A mem HA h.
Proof.
  intros L A mem HA h Z S. destruct S as (C & _ & _ & HO & _).
  destruct Z as [[_ BZ] _]. destruct C as [[_ BC] _].
  rewrite HO in BC.
  destruct BZ as (_ & _ & BZ). destruct BC as (_ & _ & BC).
  specialize (BZ 4%nat ltac:(cbn; lia)). specialize (BC 4%nat ltac:(cbn; lia)).
  rewrite BZ in BC.
  assert (X : nth_error (cells_bytes [C4 (Z_to_bv 64 (hs_fd h)); C4 (Z_to_bv 64 1);
                C4 (Z_to_bv 64 (hs_closed h)); C4 (Z_to_bv 64 (hs_eintr h))]) 4 = Some (Z_to_bv 8 1))
    by reflexivity.
  rewrite X in BC. injection BC as BC. vm_compute in BC. discriminate.
Qed.

Lemma oa_hi : forall K sp E F L A mem md L' A' mem' md' a cs,
  ms_segs Bm = rsegs -> alloc_ceiling <= sp -> errno_addr Bm + 4 <= sp -> aa_MR API L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' -> rw_cells rsegs mem a cs -> sp <= a ->
  a + Z.of_nat (cells_size cs) <= 2 ^ 64 -> (forall j, 0 <= j < Z.of_nat (cells_size cs) -> ~ E (a + j)) ->
  rw_cells rsegs mem' a cs.
Proof.
  intros K sp E F L A mem md L' A' mem' md' a cs SEG H1 H2 HM R H Ha Hb D.
  rewrite <- SEG in H |- *. exact (rmid_rw_hi Bm API K sp E F L A mem md L' A' mem' md' a cs H1 H2 HM R H Ha Hb D).
Qed.

Lemma oa_img : forall K sp E F L A mem md L' A' mem' md' a cs,
  ms_segs Bm = rsegs -> alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' -> rw_cells rsegs mem a cs ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) -> img_plain Bm (a + j) /\ ~ E (a + j)) ->
  rw_cells rsegs mem' a cs.
Proof.
  intros K sp E F L A mem md L' A' mem' md' a cs SEG H1 HM R H D.
  rewrite <- SEG in H |- *.
  exact (rmid_rw_img Bm API AX K sp E F L A mem md L' A' mem' md' a cs (hg_img_low Bm SEG) H1 HM R H D).
Qed.

Lemma new_src_at : forall L A mem HA fd q pj,
  ms_segs Bm = rsegs ->
  rw_cells rsegs mem HA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1); CB 32 (nulbytes 32); C8 (Z_to_bv 64 q);
                         CB 48 (nulbytes 48)] ->
  0 <= fd < 2 ^ 31 -> In (q, 6000) (blocks L A) -> fresh_block Bm q 6000 ->
  rw_cells rsegs mem q [CB (Z.to_nat 6000) pj] ->
  src_at Bm L A mem HA (new_src fd q pj).
Proof.
  intros L A mem HA fd q pj SEG H Hfd Hin Hfr Hq.
  assert (R : rw_cells rsegs mem HA
    ([C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
     [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
     [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)] ++
     [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
     [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])).
  { apply (rw_cells_retype rsegs mem HA _ _ H); [cbn; tauto|].
    cbn [app cells_bytes cbytes]. generalize (le4 (Z_to_bv 64 fd)) (le8 (Z_to_bv 64 q)). intros X Y.
    vm_compute. reflexivity. }
  destruct (hg_cut rsegs mem HA _ _ R) as (P1 & R1). clear R.
  destruct (hg_cut rsegs mem _ _ _ R1) as (P2 & R2). clear R1.
  destruct (hg_cut rsegs mem _ _ _ R2) as (P3 & R3). clear R2.
  destruct (hg_cut rsegs mem _ _ _ R3) as (_ & R4). clear R3.
  destruct (hg_cut rsegs mem _ _ _ R4) as (P4 & P5). clear R4.
  cbn [cells_size csize Nat.add] in P2, P3, P4, P5.
  match type of P2 with rw_cells _ _ ?a _ => replace a with (HA + 16) in P2 by lia end.
  match type of P3 with rw_cells _ _ ?a _ => replace a with (HA + 32) in P3 by lia end.
  match type of P4 with rw_cells _ _ ?a _ => replace a with (HA + 64) in P4 by lia end.
  match type of P5 with rw_cells _ _ ?a _ => replace a with (HA + 80) in P5 by lia end.
  assert (LJ : Z.of_nat (length pj) = 6000).
  { destruct Hq as [[W _] _]. destruct W as [W _]. cbn [cell_wf] in W. rewrite W. apply Z2Nat.id. lia. }
  unfold src_at. unfold list_at. rewrite SEG. unfold new_src, empty_list, hs_W, hs_blocks, list_blocks, hl_n.
  cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
       hs_expected hs_held hl_v hl_cap hl_recs hl_n length Z.of_nat Z.eqb map app firstn Z.to_nat].
  split; [exact P1|]. split; [left; reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|].
  split; [lia|].
  split.
  { split; [exact P2|]. split; [lia|]. split; [left; split; reflexivity|].
    split; [constructor|]. split; [intros []|]. constructor. }
  split; [exact P3|]. split; [left; split; reflexivity|]. split; [lia|]. split; [left; reflexivity|].
  split; [exact Hin|]. split; [exact Hfr|]. split; [exact LJ|]. split; [exact Hq|]. split; [intros []|].
  split.
  { split; [exact P4|]. split; [lia|]. split; [left; split; reflexivity|].
    split; [constructor|]. split; [intros []|]. constructor. }
  split.
  { split; [exact P5|]. split; [lia|]. split; [left; split; reflexivity|].
    split; [constructor|]. split; [intros X; exact X|]. apply Forall_nil. }
  apply NoDup_cons_2; [intros X; inversion X | apply NoDup_nil_2].
Qed.

Ltac oa_saved GR :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; rewrite GR; unfold callee_saved in Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity.

Theorem op_add_holds : source_reset_contract Bm API Fr -> malloc_contract_rt Bm API Fr -> relay_add_contract Bm API Fr ->
  op_add_contract Bm API Fr.
Proof.
  intros SRS MAL RAD. unfold op_add_contract.
  intros L A regs mem md bnd os n0 N C G ents tail. cbv zeta.
  intros SEG PRE INIT RO ERRI PLR PLW LOS OPN ZER NFD N0R LOCK WAKE NSRC GSRC CASES RES N4 ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (EK : OP_ADD_K = 8352) by reflexivity. rewrite EK in *.
  unfold OP_ADD, G_S, SRC_SIZE, G_NFD, G_RELAY_LO, G_LOCK, G_LOCK_HI, G_NSRC, G_SRC, G_WAKE1, SRC_TABLE, SRC_ENTRY,
    FIRST_FD, PARTIAL_BYTES, SOURCES_MAX in *.
  set (sp := reg_get regs 2) in *.
  assert (SPE : spZ regs = bv_unsigned sp) by reflexivity. rewrite SPE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (hg_img_low Bm SEG) as HIMG.
  assert (EL : 0 <= errno_addr Bm /\ errno_addr Bm + 4 <= alloc_ceiling).
  { pose proof (HIMG _ (ERRI (errno_addr Bm) ltac:(lia))). pose proof (HIMG _ (ERRI (errno_addr Bm + 3) ltac:(lia))). lia. }
  destruct os as [|o0 [|o1 [|o2 [|o3 [|o4 os]]]]]; cbn [length] in LOS; try discriminate. clear LOS.
  destruct (OPN 0%nat ltac:(lia)) as [R0 W0]. destruct (OPN 1%nat ltac:(lia)) as [R1 W1].
  destruct (OPN 2%nat ltac:(lia)) as [R2 W2]. destruct (OPN 3%nat ltac:(lia)) as [R3 W3].
  cbn [nth] in R0, R1, R2, R3, W0, W1, W2, W3.
  change (203040 + 96 * Z.of_nat 0 + 4) with 203044 in W0.
  change (203040 + 96 * Z.of_nat 1 + 4) with 203140 in W1.
  change (203040 + 96 * Z.of_nat 2 + 4) with 203236 in W2.
  change (203040 + 96 * Z.of_nat 3 + 4) with 203332 in W3.
  rewrite SEG in RO, W0, W1, W2, W3, HWS, HERR |- *.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8352) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha. assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as ST0.
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  assert (RG : forall a k, 0x318a0 <= a -> a + Z.of_nat k <= 0x31aa0 ->
                 forall i, 0 <= i < Z.of_nat k -> ro_addr rsegs (Z_to_bv 64 (a + i)) = false).
  { intros a k H1 H2 i Hi. apply oa_ro_glob. lia. }
  pose proof (rw_cells_normalize rsegs mem _ _ RO W0 (RG 203044 4%nat ltac:(lia) ltac:(lia))) as W0n.
  pose proof (rw_cells_normalize rsegs mem _ _ RO W1 (RG 203140 4%nat ltac:(lia) ltac:(lia))) as W1n.
  pose proof (rw_cells_normalize rsegs mem _ _ RO W2 (RG 203236 4%nat ltac:(lia) ltac:(lia))) as W2n.
  pose proof (rw_cells_normalize rsegs mem _ _ RO W3 (RG 203332 4%nat ltac:(lia) ltac:(lia))) as W3n.
  eapply (kseg regs (Z_to_bv 64 83880) mem md); [exact oa_wx | exact RO | exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. fold sp.
    eapply oa_scan with (lo := bv_unsigned sp - 8352).
    all: try first [exact ST0 | exact MI0 | exact W0n | exact W1n | exact W2n | exact W3n | lia].
    all: first [exact R0 | exact R1 | exact R2 | exact R3]. }
  { intros s0 HQ. unfold oa_scan_post in HQ.
    destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk &
      _ & _ & _ & [[_ ->] | (i & _ & -> & _)]); do 3 eexists; reflexivity. }
  intros R pc' m0 regs1 m1 HQ GR MREL ROS. unfold oa_scan_post in HQ.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk &
    MU & WM & MI & [[FZ EQ] | (i & FZ & EQ & FRM & STK)]).
  - injection EQ as ER EP EM. subst R pc' m0.
    destruct (rmid_norm Bm API 8352 (bv_unsigned sp) (fun _ => False) (fun _ => False) L A mem md m' m1
                [(bv_unsigned sp - 32, bv_unsigned sp)] SEG RO MREL ROS MU WM HMR HWF HBD ltac:(lia))
      as (RM & MUr & WMr).
    { unfold sk. rewrite SEG. intros a [X|X]; [apply HWS; lia | apply HERR; exact X]. }
    { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. left. lia. }
    { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho). apply hg_out. intros lo hi [E|[]].
      injection E as <- <-. left. lia. }
    { intros p n i Hp Hi O. exfalso. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HMR Hp Hi) as (_ & B1 & B2 & _).
      destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. lia. }
    apply SR_ret. exists L, A, regs1, m1, md.
    split; [f_equal; f_equal; change (reg_get regs 1) with (getr regs 1); exact (ret_pc_of_ok _ HRA)|].
    split; [exact INIT|]. split; [exact (ro_agree_same rsegs mem m1 RO ROS)|].
    split.
    + intros _. split; [|split; [reflexivity | exact RES]].
      apply rp_join; [rewrite SPE; exact RM|]. oa_saved GR.
    + intros i HF. rewrite FZ in HF. discriminate.
  - injection EQ as ER EP EM. subst R pc' m0.
    destruct (first_zero_some _ _ FZ) as (Hi4 & Hz & _). cbn [length] in Hi4.
    destruct (rmid_norm Bm API 8352 (bv_unsigned sp) (fun _ => False) (fun _ => False) L A mem md m' m1
                [(bv_unsigned sp - 32, bv_unsigned sp)] SEG RO MREL ROS MU WM HMR HWF HBD ltac:(lia))
      as (RM0 & MU0 & WM0).
    { unfold sk. rewrite SEG. intros a [X|X]; [apply HWS; lia | apply HERR; exact X]. }
    { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. left. lia. }
    { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho). apply hg_out. intros lo hi [E|[]].
      injection E as <- <-. left. lia. }
    { intros p n j Hp Hj O. exfalso. destruct (mr_blocks _ _ LAWS _ _ _ _ p n j HMR Hp Hj) as (_ & B1 & B2 & _).
      destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. lia. }
    pose proof (ro_agree_same rsegs mem m1 RO ROS) as RO1.
    pose proof (rw_cells_of_rel rsegs m1 m' _ _ MREL FRM) as FRM1.
    set (HA := 203040 + 96 * Z.of_nat i) in *.
    assert (HAr : 203040 <= HA <= 203328) by (unfold HA; lia).
    assert (E1_1 : getr regs1 1 = Z_to_bv 64 83944) by (rewrite GR; reflexivity).
    assert (E1_2 : getr regs1 2 = Z_to_bv 64 (bv_unsigned sp + -32)) by (rewrite GR; reflexivity).
    assert (E1_4 : getr regs1 4 = getr regs 4) by (rewrite GR; reflexivity).
    assert (E1_8 : getr regs1 8 = Z_to_bv 64 HA) by (rewrite GR; reflexivity).
    assert (E1_9 : getr regs1 9 = Z_to_bv 64 202912) by (rewrite GR; reflexivity).
    assert (E1_10 : getr regs1 10 = Z_to_bv 64 HA) by (rewrite GR; reflexivity).
    assert (KEEP1 : forall r, (r = 3 \/ r = 4 \/ 18 <= r <= 27) ->
              getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite GR.
      assert (Hc : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                   r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
    assert (SP1 : spZ regs1 = bv_unsigned sp - 32).
    { unfold spZ. rewrite E1_2. apply unsigned_lit. lia. }
    assert (ZM : rw_cells rsegs m1 HA [CB 96%nat (nulbytes 96)]).
    { pose proof (ZER i Hi4 Hz) as Z0. rewrite SEG in Z0. change (203040 + 96 * Z.of_nat i) with HA in Z0.
      apply (rw_cells_transport rsegs _ mem m1 _ _ Z0 MU0 WM0). cbn. lia. }
    assert (EKS : SOURCE_RESET_K = 8272) by reflexivity.
    pose proof SRS as SRSc. unfold source_reset_contract in SRSc. rewrite SEG in SRSc.
    unfold SOURCE_RESET, G_S, SRC_SIZE, SOURCES_MAX in SRSc. rewrite EKS in SRSc.
    eapply SR_bind.
    { apply (SRSc L A regs1 m1 md bnd (new_src 0 0 []) i).
      - reflexivity.
      - eapply cpk_of_rmid; [exact RM0 | exact INIT | rewrite E1_1; apply ret_ok_even; vm_compute; reflexivity
                             | rewrite E1_4; exact HTP | rewrite SP1; Z.div_mod_to_equations; lia | rewrite SP1; lia
                             | rewrite SP1; lia | lia | rewrite SP1; lia | rewrite SP1; lia].
      - exact INIT.
      - exact RO1.
      - intros a Ha. apply PLR. lia.
      - exact Hi4.
      - exact E1_10.
      - right. exact ZM.
      - exists (nulbytes 4).
        assert (Z3 : rw_cells rsegs m1 HA [CB 60%nat (nulbytes 60); CB 4%nat (nulbytes 4); CB 32%nat (nulbytes 32)]).
        { apply (rw_cells_retype rsegs m1 HA _ _ ZM); [cbn; tauto | vm_compute; reflexivity]. }
        destruct (hg_cut rsegs m1 HA [_] [_; _] Z3) as (_ & Z4).
        destruct (hg_cut rsegs m1 _ [_] [_] Z4) as (Z5 & _).
        match type of Z5 with rw_cells _ _ ?a _ => replace a with (HA + 60) in Z5 by (cbn; lia) end. exact Z5.
      - exact RES. }
    intros c2 (L1 & A1 & regs2 & m2 & md1 & -> & RP1 & INIT1 & RO2 & Z2 & _ & ZS).
    destruct (ZS ZM) as (RES1 & BLK1).
    destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP1) as (RM1 & PR1).
    rewrite SP1 in RM1.
    pose proof RM0 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
    assert (NFS : forall q, ~ (src_at Bm L A m1 HA (new_src 0 0 []) /\ In q (hs_blocks (new_src 0 0 [])))).
    { intros q [X _]. rewrite <- SEG in ZM. exact (zero_not_src L A m1 _ _ ZM X). }
    pose proof (rmid_EF Bm API _ _ _ _ _ (fun _ => False) _ _ _ _ _ _ _ _ RM1 (fun a X => X) (fun q X => NFS q X))
      as RM1f.
    assert (WR1 : forall a, bv_unsigned sp - 8352 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m1 a)
      by (intros a Ha; apply SC1; unfold sk; left; exact Ha).
    assert (NE1 : forall a, bv_unsigned sp - 8352 <= a < bv_unsigned sp -> ~ (HA <= a < HA + 96))
      by (intros a Ha X; lia).
    pose proof (rmid_widen Bm API 8272 (bv_unsigned sp - 32) 8352 (bv_unsigned sp) _ _ _ _ _ _ _ _ _ _ HM1
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR1 NE1 RM1f) as RM1w.
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM0 RM1w) as RM01.
    pose proof RM01 as (HM2 & HWF2 & HBD2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
    destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    assert (E2_2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned sp + -32))
      by exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (E2_4 : getr regs2 4 = getr regs 4) by exact (eq_trans (PR1 4 ltac:(unfold callee_saved; lia)) E1_4).
    assert (E2_8 : getr regs2 8 = Z_to_bv 64 HA) by exact (eq_trans (PR1 8 ltac:(unfold callee_saved; lia)) E1_8).
    assert (E2_9 : getr regs2 9 = Z_to_bv 64 202912)
      by exact (eq_trans (PR1 9 ltac:(unfold callee_saved; lia)) E1_9).
    assert (KEEP2 : forall r, (r = 3 \/ r = 4 \/ 18 <= r <= 27) ->
              getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite (PR1 r ltac:(unfold callee_saved; lia)). exact (KEEP1 r Hr). }
    assert (NFD2 : rw_cells rsegs m2 202944 [C4 (Z_to_bv 64 n0)]).
    { rewrite <- SEG.
      eapply (rmid_rw_img Bm API AX 8352 (bv_unsigned sp)); [exact HIMG | lia | exact HMR | exact RM01 | exact NFD |].
      intros j Hj. cbn in Hj. split; [apply PLR; lia | cbv beta; lia]. }
    assert (Z2r : rw_cells rsegs m2 HA [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 32 (nulbytes 32);
                                       C8 (Z_to_bv 64 0); CB 48 (nulbytes 48)]).
    { apply (rw_cells_retype rsegs m2 HA _ _ Z2); [cbn; tauto | vm_compute; reflexivity]. }
    destruct (hg_cut rsegs m2 HA [_] [_; _; _; _] Z2r) as (Z2a & Z2r1). cbn [cells_size csize] in Z2r1.
    destruct (hg_cut rsegs m2 (HA + Z.of_nat 4) [_] [_; _; _] Z2r1) as (Z2b & Z2r2). cbn [cells_size csize] in Z2r2.
    destruct (hg_cut rsegs m2 (HA + Z.of_nat 4 + Z.of_nat 4) [_] [_; _] Z2r2) as (Z2c & Z2r3).
    cbn [cells_size csize] in Z2r3.
    destruct (hg_cut rsegs m2 (HA + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 32) [_] [_] Z2r3) as (Z2d & Z2e).
    cbn [cells_size csize] in Z2e.
    replace (HA + Z.of_nat 4) with (HA + 4) in Z2b by lia.
    replace (HA + Z.of_nat 4 + Z.of_nat 4) with (HA + 8) in Z2c by lia.
    replace (HA + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 32) with (HA + 40) in Z2d by lia.
    replace (HA + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 32 + Z.of_nat 8) with (HA + 48) in Z2e by lia.
    clear Z2r Z2r1 Z2r2 Z2r3.
    assert (P1 : PropExec.getr regs1 1 = Z_to_bv 64 83944) by exact E1_1.
    rewrite P1.
    eapply (kseg regs2 (Z_to_bv 64 83944) m2 md1); [exact oa_wx | exact RO2 | exact Hh2 | exact Hl2 | | |].
    { unfold Regs6ss.mkR_of.
      eapply oa_mid1 with (HA := HA) (n0 := n0).
      - exact E2_8.
      - exact E2_9.
      - lia.
      - lia.
      - apply mem_inv_normalize.
      - apply (rw_cells_normalize rsegs m2 _ _ RO2 NFD2). intros j Hj. apply oa_ro_glob. cbn in Hj. lia.
      - apply (rw_cells_normalize rsegs m2 _ _ RO2 Z2a). intros j Hj. apply oa_ro_glob. cbn in Hj. lia. }
    { intros s0 HQ. destruct HQ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & -> & _).
      do 3 eexists. reflexivity. }
    intros Rg3 pc3 m3' regs3 m3 HQ3 GR3 MREL3 ROS3.
    destruct HQ3 as (v0 & v1 & v2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & m3n &
      EQ3 & MU3 & WM3 & MI3 & NFD3 & HA3).
    injection EQ3 as ER3 EP3 EM3. subst Rg3 pc3 m3'.
    assert (E3_1 : getr regs3 1 = Z_to_bv 64 83984) by (rewrite GR3; reflexivity).
    assert (E3_2 : getr regs3 2 = Z_to_bv 64 (bv_unsigned sp + -32)) by (rewrite GR3; exact E2_2).
    assert (E3_4 : getr regs3 4 = getr regs 4) by (rewrite GR3; exact E2_4).
    assert (E3_8 : getr regs3 8 = Z_to_bv 64 HA) by (rewrite GR3; exact E2_8).
    assert (E3_9 : getr regs3 9 = Z_to_bv 64 202912) by (rewrite GR3; exact E2_9).
    assert (E3_10 : getr regs3 10 = Z_to_bv 64 6000) by (rewrite GR3; reflexivity).
    assert (KEEP3 : forall r, (r = 3 \/ r = 4 \/ 18 <= r <= 27) ->
              getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite <- (KEEP2 r Hr), GR3.
      assert (Hc : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                   r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
    assert (SP3 : spZ regs3 = bv_unsigned sp - 32).
    { unfold spZ. rewrite E3_2. apply unsigned_lit. lia. }
    destruct (rmid_norm Bm API 8352 (bv_unsigned sp) (fun a => 202944 <= a < 202948 \/ HA <= a < HA + 96)
                (fun _ => False) L1 A1 m2 md1 m3n m3 [(202944, 202944 + 4); (HA, HA + 4)]
                SEG RO2 MREL3 ROS3 MU3 WM3 HM2 HWF2 HBD2 ltac:(lia) SC2)
      as (RM2 & MU3r & WM3r).
    { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[E|[]]] & Hlh); injection E as <- <-;
        right; lia. }
    { intros a Ho. apply hg_out. intros lo hi Hin.
      destruct (Z_lt_le_dec a lo) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec hi a) as [D'|D']; [right; lia|].
      exfalso. destruct Hin as [E|[E|[]]]; injection E as E1 E2; subst lo hi;
        exact (hg_img_not_owned Bm API AX L1 A1 m2 md1 a HM2 (PLR a ltac:(lia)) Ho). }
    { intros p n j Hp Hj O. exfalso. destruct (hg_not_out _ _ O) as (lo & hi & [E|[E|[]]] & Hlh);
        injection E as <- <-; apply (ax_blocks_img AX L1 A1 m2 md1 p n j HM2 Hp Hj);
        exact (proj1 (PLR (ptr_addr L1 p + j) ltac:(lia))). }
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM01 RM2) as RM012.
    pose proof RM012 as (HM3 & HWF3 & HBD3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC3).
    pose proof (ro_agree_same rsegs m2 m3 RO2 ROS3) as RO3.
    pose proof (rw_cells_of_rel rsegs m3 m3n _ _ MREL3 NFD3) as NFD3r.
    pose proof (rw_cells_of_rel rsegs m3 m3n _ _ MREL3 HA3) as HA3r.
    pose proof (ROOM _ (repeat_length (SP 0 0) _)) as ROOM0.
    rewrite FZ in ROOM0. unfold roomF, RelayRunT.room_run in ROOM0. cbn [op_add_tr RelayRunT.room_from] in ROOM0.
    pose proof MAL as MALc. unfold malloc_contract_rt in MALc. rewrite SEG, HMAL in MALc.
    eapply SR_bind.
    { apply (MALc L1 A1 regs3 m3 md1 6000 bnd).
      - change (call_pre_k Bm (aa_MR API) ALLOC_STACK L1 A1 regs3 m3 md1).
        eapply cpk_of_rmid; [exact RM012 | exact INIT1 | rewrite E3_1; apply ret_ok_even; vm_compute; reflexivity
                             | rewrite E3_4; exact HTP | rewrite SP3; Z.div_mod_to_equations; lia
                             | rewrite SP3; unfold ALLOC_STACK; lia | rewrite SP3; lia | unfold ALLOC_STACK; lia
                             | rewrite SP3; unfold ALLOC_STACK; lia | rewrite SP3; lia].
      - exact RO3.
      - exact E3_10.
      - exact RES1.
      - exact (proj1 ROOM0). }
    intros c3 RET. unfold malloc_ret_rt in RET.
    destruct RET as (L2 & A2 & regs4 & m4 & md2 & q & -> & CPK & A0' & NZ & AL & FRESH & BLK & KEPT & RO4 & GK &
      SURV & INIT2 & LEN2 & RES2).
    destruct (rmid_of_cpk Bm API _ _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ AX CTX HM3 CPK LEN2
                (fun p n H _ _ => SURV p n H) (fun p H => SURV p 0 H)) as (RM3 & PR3).
    rewrite SP3 in RM3.
    assert (WR3 : forall a, bv_unsigned sp - 8352 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m3 a)
      by (intros a Ha; apply SC3; unfold sk; left; exact Ha).
    pose proof (rmid_widen Bm API ALLOC_STACK (bv_unsigned sp - 32) 8352 (bv_unsigned sp) _ _ _ _ _ _ _ _ _ _ HM3
                  ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) ltac:(lia) WR3 (fun a _ X => X) RM3) as RM3w.
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM012 RM3w) as RM0123.
    pose proof RM0123 as (HM4 & HWF4 & HBD4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC4).
    destruct (mr_model _ _ LAWS _ _ _ _ HM4) as (Hh4 & Hl4 & _).
    pose proof FRESH as (FR1 & FR2 & FR3).
    rewrite SEG in RO4.
    assert (E4_2 : getr regs4 2 = Z_to_bv 64 (bv_unsigned sp + -32))
      by exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E3_2).
    assert (E4_4 : getr regs4 4 = getr regs 4) by exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E3_4).
    assert (E4_8 : getr regs4 8 = Z_to_bv 64 HA) by exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E3_8).
    assert (E4_9 : getr regs4 9 = Z_to_bv 64 202912)
      by exact (eq_trans (PR3 9 ltac:(unfold callee_saved; lia)) E3_9).
    assert (KEEP4 : forall r, (r = 3 \/ r = 4 \/ 18 <= r <= 27) ->
              getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite (PR3 r ltac:(unfold callee_saved; lia)). exact (KEEP3 r Hr). }
    assert (T3 : forall a cs, rw_cells (ms_segs Bm) m3 a cs ->
              (forall j, 0 <= j < Z.of_nat (cells_size cs) -> img_plain Bm (a + j)) -> rw_cells (ms_segs Bm) m4 a cs).
    { intros a cs H D. eapply (rmid_rw_img Bm API AX ALLOC_STACK (bv_unsigned sp - 32));
        [exact HIMG | unfold ALLOC_STACK; lia | exact HM3 | exact RM3 | exact H |].
      intros j Hj. split; [exact (D j Hj) | intros []]. }
    assert (HA4 : rw_cells rsegs m4 HA [C4 (Z_to_bv 64 (n0 + 100)); C4 (Z_to_bv 64 0)]).
    { apply (hg_join rsegs m4 HA (HA + 4) [C4 (Z_to_bv 64 (n0 + 100))] [C4 (Z_to_bv 64 0)]); [ | | reflexivity].
      - rewrite <- SEG. apply T3; [rewrite SEG; exact HA3r | intros j Hj; cbn in Hj; apply PLR; lia].
      - rewrite <- SEG. apply T3; [|intros j Hj; cbn in Hj; apply PLR; lia]. rewrite SEG.
        apply (rw_cells_transport rsegs _ m2 m3 _ _ Z2b MU3r WM3r). cbn. lia. }
    assert (Q4 : rw_cells rsegs m4 (HA + 40) [C8 (Z_to_bv 64 0)]).
    { rewrite <- SEG. apply T3; [|intros j Hj; cbn in Hj; apply PLR; lia]. rewrite SEG.
      apply (rw_cells_transport rsegs _ m2 m3 _ _ Z2d MU3r WM3r). cbn. lia. }
    rewrite SEG, E3_1.
    eapply (kseg regs4 (Z_to_bv 64 83984) m4 md2); [exact oa_wx | exact RO4 | exact Hh4 | exact Hl4 | | |].
    { unfold Regs6ss.mkR_of.
      eapply oa_mid2 with (HA := HA) (fd := n0 + 100) (q := q).
      - exact E4_8.
      - exact A0'.
      - lia.
      - lia.
      - lia.
      - apply mem_inv_normalize.
      - apply (rw_cells_normalize rsegs m4 _ _ RO4 HA4). intros j Hj. apply oa_ro_glob. cbn in Hj. lia.
      - apply (rw_cells_normalize rsegs m4 _ _ RO4 Q4). intros j Hj. apply oa_ro_glob. cbn in Hj. lia. }
    { intros s0 HQ. destruct HQ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & -> & _).
      do 3 eexists. reflexivity. }
    intros Rg5 pc5 m5' regs5 m5 HQ5 GR5 MREL5 ROS5.
    destruct HQ5 as (x0 & x1 & x2 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m5n &
      EQ5 & MU5 & WM5 & MI5 & HA5 & Q5).
    injection EQ5 as ER5 EP5 EM5. subst Rg5 pc5 m5'.
    assert (HAe : HA = 203040 + 96 * Z.of_nat i) by reflexivity.
    assert (E5_1 : getr regs5 1 = Z_to_bv 64 84008) by (rewrite GR5; reflexivity).
    assert (E5_2 : getr regs5 2 = Z_to_bv 64 (bv_unsigned sp + -32)) by (rewrite GR5; exact E4_2).
    assert (E5_4 : getr regs5 4 = getr regs 4) by (rewrite GR5; exact E4_4).
    assert (E5_8 : getr regs5 8 = Z_to_bv 64 HA) by (rewrite GR5; exact E4_8).
    assert (E5_9 : getr regs5 9 = Z_to_bv 64 202912) by (rewrite GR5; exact E4_9).
    assert (E5_10 : getr regs5 10 = Z_to_bv 64 (n0 + 100)) by (rewrite GR5; reflexivity).
    assert (KEEP5 : forall r, (r = 3 \/ r = 4 \/ 18 <= r <= 27) ->
              getr regs5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite <- (KEEP4 r Hr), GR5.
      assert (Hc : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                   r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
    assert (SP5 : spZ regs5 = bv_unsigned sp - 32).
    { unfold spZ. rewrite E5_2. apply unsigned_lit. lia. }
    destruct (rmid_norm Bm API 8352 (bv_unsigned sp) (fun a => HA <= a < HA + 8 \/ HA + 40 <= a < HA + 48)
                (fun _ => False) L2 A2 m4 md2 m5n m5 [(HA, HA + 8); (HA + 40, HA + 48)]
                SEG RO4 MREL5 ROS5 MU5 WM5 HM4 HWF4 HBD4 ltac:(lia) SC4)
      as (RM4 & MU5r & WM5r).
    { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[E|[]]] & Hlh); injection E as <- <-;
        right; lia. }
    { intros a Ho. apply hg_out. intros lo hi Hin.
      destruct (Z_lt_le_dec a lo) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec hi a) as [D'|D']; [right; lia|].
      exfalso. destruct Hin as [E|[E|[]]]; injection E as E1 E2; subst lo hi;
        exact (hg_img_not_owned Bm API AX L2 A2 m4 md2 a HM4 (PLR a ltac:(lia)) Ho). }
    { intros p n j Hp Hj O. exfalso. destruct (hg_not_out _ _ O) as (lo & hi & [E|[E|[]]] & Hlh);
        injection E as <- <-; apply (ax_blocks_img AX L2 A2 m4 md2 p n j HM4 Hp Hj);
        exact (proj1 (PLR (ptr_addr L2 p + j) ltac:(lia))). }
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM0123 RM4) as RM01234.
    pose proof RM01234 as (HM5 & HWF5 & HBD5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC5).
    destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
    pose proof (ro_agree_same rsegs m4 m5 RO4 ROS5) as RO5.
    pose proof (rw_cells_of_rel rsegs m5 m5n _ _ MREL5 HA5) as HA5r.
    pose proof (rw_cells_of_rel rsegs m5 m5n _ _ MREL5 Q5) as Q5r.
    rewrite SEG in LOCK, WAKE, NSRC, GSRC, CASES.
    assert (CC : C = 0 \/ C = 16) by (destruct CASES as [(X & _)|(X & _)]; lia).
    assert (GF : 0 < C -> fresh_block Bm G (16 * 56) /\ In (G, 16 * 56) (blocks L A)).
    { intros HC. destruct CASES as [(X & _)|(_ & I1 & F1 & _)]; [lia|]. split; [exact F1 | exact I1]. }
    pose proof (N4 ltac:(rewrite FZ; discriminate)) as NR.
    assert (TRE : forall fd g, 0 <= fd -> relay_add_tr fd N C g = if C =? 0 then [RMalloc (16 * 56)] else []).
    { intros fd g Hfd. unfold relay_add_tr, SRC_ENTRY.
      replace (fd <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct CASES as [(EC & _ & EN & _)|(EC & _)]; subst C; [subst N; reflexivity|].
      replace (N =? 16) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    assert (TBE : forall fd j g, 0 <= fd -> relay_add_tbl fd N C j g = if C =? 0 then Ret j else g).
    { intros fd j g Hfd. unfold relay_add_tbl.
      replace (fd <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct CASES as [(EC & _ & EN & _)|(EC & _)]; subst C; [subst N; reflexivity|].
      replace (N =? 16) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    assert (TG : forall a cs, rw_cells rsegs mem a cs ->
              (forall j, 0 <= j < Z.of_nat (cells_size cs) ->
                 202912 <= a + j < 203040 /\ ~ (202944 <= a + j < 202948)) -> rw_cells rsegs m5 a cs).
    { intros a cs H D. rewrite <- SEG.
      eapply (rmid_rw_img Bm API AX 8352 (bv_unsigned sp)); [exact HIMG | lia | exact HMR | exact RM01234 |
        rewrite SEG; exact H |].
      intros j Hj. destruct (D j Hj) as (D1 & D2). split; [apply PLR; lia | intros X; cbv beta in X; lia]. }
    assert (LOCK5 := TG _ _ LOCK ltac:(intros j Hj; cbn in Hj; lia)).
    assert (NSRC5 := TG _ _ NSRC ltac:(intros j Hj; cbn in Hj; lia)).
    assert (GSRC5 := TG _ _ GSRC ltac:(intros j Hj; cbn in Hj; lia)).
    assert (WAKE5 : bytes_at rsegs m5 136748 (le4 (Z_to_bv 64 (-1)))).
    { rewrite <- SEG.
      eapply (rmid_bytes_img Bm API AX 8352 (bv_unsigned sp)); [exact HIMG | lia | exact HMR | exact RM01234 |
        rewrite SEG; exact WAKE |].
      intros j Hj. rewrite length_le4 in Hj. split; [apply PLW; lia | intros X; cbv beta in X; lia]. }
    assert (CASES5 : (C = 0 /\ G = 0 /\ N = 0 /\ ents = []) \/
              (C = 16 /\ In (G, 16 * 56) (blocks L2 A2) /\ fresh_block Bm G (16 * 56) /\
               Z.of_nat (length ents) = 56 * N /\ Z.of_nat (length tail) = 16 * 56 - 56 * N /\
               rw_cells rsegs m5 G [CB (Z.to_nat (16 * 56)) (ents ++ tail)])).
    { destruct CASES as [X|(EC & I1 & F1 & L1' & L2' & TB)]; [left; exact X|right].
      pose proof F1 as (F1a & F1b & F1c).
      assert (NE : forall x, 0 <= x - G < 16 * 56 -> ~ (202912 <= x < 203424)).
      { intros x Hx X. apply (F1c (x - G)); [lia|]. replace (G + (x - G)) with x by lia.
        exact (proj1 (PLR x ltac:(lia))). }
      destruct (rmid_block Bm API BW _ _ _ _ _ _ _ _ _ _ _ _ G (16 * 56) 0 RM01234 I1 ltac:(lia)
                  ltac:(intros X; cbv beta in X; tauto) ltac:(lia)
                  ltac:(intros X; cbv beta in X; apply (NE (G + 0)); lia)) as (I5 & _).
      split; [exact EC|]. split; [exact I5|]. split; [exact F1|]. split; [exact L1'|]. split; [exact L2'|].
      rewrite <- SEG.
      eapply (rmid_rw_block Bm API BW _ _ _ _ _ _ _ _ _ _ _ _ G (16 * 56));
        [exact RM01234 | exact I1 | lia | intros X; cbv beta in X; tauto | rewrite SEG; exact TB | lia
        | cbn [cells_size csize]; change (Z.of_nat (Z.to_nat (16 * 56) + 0)) with 896; lia |].
      intros j Hj. cbn [cells_size csize] in Hj. change (Z.of_nat (Z.to_nat (16 * 56) + 0)) with 896 in Hj.
      intros X; cbv beta in X. apply (NE (G + j)); lia. }
    pose proof RAD as RADc. unfold relay_add_contract in RADc. rewrite SEG in RADc.
    assert (EKR : RELAY_ADD_K = 8320) by reflexivity. rewrite EKR in RADc.
    unfold RELAY_ADD, G_NSRC, G_SRC, G_WAKE1, SRC_TABLE, SRC_ENTRY, G_RELAY_LO, G_LOCK, G_LOCK_HI in RADc.
    cbv zeta in RADc.
    eapply SR_bind.
    { apply (RADc L2 A2 regs5 m5 md2 (rt_malloc Fr bnd 6000) N C G ents tail).
      - reflexivity.
      - eapply cpk_of_rmid; [exact RM01234 | exact INIT2 | rewrite E5_1; apply ret_ok_even; vm_compute; reflexivity
                             | rewrite E5_4; exact HTP | rewrite SP5; Z.div_mod_to_equations; lia
                             | rewrite SP5; lia | rewrite SP5; lia | lia | rewrite SP5; lia | rewrite SP5; lia].
      - exact INIT2.
      - exact RO5.
      - exact ERRI.
      - intros a Ha. apply PLR. lia.
      - exact PLW.
      - exact LOCK5.
      - exact WAKE5.
      - exact NSRC5.
      - exact GSRC5.
      - match goal with |- context [bv_signed ?t] => replace t with (Z_to_bv 64 (n0 + 100)) by (symmetry; exact E5_10) end.
        rewrite oa_signed by lia. lia.
      - intros _. exact NR.
      - exact CASES5.
      - exact RES2.
      - match goal with |- context [bv_signed ?t] => replace t with (Z_to_bv 64 (n0 + 100)) by (symmetry; exact E5_10) end.
        rewrite oa_signed by lia. intros qs' _. rewrite TRE by lia. rewrite TRE in ROOM0 by lia.
        revert ROOM0. destruct (C =? 0); unfold roomF, RelayRunT.room_run; cbn [RelayRunT.room_from]; tauto. }
    intros c6 (L6 & A6 & regs6 & m6 & md6 & G' & rest & -> & RP6 & INIT6 & RES6 & RO6 & LOCK6 & WAKE6 &
      NEG6 & POS6).
    assert (FDv : bv_signed (getr regs5 10) = n0 + 100) by (rewrite E5_10; apply oa_signed; lia).
    assert (FDP : 0 <= bv_signed (getr regs5 10)) by lia.
    destruct (POS6 FDP) as (A06 & NSRC6 & GSRC6 & INB6 & FRG6 & LREST & TBL6 & BLK6). clear NEG6 POS6.
    destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP6) as (RM6 & PR6).
    rewrite SP5 in RM6.
    assert (ERA : forall x, (203000 + 4 <= x < 203000 + 8 \/ 202936 <= x < 202936 + 8 \/ 202960 <= x < 202960 + 8 \/
                   0 <= bv_signed (PropExec.getr regs5 10) /\ 0 < C /\ G + 56 * N <= x < G + 56 * (N + 1)) ->
                 (203004 <= x < 203008 \/ 202936 <= x < 202944 \/ 202960 <= x < 202968) \/
                 (4096 <= x /\ x < alloc_ceiling /\ ~ in_img Bm x)).
    { intros x [X|[X|[X|(_ & HC & X)]]]; [left; lia | left; lia | left; lia | right].
      destruct (GF HC) as ((F1 & F2 & F3) & _). split; [lia|]. split; [lia|].
      replace x with (G + (x - G)) by lia. apply F3. lia. }
    assert (WR5 : forall a, bv_unsigned sp - 8352 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m5 a)
      by (intros a Ha; apply SC5; unfold sk; left; exact Ha).
    assert (NE5 : forall a, bv_unsigned sp - 8352 <= a < bv_unsigned sp ->
              ~ (fun a => 203000 + 4 <= a < 203000 + 8 \/ 202936 <= a < 202936 + 8 \/ 202960 <= a < 202960 + 8 \/
                   0 <= bv_signed (PropExec.getr regs5 10) /\ 0 < C /\ G + 56 * N <= a < G + 56 * (N + 1)) a).
    { intros a Ha X. cbv beta in X. destruct (ERA a X) as [Y|(Y1 & Y2 & Y3)]; lia. }
    pose proof (rmid_widen Bm API 8320 (bv_unsigned sp - 32) 8352 (bv_unsigned sp) _ _ _ _ _ _ _ _ _ _ HM5
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR5 NE5 RM6) as RM6w.
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM01234 RM6w) as RMall.
    pose proof RMall as (HM6 & HWF6 & HBD6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC6).
    destruct (mr_model _ _ LAWS _ _ _ _ HM6) as (Hh6 & Hl6 & _).
    pose proof (oa_hi 8272 (bv_unsigned sp - 32) _ _ _ _ _ _ _ _ _ _ _ _ SEG ltac:(lia) ltac:(lia) HM1 RM1f FRM1
                  ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)
                  ltac:(intros j Hj X; cbv beta in X; cbn [cells_size csize Nat.add] in Hj; lia)) as FM2.
    pose proof (rw_cells_transport rsegs _ m2 m3 _ _ FM2 MU3r WM3r ltac:(cbn; lia)) as FM3.
    pose proof (oa_hi ALLOC_STACK (bv_unsigned sp - 32) _ _ _ _ _ _ _ _ _ _ _ _ SEG ltac:(lia) ltac:(lia) HM3 RM3 FM3
                  ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros j Hj X; exact X)) as FM4.
    pose proof (rw_cells_transport rsegs _ m4 m5 _ _ FM4 MU5r WM5r ltac:(cbn; lia)) as FM5.
    pose proof (oa_hi 8320 (bv_unsigned sp - 32) _ _ _ _ _ _ _ _ _ _ _ _ SEG ltac:(lia) ltac:(lia) HM5 RM6 FM5
                  ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)
                  ltac:(intros j Hj X; cbv beta in X; cbn [cells_size csize Nat.add] in Hj;
                        destruct (ERA _ X) as [Y|(Y1 & Y2 & Y3)]; lia)) as FM6.
    assert (I3 : forall a cs, rw_cells rsegs m3 a cs -> HA <= a -> a + Z.of_nat (cells_size cs) <= HA + 96 ->
                   rw_cells rsegs m4 a cs).
    { intros a cs H Ha Hb. apply (oa_img ALLOC_STACK (bv_unsigned sp - 32) _ _ _ _ _ _ _ _ _ _ _ _ SEG
        ltac:(unfold ALLOC_STACK; lia) HM3 RM3 H). intros j Hj. split; [apply PLR; lia | intros X; exact X]. }
    assert (I6 : forall a cs, rw_cells rsegs m5 a cs -> 202944 <= a -> a + Z.of_nat (cells_size cs) <= HA + 96 ->
                   (a + Z.of_nat (cells_size cs) <= 202948 \/ HA <= a) -> rw_cells rsegs m6 a cs).
    { intros a cs H Ha Hb Hc. apply (oa_img 8320 (bv_unsigned sp - 32) _ _ _ _ _ _ _ _ _ _ _ _ SEG ltac:(lia) HM5 RM6 H).
      intros j Hj. split; [apply PLR; lia|]. intros X. cbv beta in X.
      destruct (ERA _ X) as [Y|(Y1 & Y2 & Y3)]; [lia|]. apply Y3. exact (proj1 (PLR (a + j) ltac:(lia))). }
    pose proof (rw_cells_transport rsegs _ m2 m3 _ _ Z2c MU3r WM3r ltac:(cbn; lia)) as Z3c.
    pose proof (rw_cells_transport rsegs _ m2 m3 _ _ Z2e MU3r WM3r ltac:(cbn; lia)) as Z3e.
    pose proof (I3 _ _ Z3c ltac:(lia) ltac:(cbn; lia)) as Z4c.
    pose proof (I3 _ _ Z3e ltac:(lia) ltac:(cbn; lia)) as Z4e.
    pose proof (rw_cells_transport rsegs _ m4 m5 _ _ Z4c MU5r WM5r ltac:(cbn; lia)) as Z5c.
    pose proof (rw_cells_transport rsegs _ m4 m5 _ _ Z4e MU5r WM5r ltac:(cbn; lia)) as Z5e.
    pose proof (I6 _ _ Z5c ltac:(lia) ltac:(cbn; lia) ltac:(right; lia)) as Z6c.
    pose proof (I6 _ _ Z5e ltac:(lia) ltac:(cbn; lia) ltac:(right; lia)) as Z6e.
    pose proof (I6 _ _ HA5r ltac:(lia) ltac:(cbn; lia) ltac:(right; lia)) as HA6.
    pose proof (I6 _ _ Q5r ltac:(lia) ltac:(cbn; lia) ltac:(right; lia)) as Q6.
    assert (NFD4 : rw_cells rsegs m4 202944 [C4 (Z_to_bv 64 (n0 + 1))]).
    { apply (oa_img ALLOC_STACK (bv_unsigned sp - 32) _ _ _ _ _ _ _ _ _ _ _ _ SEG
        ltac:(unfold ALLOC_STACK; lia) HM3 RM3 NFD3r). intros j Hj. cbn in Hj.
      split; [apply PLR; lia | intros X; exact X]. }
    pose proof (rw_cells_transport rsegs _ m4 m5 _ _ NFD4 MU5r WM5r ltac:(cbn; lia)) as NFD5.
    pose proof (I6 _ _ NFD5 ltac:(lia) ltac:(cbn; lia) ltac:(left; cbn; lia)) as NFD6.
    match type of Z6c with rw_cells _ _ ?a _ => replace a with (HA + 8) in Z6c by lia end.
    match type of Z6e with rw_cells _ _ ?a _ => replace a with (HA + 48) in Z6e by lia end.
    assert (HAC : rw_cells rsegs m6 HA [C4 (Z_to_bv 64 (n0 + 100)); C4 (Z_to_bv 64 1); CB 32 (nulbytes 32);
                                       C8 (Z_to_bv 64 q); CB 48 (nulbytes 48)]).
    { apply (hg_join rsegs m6 HA (HA + 48) [C4 (Z_to_bv 64 (n0 + 100)); C4 (Z_to_bv 64 1); CB 32 (nulbytes 32);
               C8 (Z_to_bv 64 q)] [CB 48 (nulbytes 48)]); [ | exact Z6e | cbn; lia].
      apply (hg_join rsegs m6 HA (HA + 40) [C4 (Z_to_bv 64 (n0 + 100)); C4 (Z_to_bv 64 1); CB 32 (nulbytes 32)]
               [C8 (Z_to_bv 64 q)]); [ | exact Q6 | cbn; lia].
      apply (hg_join rsegs m6 HA (HA + 8) [C4 (Z_to_bv 64 (n0 + 100)); C4 (Z_to_bv 64 1)] [CB 32 (nulbytes 32)]);
        [exact HA6 | exact Z6c | cbn; lia]. }
    destruct BLK as (b1 & b2 & BLKa & BLKb).
    assert (INq : In (q, 6000) (blocks L6 A6)).
    { destruct BLK6 as [(_ & c1 & c2 & Ec & Ec2)|(_ & _ & Ec & _)].
      - assert (I2 : In (q, 6000) (c1 ++ c2)) by (rewrite Ec2, BLKa; apply in_or_app; right; left; reflexivity).
        rewrite Ec. apply in_app_iff in I2 as [I2|I2]; apply in_or_app; [left; exact I2 | right; right; exact I2].
      - rewrite Ec, BLKa. apply in_or_app. right. left. reflexivity. }
    assert (PRq : forall j, 0 <= j < Z.of_nat (Z.to_nat 6000) -> present m6 (q + j)).
    { intros j Hj. rewrite Z2Nat.id in Hj by lia.
      exact (proj1 (block_facts Bm (aa_MR API) LAWS L6 A6 m6 md6 q 6000 j HM6 INq Hj)). }
    destruct (present_rw_cells rsegs m6 q (Z.to_nat 6000) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) PRq)
      as [pj PJ].
    assert (FDv' : bv_signed (PropExec.getr regs5 10) = n0 + 100) by exact FDv.
    rewrite FDv' in TBL6.
    change (PropExec.getr regs5 1) with (getr regs5 1). rewrite E5_1.
    eapply (kseg_raw regs6 (Z_to_bv 64 84008) m6 md6); [exact Hh6 | exact Hl6 | | |].
    { unfold Regs6ss.mkR_of.
      eapply oa_tail with (B := bv_unsigned sp + -32) (junk := junk).
      - transitivity (getr regs6 2); [reflexivity|].
        exact (eq_trans (PR6 2 ltac:(unfold callee_saved; lia)) E5_2).
      - transitivity (getr regs6 10); [reflexivity | exact A06].
      - lia.
      - lia.
      - exact FM6. }
    { intros s0 ->. do 3 eexists. reflexivity. }
    intros R7 pc7 m7 regs7 HQ7 GR7.
    injection HQ7 as ER7 EP7 EM7. subst R7 pc7 m7.
    apply SR_ret. exists L6, A6, regs7, m6, md6.
    split; [f_equal; f_equal; change (reg_get regs 1) with (getr regs 1); exact (ret_pc_of_ok _ HRA)|].
    split; [exact INIT6|]. split; [exact RO6|].
    split; [intros X; rewrite FZ in X; discriminate|].
    intros i0 Hi0. rewrite FZ in Hi0. injection Hi0 as Ei. subst i0.
    change (203040 + 96 * Z.of_nat i) with HA.
    replace (100 + n0) with (n0 + 100) by lia.
    exists q, G', pj, rest.
    split.
    { apply rp_join.
      - rewrite SPE. apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMall).
        + intros a X. cbv beta in X |- *. lia.
        + intros q0 X. cbv beta in X. tauto.
      - intros r Hr. rewrite GR7. unfold callee_saved in Hr.
        assert (Hc : r = 2 \/ r = 8 \/ r = 9 \/ r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                     r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hc as [->|[->|[->|Hc]]].
        + transitivity (Z_to_bv 64 (bv_unsigned sp + -32 + 32)); [reflexivity|].
          replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
        + reflexivity.
        + reflexivity.
        + repeat (destruct Hc as [Hc|Hc];
            [subst r; match goal with |- _ = _ (Z_to_bv 5 ?n) =>
               transitivity (getr regs6 (Z_to_bv 5 n)); [reflexivity|];
               exact (eq_trans (PR6 n ltac:(unfold callee_saved; lia)) (KEEP5 n ltac:(lia))) end|]).
          subst r. match goal with |- _ = _ (Z_to_bv 5 ?n) =>
            transitivity (getr regs6 (Z_to_bv 5 n)); [reflexivity|];
            exact (eq_trans (PR6 n ltac:(unfold callee_saved; lia)) (KEEP5 n ltac:(lia))) end. }
    split.
    { destruct RES6 as (qr & LQr & RTr & LVr). pose proof (NDB L2 A2 m4 md2 HM4) as ND2.
      assert (IQ : In (q, 6000) (blocks L2 A2)) by (rewrite BLKa; apply in_or_app; right; left; reflexivity).
      destruct (sptr_of_spec L2 A2 q 6000 ND2 IQ) as (PQa & PQb).
      pose proof RP6 as (_ & _ & _ & _ & _ & PA6 & SV6 & _).
      pose proof (SV6 (sptr_of L2 A2 q) 6000 PQa ltac:(lia) ltac:(intros X; exact X)) as PQ6a.
      pose proof (PA6 (sptr_of L2 A2 q) 6000 PQa PQ6a ltac:(intros X; exact X)) as PQ6b.
      rewrite TRE in LQr, RTr by exact FDP. specialize (LVr FDP). rewrite TBE in LVr by exact FDP.
      exists (sptr_of L2 A2 q :: qr). cbn [op_add_tr]. rewrite TRE, TBE by lia.
      revert LQr RTr LVr. destruct (C =? 0) eqn:EC0; intros LQr RTr LVr;
        unfold runF, RelayRunT.run_tr in RTr |- *;
        cbn [RelayRunT.run_from RelayRunT.resolve nth length RelayRunT.nret fold_right RelayRunT.rets] in LQr, RTr, LVr |- *.
      - split; [lia|]. split; [exact RTr|]. split; [exact (conj PQ6a (eq_trans PQ6b PQb)) | exact LVr].
      - assert (C16 : 0 < C) by (apply Z.eqb_neq in EC0; lia).
        destruct (GF C16) as (_ & IG).
        pose proof (NDB L A mem md HMR) as ND0.
        destruct (sptr_of_spec L A G (16 * 56) ND0 IG) as (PGa & PGb).
        pose proof RM0123 as (_ & _ & _ & _ & _ & PA3 & SV3 & _).
        pose proof (SV3 (sptr_of L A G) (16 * 56) PGa ltac:(lia) ltac:(intros X; cbv beta in X; tauto)) as PG2a.
        pose proof (PA3 (sptr_of L A G) (16 * 56) PGa PG2a ltac:(intros X; cbv beta in X; tauto)) as PG2b.
        pose proof (sptr_of_eq L2 A2 _ _ ND2 PG2a) as SG. rewrite PG2b, PGb in SG.
        unfold known_at in LVr |- *. cbn [RelayRunT.resolve] in LVr |- *. rewrite SG in LVr.
        split; [lia|]. split; [exact RTr|]. split; [exact (conj PQ6a (eq_trans PQ6b PQb)) | exact LVr]. }
    split; [exact HAC|].
    split; [apply new_src_at; [exact SEG | exact HAC | lia | exact INq | exact FRESH | exact PJ]|].
    split; [exact NFD6|]. split; [exact LOCK6|]. split; [exact WAKE6|]. split; [exact NSRC6|].
    split; [exact GSRC6|]. split; [exact INB6|]. split; [exact FRG6|]. split; [exact LREST|].
    split; [exact TBL6|]. split; [exact INq|]. split; [exact FRESH|].
    split.
    { intros p m Hp Hm. rewrite <- BLK1, BLKb in Hp.
      destruct (blocks_mid_disjoint Bm (aa_MR API) LAWS L2 A2 m4 md2 b1 b2 q 6000 p m HM4 BLKa Hp); lia. }
    destruct BLK6 as [(EC & c1 & c2 & Ec & Ec2)|(EC & EG & Ec & Er)].
    * left. split; [exact EC|]. split.
      + intros p m Hp Hm.
        assert (Hp2 : In (p, m) (c1 ++ c2)).
        { rewrite Ec2, BLKa. rewrite <- BLK1, BLKb in Hp.
          apply in_app_iff in Hp as [Hp|Hp]; apply in_or_app; [left; exact Hp | right; right; exact Hp]. }
        destruct (blocks_mid_disjoint Bm (aa_MR API) LAWS L6 A6 m6 md6 c1 c2 G' (16 * 56) p m HM6 Ec Hp2); lia.
      + exists c1, c2, b1, b2. split; [exact Ec|]. split; [rewrite Ec2; exact BLKa|]. rewrite <- BLKb. exact BLK1.
    * right. split; [exact EC|]. split; [exact EG|]. split; [exact Er|].
      exists b1, b2. split; [rewrite Ec; exact BLKa|]. rewrite <- BLKb. exact BLK1.
Qed.

End OA.
