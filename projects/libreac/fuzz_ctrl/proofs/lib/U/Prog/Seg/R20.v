(* Segment R20 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x135f8, 0x13640], U135f8 (b = 1, 2) -> U13644:
   k_b = 5 passes 0x135fc (#22), the room value of AF9, the 32-turn block sum loop (head 0x13620, counter a3 = 32 - i;
   T08 at 0x13624 not taken: Φ + 18 + i does not wrap, HBR), blocksum X(b) = 0 passes 0x13640 (#23). The
   round-trip facts are RTM: u2_rtm_k5, u2_rtm_sum (Tac_u2). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

(* The loop at 0x13620, turn i (k = 32 - i turns left): a0 = Φ[18] + ... + Φ[17 + i], a1 = Φ + 18 + i,
   a2 = 2^64 - 18 - Φ, a3 = k, s8 = 32. *)
Lemma r20_loop : forall (bs : list byte) (phi : Z) (k i : nat)
  (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (1 <= k)%nat -> (i + k = 32)%nat -> 4096 <= phi -> phi + 50 < 2 ^ 63 ->
  (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  evt rsegs
    (fun ms' => exists a3' a4', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs 32))
                   (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 (18446744073709551598 - phi)) a3' a4' a5 a6 a7
                   s2 s3 s4 s5 s6 s7 (Z_to_bv 64 32) s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1363c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
             (Z_to_bv 64 (18446744073709551598 - phi)) (Z_to_bv 64 (Z.of_nat k)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (Z_to_bv 64 32) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13620) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi k. induction k as [|k IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hk Hik Hphi Hhi Hrd; [lia|].
  pose proof (Hrd i ltac:(lia)) as HR.
  pose proof (u2_psum_rng bs i) as Hps.
  step. step. u2_if_false. step. step. step. step. step.
  rewrite u2_zxb_u.
  destruct (Nat.eq_dec k 0) as [-> | Hk0].
  - assert (Ei : i = 31%nat) by lia. subst i.
    u2_if_false.
    replace (phi + 18 + Z.of_nat 31 + 1) with (phi + 50) by lia.
    rewrite <- (u2_psum_S bs 31).
    apply evt_done. do 2 eexists. reflexivity.
  - u2_if_true.
    replace (phi + 18 + Z.of_nat i + 1) with (phi + 18 + Z.of_nat (S i)) by lia.
    replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
    rewrite <- (u2_psum_S bs i).
    apply (IH (S i)); [lia | lia | lia | lia | exact Hrd].
Qed.

Lemma r20_evt : forall (bs : list byte) (phi : Z)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 5 -> s4 = Z_to_bv 64 phi -> s8 = Z_to_bv 64 32 -> 4096 <= phi -> phi + 50 < 2 ^ 63 ->
  (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  RcModel.blocksum bs = 0 ->
  evt rsegs
    (fun ms' => exists a0' a1' a2' a3' a4', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x13644) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135f8) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> -> -> Hphi Hhi Hrd Hsum.
  rewrite <- u2_blocksum in Hsum.
  step. step. if_false. step. step. step. step. step. step. step. step.
  rewrite u2_room by lia.
  eapply evt_cut.
  { replace (phi + 18) with (phi + 18 + Z.of_nat 0) by lia.
    apply (r20_loop bs phi 32 0); [lia | lia | lia | lia | exact Hrd]. }
  intros ms' (a3' & a4' & ->).
  pose proof (u2_psum_rng bs 32) as Hps.
  step. step.
  rewrite MState.unsigned_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  replace (RcModel.psum bs 32 mod 2 ^ 8) with 0 by (rewrite <- Hsum; reflexivity).
  if_false. apply evt_done. do 5 eexists. reflexivity.
Qed.

Section R20.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R20 : forall b : nat, Hat B APIf ra (Inv_U13644_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_U135f8_at B APIf ra empty) b.
Proof.
  intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & Hb12 & H10).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
  pose proof HRB as (Hb6 & _ & _ & (_ & _ & _ & H24 & _) & _ & H9 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (u2_hb B APIf ra empty FF g phi (rnb g b) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  destruct (u2_RS_len (g_in g) (S b)) as (LI & LF).
  destruct (u2_RS_012 (g_in g) b ltac:(lia)) as (E1 & E2).
  unfold rnb, rFb, rgb in *.
  destruct (u2_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
  pose proof (u2_rtm_k5 (g_in g) (Z.of_nat b) ltac:(lia)) as Hk.
  pose proof (u2_rtm_sum (g_in g) (Z.of_nat b) ltac:(lia)) as Hs.
  pose proof alloc_ceiling_value as Hac.
  pose proof (bytes_at_normalize rsegs mem phi _ HMI HF) as HFn.
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of. apply (r20_evt (skipn 18 (rt_g (g_in g) (Z.of_nat b))) phi).
    + unfold rg in H10. rewrite Hk in H10. exact H10.
    + exact H20.
    + exact H24.
    + lia.
    + lia.
    + intros j Hj. exact (u2_rd_blk _ phi (rt_F (g_in g) (Z.of_nat b)) j HFn ltac:(lia) Hj).
    + exact Hs.
  - intros ms (? & ? & ? & ? & ? & ->). do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros z _ O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & HE). injection HE; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (KR : u2_kr regs' regs).
    { unfold u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    rewrite E1, E2.
    destruct (u2_RS_len (g_in g) b) as (LI0 & LF0).
    split; [exact (u2_RB_keep g b _ _ regs regs' mem (normalize rsegs mem) m' [] HMI (munch_refl _ _) Hrel
                     LI0 LF0 I KR HRB)|].
    split; [exact Hnz|]. unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). exact H20.
Qed.

End R20.
