(* Segment R20 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x134e8, 0x13510], K134e8 (b = 1, 2) -> K13514:
   k_b = 5 passes 0x134ec, the 32-turn block sum loop (head 0x134fc, measure 32 - i) and blocksum X(b) = 0
   pass 0x13510. The two round-trip facts are RTM (slot plan 6.3 (b), (c)): b2_rtm_k5, b2_rtm_sum (Tac_b2). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b3 Tac_b2.
Import ListNotations.
Open Scope Z_scope.

(* One unfolding of psum; applied by rewriting so that no conversion unfolds psum at a numeral. *)
Lemma r20_psum_S : forall bs i,
  RcModel.psum bs (S i) = RcModel.psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

(* blocksum unfolded by rewriting: the kernel unfolds the right-hand constant first, so blocksum stands on the
   right and no conversion has to unfold Z.modulo over psum. *)
Lemma r20_blocksum : forall bs, RcModel.psum bs 32 mod 256 = RcModel.blocksum bs.
Proof. intros bs. unfold RcModel.blocksum. reflexivity. Qed.

Lemma r20_loop : forall (bs : list byte) (phi : Z) (k i : nat)
  (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (1 <= k)%nat -> (i + k = 32)%nat -> 0 <= phi -> phi + 50 < 2 ^ 64 ->
  (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  evt rsegs
    (fun ms' => exists a3', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs 32))
                   (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 (phi + 50)) a3' a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1350c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
             (Z_to_bv 64 (phi + 50)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134fc) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi k. induction k as [|k IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hk Hik Hphi Hhi Hrd; [lia|].
  pose proof (Hrd i ltac:(lia)) as HR.
  pose proof (b3_psum_rng bs i) as Hps.
  step. step. step. step.
  rewrite b3_zxb_u. rewrite b3_bv_eqb_u by lia.
  destruct (Nat.eq_dec k 0) as [-> | Hk0].
  - assert (Ei : i = 31%nat) by lia. subst i.
    replace (phi + 18 + Z.of_nat 31 + 1 =? phi + 50) with true by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota delta [negb].
    replace (phi + 18 + Z.of_nat 31 + 1) with (phi + 50) by lia.
    rewrite <- (r20_psum_S bs 31).
    apply evt_done. eexists. reflexivity.
  - replace (phi + 18 + Z.of_nat i + 1 =? phi + 50) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv beta iota delta [negb].
    replace (phi + 18 + Z.of_nat i + 1) with (phi + 18 + Z.of_nat (S i)) by lia.
    rewrite <- (r20_psum_S bs i).
    apply (IH (S i)); [lia | lia | lia | lia | exact Hrd].
Qed.

Lemma r20_evt : forall (bs : list byte) (phi : Z)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 5 -> s4 = Z_to_bv 64 phi -> 0 <= phi -> phi + 50 < 2 ^ 64 ->
  (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  RcModel.blocksum bs = 0 ->
  evt rsegs
    (fun ms' => exists a0' a1' a2' a3', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x13514) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134e8) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> -> Hphi Hhi Hrd Hsum.
  rewrite <- r20_blocksum in Hsum.
  step. step. if_false. step. step. step.
  eapply evt_cut.
  { replace (phi + 18) with (phi + 18 + Z.of_nat 0) by lia.
    apply (r20_loop bs phi 32 0); [lia | lia | lia | lia | exact Hrd]. }
  intros ms' (a3' & ->).
  pose proof (b3_psum_rng bs 32) as Hps.
  step. step.
  rewrite MState.unsigned_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  replace (RcModel.psum bs 32 mod 2 ^ 8) with 0 by (rewrite <- Hsum; reflexivity).
  if_false. apply evt_done. do 4 eexists. reflexivity.
Qed.

Lemma r20_rd : forall (m : word -> option byte) g b phi j, bytes_at rsegs m phi (rFb g b) ->
  (50 <= length (rFb g b))%nat -> (j < 32)%nat ->
  ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j (skipn 18 (rgb g b)) (Z_to_bv 8 0)].
Proof. intros m g b phi j HB HL Hj. exact (b3_rd_blk m phi (rFb g b) j HB HL Hj). Qed.

Section R20.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Lemma seg_R20 : forall b, Hat B APIf ra (Inv_K13514_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_K134e8_at B APIf ra empty) b.
Proof.
  intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (((HRB & Hn & H20 & HF) & H22) & Hb12 & H10)).
  pose proof (b2_rtm_k5 (g_in g) (Z.of_nat b) ltac:(lia)) as Hk.
  pose proof (b2_rtm_sum (g_in g) (Z.of_nat b) ltac:(lia)) as Hs.
  pose proof (b3_rF_len g b Hn) as Hlen.
  pose proof (bytes_at_bound rsegs _ _ _ HF) as Hbnd.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMI).
  pose proof (bytes_at_normalize rsegs mem phi (rFb g b) HMI HF) as HFn.
  eapply (b3_mid B APIf ra empty FF g (hb1 phi (rnb g b)) L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (b3_fp g _ x _ Hx O). apply Forall_nil.
  - rewrite sl_mkR_of. apply (r20_evt (skipn 18 (rgb g b)) phi).
    + unfold rg in H10. rewrite Hk in H10. exact H10.
    + exact H20.
    + lia.
    + lia.
    + intros j Hj. exact (r20_rd _ g b phi j HFn ltac:(lia) Hj).
    + exact Hs.
  - intros ms (? & ? & ? & ? & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & HQ). injection HQ as E1 E2 E3. subst R pc' m0'.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    unfold RID, RFG. rewrite (b3_rt_keep (g_in g) b Hb12).
    destruct (b3_RB_bytes g b _ _ regs mem m' [] HRB MU' I I I) as (B1 & B2 & B3).
    split; [|split; [exact Hn|]].
    + apply (b3_RB g b _ _ regs mem regs' m' HRB); try exact B1; try exact B2; try exact B3;
        rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.
    + unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). exact H20.
Qed.

End R20.
