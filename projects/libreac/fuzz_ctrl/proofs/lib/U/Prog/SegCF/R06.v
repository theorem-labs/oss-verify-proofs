(* Segment R06 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x1340c, 0x1344c], U1340c -> U13450,
   U1364c (turn b) (n_b = 0 -> the latch U1364c; else fuzz_dup's checks #3-#5 (AF1) not taken, malloc(n_b)). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

(* #3: n_b - 1493 <u -1441 is n_b < 52 or n_b > 1492. *)
Lemma r06_c2 : forall n, 52 <= n <= 1492 ->
  bv_ltu (Z_to_bv 64 (n + -1493)) (Z_to_bv 64 (-1441)) = false.
Proof.
  intros n Hn. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. apply Z.ltb_ge. lia.
Qed.

Lemma r06z_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                t3 t4 t5 t6) F (Z_to_bv 64 0x1364c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1340c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step. if_true. apply evt_done. reflexivity.
Qed.

Lemma r06_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
    a0 = Z_to_bv 64 n -> s10 = Z_to_bv 64 0xe38f0000 -> s11 = Z_to_bv 64 36 ->
    (exists u, n = 52 + 36 * u /\ 2 <= u <= 40) ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13450) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 (Z_to_bv 64 0xe38f0000) (Z_to_bv 64 36) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x173c0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1340c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m n -> -> -> Hu.
  assert (Hn : 124 <= n <= 1492) by (destruct Hu as (u & -> & Hu); lia).
  step. if_false_by (u1_beq0 n ltac:(lia)).
  step. step. step. step. if_false_by (r06_c2 n ltac:(lia)).
  step. step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; clear - Hu; u1_by_u Hu); cbv iota
  end.
  step. step. step. step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; clear - Hu; u1_by_u Hu); cbv iota
  end.
  step. step.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Section R06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R06 : forall b, Hat B APIf ra (Inv_U13450_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_U1364c_at B APIf ra empty) b -> Hat B APIf ra (Inv_U1340c_at B APIf ra empty) b.
Proof.
  intros b H1 H0 g c (L & A & regs & mem & md & -> & HFR & HP & (HRS & H10 & HF)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (u1_RS_len (g_in g) b) as (LI & LF).
  unfold rnb, rFb in *.
  destruct (Z.eq_dec (rt_n (g_in g) (Z.of_nat b)) 0) as [Hz|Hnz].
  - (* n_b = 0: the latch, id and frag unchanged *)
    rewrite Hz in H10.
    destruct (u1_RS_zero (g_in g) b Hz) as (ER & EF).
    eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply r06z_evt. exact H10.
    + intros ms ->. do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros z Hz' O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      injection HQ; intros; subst.
      apply H0. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold RS in HRS. rewrite ER, EF.
      apply (u1_RB_keep g b _ _ regs regs' mem _ m' [] HMI (munch_refl _ _) Hrel LI LF (conj I (conj I I)));
        [|exact HRS].
      unfold u1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split.
  - (* n_b != 0: AF1, then malloc(n_b) *)
    destruct (u1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
    pose proof (u1_rtn_u (g_in g) (Z.of_nat b) Hnz) as Hu.
    pose proof HRS as (_ & _ & _ & (_ & _ & _ & _ & _ & H26 & H27) & _).
    pose proof (HF Hnz) as HO.
    eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply r06_evt; [exact H10 | exact H26 | exact H27 | exact Hu].
    + intros ms (a1' & a2' & ->). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros z Hz O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a1' & a2' & HE). injection HE; intros; subst.
      assert (HRS' : RS g b regs' m').
      { apply (u1_RB_keep g b _ _ regs regs' mem _ m' [] HMI (munch_refl _ _) Hrel LI LF (conj I (conj I I)));
          [|exact HRS].
        unfold u1_kr. rewrite !(sl_getr_eqv _ _ _ Hx).
        repeat split; symmetry; first [exact H26 | exact H27]. }
      pose proof (u1_keep [] mem _ m' _ _ HMI (munch_refl _ _) Hrel I HO) as HO'.
      assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13450) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      assert (E10 : YK11.getr regs' 10 = Z_to_bv 64 (rt_n (g_in g) (Z.of_nat b)))
        by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      assert (E21 : YK11.getr regs' 21 = Z_to_bv 64 (rt_n (g_in g) (Z.of_nat b)))
        by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      apply (u1_malloc_call B APIf ra empty FF g L A regs' m' md regs' (rt_n (g_in g) (Z.of_nat b)));
        [exact HFR' | exact HP | reflexivity | reflexivity | reflexivity | rewrite E1; vm_compute; reflexivity
        | exact E10 | lia |].
      intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 HK.
      rewrite E1. apply H1. exists res, L', A', regs'', mem'', md'.
      split; [reflexivity|]. split; [exact HF''|]. split; [exact HP''|].
      unfold RS, rnb, rFb, rg in *.
      split.
      { apply (u1_RB_mb g b _ _ regs' regs'' m' mem''); [| exact LI | exact LF | exact (u1_kr_pres _ _ RP) | exact HRS'].
        intros a Ha. apply HK. unfold spk, fsp, SLOT_FRAME in *. lia. }
      split; [exact Hnz|].
      split; [etransitivity; [exact (RP 21 ltac:(unfold callee_saved; lia)) | exact E21]|].
      split; [exact Hres10|]. split; [exact Hres0|].
      apply (u1_ba_mbyte m' mem'' _ _ HO'). rewrite HL. intros i Hi. apply HK. unfold spk, fsp, SLOT_FRAME in *. lia.
Qed.

End R06.
