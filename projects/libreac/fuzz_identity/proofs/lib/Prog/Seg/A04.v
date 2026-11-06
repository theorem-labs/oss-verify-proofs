From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import RcIdentModel reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sa.
Import ListNotations.
Open Scope Z_scope.

Lemma a04_ref : forall id idb pb, ingest_refused id 0 4 = true /\ ingest_ret id 0 0 4 idb pb = -1.
Proof.
  intros id idb pb. unfold ingest_ret, ingest_refused. cbn [Z.eqb negb andb]. rewrite Bool.orb_true_r.
  split; reflexivity.
Qed.

Lemma a04_evt : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (idb : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (-1) -> 0 <= spv -> spv + 368 <= 2 ^ 64 -> spv mod 2 = 0 ->
    rw_cells rsegs m (spv + 130) [Cells.CB 38 idb] ->
    evt rsegs
      (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
         ms' = MS (mkR (Z_to_bv 64 0x12f24) sp gp tp t0' t1' t2 (Z_to_bv 64 (-1)) s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12f24) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f08) fc None m (seg_rom rsegs)).
Proof.
  intros IG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv idb -> -> Hs Hsp Hev HC.
  step. step. if_false.
  step. step. step. step. step.
  destruct (a04_ref (spv + 130) idb (repeat (Z_to_bv 8 0) 4)) as [Hrf Hrt].
  eapply evt_cut.
  { eapply IG with (id := spv + 130) (ad := 0) (p := 0) (len := 4) (idb := idb) (pb := repeat (Z_to_bv 8 0) 4);
      first [ reflexivity | apply bv_eq; reflexivity | lia
            | intros _; split; [rewrite Zplus_mod, Hev; reflexivity | exact HC]
            | intros _ C; exfalso; apply C; reflexivity
            | intros _ _ C; exfalso; apply C; reflexivity ]. }
  intros ms' (t0' & t1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & _ & _ & _ & Hz & _).
  subst ms'. specialize (Hz Hrf). subst m'. rewrite Hrt.
  replace (ret_pc (Z_to_bv 64 77604)) with (Z_to_bv 64 77604) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', a1', a2', a3', a4', a5', a6', a7'. reflexivity.
Qed.

Section A04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis INGEST : reac_identity_ingest_contract.

Lemma seg_A04 : Hcut B APIf ra (Inv_K12f24 B APIf ra empty) -> Hcut B APIf ra (Inv_K12f08 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn & Hp) & HID & H10).
  destruct (sa_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sa_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SA_TOP, fsp, SLOT_FRAME in *.
  destruct (sa_rw_of_stk _ _ _ (g_S g - 368 + 130) 38 ST ltac:(lia) ltac:(lia)) as (idb & HC).
  eapply (sa_mid B APIf ra empty FF g 0 [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sa_mkR_of.
    apply (a04_evt INGEST) with (spv := g_S g - 368) (idb := idb); [exact Hsp | exact H10 | lia | lia | lia | exact HC].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 65536, g_S g - 368 + 264)]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    exact (sa_fp g).
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & HE).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; rewrite (sa_getr_eqv _ _ _ Hx); [exact Hn | exact Hp]|].
    split; [exact (proj2 (bytes_at_rel rsegs m' (normalize rsegs mem) _ _ Hrel) (bytes_at_normalize rsegs mem _ _ HMI HID))|].
    split; rewrite (sa_getr_eqv _ _ _ Hx); reflexivity.
Qed.

End A04.
