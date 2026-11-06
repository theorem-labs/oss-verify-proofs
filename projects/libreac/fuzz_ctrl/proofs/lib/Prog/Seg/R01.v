(* Segment R01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x132a0, 0x132a8], K132a0 -> K132ac
   (count = 0 at sp+1792, reac_box_catalogue(&count)). libreac v1.9.0: count sp+1808 -> sp+1792, frame 1936,
   the catalogue at 0x1ed30 (BOX_CATALOGUE, plain .data.tsv). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

Lemma r01_evt : reac_box_catalogue_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> 0 < spv -> spv + 1936 <= 2 ^ 64 -> spv mod 8 = 0 ->
    rw_cells rsegs m (spv + 1792) [Cells.CB 8 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x132ac) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x1ed30) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x132ac) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1792, spv + 1800)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1792) (le8 (Z_to_bv 64 11)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x132a0) fc None m (seg_rom rsegs)).
Proof.
  intros CATC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk -> Hsp0 Hsp Hal HC MI.
  pose proof (munch_refl [(spv + 1792, spv + 1800)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step.
  eapply evt_cut.
  { eapply CATC with (c := spv + 1792).
    - first [reflexivity | apply bv_eq; reflexivity].
    - right. split; [lia | exact (proj2 HC)]. }
  intros ms' (a1' & m' & E & Hif). subst ms'.
  rewrite (proj2 (Z.eqb_neq (spv + 1792) 0) ltac:(lia)) in Hif.
  destruct Hif as (Hb & MUc & WMc & _).
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. exists a1', m'. split; [reflexivity|].
  split; [|split; [exact (wmono_trans rsegs _ _ _ WM WMc) | exact Hb]].
  apply (munch_trans _ _ _ _ MU). eapply munch_weaken; [|exact MUc].
  unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
Qed.

Section R01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CATC : reac_box_catalogue_contract.

Lemma seg_R01 : Hcut B APIf ra (Inv_K132ac B APIf ra empty) -> Hcut B APIf ra (Inv_K132a0 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn7 & HCUR & HOUR) & Hs0 & Hon).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1792) 8 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r01_evt CATC) with (spv := g_S g - 1936) (junk := junk);
      [exact Hsp | lia | lia | lia | exact HC | exact (mem_inv_normalize rsegs mem)].
  - intros ms (a1' & m' & -> & MU & WM & _). do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 + 1792, g_S g - 1936 + 1800)]. split; [exact MU|]. split; [exact WM|].
    intros x Hx O. apply (sl_fp1 g (g_S g - 1936 + 1792) (g_S g - 1936 + 1800) x);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (a1' & m'' & HE & MU & _ & HZ).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    destruct HCUR as (Hc7 & Hp7 & Hn7').
    unfold RA, CUR, OURb, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split.
    { split; [exact Hn7|]. split; [split; [exact Hc7|]; split; [exact Hp7 | exact Hn7']|].
      apply (b1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HOUR].
      rewrite OUR_length. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME. lia. }
    split; [exact Hs0|]. split; [exact Hon|]. split; [reflexivity|].
    unfold q64. exact (b1_out _ _ _ _ Hrel HZ).
Qed.

End R01.
