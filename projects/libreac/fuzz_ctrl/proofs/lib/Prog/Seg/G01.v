(* Segment G01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x138c4, 0x138d4], K138c4 (the ingest result is 0 or
   1, so 0x138c4 is not taken (P4f)) and K138c8 -> K138d8 (memcpy(sp+192, sp+82, 72): before = FG_j).
   libreac v1.9.0 (table 5a S_G01, IDENTICAL-RENUMBER): pcs + 0xc, frag sp+82 / before sp+192 (v1.8 66 / 176), the
   frame 1936 bytes. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcIdentModel memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Open Scope Z_scope.

Lemma g01_core : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (st junk : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> mem_inv rsegs m -> length st = 72%nat ->
    bytes_at rsegs m (spv + 82) st -> rw_cells rsegs m (spv + 192) [CB 72 junk] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x138d8) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x138d8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 192, spv + 264)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' (spv + 192) st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138c8) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv st junk Hsp Hlo Hhi MI Hst Hsrc Hdst.
  subst sp.
  step. step. step. step.
  eapply evt_cut.
  { eapply MC with (src := st) (junk := junk);
      [ b5_ul; exact Hsrc | b5_ul; rewrite Hst; reflexivity | b5_ul; exact Hdst | b5_ul; lia | exact MI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & RWc & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x138d8)) with (Z_to_bv 64 0x138d8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite !MState.unsigned_lit in MUc, RWc by lia.
  replace (spv + 192 + 72) with (spv + 264) in MUc by lia.
  apply evt_done. do 15 eexists. exists m'.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|]. exact (sl_rw_bytes _ _ _ _ RWc).
Qed.

Lemma g01_evt : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv pc : Z) (st junk : list byte),
    sp = Z_to_bv 64 spv ->
    (pc = 0x138c8 \/ (pc = 0x138c4 /\ (a0 = Z_to_bv 64 0 \/ a0 = Z_to_bv 64 1))) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> mem_inv rsegs m -> length st = 72%nat ->
    bytes_at rsegs m (spv + 82) st -> rw_cells rsegs m (spv + 192) [CB 72 junk] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x138d8) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x138d8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 192, spv + 264)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' (spv + 192) st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv pc st junk Hsp Hpc Hlo Hhi MI Hst Hsrc Hdst.
  destruct Hpc as [-> | (-> & [-> | ->])].
  - exact (g01_core MC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m spv st junk Hsp Hlo Hhi MI Hst Hsrc Hdst).
  - step. b5_br false. eapply (g01_core MC); eassumption.
  - step. b5_br false. eapply (g01_core MC); eassumption.
Qed.

Section G01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MC : memcpy_contract.

Lemma seg_G01 : forall j, Hat B APIf ra (Inv_K138d8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K138c4_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K138c8_at B APIf ra empty) j.
Proof.
  intros j H.
  assert (CORE : Hat B APIf ra (fun g j c => exists pc, FCUT B APIf ra empty g pc j
      (fun phi regs m => GA g j phi regs m /\
         (pc = 0x138c8 \/ (pc = 0x138c4 /\ (rg regs 10 0 \/ rg regs 10 1)))) c) j).
  { intros g c (pc & phi & L & A & regs & mem & md & -> & HFR & HP & (HFB & HI & HG & HS) & Hpc).
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    pose proof (b5_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
    pose proof (b5_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
    pose proof (b5_nb_range (g_in g) j) as Hnb.
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 192) 72 ST ltac:(lia) ltac:(lia)) as (jk & Hjk).
    eapply (b5_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 192, g_S g - 1936 + 264)]);
      [exact HFR | exact HP | b5_fp_tac | | |].
    - rewrite sl_mkR_of.
      apply (g01_evt MC) with (spv := g_S g - 1936) (st := t_FG (g_in g) j) (junk := jk);
        [exact Hsp | exact Hpc | lia | lia | exact (mem_inv_normalize rsegs mem) | apply b5_tFG_len
        | exact (bytes_at_normalize rsegs mem _ _ HMI (proj1 HG)) | exact Hjk].
    - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & Hb).
      injection HE; intros; subst.
      assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      apply H. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [split; [|split; [|split]]|].
      + apply (b5_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); b5_dj.
      + exact (b5_IDb_keep g _ mem m' _ (b5_tIDr_len _ _) HI MU' ltac:(b5_dj)).
      + exact (b5_FGb_keep g _ mem m' _ (b5_tFG_len _ _) HG MU' ltac:(b5_dj)).
      + exact (b5_FSb_keep g _ _ regs regs' mem m' _ HS (proj1 (proj2 (proj2 (proj2 HKP)))) MU' ltac:(b5_dj)
                 ltac:(b5_dj)).
      + unfold spk, fsp, SLOT_FRAME. apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). exact Hb. }
  split.
  - intros g c (phi & L & A & regs & mem & md & E & HFR & HP & HGA & Hir & H10).
    apply CORE. exists 0x138c4, phi, L, A, regs, mem, md.
    split; [exact E|]. split; [exact HFR|]. split; [exact HP|]. split; [exact HGA|].
    right. split; [reflexivity|]. unfold rg in H10 |- *. rewrite H10.
    destruct (ING_ret (t_ID (g_in g) j) (r_addr (t_g (g_in g) j)) (r_pl (t_g (g_in g) j))) as [Er | Er];
      rewrite Er; [left | right]; reflexivity.
  - intros g c (phi & L & A & regs & mem & md & E & HFR & HP & HGA).
    apply CORE. exists 0x138c8, phi, L, A, regs, mem, md.
    split; [exact E|]. split; [exact HFR|]. split; [exact HP|]. split; [exact HGA|].
    left. reflexivity.
Qed.

End G01.
