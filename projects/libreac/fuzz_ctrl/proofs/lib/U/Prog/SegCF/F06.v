(* Segment F06 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x138a8, 0x138c4], U138a8 (v1.8 U138ac,
   0x138a8) -> U13954 (len <= 49: the parse result is 0 (#41; struct P2.1 gives k = 0), then the FV' zeros of
   v1.9: s4 (big), TF at sp+16, s3 (is_8819), s8 (Φ + 18), s9 (k), s11 (sum_ok); v1.8 zeroed s3, sp+56, s1, s7, s8,
   s10). Entered only from F04. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u4.
Import ListNotations.
Open Scope Z_scope.

Lemma f06_c : negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) = false.
Proof. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma f06_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (jt : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 0 -> 0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 16) [CB 8 jt] ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 0) (Z_to_bv 64 0) s5 s6 s7 (Z_to_bv 64 0) (Z_to_bv 64 0) s10 (Z_to_bv 64 0)
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13954) fc None m' (seg_rom rsegs) /\
         munch [(spv + 16, spv + 24)] m m' /\ wmono rsegs m m' /\ q64 m' (spv + 16) 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138a8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv jt Hsp Ha0 Hlo Hhi Hjt.
  subst sp a0.
  pose proof (munch_refl [(spv + 16, spv + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false_by f06_c.
  step. step. step. step. step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  unfold q64. exact (u4_c_bytes _ _ _ Hjt).
Qed.

Section F06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_F06 : forall j : nat, Hat B APIf ra (Inv_U13954_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U138a8_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFT & Hs & HIFS & H10 & HB).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  destruct (u4_small (g_in g) j Hs) as (Ek & Eb & E8 & Es & Et).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 16) 8 ST ltac:(lia) ltac:(lia)) as (jt & Hjt).
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 16, g_S g - 1936 + 24)]);
    [exact HFR | exact HP | u4_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply f06_evt with (spv := g_S g - 1936) (jt := jt); [exact Hsp | | lia | lia | exact Hjt].
    unfold rg in H10. rewrite H10, Ek. reflexivity.
  - intros ms (m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (m'' & HE & _ & _ & H16t).
    injection HE; intros; subst.
    assert (HK : FTK regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split|].
    + apply (u4_FT_keep g j phi regs regs' mem m' _ HFT HK MU'); u4_dj.
    + unfold FV, V7, V1, V0, V2, VC, rg. rewrite Ek, Eb, E8, Es, Et. cbn [b2z].
      rewrite !(sl_getr_eqv _ _ _ Hx).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split.
      * apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). unfold spk, fsp, SLOT_FRAME. exact H16t.
      * eapply (u4_ba _ mem); [exact HB | exact MU' |]. unfold t_B. rewrite RcParse.ctrlparse_length. u4_dj.
    + apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
Qed.

End F06.
