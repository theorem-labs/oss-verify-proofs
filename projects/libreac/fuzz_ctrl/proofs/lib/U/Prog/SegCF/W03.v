(* Segment W03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x14090, 0x140a0], row i of row_of_block:
   0x14090 `beqz a0` not taken (DECL C1.2: declaration_of returned 1), then bcmp(blk = s8, sp+1792, 32) (BCMP).
   U14090 -> U140a4; U140b0 is not reached. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF bcmp_c bcmp_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Ltac w03_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

Lemma w03_evt : bcmp_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv blk v : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> a0 = Z_to_bv 64 1 ->
    s8 = Z_to_bv 64 blk -> 0 <= blk < 2 ^ 64 ->
    bytes_at rsegs m blk ls -> bytes_at rsegs m (spv + 1792) rs -> memcmp_model ls rs 32 = Some v ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x140a4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x140a4) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14090) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv blk v ls rs -> Hs0 Hs1 -> -> Hb HL HR Hm MI.
  step. w03_if false.
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := ls) (rs := rs) (v := v); rewrite ?MState.unsigned_lit by lia;
      first [exact HL | exact HR | exact Hm | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x140a4)) with (Z_to_bv 64 0x140a4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Section W03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BCMP : bcmp_ro_contract.

Lemma seg_W03 : forall j i : nat, Hat2 B APIf ra (Inv_U140a4_at B APIf ra empty) j i ->
  Hat2 B APIf ra (Inv_U140b0_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_U14090_at B APIf ra empty) j i.
Proof.
  intros j i H _ g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HWB & H20 & H10 & HD)).
  pose proof HWB as (HRS & Hi & H26 & H19 & H25 & Hq & Hne).
  pose proof HRS as ((HFT & HVC & HIFS) & Hsel).
  destruct (u8_rowsel (g_in g) j Hsel) as (Hk & H16' & H17' & Hlen & Hbig).
  pose proof HVC as (H24 & HTF & HB).
  rewrite Hbig in H24.
  pose proof HFT as (_ & _ & _ & Hphi & _).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (u8_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  destruct (u8_mcmp_total (t_blk (g_in g) j) (decl_i (Z.of_nat i)) 32 (u8_blk_len _ _)
              (u8_decl_len i ltac:(lia))) as (v & Hm).
  pose proof (u8_mcmp_rng _ _ _ _ Hm) as Hv.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | u8_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (w03_evt BCMP) with (spv := g_S g - 1936) (blk := phi + 18) (v := v) (ls := t_blk (g_in g) j)
      (rs := decl_i (Z.of_nat i)); [exact Hsp | lia | lia | exact H10 | exact H24 | lia | | | exact Hm |].
    + apply u8_blk_at; [|exact Hlen]. exact (bytes_at_normalize rsegs mem phi _ HMI Hphi).
    + exact (bytes_at_normalize rsegs mem _ _ HMI HD).
    + exact (u8_ro_norm mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _).
    injection HE; intros; subst.
    apply (H g). exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
    split; [|split; [|split]].
    + split; [split; [|exact Hsel]|].
      { apply (u8_CC7_keep g j phi regs regs' mem m' _ (proj1 HRS) HK MU'); exact I. }
      split; [exact Hi|].
      split; [unfold rg; rewrite HG; exact H26|].
      split; [unfold rg; rewrite HG; exact H19|].
      split; [unfold rg; rewrite HG; exact H25|].
      split; [apply (u8_q64 _ mem m' _ _ Hq MU'); exact I | exact Hne].
    + unfold rg. rewrite HG. exact H20.
    + apply (u8_ba _ mem m' _ _ HD MU'). exact I.
    + assert (E10 : YK11.getr regs' 10 = Z_to_bv 64 v) by (rewrite HG; reflexivity).
      rewrite E10, (u8_bv0 v Hv).
      exact (u8_mcmp 32 _ _ v (u8_blk_len _ _) (u8_decl_len i ltac:(lia)) Hm).
Qed.

End W03.
