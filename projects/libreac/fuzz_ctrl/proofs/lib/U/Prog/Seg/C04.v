(* Segment C04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x140c0, 0x140cc], reac_box_catalogue_match(Φ, len)
   (CM_T = 0x1fcc8, K = 240). U140c0 (`li s9,0`: want_m = 0) -> U140c4; U140c4 -> U140d0 with a0 = want(Φ, len)
   (C21 C1.2, C1.3(d)). The catalogue rows are RELRO image bytes (u8_relro_mrd); the stack lies above every image
   segment (u8_rom_none). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

(* 0x140c0 `li s9,0`. *)
Lemma c04_z :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0)
                              s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x140c4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140c0) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

(* 0x140c4 .. 0x140cc: a0 = Φ (s7), a1 = len (s6), reac_box_catalogue_match returns to 0x140d0. *)
Lemma c04_m : reac_box_catalogue_match_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv f len : Z) (fb : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 f -> s6 = Z_to_bv 64 len ->
    0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> 240 <= spv -> spv < 2 ^ 64 -> spv mod 16 = 0 ->
    stk rsegs m (spv - 240) spv -> (forall a, spv - 240 <= a < spv -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ bytes_at rsegs m f fb /\ (f + 50 <= spv - 240 \/ spv <= f)) ->
    (forall a, 0x1fcc8 <= a < 0x1fcc8 + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x140d0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (RcMatch.want CAT len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x140d0) fc None m' (seg_rom rsegs) /\
         munch [(spv - 240, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140c4) fc None m (seg_rom rsegs)).
Proof.
  intros MATCH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv f len fb -> -> -> Hf Hl H0 H1 H16 ST HSR Hfb HB HRO HMI.
  step. step. step.
  eapply evt_cut.
  { eapply MATCH with (f := f) (len := len) (S := spv) (fb := fb); unfold CM_K, CM_T;
      [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H16 | lia | exact ST | exact HSR | exact Hfb |
       exact HB | exact HRO | exact HMI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _ & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x140d0)) with (Z_to_bv 64 0x140d0)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Section C04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MATCH : reac_box_catalogue_match_contract.

Lemma seg_C04_d0 : forall j : nat, Hat B APIf ra (Inv_U140d0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j.
Proof.
  intros j Hdc g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HC7 & H25)).
  pose proof HC7 as ((HLK & HFC & H23 & Hphi & H18) & HVC & HIFS).
  pose proof HFC as (_ & H21 & H22).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & HREL & _).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as HST.
  pose proof (u8_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u8_t_facts (g_in g) j) as (_ & _ & _ & _ & Hlen & _).
  pose proof (u8_phi_length (g_in g) j) as Hpl.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 - 240, g_S g - 1936)]);
    [exact HFR | exact HP | u8_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (c04_m MATCH) with (spv := g_S g - 1936) (f := phi) (len := t_len (g_in g) j)
      (fb := t_g (g_in g) j); [exact Hsp | exact H23 | exact H22 | lia | lia | lia | lia | exact H16 | | | | | |].
    + apply (u8_stk_sub _ _ _ _ _ HST); lia.
    + intros a Ha. apply u8_rom_none. unfold SL_TOP. lia.
    + exact (u8_tg_len _ _).
    + intros Hbig. split; [lia|]. split; [lia|]. split; [|lia].
      rewrite u8_g_bytes by exact Hbig.
      pose proof (u8_at_slice _ phi _ 0%nat 50%nat (bytes_at_normalize rsegs mem phi _ HMI Hphi)
                    ltac:(rewrite Hpl; lia)) as Hs.
      replace (phi + Z.of_nat 0) with phi in Hs by lia. exact Hs.
    + intros a Ha. apply (u8_relro_mrd B APIf ra empty FF mem a HREL). lia.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _).
    injection HE; intros; subst.
    apply (Hdc g). exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
    split; [|split].
    + apply (u8_CC7_keep g j phi regs regs' mem m' _ HC7 HK MU'); u8_dj.
    + unfold rg. rewrite HG. exact H25.
    + unfold rg, t_want. rewrite HG. reflexivity.
Qed.

Lemma seg_C04 : forall j : nat, Hat B APIf ra (Inv_U140d0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j.
Proof.
  intros j Hdc. pose proof (seg_C04_d0 j Hdc) as Hd0. split; [|exact Hd0].
  intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HC7 & Hw0)).
  eapply (u8_run_to B APIf ra empty FF); [exact HFR | unfold rmk; apply c04_z | intros regs' HG].
  apply (Hd0 g). exists phi. apply (u8_cut_close B APIf ra empty _ _ _ _ L A).
  - apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HFR | rewrite HG; reflexivity ..].
  - exact HP.
  - assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
    split; [exact (u8_CC7_keep g j phi regs regs' mem mem [] HC7 HK (munch_refl [] mem) I I I)|].
    unfold rg. rewrite HG, Hw0. reflexivity.
Qed.

End C04.
