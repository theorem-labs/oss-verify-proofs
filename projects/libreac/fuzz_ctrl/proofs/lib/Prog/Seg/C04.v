(* Segment C04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13d7c, 0x13d88], reac_box_catalogue_match(Φ, len).
   K13d7c (s7 = 0), K13d80 -> K13d8c.
   libreac v1.9.0 (table 5a S_C04: IDENTICAL, OLD 0x13d4c .. 0x13d58): pcs and the frame size 1920 -> 1936;
   CM_T / CM_K are reac_box_catalogue_match_c's (by name), CM_T's bytes lie in frame_RELRO's first block
   [0x1ed20, 0x1ed20 + 3680); cuts K13d4c -> K13d7c, K13d50 -> K13d80, K13d5c -> K13d8c (SlotInv.v's renames), so
   seg_C04_50 / seg_C04 are stated on the renamed cuts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcMatch SlotModel SlotInv reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma kC04z : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
                           (Z_to_bv 64 0) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d80) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d7c) fc None m ro).
Proof. intros. step. apply evt_done. reflexivity. Qed.

Lemma kC04 : reac_box_catalogue_match_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp0 f len : Z) (fb : list byte),
  x2 = Z_to_bv 64 sp0 -> x21 = Z_to_bv 64 f -> x20 = Z_to_bv 64 len ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> 272 <= sp0 -> sp0 + 1936 < 2 ^ 64 -> sp0 mod 16 = 0 ->
  stk rsegs m (sp0 - 272) sp0 -> (forall a, sp0 - 272 <= a < sp0 -> seg_rom rsegs (wa a) = None) ->
  length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ bytes_at rsegs m f fb /\ (f + 50 <= sp0 - 272 \/ sp0 <= f)) ->
  (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
  mem_inv rsegs m ->
  Exec.evt rsegs
    (fun ms' => exists R m', ms' = MS R F (Z_to_bv 64 0x13d8c) fc None m' (seg_rom rsegs) /\
       (getr R 10 = Z_to_bv 64 (want CM_T len fb) /\ getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\ getr R 4 = x4 /\
        getr R 8 = x8 /\ getr R 9 = x9 /\ getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\
        getr R 21 = x21 /\ getr R 22 = x22 /\ getr R 23 = x23 /\ getr R 24 = x24 /\ getr R 25 = x25 /\
        getr R 26 = x26 /\ getr R 27 = x27 /\
        munch [(sp0 - 272, sp0)] m m' /\ wmono rsegs m m'))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d80) fc None m (seg_rom rsegs)).
Proof.
  intros MATCH x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m sp0 f len fb E2 E21 E20 Hf Hl H0 H1 H16 ST HSR Hfb HB HRO HMI.
  subst x2 x20 x21. step. step. step.
  eapply evt_cut.
  { eapply MATCH with (f := f) (len := len) (S := sp0) (fb := fb); unfold CM_K;
      [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H16 | lia | exact ST | exact HSR | exact Hfb |
       exact HB | exact HRO | exact HMI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST').
  subst ms'. rewrite (b8_ret_pc 0x13d8c) by lia.
  apply evt_done. eexists _, _. split; [reflexivity|].
  repeat (split; [reflexivity|]). split; [exact MU | exact WM].
Qed.

Section C04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MATCH : reac_box_catalogue_match_contract.

Lemma seg_C04_50 : forall j : nat, Hat B APIf ra (Inv_K13d8c_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j.
Proof.
  intros j H5c g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HC7 & H23).
  pose proof HC7 as ((Hj & H26 & (H27 & H32 & H20) & H21 & HBphi & HO & HM7) & H18 & HVC & HI).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HF) as HST.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & HREL & _).
  pose proof alloc_ceiling_value as HAC. pose proof sl_ceil as HSL.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Hin : In (phi, t_len (g_in g) j) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_block_pos B APIf ra empty g _ L A regs mem md _ _ HF Hin) as [Hph1 Hph2].
  pose proof (b8_t_facts (g_in g) j) as (_ & _ & _ & _ & Hlen & _).
  pose proof (b8_phi_length (g_in g) j) as Hpl.
  pose proof HMI as HMI'. unfold MI in HMI'. rewrite (b8_segs B APIf ra empty FF) in HMI'.
  pose proof (mem_rel_normalize rsegs mem HMI') as HR0.
  eapply (b8_mid B APIf ra empty FF g _ L A regs mem md (Z_to_bv 64 0x13d80)
            [(g_S g - 1936 - 272, g_S g - 1936)]).
  - exact HF.
  - exact HP.
  - intros x Hx O. unfold SLOT_K, SLOT_STACK.
    destruct (Z_le_dec (g_S g - 1936 - 272) x); destruct (Z_lt_dec x (g_S g - 1936)); try lia;
      exfalso; apply O; cbn [outside]; repeat split; try exact I; lia.
  - rewrite sl_mkR_of. eapply (kC04 MATCH) with (sp0 := g_S g - 1936) (f := phi) (len := t_len (g_in g) j)
      (fb := t_g (g_in g) j).
    + exact Hsp.
    + exact H21.
    + exact H20.
    + lia.
    + nia.
    + lia.
    + lia.
    + exact H16.
    + apply (b8_stk_sub _ _ _ _ _ _ HST); lia.
    + intros a Ha. apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + apply fr50_length.
    + intros Hbig. split; [lia|]. split; [lia|]. split; [|lia].
      rewrite b8_g_bytes by exact Hbig.
      apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0)).
      replace phi with (phi + Z.of_nat 0) at 1 by lia.
      apply (b8_ba_sub rsegs mem phi _ 0 50 HBphi). lia.
    + intros a Ha. apply (b8_relro_norm B APIf ra empty FF); [exact HREL | exact HMI | unfold CM_T in Ha; lia].
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (R & m' & -> & (H10 & E2 & E3 & E4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM)).
    exists R, (Z_to_bv 64 0x13d8c), m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [rewrite E2; symmetry; exact Hsp|]. split; [exact E3 | exact E4].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HF'.
    destruct HQ as (R1 & m1 & E & (H10 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 &
                    E26 & E27 & MU & WM)).
    injection E; intros; subst.
    apply H5c. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A); [exact HF' | exact HP |].
    assert (G : forall r0, getr regs' r0 = getr R1 r0) by (intros r0; apply sl_getr_eqv; exact Hx).
    split; [|split].
    + apply (b8_CC7_munch g j phi regs' mem m' [(g_S g - 1936 - 272, g_S g - 1936)]); [| exact MU' |].
      * apply (b8_CC7_regs _ _ _ regs); [exact HC7 | rewrite G; assumption ..].
      * intros x Hx'. unfold spk, fsp, SLOT_FRAME in Hx'. cbn [outside]. repeat split; try exact I; lia.
    + unfold rg. rewrite G, E23. exact H23.
    + unfold rg, t_want. rewrite G, H10. reflexivity.
Qed.

Lemma seg_C04 : forall j : nat, Hat B APIf ra (Inv_K13d8c_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j.
Proof.
  intros j H5c. pose proof (seg_C04_50 j H5c) as H50. split; [|exact H50].
  intros g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HC7 & Hw0).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kC04z | intros regs' HG].
  apply H50. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
  - apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
  - exact HP.
  - split; [apply (b8_CC7_regs _ _ _ regs); [exact HC7 | b8rg HG ..]|].
    unfold rg. rewrite HG, Hw0. reflexivity.
Qed.

End C04.
